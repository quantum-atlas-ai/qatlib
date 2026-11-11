/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Multidimensional quantum walks: shared framework model

This file fixes the semantic model used by the paper-layer formalisation of
S. Jeffery and S. Zur, *Multidimensional Quantum Walks, with Application to
`k`-Distinctness* (arXiv:2208.13492, fixed version of 2022-11-01).

The paper works with a finite-dimensional complex inner-product space `H`
(Definition 3.1), orthogonal projectors onto subspaces `A = span Ψ_A`,
`B = span Ψ_B`, the two-reflection unitary `U_AB = (2Π_A - I)(2Π_B - I)`
(equation (2)), and the spectral projector `Λ_Θ` onto the eigenphases of
`U_AB` with `|θ| ≤ Θ` (Definition 3.1 and the paragraph after Definition 3.2).

We model

* `H` as a finite-dimensional complex normed inner-product space `E`;
* the projectors as Mathlib's `Submodule.starProjection` for submodules
  `A B : Submodule ℂ E`;
* the initial state `|ψ₀⟩` and the witness vectors as elements of `E`;
* quantum subroutines (Definition 2.5) as finite sequences of unitary linear
  isometric equivalences on `EuclideanSpace ℂ Z` with basis kets `|z⟩`;
* the paper's `polylog`/`Õ` cost convention as the predicate `SoftO`.

Gate-level synthesis is *not* rebuilt here: cost statements are recorded as
existence of the paper's subroutine objects together with the paper's stated
cost bounds.  Every such statement is flagged in its docstring.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped InnerProductSpace BigOperators
open Complex

namespace Qatlib.Papers.MultiDimWalk22.MainResults

/-! ## Asymptotic cost notation (paper §3, `polylog` and `Õ`) -/

/-- `SoftO cost bound size` is the paper's `Õ` notation: `cost` is at most
`bound` times a polylogarithmic factor in `size`.  The paper uses this for all
complexity claims, e.g. `Õ(1)`, `Õ(n^{5/7})`, `Õ(√(n/m₂))`. -/
def SoftO (cost bound size : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 ≤ c ∧ cost ≤ C * bound * (max 1 (Real.log size)) ^ c

/-- A cost is `polylog`-bounded in `size` when it is `Õ(1)`. -/
def PolylogCost (cost size : ℝ) : Prop := SoftO cost 1 size

/-- The paper's `O` notation (without suppressing polylogarithms). -/
def BigO (cost bound : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ cost ≤ C * bound

/-- The paper's `n^{-κ}` error convention for a constant `κ ≥ 0`. -/
def InvPow (n κ : ℝ) : ℝ := n ^ (-κ)

/-! ## Quantum states and subroutines (Definition 2.5) -/

/-- The computational Hilbert space `span{|z⟩ : z ∈ Z}` of a finite register
set `Z`, realised as `EuclideanSpace ℂ Z`. -/
abbrev QState (Z : Type*) [Fintype Z] := EuclideanSpace ℂ Z

/-- The computational basis ket `|z⟩`. -/
def ket {Z : Type*} [Fintype Z] [DecidableEq Z] (z : Z) : QState Z :=
  EuclideanSpace.single z 1

/-- The computational basis ket `|z⟩` has unit norm. -/
@[simp] theorem ket_norm {Z : Type*} [Fintype Z] [DecidableEq Z] (z : Z) : ‖ket z‖ = 1 := by
  simp [ket]

/-- A quantum subroutine in the sense of Definition 2.5: a finite sequence
`U₀, …, U_{Tmax-1}` of unitaries on a finite register space. -/
structure Subroutine (Z : Type*) [Fintype Z] where
  /-- The number `Tmax` of unitaries in the sequence. -/
  Tmax : ℕ
  /-- The unitary applied at each time step.  Steps past `Tmax` are unused. -/
  U : ℕ → QState Z ≃ₗᵢ[ℂ] QState Z

namespace Subroutine

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The state obtained from `x` after `t` steps of the subroutine. -/
def run (S : Subroutine Z) : ℕ → QState Z → QState Z
  | 0, x => x
  | t + 1, x => S.U t (S.run t x)

/-- Definition 2.5, condition 2 (paper equation (7)): the subroutine sends the
basis ket `|x⟩` to `|f x⟩` in `T x` steps up to squared `L²` error `ε x`. -/
def Computes (S : Subroutine Z) (f : Z → Z) (T : Z → ℕ) (ε : Z → ℝ) : Prop :=
  ∀ x, ‖S.run (T x) (ket x) - ket (f x)‖ ^ 2 ≤ ε x

/-- Definition 2.5 restricted to a set `X` of inputs, with a target map `f`
that may depend on the full input.  This is the form used for the uniform
transition subroutines of Sections 4 and 5. -/
def ComputesOn (S : Subroutine Z) (X : Set Z) (f : Z → Z) (T : Z → ℕ) (ε : Z → ℝ) :
    Prop :=
  ∀ x ∈ X, ‖S.run (T x) (ket x) - ket (f x)‖ ^ 2 ≤ ε x

end Subroutine

/-! ## Decision algorithms -/

/-- A decision algorithm for a family of inputs: its (query or total) cost,
its time complexity, and the probability with which it accepts each input.
Algorithmic existence claims of the paper are stated as existence of an
element of this structure together with the paper's cost bounds. -/
structure DecisionAlgorithm (Input : Type*) where
  /-- The query (or total) complexity advertised by the paper. -/
  cost : ℝ
  /-- The time complexity advertised by the paper. -/
  time : ℝ
  /-- The probability that the algorithm accepts input `x`. -/
  acceptProb : Input → ℝ

namespace DecisionAlgorithm

/-- Bounded-error decidability of a promise problem `p`: accept with
probability at least `2/3` when `p` holds and at most `1/3` otherwise. -/
def BoundedError {Input : Type*} (p : Input → Prop) (A : DecisionAlgorithm Input) : Prop :=
  ∀ x, (p x → 2 / 3 ≤ A.acceptProb x) ∧ (¬ p x → A.acceptProb x ≤ 1 / 3)

end DecisionAlgorithm

/-! ## Phase-estimation parameters and witnesses (Definitions 3.1, 3.2, 3.5) -/

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Definition 3.1: the parameters `(H, |ψ₀⟩, Ψ_A, Ψ_B)` of a phase-estimation
algorithm.  `A` and `B` are the spans of `Ψ_A` and `Ψ_B`; the paper assumes
`|ψ₀⟩ ⟂ Ψ_B`, recorded as `ψ₀ ∈ Bᗮ`. -/
structure PhaseEstParams where
  /-- The subspace `A = span Ψ_A`. -/
  A : Submodule ℂ E
  /-- The subspace `B = span Ψ_B`. -/
  B : Submodule ℂ E
  /-- The initial state `|ψ₀⟩`. -/
  psi0 : E
  norm_psi0 : ‖psi0‖ = 1
  /-- `|ψ₀⟩` is orthogonal to every vector in `Ψ_B`, written `ψ₀ ∈ Bᗮ`. -/
  psi0_mem_orthogonal : psi0 ∈ Bᗮ

/-- Definition 3.5: a `δ`-positive witness `|w⟩`: non-zero overlap with
`|ψ₀⟩`, and almost orthogonal to `A` and `B` in the relative sense
`‖Π_A w‖² ≤ δ‖w‖²`, `‖Π_B w‖² ≤ δ‖w‖²`. -/
def IsPositiveWitness (P : PhaseEstParams E) (δ : ℝ) (w : E) : Prop :=
  inner ℂ P.psi0 w ≠ 0 ∧
    ‖P.A.starProjection w‖ ^ 2 ≤ δ * ‖w‖ ^ 2 ∧
    ‖P.B.starProjection w‖ ^ 2 ≤ δ * ‖w‖ ^ 2

/-- Definition 3.2: a `δ`-negative witness `(|w_A⟩, |w_B⟩)`:
`|ψ₀⟩ = |w_A⟩ + |w_B⟩`, `|w_A⟩` is `δ`-close to `A` and `|w_B⟩` is `δ`-close to
`B` in the absolute squared norm sense `‖(I - Π_A) w_A‖² ≤ δ`. -/
def IsNegativeWitness (P : PhaseEstParams E) (δ : ℝ) (wA wB : E) : Prop :=
  P.psi0 = wA + wB ∧
    ‖wA - P.A.starProjection wA‖ ^ 2 ≤ δ ∧
    ‖wB - P.B.starProjection wB‖ ^ 2 ≤ δ

/-- Lemma 3.3 (Effective Spectral Gap Lemma, [31]): for `|ψ_A⟩ ∈ A`,
`‖Λ_Θ (I - Π_B) |ψ_A⟩‖ ≤ (Θ/2)‖|ψ_A⟩‖`.  We record it as the defining
property of the spectral projector family `Λ`. -/
structure EffectiveGapModel (P : PhaseEstParams E) where
  /-- The spectral projector `Λ_Θ` onto eigenphases `|θ| ≤ Θ` of `U_AB`. -/
  Λ : ℝ → E →L[ℂ] E
  /-- `Λ_Θ` is a contraction (it is an orthogonal projector). -/
  contract : ∀ Θ, ‖Λ Θ‖ ≤ 1
  /-- Lemma 3.3, in the form used by the paper's negative analysis. -/
  spectral_gap : ∀ (Θ : ℝ), 0 < Θ → Θ < Real.pi → ∀ v ∈ P.A,
    ‖Λ Θ ((1 - P.B.starProjection) v)‖ ≤ Θ / 2 * ‖v‖

/-! ## Lemma 3.4: negative analysis -/

/-- **Lemma 3.4 (Negative Analysis)**, arXiv:2208.13492 p. 19.  Fix `δ ≥ 0`
and `Θ ∈ (0, π)`.  If `(|w_A⟩, |w_B⟩)` is a `δ`-negative witness for
`(H, |ψ₀⟩, Ψ_A, Ψ_B)`, then
`‖Λ_Θ |ψ₀⟩‖ ≤ (Θ/2)‖|w_A⟩‖ + 2√δ`.

The proof follows the paper line by line: apply Lemma 3.3 to `Π_A |w_A⟩`,
split off the `(I - Π_A)` remainder, use `|ψ₀⟩ = |w_A⟩ + |w_B⟩` and
`|ψ₀⟩ ⟂ B`, and bound both remainders by `√δ`. -/
theorem lemma3_4_negative_analysis (P : PhaseEstParams E) (M : EffectiveGapModel E P)
    (δ Θ : ℝ) (hδ : 0 ≤ δ) (hΘ0 : 0 < Θ) (hΘπ : Θ < Real.pi)
    (wA wB : E) (hw : IsNegativeWitness E P δ wA wB) :
    ‖M.Λ Θ P.psi0‖ ≤ Θ / 2 * ‖wA‖ + 2 * Real.sqrt δ := by
  obtain ⟨hpsi, hA, hB⟩ := hw
  set PA := P.A.starProjection with hPA
  set PB := P.B.starProjection with hPB
  set L := M.Λ Θ with hL
  -- The two absolute error bounds, converted to norms.
  have hAle : ‖wA - PA wA‖ ≤ Real.sqrt δ := by
    rw [← Real.sqrt_sq (norm_nonneg (wA - PA wA))]
    exact Real.sqrt_le_sqrt hA
  have hBle : ‖wB - PB wB‖ ≤ Real.sqrt δ := by
    rw [← Real.sqrt_sq (norm_nonneg (wB - PB wB))]
    exact Real.sqrt_le_sqrt hB
  -- `|ψ₀⟩ ⟂ B` implies `Π_B |ψ₀⟩ = 0`.
  have hPBpsi : PB P.psi0 = 0 := by
    exact Submodule.eq_starProjection_of_mem_orthogonal (K := P.B) (u := P.psi0) (v := 0)
      (Submodule.zero_mem P.B) (by simpa using P.psi0_mem_orthogonal)
  -- `(I - Π_B)` is the orthogonal projector onto `Bᗮ`.
  have hI_PB : (1 - PB : E →L[ℂ] E) = P.Bᗮ.starProjection := by
    rw [Submodule.starProjection_orthogonal]
    rfl
  -- Step 1: `‖Λ (I-Π_B) wA‖ ≤ (Θ/2)‖wA‖ + ‖wA - Π_A wA‖`.
  have hstep1 : ‖L ((1 - PB) wA)‖ ≤ Θ / 2 * ‖wA‖ + ‖wA - PA wA‖ := by
    -- Apply Lemma 3.3 to `Π_A wA ∈ A`.
    have hmem : PA wA ∈ P.A := Submodule.starProjection_apply_mem P.A wA
    have hgap := M.spectral_gap Θ hΘ0 hΘπ (PA wA) hmem
    have hgap' : ‖L ((1 - PB) (PA wA))‖ ≤ Θ / 2 * ‖wA‖ := by
      refine hgap.trans ?_
      gcongr
      exact Submodule.norm_starProjection_apply_le (K := P.A) wA
    -- `(I-Π_B) wA = (I-Π_B)(Π_A wA) + (I-Π_B)(wA - Π_A wA)`.
    have hZ : ‖L ((1 - PB) (wA - PA wA))‖ ≤ ‖(1 - PB) (wA - PA wA)‖ := by
      calc ‖L ((1 - PB) (wA - PA wA))‖
          ≤ ‖L‖ * ‖(1 - PB) (wA - PA wA)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖(1 - PB) (wA - PA wA)‖ := by
            gcongr
            exact M.contract Θ
        _ = ‖(1 - PB) (wA - PA wA)‖ := one_mul _
    have hdecomp : (1 - PB) wA = (1 - PB) (PA wA) + (1 - PB) (wA - PA wA) := by
      rw [show (1 - PB) (PA wA) + (1 - PB) (wA - PA wA)
            = (1 - PB) (PA wA + (wA - PA wA)) from
            (ContinuousLinearMap.map_add _ _ _).symm]
      congr 1
      abel
    calc ‖L ((1 - PB) wA)‖
        = ‖L ((1 - PB) (PA wA)) + L ((1 - PB) (wA - PA wA))‖ := by rw [hdecomp, map_add]
      _ ≤ ‖L ((1 - PB) (PA wA))‖ + ‖L ((1 - PB) (wA - PA wA))‖ := norm_add_le _ _
      _ ≤ Θ / 2 * ‖wA‖ + ‖(1 - PB) (wA - PA wA)‖ :=
            add_le_add hgap' hZ
      _ = Θ / 2 * ‖wA‖ + ‖P.Bᗮ.starProjection (wA - PA wA)‖ := by rw [hI_PB]
      _ ≤ Θ / 2 * ‖wA‖ + ‖wA - PA wA‖ := by
            gcongr
            exact Submodule.norm_starProjection_apply_le (K := P.Bᗮ) (wA - PA wA)
  -- Step 2: `‖Λ ψ₀‖ ≤ ‖Λ (I-Π_B) wA‖ + ‖wB - Π_B wB‖`.
  have hstep2 : ‖L P.psi0‖ ≤ ‖L ((1 - PB) wA)‖ + ‖wB - PB wB‖ := by
    have hpsi' : P.psi0 = wA + wB := hpsi
    have hPB' : PB P.psi0 = 0 := hPBpsi
    have hrewrite : P.psi0 = (1 - PB) P.psi0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPB', sub_zero]
    calc ‖L P.psi0‖ = ‖L ((1 - PB) (wA + wB))‖ := by rw [hrewrite, hpsi']
      _ = ‖L ((1 - PB) wA + (1 - PB) wB)‖ := by rw [ContinuousLinearMap.map_add]
      _ = ‖L ((1 - PB) wA) + L ((1 - PB) wB)‖ := by rw [ContinuousLinearMap.map_add]
      _ ≤ ‖L ((1 - PB) wA)‖ + ‖L ((1 - PB) wB)‖ := norm_add_le _ _
      _ ≤ ‖L ((1 - PB) wA)‖ + ‖(1 - PB) wB‖ := by
            gcongr
            calc ‖L ((1 - PB) wB)‖
                ≤ ‖L‖ * ‖(1 - PB) wB‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖(1 - PB) wB‖ := by
                  gcongr
                  exact M.contract Θ
              _ = ‖(1 - PB) wB‖ := one_mul _
      _ = ‖L ((1 - PB) wA)‖ + ‖wB - PB wB‖ := by
            have hb : P.Bᗮ.starProjection wB = wB - PB wB := by
              rw [← hI_PB]
              rfl
            rw [hI_PB, hb]
  nlinarith [hstep1, hstep2, hAle, hBle]

end Qatlib.Papers.MultiDimWalk22.MainResults
