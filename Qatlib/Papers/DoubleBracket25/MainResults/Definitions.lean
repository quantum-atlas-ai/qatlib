/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket25 — paper-layer source model

Fixed source: arXiv:2504.01077, *Double-bracket algorithm for quantum signal
processing without post-selection* (accepted in Quantum, 2025-12-16).

This file records the paper's state-model and parameter definitions used by all
`MainResults` claim files:

* `vecInner`/`vecNorm` — the paper's Euclidean bra-ket convention;
* `pureDM` — the pure-state density matrix `Ψ = |Ψ⟩⟨Ψ|`;
* `energy`/`energyVariance` — `E_Ψ` and `V_Ψ` of Lem. 1 (Eq. (8));
* `comm`/`bracketExp`/`phaseExp` — the elementary DB-QSP gates
  `e^{s[Ψ,H]}` and `e^{iθΨ}` of Eq. (7)/(17);
* `qspStep`/`qspIter` — the recursive state of Eq. (18);
* `sOf`/`thetaOf`/`aCoeff`/`bCoeff` — the parameters of Eq. (8), Eq. (72)-(73),
  Eq. (161)-(162).

The definitions are kept independent of any norm choice: the vector norm is the
Euclidean one built from `vecInner`, and matrix norms explicitly use the L2
operator (spectral) norm, matching the paper's `‖H‖ ≤ 1` hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.DoubleBracket25.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's bra-ket inner product `⟨u|v⟩ = ∑ᵢ conj(uᵢ) vᵢ`,
conjugate-linear in the first argument. -/
def vecInner (u v : ι → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- Euclidean vector norm `‖v‖ = √(⟨v|v⟩)`, the norm used for state vectors in
the paper (Eq. (6) and throughout). -/
def vecNorm (v : ι → ℂ) : ℝ := Real.sqrt (vecInner v v).re

/-- The pure-state density matrix `Ψ = |ψ⟩⟨ψ|`. -/
def pureDM (ψ : ι → ℂ) : Matrix ι ι ℂ := Matrix.of (fun i j => ψ i * star (ψ j))

/-- Energy mean `E_Ψ = Re⟨ψ|H|ψ⟩` of Eq. (8). -/
def energy (H : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ := (vecInner ψ (H.mulVec ψ)).re

/-- Energy variance `V_Ψ = Re⟨ψ|H²|ψ⟩ - E_Ψ²` of Eq. (8). -/
def energyVariance (H : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  (vecInner ψ ((H * H).mulVec ψ)).re - (energy H ψ) ^ 2

/-- The commutator `[A,B] = AB - BA`. -/
def comm (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

/-- The DB-QSP elementary unitary `e^{s [A,B]}` of Eq. (7). -/
def bracketExp (s : ℝ) (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((s : ℂ) • comm A B)

/-- The state-dependent reflection gate `e^{iθΨ}` of Eq. (16). -/
def phaseExp (θ : ℝ) (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp (((θ : ℂ) * Complex.I) • pureDM ψ)

/-- The coefficients `a(s), b(s)` of Eq. (12)-(13) / Eq. (72)-(73), for `H`
and pure state `ψ`. -/
def aCoeff (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (s : ℝ) : ℝ :=
  energy H ψ / Real.sqrt (energyVariance H ψ) *
      Real.sin (s * Real.sqrt (energyVariance H ψ)) +
    Real.cos (s * Real.sqrt (energyVariance H ψ))

/-- The coefficient `b(s)` of Eq. (13) / Eq. (73). -/
def bCoeff (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (s : ℝ) : ℝ :=
  -(1 / Real.sqrt (energyVariance H ψ)) *
    Real.sin (s * Real.sqrt (energyVariance H ψ))

/-- `A(s)` of Prop. B.2, Eq. (62): `sin(s√V)/√V`. -/
def idemA (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (s : ℝ) : ℝ :=
  Real.sin (s * Real.sqrt (energyVariance H ψ)) / Real.sqrt (energyVariance H ψ)

/-- `B(s)` of Prop. B.2, Eq. (62): `(1 - cos(s√V))/V`. -/
def idemB (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (s : ℝ) : ℝ :=
  (1 - Real.cos (s * Real.sqrt (energyVariance H ψ))) / energyVariance H ψ

/-- The duration `s(E,V)` of Eq. (161), for polynomial root `z ∈ ℂ`. -/
def sOf (E V : ℝ) (z : ℂ) : ℝ :=
  -(1 / Real.sqrt V) *
    Real.arccos (‖((E : ℂ) - z)‖ / Real.sqrt (V + ‖((E : ℂ) - z)‖ ^ 2))

/-- The angle `θ(E,V)` of Eq. (162), `arg((E-z)/|E-z|)`. -/
def thetaOf (E : ℝ) (z : ℂ) : ℝ :=
  Complex.arg (((E : ℂ) - z) / (‖((E : ℂ) - z)‖ : ℂ))

/-- The maximal characteristic instability scale `η` of Prop. C.4/C.5. -/
def instabilityScale (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (z : ℂ) (E' V' : ℝ) : ℝ :=
  max (1 / Real.sqrt (energyVariance H ψ))
    (max (1 / Real.sqrt V')
      (max (1 / ‖energy H ψ - z‖)
        (max (1 / ‖E' - z‖) (1 + ‖z‖))))

/-- A single recursive DB-QSP step `e^{iθΨ} e^{s[Ψ,H]} |ψ⟩` of Eq. (18). -/
def qspStep (H : Matrix ι ι ℂ) (θ s : ℝ) (ψ : ι → ℂ) : ι → ℂ :=
  (phaseExp θ ψ).mulVec ((bracketExp s (pureDM ψ) H).mulVec ψ)

/-- The recursive DB-QSP state of Eq. (18), with parameter sequences `θ, s` and
initial state `ψ₀`: `|Ψ₀⟩ = |ψ₀⟩`, `|Ψ_{k+1}⟩ = e^{iθ_k Ψ_k} e^{s_k [Ψ_k,H]} |Ψ_k⟩`. -/
def qspIter (H : Matrix ι ι ℂ) (θ s : ℕ → ℝ) (ψ₀ : ι → ℂ) : ℕ → ι → ℂ
  | 0 => ψ₀
  | n + 1 => qspStep H (θ n) (s n) (qspIter H θ s ψ₀ n)

/-- The group-commutator unitary `G_k` of Alg. 1 / Eq. (102):
`e^{isΨ} e^{isH} e^{-isΨ} e^{-isH}`. -/
def groupComm (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp (((s : ℂ) * Complex.I) • pureDM ψ) *
    NormedSpace.exp (((s : ℂ) * Complex.I) • H) *
    NormedSpace.exp (((-s : ℂ) * Complex.I) • pureDM ψ) *
    NormedSpace.exp (((-s : ℂ) * Complex.I) • H)

/-- One DB-QSP step of Eq. (102)/(106): apply `G_k^N` after the reflection. -/
def dbspStep (H : Matrix ι ι ℂ) (θ sN : ℝ) (N : ℕ) (ψ : ι → ℂ) : ι → ℂ :=
  (phaseExp θ ψ).mulVec (((groupComm H ψ sN) ^ N).mulVec ψ)

/-- The recursive DB-QSP state of Eq. (106). -/
def dbspIter (H : Matrix ι ι ℂ) (θ sN : ℕ → ℝ) (N : ℕ) (ψ₀ : ι → ℂ) : ℕ → ι → ℂ
  | 0 => ψ₀
  | n + 1 => dbspStep H (θ n) (sN n) N (dbspIter H θ sN N ψ₀ n)

/-- Product `∏_{k<K}(H - z_k I)` of the polynomial roots, built recursively to
avoid requiring commutativity of the matrix ring. -/
def polyProd (H : Matrix ι ι ℂ) (z : ℕ → ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | n + 1 => polyProd H z n * (H - z n • (1 : Matrix ι ι ℂ))

/-- The leading-coefficient-root polynomial `p(H) = a_K ∏_{k}(H - z_k I)` of
Eq. (15). -/
def polyEval (H : Matrix ι ι ℂ) (aK : ℂ) (K : ℕ) (z : ℕ → ℂ) : Matrix ι ι ℂ :=
  aK • polyProd H z K

/-- Big-O of a real sequence with a uniform constant, used to state Thm. 3. -/
def IsBigOSeq (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, |f K| ≤ C * |g K|

end Qatlib.Papers.DoubleBracket25.MainResults
