/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 — low-phase spectral mass on a tree walk

Source: Ashley Montanaro, "Quantum walk speedup of backtracking algorithms",
fixed arXiv:1509.02374 (v2, 6 Oct 2015). Lemma 7 on p.10 and its proof in
Appendix A, pp.17-19.

The paper runs a discrete-time quantum walk on a rooted tree with `T` vertices and
depth `n`.  `R_A`, `R_B` are the even/odd reflection products, `Π_A`, `Π_B` their
invariant-subspace projectors, and `P_ε` the projector onto the span of
eigenvectors of `R_B R_A` whose phase `θ` satisfies `|θ| ≤ ε`.  Lemma 7 states

    ‖P_ε |φ^⊥⟩‖ = O(ε √(T n)).

The proof constructs a vector `|ξ⟩` with `Π_A|ξ⟩ = 0` and `Π_B|ξ⟩ = |φ^⊥⟩` whose
coefficients obey `|α_x| ≤ √(n/2)` for all `x`; since `|ξ⟩` ranges over the `T`
basis vectors this gives `‖|ξ⟩‖² = ∑_x |α_x|² ≤ T·n/2`.  The effective spectral gap
lemma (Lemma 3) then yields `‖P_ε|φ^⊥⟩‖ ≤ ε‖|ξ⟩‖ ≤ ε√(T n)` (absorbing `1/√2`).

This file formalises exactly that reduction, with the constant `1`.  The underlying
effective spectral gap argument is the already-proved Frozen theorem
`QuantumAlgorithm.Concepts.ConversionCore.WitnessCompile.effectiveSpectralGap`
(Lee et al. Lemma 4.2, reusing `sourcePhaseProjector`); we only add the tree walk's
coefficient/norm bookkeeping and the resulting `ε√(T n)` bound.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.WalkBacktrack15.MainResults.Lemma7

/-- Fixed arXiv:1509.02374, Appendix A, p.18: the coefficient bound `|α_x| ≤ √(n/2)`
for the constructed vector `|ξ⟩` gives `‖|ξ⟩‖² ≤ T·n/2`, because `|ξ⟩` is supported
on the `T` tree vertices. This is the quantitative content of the line
"So ‖|ξ⟩‖ = O(√(T n))" (p.19). -/
theorem source_xi_norm_sq_bound
    (X : Type) [Fintype X] (n : ℕ) (α : X → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ Real.sqrt ((n : ℝ) / 2)) :
    ‖toEuclidean_fromVec (α : X → ℂ)‖ ^ 2 ≤ (Fintype.card X : ℝ) * ((n : ℝ) / 2) := by
  have hnorm : ‖toEuclidean_fromVec (α : X → ℂ)‖ ^ 2 = ∑ x, ‖α x‖ ^ 2 := by
    simp only [toEuclidean_fromVec, PiLp.norm_sq_eq_of_L2]
  rw [hnorm]
  calc ∑ x, ‖α x‖ ^ 2 ≤ ∑ _x : X, ((n : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro x _
        have hx : ‖α x‖ ^ 2 ≤ (Real.sqrt ((n : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hα x) 2
        rwa [Real.sq_sqrt (by positivity)] at hx
    _ = (Fintype.card X : ℝ) * ((n : ℝ) / 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- Fixed arXiv:1509.02374, Appendix A, p.18: `|ξ⟩` is supported on the `T` tree
vertices with each coefficient norm at most `√(n/2)`, hence `‖|ξ⟩‖ ≤ √(T n/2)`. -/
theorem source_xi_norm_bound
    (X : Type) [Fintype X] (n : ℕ) (α : X → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ Real.sqrt ((n : ℝ) / 2)) :
    ‖toEuclidean_fromVec (α : X → ℂ)‖ ≤ Real.sqrt ((Fintype.card X : ℝ) * ((n : ℝ) / 2)) := by
  have hsq := source_xi_norm_sq_bound X n α hα
  calc ‖toEuclidean_fromVec (α : X → ℂ)‖
      = Real.sqrt (‖toEuclidean_fromVec (α : X → ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card X : ℝ) * ((n : ℝ) / 2)) := Real.sqrt_le_sqrt hsq

/-- Fixed arXiv:1509.02374, Lemma 7 (p.10), proved in Appendix A (pp.17-19).

Let `P = Π_B`, `L = Π_A` be the orthogonal projectors on the invariant subspaces of
`R_B` and `R_A`; suppose `R_B R_A = V · diag(e^{2iθ}) · V†` with phases in `(-π, π]`,
and let `P_ε = sourcePhaseProjector V angles ε` be the span of eigenvectors with
`|θ| ≤ ε`.  For any `|ξ⟩` with `Π_A |ξ⟩ = 0` and `‖|ξ⟩‖ ≤ √(T n / 2)` (the vector
constructed in Appendix A, supported on the `T` vertices with depth bound `n`), the
low-phase component of `Π_B |ξ⟩` obeys `‖P_ε (Π_B |ξ⟩)‖ ≤ ε √(T n)`.

This is Lemma 7 with the paper's `O(·)` replaced by the sharp constant `1`. -/
theorem source_lemma7
    (H : Type) [Fintype H] [DecidableEq H] (P L V : Matrix H H ℂ)
    (angles : H → ℝ) (ε : ℝ) (T n : ℕ) (ξ : QState H)
    (hP : IsOrthogonalProjector P) (hL : IsOrthogonalProjector L)
    (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hangles : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : ReflectionAbout P * ReflectionAbout L =
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I * angles h)) * Vᴴ)
    (hε : 0 ≤ ε) (hLξ : L *ᵥ ξ = 0)
    (_hcard : Fintype.card H = T)
    (hξ : ‖toEuclidean_fromVec ξ‖ ≤ Real.sqrt ((T : ℝ) * ((n : ℝ) / 2))) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles ε *ᵥ (P *ᵥ ξ))‖ ≤
      ε * Real.sqrt ((T : ℝ) * (n : ℝ)) := by
  -- Effective spectral gap lemma (Frozen, Lee et al. Lemma 4.2).
  have hgap := effectiveSpectralGap H P L V angles ε ξ hP hL hV hangles hU hε hLξ
  -- `√(T·(n/2)) = √(T·n)/√2 ≤ √(T·n)`.
  have hTn : (0 : ℝ) ≤ (T : ℝ) * (n : ℝ) := by positivity
  have hsqrt_le : Real.sqrt ((T : ℝ) * ((n : ℝ) / 2)) ≤ Real.sqrt ((T : ℝ) * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [show (0 : ℝ) ≤ (T : ℝ) by positivity, show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hξ' : ‖toEuclidean_fromVec ξ‖ ≤ Real.sqrt ((T : ℝ) * (n : ℝ)) := le_trans hξ hsqrt_le
  calc ‖toEuclidean_fromVec (sourcePhaseProjector V angles ε *ᵥ (P *ᵥ ξ))‖
      ≤ ε / 2 * ‖toEuclidean_fromVec ξ‖ := hgap
    _ ≤ ε / 2 * Real.sqrt ((T : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hξ' (by positivity)
    _ ≤ ε * Real.sqrt ((T : ℝ) * (n : ℝ)) := by
        nlinarith [Real.sqrt_nonneg ((T : ℝ) * (n : ℝ)), hε]

end Qatlib.Papers.WalkBacktrack15.MainResults.Lemma7
