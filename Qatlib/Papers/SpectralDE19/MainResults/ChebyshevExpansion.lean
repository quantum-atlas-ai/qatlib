/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Tactic
public import Qatlib.Papers.SpectralDE19.MainResults.ConditionNumber
public import Qatlib.Papers.SpectralDE19.MainResults.MainComplexity
public import Qatlib.Papers.SpectralDE19.MainResults.SolutionError
public import Qatlib.Papers.SpectralDE19.MainResults.StatePreparation
public import Qatlib.Papers.SpectralDE19.MainResults.SuccessProbability

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open MeasureTheory Polynomial.Chebyshev

open Qatlib.Papers.SpectralDE19.MainResults

namespace Qatlib.Papers.SpectralDE19.MainResults

section

/-- The `k`-th Chebyshev polynomial of the first kind, as a function `ℝ → ℝ`. -/
noncomputable def chebT (k : ℕ) : ℝ → ℝ := fun x => (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x

/-- Chebyshev inner product `⟨u, v⟩ = ∫ u v dμ` where `μ = measureT` is Lebesgue measure
weighted by `1/√(1-x²)` on `[-1,1]`. This is the inner product of (A.1)–(A.5). -/
noncomputable def chebInner (u v : ℝ → ℝ) : ℝ := ∫ x, u x * v x ∂Polynomial.Chebyshev.measureT

/-- Chebyshev coefficient of (A.10): `c_0 = (1/π)⟨u, T_0⟩`, `c_k = (2/π)⟨u, T_k⟩` for `k ≥ 1`. -/
noncomputable def chebCoeff (u : ℝ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (1 / Real.pi) * chebInner u (chebT 0)
  else (2 / Real.pi) * chebInner u (chebT k)

/-- `HasChebyshevExpansion u c` means that the partial sums `∑_{k ≤ M} c k * T_k` converge to
`u` in `L²(μ)`; this is the convergence statement of Lemma 7 (A.13). -/
def HasChebyshevExpansion (u : ℝ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ M ≥ N,
    ∫ x, (u x - ∑ k ∈ Finset.range (M + 1), c k * chebT k x) ^ 2
      ∂Polynomial.Chebyshev.measureT ≤ ε ^ 2

/-- The zeroth Chebyshev polynomial has squared weighted norm `π`, as in (A.1)/(A.3). -/
theorem chebInner_self_zero : chebInner (chebT 0) (chebT 0) = Real.pi := by
  unfold chebInner chebT
  simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero

/-- Every positive-degree Chebyshev polynomial has squared weighted norm `π/2`, as in (A.3). -/
theorem chebInner_self_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    chebInner (chebT k) (chebT k) = Real.pi / 2 := by
  unfold chebInner chebT
  simpa using Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hk

/-- Distinct Chebyshev polynomials are orthogonal for the weighted inner product, as in (A.2). -/
theorem chebInner_of_ne {k l : ℕ} (hkl : k ≠ l) :
    chebInner (chebT k) (chebT l) = 0 := by
  unfold chebInner chebT
  simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hkl

/-- The `k`-th Chebyshev polynomial is continuous. -/
theorem continuous_chebT (k : ℕ) : Continuous (chebT k) :=
  Polynomial.continuous _

/-- (A.12): the projection identity. The `k`-th Chebyshev coefficient of the `N`-th partial sum
equals the `k`-th coefficient of `u` itself, for every `k ≤ N`. This is the algebraic heart of
the proof of Lemma 7: it shows the partial sums are the orthogonal projections onto the span of
`T_0, …, T_N`. -/
theorem cheb_projection_inner (u : ℝ → ℝ)
    (N k : ℕ) (hk : k ≤ N) :
    chebInner (fun x => ∑ j ∈ Finset.range (N + 1), chebCoeff u j * chebT j x) (chebT k)
      = chebInner u (chebT k) := by
  have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  unfold chebInner
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_eq_single_of_mem k hmem]
    · -- the `k`-th summand contributes exactly `⟨u, T_k⟩`
      simp_rw [mul_assoc]
      rw [MeasureTheory.integral_const_mul]
      change chebCoeff u k * chebInner (chebT k) (chebT k) = chebInner u (chebT k)
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [chebCoeff, ite_eq_left rfl, chebInner_self_zero]
        field_simp
      · rw [chebCoeff, ite_eq_right hkpos.ne', chebInner_self_of_ne_zero hkpos.ne']
        field_simp
    · -- every other summand vanishes by orthogonality (A.2)
      intro j hj hjne
      simp_rw [mul_assoc]
      rw [MeasureTheory.integral_const_mul]
      change chebCoeff u j * chebInner (chebT j) (chebT k) = 0
      rw [chebInner_of_ne hjne, mul_zero]
  · -- integrability of each summand
    intro j _
    have hcont : ContinuousOn (fun x => chebT j x * chebT k x) (Set.Icc (-1) 1) :=
      (continuous_chebT j).continuousOn.mul (continuous_chebT k).continuousOn
    simpa [mul_assoc] using
      (Polynomial.Chebyshev.integrable_measureT hcont).const_mul (chebCoeff u j)

end

end Qatlib.Papers.SpectralDE19.MainResults
