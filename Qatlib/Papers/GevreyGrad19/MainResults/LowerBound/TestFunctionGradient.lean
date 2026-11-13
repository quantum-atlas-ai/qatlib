/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option backward.isDefEq.respectTransparency false

/-!
# Gradient of Hypercube Test Functions at the Origin

This module computes the exact gradient at the origin of the trigonometric test
functions `testFunction d c ε b` used in the Gevrey gradient-estimation lower bound
(Lemma 4.3).

## Main statements

* `testFunction_grad_zero`: `∇ f_{d,c,ε,b}(0) = (73 ε / d) b`.

## References

* [Cornelissen, 2019][Cornelissen2019], Lemma 4.3, p. 37.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults.LowerBound

open Qatlib.Papers.GevreyGrad19.MainResults

/-- **Lemma 4.3**: for `c > 0`, `ε > 0`, and a hypercube vertex `b ∈ {-1, 1}^d`,
the gradient of `testFunction d c ε b` at the origin equals `fun i => 73 * ε / d * b i`. -/
theorem testFunction_grad_zero (d : ℕ) {c ε : ℝ} (hc : 0 < c) (_hε : 0 < ε)
    {b : Fin d → ℝ} (_hb : IsVertex b) :
    grad (testFunction d c ε b) 0 = fun i => 73 * ε / (d : ℝ) * b i := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · funext i
    exact Fin.elim0 i
  funext i
  have hf : DifferentiableAt ℝ (testFunction d c ε b) 0 := by
    unfold testFunction
    fun_prop
  have hline : (fun t : ℝ => testFunction d c ε b (t • Pi.single i 1)) =
      (fun t : ℝ => (73 * ε * b i / (c * (d : ℝ))) * Real.sin (c * t)) := by
    funext t
    unfold testFunction
    rw [Finset.sum_eq_single i]
    · have hp : (∏ k ∈ Finset.univ.erase i,
          Real.cos (c * (t • Pi.single i (1 : ℝ)) k)) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
      rw [hp]
      simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have hf' : DifferentiableAt ℝ (testFunction d c ε b)
      ((0 : ℝ) • (Pi.single i 1 : Fin d → ℝ)) := by simpa using hf
  have hderiv := (hf'.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single i (1 : ℝ) : Fin d → ℝ))).deriv
  simp only [zero_smul, one_smul] at hderiv
  change deriv (fun t : ℝ => testFunction d c ε b (t • Pi.single i 1)) 0 =
    fderiv ℝ (testFunction d c ε b) 0 (Pi.single i 1) at hderiv
  change iteratedFDeriv ℝ 1 (testFunction d c ε b) 0
    (fun _ => Pi.single i (1 : ℝ)) = _
  rw [iteratedFDeriv_one_apply, ← hderiv, hline]
  have ht := (((hasDerivAt_id (0 : ℝ)).const_mul c).sin.const_mul
    (73 * ε * b i / (c * (d : ℝ)))).deriv
  simp only [id_eq] at ht
  rw [ht]
  simp only [mul_zero, Real.cos_zero, mul_one, one_mul]
  field_simp [hc.ne', Nat.cast_ne_zero.mpr hd.ne']

end Qatlib.Papers.GevreyGrad19.MainResults.LowerBound
