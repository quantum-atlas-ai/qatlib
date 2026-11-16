/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Qatlib.Papers.GevreyGrad19.MainResults

namespace Qatlib.Papers.GevreyGrad19.MainResults

/-- The test functions have the source gradient at the origin, including dimension zero. -/
theorem testFunction_grad_zero (d : ℕ) {c ε : ℝ} (hc : 0 < c) (_hε : 0 < ε)
    {b : Fin d → ℝ} (_hb : IsVertex b) :
    grad (testFunction d c ε b) 0 = fun i => 73 * ε / (d : ℝ) * b i := by
  have hterm (j : Fin d) :
      HasFDerivAt
        (fun x : Fin d → ℝ =>
          (73 * ε * b j / (c * d)) * Real.sin (c * x j) *
            ∏ k ∈ Finset.univ.erase j, Real.cos (c * x k))
        ((73 * ε * b j / (c * d) * c) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) 0 := by
    have hcoord (k : Fin d) : HasFDerivAt (fun x : Fin d → ℝ => c * x k)
        (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) 0 :=
      (hasFDerivAt_apply (𝕜 := ℝ) k (0 : Fin d → ℝ)).const_mul c
    have hprod : HasFDerivAt (𝕜 := ℝ)
        (fun x : Fin d → ℝ => ∏ k ∈ Finset.univ.erase j, Real.cos (c * x k))
        (0 : (Fin d → ℝ) →L[ℝ] ℝ) (0 : Fin d → ℝ) := by
      simpa using HasFDerivAt.finsetProd (u := Finset.univ.erase j)
        (fun k _ => (hcoord k).cos)
    simpa [smul_smul] using
      (((hcoord j).sin.const_mul (73 * ε * b j / (c * d))).fun_mul hprod)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
  have hf : fderiv ℝ (testFunction d c ε b) 0 =
      ∑ j : Fin d, (73 * ε * b j / (c * d) * c) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j := by
    unfold testFunction
    exact hsum.fderiv
  funext i
  change iteratedFDeriv ℝ 1 (testFunction d c ε b) 0 (fun _ => Pi.single i (1 : ℝ)) = _
  rw [iteratedFDeriv_one_apply, hf]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))
  field_simp [hc.ne', hd]


end Qatlib.Papers.GevreyGrad19.MainResults
