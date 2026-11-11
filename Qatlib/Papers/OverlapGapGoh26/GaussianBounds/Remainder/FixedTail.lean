/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.CollisionCount

/-!
# Gaussian tails for repeated index energies

`repeated_subgaussian` bounds the subgaussian parameter of the repeated index energy at a fixed
cube vector by `(r+1)²`. The module derives absolute tail estimates for a single vector and
finite families, providing probabilistic input to the remainder analysis associated with
[GohMuller2026].

## Main statements

* `repeated_subgaussian`: For `N > 0` and a fixed cube vector, the repeated index energy is
  subgaussian with parameter `(r+1)²`.
* `repeated_finite_tail`: For `N > 0`, a finite family of cube vectors, and `a ≥ 0`, the
  probability that some repeated index energy has absolute value at least `a` is at most `2 |I|
  exp(-a²/(2(r+1)²))`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- A subgaussian moment generating function bound remains valid after increasing its
nonnegative parameter. -/
theorem subgaussian_enlarge {Ω:Type} [MeasurableSpace Ω] {P:Measure Ω} {X:Ω→ℝ}
    {c d:NNReal} (h:HasSubgaussianMGF X c P) (hcd:c≤d) : HasSubgaussianMGF X d P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    apply (h.mgf_le t).trans
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c:ℝ)≤d by exact_mod_cast hcd) (sq_nonneg t)) (by norm_num)

/-- For `N > 0` and a fixed cube vector, the repeated index energy is subgaussian with parameter
`(r+1)²`. -/
theorem repeated_subgaussian {r N : ℕ} (hN:0<N) (u:Fin N→ℝ) (hu:u∈hilbertCube N) :
    HasSubgaussianMGF (fun A:Tensor (r+1) N=>tensorEnergy (repeated A) u)
      ((r+1:NNReal)^2) (gaussianTensorLaw r N) := by
  let w := fun k : (Fin (r+1) → Fin N) => if Function.Injective k then (0:ℝ) else ∏ a, u (k a)
  have hw (k:Fin (r+1)→Fin N) : (w k)^2 ≤ if Function.Injective k then 0 else 1 := by
    by_cases hk:Function.Injective k
    · simp [w,hk]
    · simp only [w,if_neg hk]
      rw [← Finset.prod_pow]
      apply Finset.prod_le_one₀ (fun a _=>sq_nonneg _)
      intro a _
      have h:=hu (k a)
      nlinarith [h.1,h.2]
  have hs : (∑ k,(w k)^2)≤(((r+1)^2*N^r:ℕ):ℝ) := by
    calc
      _ ≤ ∑ k:Fin (r+1)→Fin N,if Function.Injective k then (0:ℝ) else 1 := Finset.sum_le_sum (fun k _=>hw k)
      _ = ((Finset.univ.filter (fun k:Fin (r+1)→Fin N=>¬Function.Injective k)).card:ℝ) := by
        have he : (fun k:Fin (r+1)→Fin N=>if Function.Injective k then (0:ℝ) else 1)=
            (fun k=>if ¬Function.Injective k then (1:ℝ) else 0) := by
          funext k
          by_cases hk:Function.Injective k <;>simp [hk]
        rw [he,Finset.sum_boole]
      _ ≤ _ := by exact_mod_cast repeated_tuple_card (r+1) N
  let v : NNReal := ((N:NNReal)^r)⁻¹
  let c : NNReal := ∑ k:Fin (r+1)→Fin N,(NNReal.mk ((w k)^2) (sq_nonneg _))*v
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc : c≤(r+1:NNReal)^2 := by
    have he : (c:ℝ)=(∑ k,(w k)^2)*((N:ℝ)^r)⁻¹ := by simp [c,v,← Finset.sum_mul]
    apply NNReal.coe_le_coe.mp
    rw [he]
    have h:=mul_le_mul_of_nonneg_right hs (by positivity : 0≤((N:ℝ)^r)⁻¹)
    push_cast at h ⊢
    refine h.trans_eq ?_
    field_simp
  have h := subgaussian_enlarge (independent_linear_subgaussian v w) hc
  convert! h using 1
  funext A
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk:Function.Injective k <;>simp [repeated,w,hk,mul_comm]

/-- For `N > 0`, a fixed cube vector, and `a ≥ 0`, the repeated index energy exceeds `a` in
absolute value with probability at most `2 exp(-a²/(2(r+1)²))`. -/
theorem repeated_fixed_tail {r N:ℕ} (hN:0<N) (u:Fin N→ℝ) (hu:u∈hilbertCube N)
    (a:ℝ) (ha:0≤a) :
    (gaussianTensorLaw r N).real {A|a≤|tensorEnergy (repeated A) u|}≤
      2*Real.exp (-a^2/(2*(r+1:ℝ)^2)) := by
  simpa only [NNReal.coe_pow,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
    subgaussian_abs_tail (repeated_subgaussian hN u hu) a ha

/-- For `N > 0`, a finite family of cube vectors, and `a ≥ 0`, the probability that some
repeated index energy has absolute value at least `a` is at most `2 |I| exp(-a²/(2(r+1)²))`. -/
theorem repeated_finite_tail {r N:ℕ} (hN:0<N) {I:Type} [Fintype I]
    (u:I→Fin N→ℝ) (hu:∀ i,u i∈hilbertCube N) (a:ℝ) (ha:0≤a) :
    (gaussianTensorLaw r N).real {A|∃i,a≤|tensorEnergy (repeated A) (u i)|}≤
      2*(Fintype.card I:ℝ)*Real.exp (-a^2/(2*(r+1:ℝ)^2)) := by
  have he : {A:Tensor (r+1) N|∃i,a≤|tensorEnergy (repeated A) (u i)|}=
      ⋃ i:I,{A|a≤|tensorEnergy (repeated A) (u i)|} := by ext A;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ i:I,2*Real.exp (-a^2/(2*(r+1:ℝ)^2)) := Finset.sum_le_sum (fun i _=>repeated_fixed_tail hN (u i) (hu i) a ha)
    _ = _ := by simp;ring
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
