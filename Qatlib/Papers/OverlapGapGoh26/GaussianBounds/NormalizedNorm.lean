/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability

/-!
# Normalized Gaussian tensor norms

`normalizedNorm` rescales the operator norm of `tensorForm` by `(√N)^(r-1)`. The module proves
continuity, nonnegativity, and a dimension independent upper tail bound, using
`normalization_identity` to cancel the Gaussian tensor scale. These estimates support the
bounded norm regions in the Gaussian analysis associated with [GohMuller2026].

## Main statements

* `normalizedNorm`: The operator norm of `tensorForm A`, multiplied by `(√N)^(r-1)`.
* `normalized_tail`: For positive `r` and `N` and `t ≥ 0`, the probability that `normalizedNorm`
  exceeds `t` is at most `2(1+8(r+1))^(r+1) exp(-t²/8)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments

/-- For positive `r` and `N`, the product `√(N/N^r) * (√N)^(r-1)` equals one. -/
theorem normalization_identity {r N : ℕ} (hr : 0<r) (hN : 0<N) :
    Real.sqrt ((N:ℝ)/(N:ℝ)^r)*(Real.sqrt (N:ℝ))^(r-1)=1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [Nat.succ_sub_one]
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hp : ((Real.sqrt (N:ℝ))^k)^2=(N:ℝ)^k := by
    rw [← pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt hn.le]
  have hs : (Real.sqrt ((N:ℝ)/(N:ℝ)^(k+1))*(Real.sqrt (N:ℝ))^k)^2=1 := by
    rw [mul_pow,Real.sq_sqrt (by positivity),hp,pow_succ]
    field_simp
  have hpos : 0≤Real.sqrt ((N:ℝ)/(N:ℝ)^(k+1))*(Real.sqrt (N:ℝ))^k := by positivity
  nlinarith

/-- The operator norm of `tensorForm A`, multiplied by `(√N)^(r-1)`. -/
def normalizedNorm {r N : ℕ} (A : Tensor (r+1) N) : ℝ :=
  ‖tensorForm A‖*(Real.sqrt (N:ℝ))^(r-1)

/-- The normalized tensor norm is nonnegative. -/
theorem normalizedNorm_nonneg {r N : ℕ} (A : Tensor (r+1) N) : 0≤normalizedNorm A := by
  unfold normalizedNorm
  positivity

/-- The normalized tensor norm is a continuous function of its tensor coefficients. -/
theorem normalizedNorm_continuous (r N : ℕ) : Continuous (normalizedNorm (r:=r) (N:=N)) := by
  unfold normalizedNorm tensorForm
  fun_prop

/-- For positive `r` and `N` and `t ≥ 0`, the probability that `normalizedNorm` exceeds `t` is
at most `2(1+8(r+1))^(r+1) exp(-t²/8)`. -/
theorem normalized_tail {r N : ℕ} (hr : 0<r) (hN : 0<N) (t : ℝ) (ht : 0≤t) :
    (gaussianTensorLaw r N).real {A | t<normalizedNorm A} ≤
      (2*(1+8*(r+1):ℝ)^(r+1))*Real.exp (-t^2/8) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hS : 0<(Real.sqrt (N:ℝ))^(r-1) := by positivity
  have hid := normalization_identity hr hN
  have hset : {A : Tensor (r+1) N | t<normalizedNorm A}=
      {A : Tensor (r+1) N | 2*(t/2)*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖} := by
    ext A
    simp only [Set.mem_setOf_eq,normalizedNorm]
    conv_rhs => rw [← mul_lt_mul_iff_left₀ hS]
    have he : 2*(t/2)*Real.sqrt ((N:ℝ)/(N:ℝ)^r)*(Real.sqrt (N:ℝ))^(r-1)=t := by
      calc
        _ = t*(Real.sqrt ((N:ℝ)/(N:ℝ)^r)*(Real.sqrt (N:ℝ))^(r-1)) := by ring
        _ = t := by rw [hid,mul_one]
    rw [he]
  rw [hset]
  let B : ℝ := 1+8*(r+1)
  let c : ℝ := (r+1)*Real.log B-t^2/8
  have hB : 0<B := by dsimp [B];positivity
  have he : 2*B^(r+1)*Real.exp (-t^2/8)=2*Real.exp c := by
    rw [show B^(r+1)=Real.exp ((r+1:ℕ)*Real.log B) by rw [Real.exp_nat_mul,Real.exp_log hB],
      mul_assoc,← Real.exp_add]
    dsimp [c]
    push_cast
    ring_nf
  change _≤2*B^(r+1)*Real.exp (-t^2/8)
  rw [he]
  by_cases hc : 0≤c
  · have hp : (gaussianTensorLaw r N).real
        {A : Tensor (r+1) N | 2*(t/2)*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖}≤1 := measureReal_le_one
    have hexp : 1≤Real.exp c := Real.one_le_exp_iff.mpr hc
    linarith
  · have h := actual_tensor_norm_tail (r:=r) hN (t/2) (by positivity)
    have hex : 2*B^(N*(r+1))*Real.exp (-(t/2)^2*(N:ℝ)/2)=2*Real.exp ((N:ℝ)*c) := by
      rw [show B^(N*(r+1))=Real.exp ((N*(r+1):ℕ)*Real.log B) by rw [Real.exp_nat_mul,Real.exp_log hB],
        mul_assoc,← Real.exp_add]
      congr 2
      dsimp [c]
      push_cast
      ring
    change _≤2*B^(N*(r+1))*Real.exp (-(t/2)^2*(N:ℝ)/2) at h
    rw [hex] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    nlinarith
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
