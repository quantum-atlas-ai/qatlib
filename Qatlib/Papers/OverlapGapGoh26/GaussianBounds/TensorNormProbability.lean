/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SphereNets.Multilinear
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteTupleTail

/-!
# Gaussian operator norm bounds for tensor forms

`actual_tensor_norm_tail` transfers finite tuple tail estimates to the operator norm of
`tensorForm`. The explicit threshold `goodNormConstant` yields failure probability at most `2
exp(-N)`, giving a useful norm region for the Gaussian dynamics analysis associated with
[GohMuller2026].

## Main statements

* `actual_tensor_norm_tail`: For `N > 0` and `a ≥ 0`, the probability that the tensor operator
  norm exceeds `2a√(N/N^r)` is at most `2(1+8(r+1))^(N(r+1)) exp(-a²N/2)`.
* `actual_tensor_norm_good`: For `N > 0`, the tensor operator norm exceeds `goodNormConstant r *
  √(N/N^r)` with probability at most `2 exp(-N)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteTupleTail
open Qatlib.Foundations.MatrixGeometry.SphereNets.Multilinear
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability

/-- For `N > 0` and `a ≥ 0`, the probability that the tensor operator norm exceeds `2a√(N/N^r)`
is at most `2(1+8(r+1))^(N(r+1)) exp(-a²N/2)`. -/
theorem actual_tensor_norm_tail {r N : ℕ} (hN : 0<N) (a : ℝ) (ha : 0≤a) :
    (gaussianTensorLaw r N).real
      {A | 2*a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖} ≤
      2*(1+8*(r+1):ℝ)^(N*(r+1))*Real.exp (-a^2*(N:ℝ)/2) := by
  let q := r+1
  have hq : (0:ℝ)<q := by dsimp [q]; positivity
  let ε : ℝ := 1/(2*q)
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨s,hs,hcover,hcard⟩ := Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet.sphere_quantitative_net
    (E:=EuclideanSpace ℝ (Fin N)) ε hε
  let J := Fin q→s
  let z : J→Fin q→EuclideanSpace ℝ (Fin N) := fun v i=>(v i : EuclideanSpace ℝ (Fin N))
  have hz : ∀ j i,‖z j i‖=1 := fun j i=>hs _ (j i).2
  have hb : ((1+ε/4)/(ε/4))=1+8*q := by dsimp [ε]; field_simp; ring
  have hcard' : (s.card:ℝ)≤(1+8*q)^N := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin,hb] using hcard
  have hJ : (Fintype.card J:ℝ)≤(1+8*q)^(N*q) := by
    calc
      _ = (s.card:ℝ)^q := by simp only [J,Fintype.card_fun,Fintype.card_coe,Nat.cast_pow,Fintype.card_fin]
      _ ≤ ((1+8*q)^N)^q := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard' q
      _ = _ := by rw [← pow_mul]
  have hsub : {A : Qatlib.Foundations.MatrixAlgebra.TensorDiff.Tensor (r+1) N | 2*a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖} ⊆
      {A | ∃ j:J,a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)≤|tensorForm A (z j)|} := by
    intro A hA
    change 2*a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖ at hA
    change ∃ j:J,a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)≤|tensorForm A (z j)|
    by_contra! hbad
    have hn := opnorm_le_twice_net (show 0<q by omega) (tensorForm A) s
      (a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)) (by positivity) hs hcover
      (fun j=>(hbad j).le)
    dsimp only [q,z] at hn
    linarith
  have ht := actual_finite_tuple_scaled_tail hN z hz a ha
  apply (measureReal_mono hsub).trans
  apply ht.trans
  have hmul := mul_le_mul_of_nonneg_right hJ (Real.exp_nonneg (-a^2*(N:ℝ)/2))
  dsimp only [q] at hmul
  simp only [Nat.cast_add,Nat.cast_one] at hmul
  nlinarith

/-- The degree dependent threshold `2√(2((r+1)log(1+8(r+1))+1))` for the Gaussian tensor
operator norm. -/
def goodNormConstant (r : ℕ) : ℝ :=
  2*Real.sqrt (2*((r+1)*Real.log (1+8*(r+1))+1))

/-- For `N > 0`, the tensor operator norm exceeds `goodNormConstant r * √(N/N^r)` with
probability at most `2 exp(-N)`. See [GohMuller2026]. -/
theorem actual_tensor_norm_good {r N : ℕ} (hN : 0<N) :
    (gaussianTensorLaw r N).real
      {A | goodNormConstant r*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖} ≤
      2*Real.exp (-(N:ℝ)) := by
  let B : ℝ := 1+8*(r+1)
  let a : ℝ := Real.sqrt (2*((r+1)*Real.log B+1))
  have hB : 0<B := by dsimp [B]; positivity
  have hBlog : 0≤Real.log B := Real.log_nonneg (by
    dsimp [B]
    have hr : (0:ℝ)≤r := Nat.cast_nonneg r
    linarith)
  have ha : 0≤a := Real.sqrt_nonneg _
  have ha2 : a^2=2*((r+1)*Real.log B+1) := by
    apply Real.sq_sqrt
    positivity
  have ht := actual_tensor_norm_tail (r:=r) hN a ha
  change (gaussianTensorLaw r N).real
    {A | 2*a*Real.sqrt ((N:ℝ)/(N:ℝ)^r)<‖tensorForm A‖}≤_
  apply ht.trans
  have hp : B^(N*(r+1))=Real.exp ((N*(r+1):ℕ)*Real.log B) := by
    rw [Real.exp_nat_mul,Real.exp_log hB]
  change 2*B^(N*(r+1))*Real.exp (-a^2*(N:ℝ)/2)≤_
  rw [hp,mul_assoc,← Real.exp_add]
  have he : ((N*(r+1):ℕ):ℝ)*Real.log B+-a^2*(N:ℝ)/2=-(N:ℝ) := by
    rw [ha2,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring
  rw [he]
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorNormProbability
