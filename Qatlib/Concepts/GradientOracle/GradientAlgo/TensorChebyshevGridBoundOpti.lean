/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorMomentBounds

/-!
# Tensor concentration on finite symmetric grids

This module proves `tensorChebyshevGridBound` from second-moment estimates for tensor
polynomials on symmetric bounded grids. The counting estimate supplies the concentration step in
the analytic gradient analysis associated with [GilyenArunachalamWiebe2019].

## Main statements

* `tensorChebyshevGridBound`: the stated degree-`k` threshold is exceeded at no more than `|S|^d
  / r^(2*k)` points.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- Proves the tensor-polynomial tail count on nonempty symmetric grids in `[-1/2, 1/2]`, with
the stated threshold and tail fraction `r^(-2*k)`. See [GilyenArunachalamWiebe2019]. -/
theorem tensorChebyshevGridBound : TensorChebyshevGridBound := by
  intro d k hd hk r hr S hbound hsym hne H hH
  let P := fun y : Fin d → S => ∑ a : Fin k → Fin d,H a*(∏ i : Fin k,(y (a i) : ℝ))
  let c := ((d : ℝ)*k/2)^k
  let t := Real.sqrt 2*(r*Real.sqrt ((d : ℝ)*k/2))^k
  let B := Finset.univ.filter fun y : Fin d → S => t≤|P y|
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hbase : (0 : ℝ)<(d : ℝ)*k/2 := by positivity
  have hc : 0<c := pow_pos hbase _
  have hrR : 0<r := by linarith
  have ht : 0≤t := by positivity
  have hsecond : (∑ y : Fin d → S,(P y)^2)≤((S.card : ℝ)^d)*c :=
    (tensorGrid_tensor_second_moment d k S hsym H hH).trans
      (tensorGrid_even_moment_bound d k S hsym hbound hne)
  have ht2 : t^2=2*r^(2*k)*c := by
    dsimp [t,c]
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),← pow_mul,Nat.mul_comm k 2,pow_mul,
      mul_pow,Real.sq_sqrt hbase.le,mul_pow,← pow_mul]
    ring
  have hpoint (y : Fin d → S) (hy : y∈B) : t^2≤(P y)^2 := by
    have h := (Finset.mem_filter.mp hy).2
    have hs := (sq_le_sq₀ ht (abs_nonneg (P y))).mpr h
    simpa only [sq_abs] using hs
  have hcount : (B.card : ℝ)*t^2≤∑ y : Fin d → S,(P y)^2 := by
    calc
      _ = ∑ _y∈B,t^2 := by simp
      _ ≤ ∑ y∈B,(P y)^2 := Finset.sum_le_sum hpoint
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun y _ _ => sq_nonneg (P y))
  have htotal := hcount.trans hsecond
  rw [ht2] at htotal
  have hrpow : 0<r^(2*k) := pow_pos hrR _
  have hb0 : (0 : ℝ)≤B.card := Nat.cast_nonneg _
  have hpow : (((S.card : ℕ)^d : ℕ) : ℝ)=(S.card : ℝ)^d := by push_cast; rfl
  change (B.card : ℝ)≤_
  rw [hpow]
  apply (le_div_iff₀ hrpow).mpr
  nlinarith
end Qatlib.Concepts.GradientOracle.GradientAlgo
