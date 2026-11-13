/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeConcentration

/-!
# Rounding estimates for classification budgets

The ceiling and floor inequalities in this module control the rounded parameters used in the
combinatorial algorithm. `source_iteration_real_bound` bounds the integer count of high degree
iterations by a real power of the graph size, assuming the rounded low degree threshold is
positive. For background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `ceil_le_twice_of_one_le`: For `1 ≤ x`, the real value of `Nat.ceil x` is at most `2 * x`.
* `source_iteration_real_bound`: For nonnegative `δ` and `ε'` and a positive rounded low degree
  threshold, the prescribed integer iteration bound is at most `21 * n^(δ + ε')`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

/-- For `1 ≤ x`, the real value of `Nat.ceil x` is at most `2 * x`. -/
theorem ceil_le_twice_of_one_le (x : ℝ) (hx : 1≤ x) : (Nat.ceil x:ℝ)≤2*x := by
  have hh:=Nat.ceil_lt_add_one (by linarith : 0≤ x)
  linarith

/-- If `1 ≤ Nat.floor x`, then the real value of `Nat.floor x` is at least `x / 2`. -/
theorem positive_floor_ge_half (x : ℝ) (hx : 1≤ Nat.floor x) : x/2≤(Nat.floor x:ℝ) := by
  have h1 : (1:ℝ)≤ Nat.floor x := by exact_mod_cast hx
  have hh:=Nat.lt_floor_add_one x
  linarith

/-- For nonnegative `δ` and `ε'` and a positive rounded low degree threshold, the prescribed
integer iteration bound is at most `21 * n^(δ + ε')`. -/
theorem source_iteration_real_bound (n : ℕ) (δ ε' : ℝ) (hn : 1≤ n) (hδ : 0≤δ) (hε : 0≤ε')
    (hdLo : 1≤ Nat.floor ((n:ℝ)^(1-δ)/10)) :
    ((n*n/(Nat.floor ((n:ℝ)^(1-δ)/10)*Nat.ceil ((n:ℝ)^(1-ε')))+1:ℕ):ℝ)≤21*(n:ℝ)^(δ+ε') := by
  have hnR : (0:ℝ)< n := by exact_mod_cast (by omega : 0< n)
  have hn1 : (1:ℝ)≤ n := by exact_mod_cast hn
  let d:=Nat.floor ((n:ℝ)^(1-δ)/10)
  let τ:=Nat.ceil ((n:ℝ)^(1-ε'))
  have hd : (n:ℝ)^(1-δ)/20≤(d:ℝ) := by
    have hh:=positive_floor_ge_half ((n:ℝ)^(1-δ)/10) hdLo
    dsimp only [d]
    linarith
  have ht : (n:ℝ)^(1-ε')≤(τ:ℝ) := Nat.le_ceil _
  have hprod : (n:ℝ)^(2-δ-ε')/20≤(d:ℝ)*(τ:ℝ) := by
    have hh:=mul_le_mul hd ht (Real.rpow_nonneg hnR.le (1-ε')) (Nat.cast_nonneg d)
    have he : (n:ℝ)^(1-δ)/20*(n:ℝ)^(1-ε')=(n:ℝ)^(2-δ-ε')/20 := by
      rw [div_mul_eq_mul_div,← Real.rpow_add hnR]
      congr 2
      ring
    exact he ▸ hh
  have hden : (0:ℝ)<(d:ℝ)*(τ:ℝ) := lt_of_lt_of_le (by positivity) hprod
  have hdiv : ((n*n/(d*τ):ℕ):ℝ)≤20*(n:ℝ)^(δ+ε') := by
    have hh : ((n*n/(d*τ):ℕ):ℝ)≤(n:ℝ)^2/((d:ℝ)*(τ:ℝ)) := by
      simpa only [Nat.cast_mul,pow_two] using (Nat.cast_div_le (m:=n*n) (n:=d*τ) (α:=ℝ))
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    have hm:=mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ)≤20*(n:ℝ)^(δ+ε'))
    have he : 20*(n:ℝ)^(δ+ε')*((n:ℝ)^(2-δ-ε')/20)=(n:ℝ)^2 := by
      calc
        _ = (n:ℝ)^(δ+ε')*(n:ℝ)^(2-δ-ε') := by ring
        _ = (n:ℝ)^2 := by rw [← Real.rpow_add hnR,show δ+ε'+(2-δ-ε')=2 by ring,Real.rpow_two]
    exact he ▸ hm
  have hp : (1:ℝ)≤(n:ℝ)^(δ+ε') := Real.one_le_rpow hn1 (add_nonneg hδ hε)
  change ((n*n/(d*τ)+1:ℕ):ℝ)≤ _
  rw [Nat.cast_add,Nat.cast_one]
  linarith
end Qatlib.Concepts.WalkSearch.MainResults
