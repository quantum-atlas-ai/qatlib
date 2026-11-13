/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkPhaseGapQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmStat
import Qatlib.Concepts.WalkFind.UniqueCollision.QueryScaleAux
import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmQuan

/-!
# Optimized Johnson-walk query bounds

This module derives explicit bounds for the query count from the iteration estimate, the marked
overlap `jwAlpha`, and the inner walk length `jwT2`. The descending-factorial expression for
`jwAlpha` supplies the lower bound needed at the scale `N^(k/(k+1))`
[Ambainis2007ElementDistinctness].

The theorem `queryComplexity` combines these scalar bounds with `ElementDistinctnessAlgorithm`
to prove the thresholded reduced-search proposition `QueryComplexity`.

## Main statements

* `jwAlpha_descFactorial`: the exact descending-factorial identity for the marked overlap.
* `jwQueryCount_optimized_scalar`: an explicit query bound at the optimized scale.
* `queryComplexity`: the reduced-search query-complexity proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

open Qatlib.Concepts.WalkFind.WalkSpectrum

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

/-- An iteration bound `t1 ≤ 8/(ε*α)` gives the query bound `r + 2*t1*t2 ≤ r + 16*t2/(ε*α)`. -/
theorem jwQueryCount_of_iteration_bound (r t1 t2 : ℕ) (ε α : ℝ)
    (ht : (t1 : ℝ) ≤ 8 / (ε * α)) :
    ((r + 2 * t1 * t2 : ℕ) : ℝ) ≤ (r : ℝ) + 16 * (t2 : ℝ) / (ε * α) := by
  have h := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ 2 * t2)
  push_cast
  calc
    (r : ℝ) + 2 * t1 * t2 = (r : ℝ) + (t1 : ℝ) * (2 * t2) := by ring
    _ ≤ (r : ℝ) + (8 / (ε * α)) * (2 * t2) := add_le_add (le_refl (r : ℝ)) h
    _ = (r : ℝ) + 16 * (t2 : ℝ) / (ε * α) := by ring

/-- For `1 ≤ k ≤ r`, the reciprocal arc parameter is at most `3*π*sqrt k / ((π-1)*π-3)`. -/
theorem jwEpsArc_reciprocal_bound (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    1/jwEpsArc k r ≤
      3*Real.pi*Real.sqrt (k : ℝ)/((Real.pi-1)*Real.pi-3) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hR : Real.sqrt (k : ℝ) ≤ Real.sqrt (r+1 : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (by omega : k ≤ r+1))
  have hD : 0 < (Real.pi-1)*Real.pi-3 := by nlinarith [Real.pi_gt_three]
  have hsmall : 1/(Real.pi*Real.sqrt (r+1 : ℝ)) ≤ 1/(Real.pi*Real.sqrt (k : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have heps : ((Real.pi-1)*Real.pi-3)/(3*Real.pi*Real.sqrt (k : ℝ)) ≤ jwEpsArc k r := by
    unfold jwEpsArc
    have hid : ((Real.pi-1)*Real.pi-3)/(3*Real.pi*Real.sqrt (k : ℝ)) =
        (Real.pi-1)/(3*Real.sqrt (k : ℝ))-1/(Real.pi*Real.sqrt (k : ℝ)) := by field_simp
    rw [hid]
    linarith
  have hlo : 0 < ((Real.pi-1)*Real.pi-3)/(3*Real.pi*Real.sqrt (k : ℝ)) := by positivity
  calc
    _ ≤ 1/(((Real.pi-1)*Real.pi-3)/(3*Real.pi*Real.sqrt (k : ℝ))) :=
      one_div_le_one_div_of_le hlo heps
    _ = _ := by field_simp

/-- If `1 ≤ R` and `r ≤ R`, the inner walk count is at most `(sqrt 2*π/6+1)*sqrt R`. -/
theorem jwT2_sqrt_scale_bound (k r : ℕ) (hk : 1 ≤ k) (R : ℝ)
    (hR : 1 ≤ R) (hr : (r : ℝ) ≤ R) :
    (jwT2 k r : ℝ) ≤ (Real.sqrt 2*Real.pi/6+1)*Real.sqrt R := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 1 ≤ Real.sqrt (k : ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg k)).mpr (by simpa)
  have hceil : (jwT2 k r : ℝ) ≤ Real.pi*Real.sqrt (r+1 : ℝ)/(6*Real.sqrt (k : ℝ))+1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hs : Real.sqrt (r+1 : ℝ) ≤ Real.sqrt 2*Real.sqrt R := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsr : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa)
  calc
    _ ≤ Real.pi*Real.sqrt (r+1 : ℝ)/(6*Real.sqrt (k : ℝ))+1 := hceil
    _ ≤ Real.pi*(Real.sqrt 2*Real.sqrt R)/6+Real.sqrt R := by
      apply add_le_add _ hsr
      exact div_le_div₀ (by positivity) (by gcongr) (by norm_num) (by linarith)
    _ = _ := by ring

/-- Under `1 ≤ k ≤ r` and `k < N-r`, the squared marked overlap times `N.descFactorial k` equals
`r.descFactorial k`. -/
theorem jwAlpha_descFactorial (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkNr : k < N-r) :
    jwAlpha k N r^2*(N.descFactorial k : ℝ) = (r.descFactorial k : ℝ) := by
  have hchooseN : (Nat.choose N r : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos (by omega : r ≤ N))
  have hfacN := Nat.descFactorial_eq_factorial_mul_choose N k
  have hfacR := Nat.descFactorial_eq_factorial_mul_choose r k
  have hmul : (Nat.choose N r : ℝ)*(Nat.choose r k : ℝ) =
      (Nat.choose N k : ℝ)*(Nat.choose (N-k) (r-k) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := N) hkr
  rw [(alphaFromInput k N r hk hkr hkNr).2.2.1,hfacN,hfacR]
  push_cast
  field_simp
  nlinarith [hmul]

/-- The squared marked overlap satisfies `(r+1-k)^k ≤ jwAlpha k N r^2 * N^k` under the stated
physical size assumptions. -/
theorem jwAlpha_probability_lower (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkNr : k < N-r) :
    ((r+1-k : ℕ) : ℝ)^k ≤ jwAlpha k N r^2*(N : ℝ)^k := by
  have hlo : ((r+1-k : ℕ) : ℝ)^k ≤ (r.descFactorial k : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial r k
  have hhi : (N.descFactorial k : ℝ) ≤ (N : ℝ)^k := by
    exact_mod_cast Nat.descFactorial_le_pow N k
  rw [← jwAlpha_descFactorial k N r hk hkr hkNr] at hlo
  exact hlo.trans (mul_le_mul_of_nonneg_left hhi (sq_nonneg _))

/-- At a positive scale satisfying `R^(k+1) = N^k` and `R/4 ≤ r+1-k`, the marked overlap is at
least `1/(2^k*sqrt R)`. -/
theorem jwAlpha_optimized_scale_lower (k N r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkNr : k < N-r) (R : ℝ) (hR : 0 < R)
    (hscale : R^(k+1) = (N : ℝ)^k)
    (hmem : R/4 ≤ ((r+1-k : ℕ) : ℝ)) :
    1/((2 : ℝ)^k*Real.sqrt R) ≤ jwAlpha k N r := by
  have hlow := jwAlpha_probability_lower k N r hk hkr hkNr
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ R/4) hmem k
  have ha : 0 < jwAlpha k N r := (alphaFromInput k N r hk hkr hkNr).2.2.2.1
  apply (sq_le_sq₀ (by positivity) (le_of_lt ha)).mp
  have hRne := ne_of_gt hR
  have htwo : (2 : ℝ)^k ≠ 0 := by positivity
  rw [div_pow,mul_pow,Real.sq_sqrt (le_of_lt hR)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 : ℝ)^k)^2*R)).mpr
  have hN : (N : ℝ)^k = R^k*R := by rw [← hscale,pow_succ]
  rw [hN] at hlow
  have hfour : ((2 : ℝ)^k)^2 = (4 : ℝ)^k := by rw [← pow_mul, mul_comm k 2,pow_mul]; norm_num
  rw [hfour]
  rw [div_pow] at hpow
  have hh : 1 ≤ jwAlpha k N r^2*(4 : ℝ)^k*R := by
    have hmul := mul_le_mul_of_nonneg_right (hpow.trans hlow) (by positivity : (0 : ℝ) ≤ (4 : ℝ)^k)
    have hid : (R^k/(4 : ℝ)^k)*(4 : ℝ)^k = R^k := by field_simp
    rw [hid] at hmul
    have hp : 0 < R^k := pow_pos hR _
    have h : R^k*1 ≤ R^k*(jwAlpha k N r^2*(4 : ℝ)^k*R) := by nlinarith
    exact (mul_le_mul_iff_right₀ hp).mp h
  nlinarith

/-- The stated optimized-scale and iteration assumptions bound the search query count by the
displayed explicit `k`-dependent constant times `R`. -/
theorem jwQueryCount_optimized_scalar (k N r t1 : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r)
    (hkNr : k < N-r) (R : ℝ) (hR : 1 ≤ R) (hr : (r : ℝ) ≤ R)
    (hscale : R^(k+1) = (N : ℝ)^k)
    (hmem : R/4 ≤ ((r+1-k : ℕ) : ℝ))
    (ht : (t1 : ℝ) ≤ 8/(jwEpsArc k r*jwAlpha k N r)) :
    ((r+2*t1*jwT2 k r : ℕ) : ℝ) ≤
      (1+16*(Real.sqrt 2*Real.pi/6+1)*3*Real.pi*Real.sqrt (k : ℝ)/
        ((Real.pi-1)*Real.pi-3)*(2 : ℝ)^(k : ℝ))*R := by
  have hRpos : 0 < R := by linarith
  have hsr : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have heps := (jwEpsArc_bounds k r hk hkr).1
  have ha := (alphaFromInput k N r hk hkr hkNr).2.2.2.1
  have ht2 := jwT2_sqrt_scale_bound k r hk R hR hr
  have hepsinv := jwEpsArc_reciprocal_bound k r hk hkr
  have halpha := jwAlpha_optimized_scale_lower k N r hk hkr hkNr R hRpos hscale hmem
  have halphainv : 1/jwAlpha k N r ≤ (2 : ℝ)^k*Real.sqrt R := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1/((2 : ℝ)^k*Real.sqrt R)) halpha
    simpa using h
  have hD : 0 < (Real.pi-1)*Real.pi-3 := by nlinarith [Real.pi_gt_three]
  have hK : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  let A : ℝ := Real.sqrt 2*Real.pi/6+1
  let B : ℝ := 3*Real.pi*Real.sqrt (k : ℝ)/((Real.pi-1)*Real.pi-3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h1 : (jwT2 k r : ℝ)*(1/jwEpsArc k r) ≤ (A*Real.sqrt R)*B :=
    mul_le_mul ht2 hepsinv (by positivity) (mul_nonneg hA (Real.sqrt_nonneg R))
  have h2 := mul_le_mul h1 halphainv (by positivity) (by positivity : 0 ≤ (A*Real.sqrt R)*B)
  have hden : (jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r) ≤ A*B*(2 : ℝ)^k*R := by
    calc
      _ = ((jwT2 k r : ℝ)*(1/jwEpsArc k r))*(1/jwAlpha k N r) := by ring
      _ ≤ ((A*Real.sqrt R)*B)*((2 : ℝ)^k*Real.sqrt R) := h2
      _ = A*B*(2 : ℝ)^k*(Real.sqrt R)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (le_of_lt hRpos)]
  have hcount := jwQueryCount_of_iteration_bound r t1 (jwT2 k r) (jwEpsArc k r) (jwAlpha k N r) ht
  calc
    _ ≤ (r : ℝ)+16*(jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r) := hcount
    _ ≤ R+16*(A*B*(2 : ℝ)^k*R) := by
      have hmul := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 16)
      have hid : 16*(jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r) =
          16*((jwT2 k r : ℝ)/(jwEpsArc k r*jwAlpha k N r)) := by ring
      rw [hid]
      exact add_le_add hr hmul
    _ = _ := by rw [Real.rpow_natCast]; dsimp [A,B]; ring

/-- The reduced element-distinctness search guarantee implies the optimized query-complexity
proposition. -/
theorem queryComplexity_from_algorithm (hAlg : ElementDistinctnessAlgorithm) : QueryComplexity := by
  intro k N hk hN I hI
  let X : ℝ := (N : ℝ)^((k : ℝ)/(k+1))
  let r : ℕ := Nat.floor X
  let B : ℝ := 32*Real.pi^2*(k : ℝ)^3*(2 : ℝ)^(k+4)*(k+1)*k
  have hB : 4*(k : ℝ) ≤ B := jw_query_threshold_ge_four_k k hk
  obtain ⟨hX,hscale,hkr,hr,hsize,hmem⟩ := jw_optimized_scale_admissibility k N B hk hB hN
  have hCsize : (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r := by
    convert hsize using 1; dsimp [B,r,X]; ring
  have hkNr := jwWalk_size_physical k N r hk hCsize
  obtain ⟨t1,ht,hamp,_⟩ := hAlg k N r hk hkr hr hCsize I hI
  refine ⟨t1,?_,hamp⟩
  exact jwQueryCount_optimized_scalar k N r t1 hk hkr hkNr X hX
    (Nat.floor_le (by linarith)) hscale hmem ht

/-- The optimized reduced-search query bound holds with the explicit threshold and
success-amplitude conditions in `QueryComplexity` [Ambainis2007ElementDistinctness]. -/
theorem queryComplexity : QueryComplexity :=
  queryComplexity_from_algorithm elementDistinctnessAlgorithm_answer

/-- The proposition `QueryComplexity` holds, supplying the restricted optimized-scale conclusion
associated with [Ambainis2007ElementDistinctness]. -/
theorem queryComplexity_answer : QueryComplexity := queryComplexity

end Qatlib.Concepts.WalkFind.UniqueCollision
