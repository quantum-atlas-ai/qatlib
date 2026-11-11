/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux4
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux2

/-!
# Scalar Taylor responses to coordinate sources

This module evaluates `scalarJumpTerm` and `scalarBlockVal` on single-coordinate sources at time
labels and positive Taylor orders. Uniform squared bounds for these responses prepare the column
estimates for the scalar inverse. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylor_label_eq_iff`: For offsets `b, d ≤ k`, equality of labels `a*(k+1)+b` and `c*(k+1)+d`
  is equivalent to equality of both block indices and offsets.
* `scalarBlockVal_unit_positive_sq_le`: Under the stated degree, factorial, and left-half-disk
  hypotheses, every boundary response to a positive-order unit source has squared norm at most
  `(31/30)² * (87/32)`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

/-- For offsets `b, d ≤ k`, equality of labels `a*(k+1)+b` and `c*(k+1)+d` is equivalent to
equality of both block indices and offsets. -/
theorem taylor_label_eq_iff (k a b c d : ℕ) (hb : b ≤ k) (hd : d ≤ k) :
    a*(k+1)+b = c*(k+1)+d ↔ a=c ∧ b=d := by
  have hdiv (u v : ℕ) (hv : v ≤ k) : (u*(k+1)+v)/(k+1)=u := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < k+1), Nat.div_eq_of_lt (by omega)]
    simp
  constructor
  · intro h
    exact ⟨by simpa only [hdiv a b hb, hdiv c d hd] using! congrArg (fun v => v/(k+1)) h,
      by simpa only [label_mod_of_le a b k hb, label_mod_of_le c d k hd] using!
        congrArg (fun v => v%(k+1)) h⟩
  · rintro ⟨rfl,rfl⟩; rfl

/-- A unit source at time label `a*(k+1)` contributes one precisely to jump source `a`. -/
theorem scalarJumpTerm_unit_time (k a s : ℕ) (z : ℂ) :
    scalarJumpTerm k z (Pi.single (a*(k+1)) 1) s = if s=a then 1 else 0 := by
  classical
  by_cases hs : s=0
  · subst s
    simp [scalarJumpTerm, Pi.single_apply, eq_comm]
  · have hmul : a*(k+1)=s*(k+1) ↔ a=s := by
      simp [Nat.mul_left_inj (show k+1 ≠ 0 by omega)]
    have hz (i : ℕ) (hi : i ∈ Finset.range k) :
        (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)) 1) ((s-1)*(k+1)+i+1) = 0 := by
      have he : a*(k+1) ≠ (s-1)*(k+1)+i+1 := by
        have hiff := taylor_label_eq_iff k a 0 (s-1) (i+1) (by omega)
          (by have := Finset.mem_range.mp hi; omega)
        intro he
        have h := hiff.mp (by simpa only [Nat.add_zero, Nat.add_assoc] using! he)
        omega
      simp [Ne.symm he]
    unfold scalarJumpTerm
    rw [if_neg hs]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, mul_zero])]
    simp [Pi.single_apply, eq_comm, hmul]

/-- A unit source at positive offset `b` contributes `taylorTransPoly k b z` precisely to jump
source `a+1`. -/
theorem scalarJumpTerm_unit_positive (k a b s : ℕ) (hb : 1 ≤ b) (hbk : b ≤ k) (z : ℂ) :
    scalarJumpTerm k z (Pi.single (a*(k+1)+b) 1) s =
      if s=a+1 then taylorTransPoly k b z else 0 := by
  classical
  have hzero : (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)+b) 1) 0 = 0 := by
    simp [show 0 ≠ a*(k+1)+b by omega]
  by_cases hs : s=0
  · subst s; simp [scalarJumpTerm, hzero]
  · have htime : (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)+b) 1) (s*(k+1)) = 0 := by
      have he : a*(k+1)+b ≠ s*(k+1) := by
        have hi := taylor_label_eq_iff k a b s 0 hbk (by omega)
        intro he
        have := hi.mp (by simpa only [Nat.add_zero] using! he)
        omega
      simp [Ne.symm he]
    have hterm (i : ℕ) (hi : i ∈ Finset.range k) :
        (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)+b) 1) ((s-1)*(k+1)+i+1) =
          if s=a+1 ∧ i=b-1 then 1 else 0 := by
      have hi' : i+1 ≤ k := by have := Finset.mem_range.mp hi; omega
      have he : a*(k+1)+b = (s-1)*(k+1)+i+1 ↔ s=a+1 ∧ i=b-1 := by
        rw [Nat.add_assoc, taylor_label_eq_iff k a b (s-1) (i+1) hbk hi']
        omega
      simp only [Pi.single_apply]
      by_cases htest : (s-1)*(k+1)+i+1 = a*(k+1)+b
      · simp only [if_pos htest, if_pos (he.mp htest.symm)]
      · have hc : ¬ (s=a+1 ∧ i=b-1) := fun hc => htest (he.mpr hc).symm
        simp only [if_neg htest, if_neg hc]
    unfold scalarJumpTerm
    rw [if_neg hs, htime, zero_add]
    rw [Finset.sum_congr rfl (fun i hi => congrArg (fun r => taylorTransPoly k (i+1) z*r) (hterm i hi))]
    by_cases hsa : s=a+1
    · simp [hsa, mul_ite, show b-1 ∈ Finset.range k by simp; omega,
        show b-1+1=b by omega]
    · simp [hsa]

/-- The boundary response to a unit time-label source is the appropriate power of `taylorPoly`,
and is zero before that source. -/
theorem scalarBlockVal_unit_time (k a d : ℕ) (z : ℂ) :
    scalarBlockVal k z (Pi.single (a*(k+1)) 1) d =
      if a ≤ d then taylorPoly k z ^ (d-a) else 0 := by
  unfold scalarBlockVal
  simp_rw [scalarJumpTerm_unit_time, mul_ite, mul_one, mul_zero]
  simp [Finset.mem_range]

/-- The boundary response to a positive-order unit source is a Taylor power times
`taylorTransPoly k b z`, and is zero before boundary `a+1`. -/
theorem scalarBlockVal_unit_positive (k a b d : ℕ) (hb : 1 ≤ b) (hbk : b ≤ k) (z : ℂ) :
    scalarBlockVal k z (Pi.single (a*(k+1)+b) 1) d =
      if a+1 ≤ d then taylorPoly k z ^ (d-(a+1))*taylorTransPoly k b z else 0 := by
  unfold scalarBlockVal
  simp_rw [scalarJumpTerm_unit_positive k a b _ hb hbk, mul_ite, mul_zero]
  simp [Finset.mem_range]

/-- Under the factorial and left-half-disk hypotheses, every boundary response to a unit
time-label source has squared norm at most `87 / 32`. -/
theorem scalarBlockVal_unit_time_sq_le (k m a d : ℕ) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hd : d ≤ m)
    (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖scalarBlockVal k z (Pi.single (a*(k+1)) 1) d‖^2 ≤ 87/32 := by
  rw [scalarBlockVal_unit_time]
  split_ifs
  · rw [norm_pow, ← pow_mul, Nat.mul_comm (d-a) 2]
    exact taylorPow_le hfac (by omega) z hz hre
  · norm_num

/-- Under the stated degree, factorial, and left-half-disk hypotheses, every boundary response
to a positive-order unit source has squared norm at most `(31/30)² * (87/32)`. -/
theorem scalarBlockVal_unit_positive_sq_le (k m a b d : ℕ) (z : ℂ)
    (hk : 5 ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hd : d ≤ m)
    (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖scalarBlockVal k z (Pi.single (a*(k+1)+b) 1) d‖^2 ≤ (31/30)^2*(87/32) := by
  rw [scalarBlockVal_unit_positive k a b d hb hbk]
  split_ifs
  · have hpow := taylorPow_le hfac (show d-(a+1) ≤ m by omega) z hz hre
    have htrans := taylorTransPoly_uniform hk hb hbk z hz hre
    have htranssq := pow_le_pow_left₀ (norm_nonneg _) htrans 2
    calc
      _ = ‖taylorPoly k z‖^(2*(d-(a+1)))*‖taylorTransPoly k b z‖^2 := by
        rw [norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm (d-(a+1)) 2]
      _ ≤ (87/32)*(31/30)^2 := by gcongr
      _ = _ := by ring
  · norm_num

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
