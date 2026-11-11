/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux5
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Forward
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Aux2

/-!
# Column bounds for the scalar Taylor inverse

Explicit coordinate-source formulas for `scalarSolve` separate history and padding
contributions. Summing their squared norms yields the uniform estimate
`scalarInverseMatrix_column_sq_le` used to bound the inverse operator norm. See
[BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `scalarSolve_unit_time_hist`: The history response to a unit time-label source is its boundary
  response multiplied by `z^j / j!`.
* `scalarInverseMatrix_column_sq_le`: Every column of `scalarInverseMatrix` has squared
  Euclidean norm at most `(31/30)² * (87/32) * (57/25) * (m+p)` under the stated hypotheses.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

/-- The history response to a unit time-label source is its boundary response multiplied by `z^j
/ j!`. -/
theorem scalarSolve_unit_time_hist (m k p a d j : ℕ) (hd : d < m) (hj : j ≤ k) (z : ℂ) :
    scalarSolve m k p z (Pi.single (a*(k+1)) 1) (d*(k+1)+j) =
      (z^j/(Nat.factorial j : ℂ)) *
        (if a ≤ d then taylorPoly k z^(d-a) else 0) := by
  rw [scalarSolve_hist m k p z _ d j hd hj,scalarBlockVal_unit_time]
  have hzero (t : ℕ) (ht : t∈Finset.range j) :
      (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)) 1) (d*(k+1)+t+1)=0 := by
    have htk : t+1 ≤ k := by have := Finset.mem_range.mp ht; omega
    have hne : a*(k+1)≠d*(k+1)+t+1 := by
      intro he
      have hc := (taylor_label_eq_iff k a 0 d (t+1) (by omega) htk).mp
        (by simpa only [Nat.add_zero,Nat.add_assoc] using! he)
      omega
    simp [Ne.symm hne]
  rw [Finset.sum_eq_zero (fun t ht => by rw [hzero t ht,mul_zero]),add_zero]

/-- The history response to a positive-order unit source is the propagated boundary response
plus the direct contribution within the source block. -/
theorem scalarSolve_unit_positive_hist (m k p a b d j : ℕ)
    (hb : 1 ≤ b) (hbk : b ≤ k) (hd : d < m) (hj : j ≤ k) (z : ℂ) :
    scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (d*(k+1)+j) =
      (z^j/(Nat.factorial j : ℂ)) *
        (if a+1 ≤ d then taylorPoly k z^(d-(a+1))*taylorTransPoly k b z else 0) +
      (if d=a ∧ b ≤ j then z^(j-b)*(Nat.factorial b : ℂ)/(Nat.factorial j : ℂ) else 0) := by
  rw [scalarSolve_hist m k p z _ d j hd hj,scalarBlockVal_unit_positive k a b d hb hbk]
  congr 1
  have hterm (t : ℕ) (ht : t∈Finset.range j) :
      (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)+b) 1) (d*(k+1)+t+1) =
        if d=a ∧ t=b-1 then 1 else 0 := by
    have htk : t+1 ≤ k := by have := Finset.mem_range.mp ht; omega
    have he : a*(k+1)+b=d*(k+1)+t+1 ↔ d=a ∧ t=b-1 := by
      rw [Nat.add_assoc,taylor_label_eq_iff k a b d (t+1) hbk htk]
      omega
    by_cases hx : d*(k+1)+t+1=a*(k+1)+b
    · simp only [Pi.single_apply,if_pos hx,if_pos (he.mp hx.symm)]
    · have hn : ¬(d=a ∧ t=b-1) := fun h => hx (he.mpr h).symm
      simp only [Pi.single_apply,if_neg hx,if_neg hn]
  rw [Finset.sum_congr rfl (fun t ht => congrArg
    (fun v => (z^(j-t-1)*(Nat.factorial (t+1) : ℂ)/(Nat.factorial j : ℂ))*v) (hterm t ht))]
  by_cases h : d=a ∧ b ≤ j
  · have ht : b-1∈Finset.range j := by simp only [Finset.mem_range]; omega
    simp [h.1,mul_ite,ht,show b-1+1=b by omega,show j-(b-1)-1=j-b by omega,h.2]
  · have hn (t : ℕ) (ht : t∈Finset.range j) : ¬(d=a ∧ t=b-1) := by
      intro he
      have hjt := Finset.mem_range.mp ht
      apply h
      exact ⟨he.1,by omega⟩
    rw [if_neg h]
    exact Finset.sum_eq_zero (fun t ht => by (try dsimp only); rw [if_neg (hn t ht),mul_zero])

/-- A source in a history block produces a constant response throughout the terminal padding
region. -/
theorem scalarSolve_unit_history_pad (m k p a b q : ℕ) (ha : a < m) (hb : b ≤ k)
    (hq : q ≤ p) (z : ℂ) :
    scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (m*(k+1)+q) =
      scalarBlockVal k z (Pi.single (a*(k+1)+b) 1) m := by
  by_cases hq0 : q=0
  · subst q
    simpa only [Nat.add_zero] using! scalarSolve_jump m k p z _ m le_rfl
  · rw [scalarSolve_pad m k p z _ q (by omega) hq]
    have hz (t : ℕ) (ht : t∈Finset.range q) :
        (Pi.single (M := fun _ : ℕ => ℂ) (a*(k+1)+b) 1) (m*(k+1)+t+1)=0 := by
      have hsmall : a*(k+1)+b < m*(k+1) := by
        have hmul := Nat.mul_le_mul_right (k+1) (show a+1 ≤ m by omega)
        rw [Nat.add_mul,one_mul] at hmul
        omega
      have hne : m*(k+1)+t+1≠a*(k+1)+b := by omega
      simp [hne]
    rw [Finset.sum_eq_zero hz,add_zero]

/-- Under the factorial and left-half-disk hypotheses, the squared mass in one history block
from a unit time-label source is at most `(87/32) * (57/25)`. -/
theorem scalarSolve_unit_time_hist_mass (m k p a d : ℕ) (hd : d < m) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    (∑ j∈Finset.range (k+1),
      ‖scalarSolve m k p z (Pi.single (a*(k+1)) 1) (d*(k+1)+j)‖^2) ≤ (87/32 : ℝ)*(57/25) := by
  have hp := scalarBlockVal_unit_time_sq_le k m a d z hfac (by omega) hz hre
  have hpoint (j : ℕ) (hj : j∈Finset.range (k+1)) :
      ‖scalarSolve m k p z (Pi.single (a*(k+1)) 1) (d*(k+1)+j)‖^2 ≤ (87/32 : ℝ)*(Nat.factorial j : ℝ)⁻¹^2 := by
    rw [scalarSolve_unit_time_hist m k p a d j hd (by have := Finset.mem_range.mp hj; omega)]
    rw [← scalarBlockVal_unit_time k a d z,norm_mul,mul_pow,norm_div,norm_pow,Complex.norm_natCast]
    have hc : ‖z‖^j/(Nat.factorial j : ℝ) ≤ (Nat.factorial j : ℝ)⁻¹ := by
      have hpow := pow_le_pow_left₀ (norm_nonneg z) hz j
      simpa only [one_pow,one_div] using!
          div_le_div_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ (Nat.factorial j : ℝ))
    have hcsq := pow_le_pow_left₀ (by positivity) hc 2
    calc
      _ ≤ (Nat.factorial j : ℝ)⁻¹^2*(87/32) := mul_le_mul hcsq hp (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ j∈Finset.range (k+1),(87/32 : ℝ)*(Nat.factorial j : ℝ)⁻¹^2 :=
      Finset.sum_le_sum (fun j hj => hpoint j hj)
    _ = (87/32 : ℝ)*(∑ j∈Finset.range (k+1),(Nat.factorial j : ℝ)⁻¹^2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_recip_sq_sum_le k) (by norm_num)

/-- For `‖z‖ ≤ 1`, the sum of squared direct factorial-ratio contributions is at most `57 / 25`. -/
theorem scalar_unit_direct_mass (k b : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∑ j∈Finset.range (k+1), if b ≤ j then
      ‖z^(j-b)*(Nat.factorial b : ℂ)/(Nat.factorial j : ℂ)‖^2 else 0) ≤ 57/25 := by
  have hpoint (j : ℕ) (hj : b ≤ j) :
      ‖z^(j-b)*(Nat.factorial b : ℂ)/(Nat.factorial j : ℂ)‖^2 ≤
        (Nat.factorial (j-b) : ℝ)⁻¹^2 := by
    have hfac : (Nat.factorial b : ℝ)*(Nat.factorial (j-b) : ℝ) ≤ (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos j) (Nat.factorial_mul_factorial_dvd_factorial hj)
    have hr : (Nat.factorial b : ℝ)/(Nat.factorial j : ℝ) ≤ (Nat.factorial (j-b) : ℝ)⁻¹ := by
      rw [← one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa only [one_mul] using! hfac
    rw [norm_div,norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_natCast]
    have hpow := pow_le_pow_left₀ (norm_nonneg z) hz (j-b)
    have hn : ‖z‖^(j-b)*(Nat.factorial b : ℝ)/(Nat.factorial j : ℝ) ≤
        (Nat.factorial (j-b) : ℝ)⁻¹ := by
      calc
        _ ≤ (Nat.factorial b : ℝ)/(Nat.factorial j : ℝ) := by
          have hm :=
              mul_le_mul_of_nonneg_right hpow (show (0 : ℝ) ≤ (Nat.factorial b : ℝ) by positivity)
          simpa only [one_pow,one_mul] using! div_le_div_of_nonneg_right hm
            (show (0 : ℝ) ≤ (Nat.factorial j : ℝ) by positivity)
        _ ≤ _ := hr
    exact pow_le_pow_left₀ (by positivity) hn 2
  have hs : (∑ j∈Finset.range (k+1), if b ≤ j then
      (Nat.factorial (j-b) : ℝ)⁻¹^2 else 0) =
      ∑ j∈Finset.Ico b (k+1),(Nat.factorial (j-b) : ℝ)⁻¹^2 := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero,add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  calc
    _ ≤ ∑ j∈Finset.range (k+1), if b ≤ j then (Nat.factorial (j-b) : ℝ)⁻¹^2 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · exact hpoint j hj
      · rfl
    _ = ∑ j∈Finset.range (k+1-b),(Nat.factorial j : ℝ)⁻¹^2 := by
      rw [hs,Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
    _ ≤ ∑ j∈Finset.range (k+1),(Nat.factorial j : ℝ)⁻¹^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _)) (fun _ _ _ => by positivity)
    _ ≤ _ := factorial_recip_sq_sum_le k

/-- Under the stated hypotheses, the squared mass in one history block from a positive-order
source is at most `(31/30)² * (87/32) * (57/25)`. -/
theorem scalarSolve_unit_positive_hist_mass (m k p a b d : ℕ)
    (hk : 5 ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hd : d < m) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    (∑ j∈Finset.range (k+1),
      ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (d*(k+1)+j)‖^2) ≤
      ((31/30 : ℝ)^2*(87/32))*(57/25) := by
  by_cases hda : d=a
  · subst d
    have he (j : ℕ) (hj : j∈Finset.range (k+1)) :
        ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (a*(k+1)+j)‖^2 =
          if b ≤ j then ‖z^(j-b)*(Nat.factorial b : ℂ)/(Nat.factorial j : ℂ)‖^2 else 0 := by
      rw [scalarSolve_unit_positive_hist m k p a b a j hb hbk hd (by have := Finset.mem_range.mp hj; omega)]
      simp only [show ¬ a+1 ≤ a by omega,if_false,mul_zero,zero_add,true_and,
        apply_ite (fun x : ℂ => ‖x‖^2),norm_zero,zero_pow (by norm_num : 2≠0)]
    rw [Finset.sum_congr rfl he]
    exact (scalar_unit_direct_mass k b z hz).trans (by norm_num)
  · have hp := scalarBlockVal_unit_positive_sq_le k m a b d z hk hb hbk hfac (by omega) hz hre
    have hpoint (j : ℕ) (hj : j∈Finset.range (k+1)) :
        ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (d*(k+1)+j)‖^2 ≤
          ((31/30 : ℝ)^2*(87/32))*(Nat.factorial j : ℝ)⁻¹^2 := by
      rw [scalarSolve_unit_positive_hist m k p a b d j hb hbk hd (by have := Finset.mem_range.mp hj; omega)]
      simp only [hda,false_and,if_false,add_zero]
      rw [← scalarBlockVal_unit_positive k a b d hb hbk z,norm_mul,mul_pow,norm_div,norm_pow,Complex.norm_natCast]
      have hc : ‖z‖^j/(Nat.factorial j : ℝ) ≤ (Nat.factorial j : ℝ)⁻¹ := by
        have hpow := pow_le_pow_left₀ (norm_nonneg z) hz j
        simpa only [one_pow,one_div] using!
            div_le_div_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ (Nat.factorial j : ℝ))
      have hcsq := pow_le_pow_left₀ (by positivity) hc 2
      calc
        _ ≤ (Nat.factorial j : ℝ)⁻¹^2*((31/30 : ℝ)^2*(87/32)) :=
          mul_le_mul hcsq hp (by positivity) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ j∈Finset.range (k+1),((31/30 : ℝ)^2*(87/32))*(Nat.factorial j : ℝ)⁻¹^2 :=
        Finset.sum_le_sum (fun j hj => hpoint j hj)
      _ = ((31/30 : ℝ)^2*(87/32))*(∑ j∈Finset.range (k+1),(Nat.factorial j : ℝ)⁻¹^2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_recip_sq_sum_le k) (by norm_num)

/-- The total squared response to any history-coordinate unit source is at most `(31/30)² *
(87/32) * (57/25) * (m+p)` under the stated degree, padding, and scalar stability
hypotheses. -/
theorem scalarSolve_unit_history_column_sq_le (m k p a b : ℕ)
    (ha : a < m) (hb : b ≤ k) (hk : 5 ≤ k) (hp : 0 < p) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    (∑ l∈Finset.range (m*(k+1)+p+1),
      ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) l‖^2) ≤
      (((31/30 : ℝ)^2*(87/32))*(57/25))*((m+p : ℕ) : ℝ) := by
  let B : ℝ := (31/30)^2*(87/32)
  have hhist (d : ℕ) (hd : d∈Finset.range m) :
      (∑ j∈Finset.range (k+1),
        ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (d*(k+1)+j)‖^2) ≤ B*(57/25) := by
    by_cases hb0 : b=0
    · subst b
      simp only [Nat.add_zero]
      exact (scalarSolve_unit_time_hist_mass m k p a d (Finset.mem_range.mp hd) z hfac hz hre).trans
        (by norm_num [B])
    · exact scalarSolve_unit_positive_hist_mass m k p a b d hk (by omega) hb
        (Finset.mem_range.mp hd) z hfac hz hre
  have hpad (q : ℕ) (hq : q∈Finset.range (p+1)) :
      ‖scalarSolve m k p z (Pi.single (a*(k+1)+b) 1) (m*(k+1)+q)‖^2 ≤ B := by
    rw [scalarSolve_unit_history_pad m k p a b q ha hb (by have := Finset.mem_range.mp hq; omega)]
    by_cases hb0 : b=0
    · subst b
      simp only [Nat.add_zero]
      exact (scalarBlockVal_unit_time_sq_le k m a m z hfac le_rfl hz hre).trans (by norm_num [B])
    · exact scalarBlockVal_unit_positive_sq_le k m a b m z hk (by omega) hb hfac le_rfl hz hre
  rw [show m*(k+1)+p+1=m*(k+1)+(p+1) by omega,Finset.sum_range_add,taylor_sum_range_mul]
  have hhistSum := Finset.sum_le_sum hhist
  have hpadSum := Finset.sum_le_sum hpad
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hhistSum hpadSum
  change _ ≤ B*(57/25)*((m+p : ℕ) : ℝ)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  norm_num [B,Nat.cast_add,Nat.cast_one] at hhistSum hpadSum ⊢
  linarith

/-- A boundary response vanishes if its unit source lies strictly after the boundary label. -/
theorem scalarBlockVal_unit_above (k c d : ℕ) (z : ℂ) (hc : d*(k+1) < c) :
    scalarBlockVal k z (Pi.single c 1) d=0 := by
  have hr (l : ℕ) (hl : l ≤ d*(k+1)) : (Pi.single (M := fun _ : ℕ => ℂ) c 1) l=0 := by
    simp [show l≠c by omega]
  have hJ (s : ℕ) (hs : s∈Finset.range (d+1)) : scalarJumpTerm k z (Pi.single c 1) s=0 := by
    have hsd : s ≤ d := by have := Finset.mem_range.mp hs; omega
    have hsm : s*(k+1) ≤ d*(k+1) := Nat.mul_le_mul_right _ hsd
    unfold scalarJumpTerm
    split_ifs with hs0
    · exact hr 0 (by omega)
    · rw [hr _ hsm,zero_add]
      apply Finset.sum_eq_zero
      intro i hi
      have hik : i+1 ≤ k+1 := by have := Finset.mem_range.mp hi; omega
      have hlast : (s-1)*(k+1)+i+1 ≤ s*(k+1) := by
        have he : (s-1)*(k+1)+(k+1)=s*(k+1) := by
          rw [← Nat.succ_mul,show (s-1).succ=s by omega]
        omega
      rw [hr _ (hlast.trans hsm),mul_zero]
  unfold scalarBlockVal
  exact Finset.sum_eq_zero (fun s hs => by rw [hJ s hs,mul_zero])

/-- A unit source at or after the terminal boundary has zero response in every history block. -/
theorem scalarSolve_unit_padding_hist (m k p b d j : ℕ) (hd : d < m) (hj : j ≤ k) (z : ℂ) :
    scalarSolve m k p z (Pi.single (m*(k+1)+b) 1) (d*(k+1)+j)=0 := by
  rw [scalarSolve_hist m k p z _ d j hd hj]
  have hsmall : d*(k+1) < m*(k+1)+b := by
    have hm := Nat.mul_le_mul_right (k+1) (show d+1 ≤ m by omega)
    rw [Nat.add_mul,one_mul] at hm
    omega
  rw [scalarBlockVal_unit_above k (m*(k+1)+b) d z hsmall,mul_zero,zero_add]
  apply Finset.sum_eq_zero
  intro t ht
  have htm : d*(k+1)+t+1 < m*(k+1) := by
    have hm := Nat.mul_le_mul_right (k+1) (show d+1 ≤ m by omega)
    rw [Nat.add_mul,one_mul] at hm
    have := Finset.mem_range.mp ht
    omega
  have hz : (Pi.single (M := fun _ : ℕ => ℂ) (m*(k+1)+b) 1) (d*(k+1)+t+1)=0 := by
    simp [show d*(k+1)+t+1≠m*(k+1)+b by omega]
  rw [hz,mul_zero]

/-- The norm of each padding coordinate in the response to a terminal-region unit source is at
most one. -/
theorem scalarSolve_unit_padding_pad_norm (m k p b q : ℕ) (hq : q ≤ p) (z : ℂ) :
    ‖scalarSolve m k p z (Pi.single (m*(k+1)+b) 1) (m*(k+1)+q)‖ ≤ 1 := by
  have hblock : scalarBlockVal k z (Pi.single (m*(k+1)+b) 1) m = if b=0 then 1 else 0 := by
    by_cases hb0 : b=0
    · subst b; simp only [Nat.add_zero]
      rw [scalarBlockVal_unit_time]
      simp
    · rw [scalarBlockVal_unit_above k (m*(k+1)+b) m z (by omega),if_neg hb0]
  by_cases hq0 : q=0
  · subst q
    simp only [Nat.add_zero]
    rw [scalarSolve_jump m k p z _ m le_rfl,hblock]
    split_ifs <;> norm_num
  · rw [scalarSolve_pad m k p z _ q (by omega) hq,hblock]
    by_cases hb0 : b=0
    · subst b
      simp only [Nat.add_zero]
      rw [Finset.sum_eq_zero (fun t _ => by
        simp [show m*(k+1)+t+1≠m*(k+1) by omega])]
      norm_num
    · have hterm (t : ℕ) :
          (Pi.single (M := fun _ : ℕ => ℂ) (m*(k+1)+b) 1) (m*(k+1)+t+1) =
          if t=b-1 then 1 else 0 := by
        have he : m*(k+1)+t+1=m*(k+1)+b ↔ t=b-1 := by omega
        simp only [Pi.single_apply,he]
      simp only [if_neg hb0,zero_add,hterm]
      rw [Finset.sum_ite_eq']
      split_ifs <;> norm_num

/-- For positive padding length, the total squared response to a terminal-region unit source
satisfies the same uniform column bound as the history sources. -/
theorem scalarSolve_unit_padding_column_sq_le (m k p b : ℕ) (hp : 0 < p) (z : ℂ) :
    (∑ l∈Finset.range (m*(k+1)+p+1),
      ‖scalarSolve m k p z (Pi.single (m*(k+1)+b) 1) l‖^2) ≤
      (((31/30 : ℝ)^2*(87/32))*(57/25))*((m+p : ℕ) : ℝ) := by
  rw [show m*(k+1)+p+1=m*(k+1)+(p+1) by omega,Finset.sum_range_add,taylor_sum_range_mul]
  have hhist : (∑ a∈Finset.range m,∑ j∈Finset.range (k+1),
      ‖scalarSolve m k p z (Pi.single (m*(k+1)+b) 1) (a*(k+1)+j)‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro j hj
    rw [scalarSolve_unit_padding_hist m k p b a j (Finset.mem_range.mp ha)
      (by have := Finset.mem_range.mp hj; omega),norm_zero]
    norm_num
  rw [hhist,zero_add]
  have hs : (∑ q∈Finset.range (p+1),
      ‖scalarSolve m k p z (Pi.single (m*(k+1)+b) 1) (m*(k+1)+q)‖^2) ≤ (p+1 : ℕ) := by
    have h := Finset.sum_le_sum (s := Finset.range (p+1)) (g := fun _ => (1 : ℝ))
      (fun q hq => by
        have hnorm := scalarSolve_unit_padding_pad_norm m k p b q
          (by have := Finset.mem_range.mp hq; omega) z
        simpa only [one_pow] using! pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    simpa using! h
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmR : (0 : ℝ) ≤ m := by positivity
  norm_num [Nat.cast_add,Nat.cast_one] at hs ⊢
  linarith

/-- Every column of `scalarInverseMatrix` has squared Euclidean norm at most `(31/30)² * (87/32)
* (57/25) * (m+p)` under the stated hypotheses. -/
theorem scalarInverseMatrix_column_sq_le (m k p : ℕ) (hk : 5 ≤ k) (hp : 0 < p) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0)
    (c : Fin (m*(k+1)+p+1)) :
    (∑ r,‖scalarInverseMatrix m k p z r c‖^2) ≤
      (((31/30 : ℝ)^2*(87/32))*(57/25))*((m+p : ℕ) : ℝ) := by
  change (∑ r : Fin (m*(k+1)+p+1),
    ‖scalarSolve m k p z (Pi.single c.val 1) r.val‖^2) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    ‖scalarSolve m k p z (Pi.single c.val 1) r‖^2) (m*(k+1)+p+1)]
  by_cases hc : c.val < m*(k+1)
  · have hdiv : c.val/(k+1) < m := (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mpr hc
    have hmod : c.val%(k+1) ≤ k := by
      have hlt : c.val%(k+1) < k+1 := Nat.mod_lt _ (by omega)
      omega
    have he : c.val=c.val/(k+1)*(k+1)+c.val%(k+1) := by
      simpa only [Nat.mul_comm,Nat.add_comm] using! (Nat.mod_add_div c.val (k+1)).symm
    conv_lhs => arg 2; intro l; rw [he]
    exact scalarSolve_unit_history_column_sq_le m k p _ _ hdiv hmod hk hp z hfac hz hre
  · have he : c.val=m*(k+1)+(c.val-m*(k+1)) := by omega
    conv_lhs => arg 2; intro l; rw [he]
    exact scalarSolve_unit_padding_column_sq_le m k p _ hp z

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
