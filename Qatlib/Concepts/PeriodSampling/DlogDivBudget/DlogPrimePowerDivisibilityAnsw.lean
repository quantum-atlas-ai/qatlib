/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogPrimePowerDivisibilityStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogOriginalContracts
import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecoveryAnsw

/-!
# Corrected discrete-logarithm divisibility bounds

This module proves range and injectivity properties of `dlogCprime` and the corrected counting
contract `DlogPrimePowerDivisibility`. For prime `p ≥ 3` with `p < q < 2 * p`, small-residue
coordinates map injectively into the integer interval from zero to `p - 1`, giving at most `(p -
1) / w + 1` coordinates whose values are divisible by a divisor `w ≥ 2`.

The module also refutes the legacy contract at `p = 3`, `q = 24` and exhibits a counting
obstruction there. These formal statements concern the coefficient-divisibility step in the
recovery analysis of [Shor1997], with the additional sampling-range condition made explicit.

## Main statements

* `dlogPrimePowerDivisibility_false`: failure of the legacy contract.
* `dlog_cprime_range`: bounds on every scaled coefficient when `1 < p < q`.
* `dlog_cprime_injective_good`: injectivity on small-residue coordinates in the corrected range.
* `dlogPrimePowerDivisibility`: the corrected range, injectivity, and counting contract.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
open Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget
open scoped Classical
set_option autoImplicit false

/-- The legacy discrete-logarithm divisibility statement fails at `p = 3` and `q = 24`. -/
theorem dlogPrimePowerDivisibility_false : ¬ DlogPrimePowerDivisibilityLegacy := by
  intro h
  have hh := (h 3 24 (by norm_num) (by norm_num) (by norm_num)).1
    (0 : Fin 24) (1 : Fin 24)
    (by norm_num [dlogSmallResidue, centeredResidue])
    (by norm_num [dlogSmallResidue, centeredResidue])
    (by norm_num [dlogCprime, centeredResidue])
  have hv := congrArg Fin.val hh
  norm_num at hv

/-- For `1 < p < q`, every value of `dlogCprime p q` lies between zero and `p - 1`, inclusive. -/
theorem dlog_cprime_range (p q : ℕ) (hp : 1 < p) (hpq : p < q) (c : Fin q) :
    0 ≤ dlogCprime p q c ∧ dlogCprime p q c ≤ (p-1 : ℕ) := by
  let m : ℤ := (p : ℤ)-1
  let z : ℤ := ((c : ℕ)*(p-1) : ℤ)
  have hpz : (1 : ℤ) < p := by exact_mod_cast hp
  have hm : 0 < m := by dsimp [m]; linarith
  have hq : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hz : z = (c : ℕ)*m := rfl
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have he : z-z%(q : ℤ) = (q : ℤ)*(z/(q : ℤ)) := by
    have hh := Int.emod_add_mul_ediv z (q : ℤ)
    linarith
  have hs : dlogCprime p q c = z/(q : ℤ) +
      if z%(q : ℤ) ≤ (q : ℤ)/2 then 0 else 1 := by
    change (z-centeredResidue (q : ℤ) z)/(q : ℤ) = _
    unfold centeredResidue
    (try dsimp only)
    split_ifs
    · rw [he, Int.mul_ediv_cancel_left _ (ne_of_gt hq)]
      ring
    · have hh : z-(z%(q : ℤ)-(q : ℤ)) = (q : ℤ)*(z/(q : ℤ)+1) := by
        rw [mul_add, mul_one]
        linarith
      rw [hh, Int.mul_ediv_cancel_left _ (ne_of_gt hq)]
  have hd0 : 0 ≤ z/(q : ℤ) := Int.ediv_nonneg hz0 (le_of_lt hq)
  have hdlt : z/(q : ℤ) < m := by
    apply (Int.ediv_lt_iff_lt_mul hq).2
    rw [hz]
    have hc : ((c : ℕ) : ℤ) < q := by exact_mod_cast c.isLt
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hc hm
  have hmc : ((p-1 : ℕ) : ℤ) = m := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  rw [hs, hmc]
  split_ifs <;> omega

/-- At `p = 3` and `q = 24`, the number of small-residue coordinates with even `dlogCprime`
exceeds the proposed bound `(3 - 1) / 2 + 1`. -/
theorem dlog_divisibility_budget_obstruction :
    (3-1)/2+1 < (Finset.univ.filter fun c : Fin 24 =>
      dlogSmallResidue 3 24 c ∧ (2 : ℤ) ∣ dlogCprime 3 24 c).card := by
  let s : Finset (Fin 24) := {0, 1, 23}
  have hsub : s ⊆ Finset.univ.filter fun c : Fin 24 =>
      dlogSmallResidue 3 24 c ∧ (2 : ℤ) ∣ dlogCprime 3 24 c := by
    intro c hc
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;>
      norm_num [Finset.mem_filter, dlogSmallResidue, dlogCprime, centeredResidue]
  have hh := Finset.card_le_card hsub
  have hscard : s.card = 3 := by
    norm_num [s, Fin.ext_iff]
  rw [hscard] at hh
  norm_num at hh ⊢
  omega

/-- For `p ≥ 3` and `p < q < 2 * p`, equal `dlogCprime` values at small-residue coordinates
force equality of those coordinates. -/
theorem dlog_cprime_injective_good (p q : ℕ) (hp : 3 ≤ p) (_hpq : p < q) (hqbound : q < 2*p)
    (c₁ c₂ : Fin q) (hs₁ : dlogSmallResidue p q c₁) (hs₂ : dlogSmallResidue p q c₂)
    (heq : dlogCprime p q c₁ = dlogCprime p q c₂) : c₁ = c₂ := by
  let P : ℝ := ((p-1 : ℕ) : ℝ)
  let s₁ : ℝ := (centeredResidue (q : ℤ) (c₁.val*(p-1) : ℤ) : ℝ)
  let s₂ : ℝ := (centeredResidue (q : ℤ) (c₂.val*(p-1) : ℤ) : ℝ)
  have h₁ := congrArg (fun z : ℤ => (z : ℝ)) (dlog_cprime_integrality p q c₁)
  have h₂ := congrArg (fun z : ℤ => (z : ℝ)) (dlog_cprime_integrality p q c₂)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] at h₁ h₂
  rw [heq] at h₁
  have hdiff : ((c₁.val : ℝ) - (c₂.val : ℝ)) * P = s₁ - s₂ := by
    dsimp [P, s₁, s₂]
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    linear_combination h₂ - h₁
  have hb₁ : |s₁| ≤ (q : ℝ)/12 := by simpa only [s₁, dlogSmallResidue, Int.cast_abs] using hs₁
  have hb₂ : |s₂| ≤ (q : ℝ)/12 := by simpa only [s₂, dlogSmallResidue, Int.cast_abs] using hs₂
  have hP : 0 < P := by dsimp [P]; exact_mod_cast (by omega : 0 < p-1)
  have ha : |(c₁.val : ℝ) - (c₂.val : ℝ)| * P ≤ (q : ℝ)/6 := by
    rw [← abs_of_pos hP, ← abs_mul, hdiff]
    have h := abs_sub_le s₁ 0 s₂
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hqP : (q : ℝ) < 6 * P := by
    have hq : (q : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hqbound
    dsimp [P]
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hab : |(c₁.val : ℝ) - (c₂.val : ℝ)| < 1 := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hP.le
    linarith
  have hi : |(c₁.val : ℤ) - (c₂.val : ℤ)| < 1 := by exact_mod_cast hab
  apply Fin.ext
  have hh := abs_lt.mp hi
  have hz : (c₁.val : ℤ) = (c₂.val : ℤ) := by omega
  exact_mod_cast hz

/-- For prime `p ≥ 3` and `p < q < 2 * p`, the corrected contract gives injectivity on
small-residue coordinates, the range `[0, p - 1]`, and the divisibility count bound `(p - 1)
/ w + 1` for divisors `w ≥ 2`. -/
theorem dlogPrimePowerDivisibility : DlogPrimePowerDivisibility := by
  intro p q _ _hprime hp hpq hqbound
  refine ⟨dlog_cprime_injective_good p q hp hpq hqbound, ?_, ?_⟩
  · intro c _hs
    exact dlog_cprime_range p q (by omega) hpq c
  · intro w hw _hwp
    let S := Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c
    have hwz : (0 : ℤ) < w := by exact_mod_cast (by omega : 0 < w)
    have hrange (c : ↥S) := dlog_cprime_range p q (by omega) hpq c.val
    have hquot0 (c : ↥S) : 0 ≤ dlogCprime p q c.val / (w : ℤ) :=
      Int.ediv_nonneg (hrange c).1 hwz.le
    have hquotBound (c : ↥S) : dlogCprime p q c.val / (w : ℤ) ≤ ((p-1)/w : ℕ) := by
      have h := Int.ediv_le_ediv hwz (hrange c).2
      simpa only [Int.natCast_ediv] using h
    let e : ↥S → Fin ((p-1)/w+1) := fun c =>
      ⟨(dlogCprime p q c.val / (w : ℤ)).toNat, by
        have h0 := hquot0 c
        have hb := hquotBound c
        omega⟩
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply dlog_cprime_injective_good p q hp hpq hqbound a.val b.val
        (Finset.mem_filter.mp a.property).2.1 (Finset.mem_filter.mp b.property).2.1
      have hnat := congrArg Fin.val hab
      have ha : ((e a).val : ℤ) = dlogCprime p q a.val / (w : ℤ) := Int.toNat_of_nonneg (hquot0 a)
      have hb : ((e b).val : ℤ) = dlogCprime p q b.val / (w : ℤ) := Int.toNat_of_nonneg (hquot0 b)
      have hquo : dlogCprime p q a.val / (w : ℤ) = dlogCprime p q b.val / (w : ℤ) := by
        rw [← ha, ← hb, hnat]
      calc
        _ = dlogCprime p q a.val / (w : ℤ) * (w : ℤ) :=
          (Int.ediv_mul_cancel (Finset.mem_filter.mp a.property).2.2).symm
        _ = dlogCprime p q b.val / (w : ℤ) * (w : ℤ) := by rw [hquo]
        _ = _ := Int.ediv_mul_cancel (Finset.mem_filter.mp b.property).2.2
    have hcard := Fintype.card_le_of_injective e he
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
