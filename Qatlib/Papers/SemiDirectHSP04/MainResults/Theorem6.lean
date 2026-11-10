/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition4
import Mathlib.Data.Fin.VecNotation
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem6

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model
open Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition4

def InClass1 (p q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Prop :=
  q ∣ p - 1 ∧ orderOf u = q

def InClass2 (p q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Prop :=
  p = 2 ∧ q = 2 ∧ 2 ≤ r ∧ (u : ZMod (p ^ r)) = ((2 ^ r - 1 : ℕ) : ZMod (p ^ r))

def InClass3 (p q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Prop :=
  p = 2 ∧ q = 2 ∧ 2 < r ∧
    (u : ZMod (p ^ r)) = ((2 ^ (r - 1) - 1 : ℕ) : ZMod (p ^ r))

def InClass4 (p q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Prop :=
  q = p ∧ 2 ≤ r ∧ ¬ (p = 2 ∧ r = 2) ∧ orderOf u = p ∧
    (p ≠ 2 ∨ ((u : ZMod (p ^ r)) ≠ ((2 ^ r - 1 : ℕ) : ZMod (p ^ r)) ∧
               (u : ZMod (p ^ r)) ≠ ((2 ^ (r - 1) - 1 : ℕ) : ZMod (p ^ r))))

def InClass5 (p _q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Prop :=
  (u : ZMod (p ^ r)) = 1

def classVec (p q r : ℕ) (u : (ZMod (p ^ r))ˣ) : Fin 5 → Prop :=
  ![InClass1 p q r u, InClass2 p q r u, InClass3 p q r u,
    InClass4 p q r u, InClass5 p q r u]

theorem two_pow_eq (r : ℕ) (hr : 1 ≤ r) : 2 ^ r = 2 * 2 ^ (r - 1) := by
  conv_lhs => rw [show r = (r - 1) + 1 from by omega]
  rw [pow_succ']

theorem zmod_natCast_ne {n a b : ℕ} (ha : a < n) (hb : b < n) (h : a ≠ b) :
    ((a : ZMod n)) ≠ ((b : ZMod n)) := by
  intro hc
  rw [ZMod.natCast_eq_natCast_iff] at hc
  exact h (Nat.ModEq.eq_of_lt_of_lt hc ha hb)

theorem neA (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) + 1 : ℕ) : ZMod (2 ^ r)) ≠ ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) := by
  have hge : 4 ≤ 2 ^ (r - 1) := by
    have h : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := two_pow_eq r (by omega)
  have hlt : 2 ^ (r - 1) + 1 < 2 ^ r := by rw [hpow]; omega
  have hlt2 : 2 ^ r - 1 < 2 ^ r := by omega
  exact zmod_natCast_ne hlt hlt2 (by rw [hpow]; omega)

theorem neB (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) + 1 : ℕ) : ZMod (2 ^ r)) ≠ ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r)) := by
  have hge : 4 ≤ 2 ^ (r - 1) := by
    have h : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := two_pow_eq r (by omega)
  have hlt : 2 ^ (r - 1) + 1 < 2 ^ r := by rw [hpow]; omega
  have hb : 2 ^ (r - 1) - 1 < 2 ^ r := by omega
  exact zmod_natCast_ne hlt hb (by omega)

theorem neC (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r)) ≠ ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) := by
  have hge : 4 ≤ 2 ^ (r - 1) := by
    have h : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := two_pow_eq r (by omega)
  have hb : 2 ^ (r - 1) - 1 < 2 ^ r := by omega
  have hlt2 : 2 ^ r - 1 < 2 ^ r := by omega
  exact zmod_natCast_ne hb hlt2 (by rw [hpow]; omega)

theorem neOneR (r : ℕ) (hr : 2 ≤ r) :
    ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) ≠ 1 := by
  have hge : 4 ≤ 2 ^ r := by
    have h : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hb : 2 ^ r - 1 < 2 ^ r := by omega
  have h1 : (1 : ℕ) < 2 ^ r := by omega
  have hne : 2 ^ r - 1 ≠ 1 := by omega
  have := zmod_natCast_ne hb h1 hne
  simpa using this

theorem neOneH (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r)) ≠ 1 := by
  have hge : 4 ≤ 2 ^ (r - 1) := by
    have h : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := two_pow_eq r (by omega)
  have hb : 2 ^ (r - 1) - 1 < 2 ^ r := by omega
  have h1 : (1 : ℕ) < 2 ^ r := by rw [hpow]; omega
  have hne : 2 ^ (r - 1) - 1 ≠ 1 := by omega
  have := zmod_natCast_ne hb h1 hne
  simpa using this

theorem d01 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass1 p q r u ∧ InClass2 p q r u) := by
  rintro ⟨⟨hq1, -⟩, hp2, hq2, -, -⟩
  subst hp2; subst hq2
  exact absurd hq1 (by norm_num)

theorem d02 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass1 p q r u ∧ InClass3 p q r u) := by
  rintro ⟨⟨hq1, -⟩, hp2, hq2, -, -⟩
  subst hp2; subst hq2
  exact absurd hq1 (by norm_num)

theorem d03 (p q r : ℕ) (hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass1 p q r u ∧ InClass4 p q r u) := by
  rintro ⟨⟨hq1, -⟩, hqp, -, -, -, -⟩
  rw [hqp] at hq1
  have hpge : 2 ≤ p := hp.two_le
  have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) hq1
  omega

theorem d04 (_p q r : ℕ) (_hp : _p.Prime) (hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (_p ^ r))ˣ) :
    ¬ (InClass1 _p q r u ∧ InClass5 _p q r u) := by
  rintro ⟨⟨-, ho⟩, hu1⟩
  have hu1' : u = 1 := Units.ext hu1
  have hq1 : q = 1 := by rw [← ho, hu1', orderOf_one]
  exact hq.ne_one hq1

theorem d12 (p q r : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass2 p q r u ∧ InClass3 p q r u) := by
  rintro ⟨⟨hp2, hq2, -, hu2⟩, -, -, hr3, hu3⟩
  subst hp2; subst hq2
  exact neC r hr3 (hu3.symm.trans hu2)

theorem d13 (p q r : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass2 p q r u ∧ InClass4 p q r u) := by
  rintro ⟨⟨hp2, hq2, -, hu2⟩, -, -, -, -, hdisj⟩
  subst hp2; subst hq2
  rcases hdisj with h | h
  · exact absurd rfl h
  · exact h.1 hu2

theorem d14 (p q r : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass2 p q r u ∧ InClass5 p q r u) := by
  rintro ⟨⟨hp2, hq2, hr2, hu2⟩, hu1⟩
  subst hp2; subst hq2
  exact neOneR r hr2 (hu2.symm.trans hu1)

theorem d23 (p q r : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass3 p q r u ∧ InClass4 p q r u) := by
  rintro ⟨⟨hp2, hq2, hr3, hu3⟩, -, -, -, -, hdisj⟩
  subst hp2; subst hq2
  rcases hdisj with h | h
  · exact absurd rfl h
  · exact h.2 hu3

theorem d24 (p q r : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass3 p q r u ∧ InClass5 p q r u) := by
  rintro ⟨⟨hp2, hq2, hr3, hu3⟩, hu1⟩
  subst hp2; subst hq2
  exact neOneH r hr3 (hu3.symm.trans hu1)

theorem d34 (p q r : ℕ) (hp : p.Prime) (_hq : q.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) :
    ¬ (InClass4 p q r u ∧ InClass5 p q r u) := by
  rintro ⟨⟨-, -, -, hop, -⟩, hu1⟩
  have hu1' : u = 1 := Units.ext hu1
  rw [hu1', orderOf_one] at hop
  exact hp.ne_one hop.symm

theorem exhaust (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) (hu : u ^ q = 1) :
    ∃ i : Fin 5, classVec p q r u i := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hdvd : orderOf u ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hu
  rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
  · have hu1 : u = 1 := orderOf_eq_one_iff.mp h1
    refine ⟨4, ?_⟩
    show InClass5 p q r u
    show (u : ZMod (p ^ r)) = 1
    rw [hu1]
    simp
  · have hordq : orderOf u = q := hq'
    rcases prop4_only_cases p q r hp hq hr u hordq with hpq | ⟨h1r, hqp⟩
    · refine ⟨0, ?_⟩
      show InClass1 p q r u
      exact ⟨hpq, hordq⟩
    · by_cases hp2 : p = 2
      · subst hp2
        have hq2 : q = 2 := hqp
        subst hq2
        have hord2 : orderOf u = 2 := hordq
        have hr2 : 2 ≤ r := h1r
        by_cases hr_eq : r = 2
        · subst hr_eq
          have hu3 : (u : ZMod (2 ^ 2)) = ((2 ^ 2 - 1 : ℕ) : ZMod (2 ^ 2)) := by
            have h := (prop4_case_iii_two (u : (ZMod 4)ˣ)).mp hord2
            simpa using h
          refine ⟨1, ?_⟩
          show InClass2 2 2 2 u
          refine ⟨rfl, rfl, by omega, ?_⟩
          simpa using hu3
        · have hr3 : 2 < r := by omega
          have hres := (prop4_case_iii_gt_two r hr3 u).mp hord2
          rcases hres with huA | huB | huC
          · have hge : 4 ≤ 2 ^ (r - 1) := by
              have h : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
              simpa using h
            have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := two_pow_eq r (by omega)
            have hlt : 2 ^ (r - 1) + 1 < 2 ^ r := by
              rw [hpow]; omega
            have hlt2 : 2 ^ r - 1 < 2 ^ r := by omega
            have hne1 : (u : ZMod (2 ^ r)) ≠ ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) := by
              intro h
              rw [huA] at h
              have hc := ZMod.natCast_eq_natCast_iff (2 ^ (r - 1) + 1) (2 ^ r - 1) (2 ^ r) |>.mp h
              have heq := Nat.ModEq.eq_of_lt_of_lt hc hlt hlt2
              rw [hpow] at heq
              omega
            have hne2 : (u : ZMod (2 ^ r)) ≠ ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r)) := by
              intro h
              rw [huA] at h
              have hc :=
                  ZMod.natCast_eq_natCast_iff (2 ^ (r - 1) + 1) (2 ^ (r - 1) - 1) (2 ^ r) |>.mp h
              have hb : 2 ^ (r - 1) - 1 < 2 ^ r := by omega
              have heq := Nat.ModEq.eq_of_lt_of_lt hc hlt hb
              omega
            refine ⟨3, ?_⟩
            show InClass4 2 2 r u
            exact ⟨rfl, by omega, by simp [hr_eq], hord2, Or.inr ⟨hne1, hne2⟩⟩
          · refine ⟨2, ?_⟩
            show InClass3 2 2 r u
            exact ⟨rfl, rfl, hr3, huB⟩
          · refine ⟨1, ?_⟩
            show InClass2 2 2 r u
            exact ⟨rfl, rfl, by omega, huC⟩
      · refine ⟨3, ?_⟩
        show InClass4 p q r u
        exact ⟨hqp, by omega, by simp [hp2], hordq.trans hqp, Or.inl hp2⟩

theorem disjoint (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) (hu : u ^ q = 1) :
    ∀ i j : Fin 5, i ≠ j → ¬ (classVec p q r u i ∧ classVec p q r u j) := by
  have _ := hu
  have key : ∀ i j : Fin 5, i < j →
      ¬ (classVec p q r u i ∧ classVec p q r u j) := by
    intro i j hij h
    rcases h with ⟨hi, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp [classVec] at hi hj
    all_goals first
      | exact d01 p q r hp hq hr u ⟨hi, hj⟩
      | exact d02 p q r hp hq hr u ⟨hi, hj⟩
      | exact d03 p q r hp hq hr u ⟨hi, hj⟩
      | exact d04 p q r hp hq hr u ⟨hi, hj⟩
      | exact d12 p q r hp hq hr u ⟨hi, hj⟩
      | exact d13 p q r hp hq hr u ⟨hi, hj⟩
      | exact d14 p q r hp hq hr u ⟨hi, hj⟩
      | exact d23 p q r hp hq hr u ⟨hi, hj⟩
      | exact d24 p q r hp hq hr u ⟨hi, hj⟩
      | exact d34 p q r hp hq hr u ⟨hi, hj⟩
      | simp_all
  intro i j hij h
  have hval : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · exact key i j hlt h
  · exact key j i hgt ⟨h.2, h.1⟩

theorem theorem6_classification
    (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) (hu : u ^ q = 1) :
    (∃ i : Fin 5, classVec p q r u i) ∧
    (∀ i j : Fin 5, i ≠ j → ¬ (classVec p q r u i ∧ classVec p q r u j)) :=
  ⟨exhaust p q r hp hq hr u hu, disjoint p q r hp hq hr u hu⟩

end Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem6
