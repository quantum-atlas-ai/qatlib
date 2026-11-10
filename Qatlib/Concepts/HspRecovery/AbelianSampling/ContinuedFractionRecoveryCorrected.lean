/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

def euclidStep (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1 % p.2)

@[simp] theorem euclidStep_apply (a b : ℕ) : euclidStep (a, b) = (b, a % b) := rfl

def euclidRem (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | j + 2 => euclidRem a b j % euclidRem a b (j + 1)

@[simp] theorem euclidRem_zero (a b : ℕ) : euclidRem a b 0 = a := rfl

@[simp] theorem euclidRem_one (a b : ℕ) : euclidRem a b 1 = b := rfl

@[simp] theorem euclidRem_two (a b : ℕ) : euclidRem a b 2 = a % b := rfl

theorem euclidRem_succ_succ (a b : ℕ) (j : ℕ) :
    euclidRem a b (j + 2) = euclidRem a b j % euclidRem a b (j + 1) := rfl

theorem euclidRem_shift (a b : ℕ) (j : ℕ) : euclidRem b (a % b) j = euclidRem a b (j + 1) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => rfl
    | 1 => rfl
    | j + 2 =>
      rw [euclidRem_succ_succ, euclidRem_succ_succ, ih j (by omega), ih (j + 1) (by omega)]

theorem euclidRem_lt_of_pos {a b : ℕ} {j : ℕ} (h : 0 < euclidRem a b (j + 1)) :
    euclidRem a b (j + 2) < euclidRem a b (j + 1) := by
  rw [euclidRem_succ_succ]
  exact Nat.mod_lt _ h

theorem euclidRem_step_le (a b : ℕ) {j : ℕ} (hj : 0 < euclidRem a b (j + 1)) :
    euclidRem a b (j + 2) ≤ euclidRem a b (j + 1) :=
  le_of_lt (euclidRem_lt_of_pos hj)

def euclidLen : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => euclidLen (b + 1) (a % (b + 1)) + 1
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

theorem euclidLen_eq (a b : ℕ) (hb : 0 < b) : euclidLen a b = euclidLen b (a % b) + 1 := by
  rcases b with _ | b'
  · omega
  · simp only [euclidLen]

theorem euclidLen_pos (a b : ℕ) (hb : 0 < b) : 0 < euclidLen a b := by
  rw [euclidLen_eq a b hb]; omega

theorem euclidLen_mod_zero (a b : ℕ) (hb : 0 < b) (hmod : a % b = 0) :
    euclidLen a b = 1 := by
  rw [euclidLen_eq a b hb, hmod]
  simp only [euclidLen]

def euclidQuotients : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, b + 1 => a / (b + 1) :: euclidQuotients (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

theorem euclidQuotients_eq (a b : ℕ) (hb : 0 < b) :
    euclidQuotients a b = a / b :: euclidQuotients b (a % b) := by
  rcases b with _ | b'
  · omega
  · simp only [euclidQuotients]

def cfValue : List ℕ → ℚ
  | [] => 0
  | m :: ms => (m : ℚ) + 1 / cfValue ms

theorem cfValue_cons (m : ℕ) (ms : List ℕ) : cfValue (m :: ms) = (m : ℚ) + 1 / cfValue ms := rfl

@[simp] theorem cfValue_single (m : ℕ) : cfValue [m] = (m : ℚ) := by
  simp [cfValue]

theorem cfValue_zero_cons (ms : List ℕ) : cfValue (0 :: ms) = 1 / cfValue ms := by
  rw [cfValue_cons]; simp

theorem cfValue_euclidQuotients : ∀ (b a : ℕ), 0 < b → 0 < a →
    cfValue (0 :: euclidQuotients a b) = (b : ℚ) / a := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a hb ha
    have hdm : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hcast : (b : ℚ) * ((a / b : ℕ) : ℚ) + (a % b : ℕ) = (a : ℚ) := by exact_mod_cast hdm
    rcases Nat.eq_zero_or_pos (a % b) with hmod | hmod
    · have hq : euclidQuotients a b = [a / b] := by
        rw [euclidQuotients_eq a b hb, hmod]
        simp only [euclidQuotients]
      have hz : (0 : ℚ) < ((a / b : ℕ) : ℚ) := by
        rcases Nat.eq_zero_or_pos (a / b) with h0 | h0
        · exfalso
          have e1 : b * (a / b) = 0 := by rw [h0, Nat.mul_zero]
          rw [e1, hmod, Nat.zero_add] at hdm
          omega
        · exact_mod_cast h0
      have haa : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
      have hcast2 : (b : ℚ) * ((a / b : ℕ) : ℚ) = (a : ℚ) := by
        rw [hmod] at hcast; simpa using hcast
      rw [hq, cfValue_zero_cons, cfValue_single, div_eq_div_iff (ne_of_gt hz) (ne_of_gt haa)]
      linarith [hcast2]
    · have hlt : a % b < b := Nat.mod_lt _ hb
      have hrec := ih (a % b) hlt b hmod hb
      rw [euclidQuotients_eq a b hb, cfValue_zero_cons, cfValue_cons]
      have hhr : 1 / cfValue (euclidQuotients b (a % b)) = (a % b : ℕ) / (b : ℚ) := by
        rw [← cfValue_zero_cons]
        exact hrec
      rw [hhr]
      have haa : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
      have hX : (0 : ℚ) < ((a / b : ℕ) : ℚ) + (a % b : ℕ) / (b : ℚ) := by
        rcases Nat.lt_or_ge b a with hlt2 | hle
        · have h1 : (0 : ℚ) < ((a / b : ℕ) : ℚ) := by
            exact_mod_cast Nat.div_pos (le_of_lt hlt2) hb
          have h2 : (0 : ℚ) ≤ (a % b : ℕ) / (b : ℚ) :=
            div_nonneg (by positivity) (Nat.cast_nonneg _)
          linarith
        · have hab : a < b := by
            rcases Nat.eq_or_lt_of_le hle with h | h
            · exact absurd hmod (by rw [h]; simp)
            · exact h
          rw [Nat.div_eq_of_lt hab, Nat.mod_eq_of_lt hab]
          have h3 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
          simpa using div_pos h3 (by exact_mod_cast hb)
      rw [div_eq_div_iff (ne_of_gt hX) (ne_of_gt haa)]
      have hbb : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
      field_simp
      nlinarith [hcast, hbb]

def TailApprox (a b a' b' : ℕ) : Prop :=
  (a : ℚ) / b * (1 - 1 / (2 * a * b)) < (a' : ℚ) / b' ∧
    (a' : ℚ) / b' ≤ (a : ℚ) / b * (2 * a * b) / (2 * a * b - 1)

def CorrectedIneq (a b a' b' : ℕ) (j : ℕ) : Prop :=
  (euclidRem a b (j + 1) : ℚ) / (euclidRem a b j : ℚ) - 1 / (2 * (euclidRem a b j : ℚ) ^ 2) ≤
        (euclidRem a' b' (j + 1) : ℚ) / (euclidRem a' b' j : ℚ)
    ∧ (euclidRem a' b' (j + 1) : ℚ) / (euclidRem a' b' j : ℚ) <
        (euclidRem a b (j + 1) : ℚ) / (euclidRem a b j : ℚ) +
          1 / ((2 * (euclidRem a b j : ℚ) - 1 / (euclidRem a b (j + 1) : ℚ)) *
            (euclidRem a b j : ℚ))

theorem tailApprox_iff_correctedIneq {a b a' b' : ℕ} (hb : 0 < b) (hba : b < a)
    (hb' : 0 < b') (hba' : b' < a') :
    TailApprox a b a' b' ↔ CorrectedIneq a b a' b' 0 := by
  have hbp : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hap : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (lt_trans hb hba)
  have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ a by omega)
  have hb1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ b by omega)
  have hden : (0 : ℚ) < 2 * (a : ℚ) * (b : ℚ) - 1 := by nlinarith [hap, hbp, ha1, hb1]
  have hpp : (0 : ℚ) < (a' : ℚ) / (b' : ℚ) := div_pos (by
    exact_mod_cast (lt_trans hb' hba')) (by exact_mod_cast hb')
  have hp1 : (0 : ℚ) < 2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) :=
    div_pos (by nlinarith [hap]) hden
  have hp2 : (0 : ℚ) < 2 * (b : ℚ) * (b : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) :=
    div_pos (by nlinarith [hbp]) hden
  have hpC : (0 : ℚ) < (2 * (a : ℚ) * (b : ℚ) - 1) / (2 * (b : ℚ) * (b : ℚ)) :=
    div_pos hden (by nlinarith [hbp])
  have e1 : (b : ℚ) / a - 1 / (2 * (a : ℚ) ^ 2)
      = (2 * (a : ℚ) * (b : ℚ) - 1) / (2 * (a : ℚ) * (a : ℚ)) := by
    field_simp
  have e2 : (b : ℚ) / a + 1 / ((2 * (a : ℚ) - 1 / (b : ℚ)) * (a : ℚ))
      = 2 * (b : ℚ) * (b : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) := by
    have hd2 : (b : ℚ) * (a : ℚ) * 2 - 1 ≠ 0 := by
      ring_nf at hden ⊢
      linarith
    field_simp
    ring
  have e3 : (a : ℚ) / b * (1 - 1 / (2 * (a : ℚ) * (b : ℚ)))
      = (2 * (a : ℚ) * (b : ℚ) - 1) / (2 * (b : ℚ) * (b : ℚ)) := by
    field_simp
  have e4 : (a : ℚ) / b * (2 * (a : ℚ) * (b : ℚ)) / (2 * (a : ℚ) * (b : ℚ) - 1)
      = 2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) := by
    field_simp
  have dA : (2 * (a : ℚ) * (b : ℚ) - 1) / (2 * (a : ℚ) * (a : ℚ))
      = 1 / (2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1)) :=
    (one_div_div _ _).symm
  have dB : 2 * (b : ℚ) * (b : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1)
      = 1 / ((2 * (a : ℚ) * (b : ℚ) - 1) / (2 * (b : ℚ) * (b : ℚ))) :=
    (one_div_div _ _).symm
  simp only [TailApprox, CorrectedIneq, euclidRem_zero, euclidRem_one, Nat.zero_add, e1, e2, e3,
    e4]
  rw [← one_div_div (a' : ℚ) (b' : ℚ)]
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨?_, ?_⟩
    · rw [dA, one_div_le_one_div hp1 hpp]
      exact hu
    · rw [dB, one_div_lt_one_div hpp hpC]
      exact hl
  · rintro ⟨hl, hu⟩
    rw [dB] at hu
    rw [dA] at hl
    exact ⟨(one_div_lt_one_div hpp hpC).mp hu, (one_div_le_one_div hp1 hpp).mp hl⟩

theorem tailApprox_of_measurement {q p q' p' : ℕ} (hp : 0 < p) (hpq : p < q) (hp' : 0 < p')
    (hp'q' : p' < q') (hqq' : 2 * q * q ≤ q')
    (hmeas : |(p' : ℚ) / q' - (p : ℚ) / q| ≤ 1 / (q' : ℚ)) :
    TailApprox q p q' p' := by
  have hq : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show (0 : ℕ) < q by omega)
  have hpp : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ q by omega)
  have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ p by omega)
  have hq'p : (0 : ℚ) < (q' : ℚ) := by exact_mod_cast (show (0 : ℕ) < q' by omega)
  have hpp' : (0 : ℚ) < (p' : ℚ) := by exact_mod_cast hp'
  have hqq'ℚ : (2 : ℚ) * (q : ℚ) * (q : ℚ) ≤ (q' : ℚ) := by exact_mod_cast hqq'
  have hqq'ℚ' : (q : ℚ) * (q : ℚ) * 2 ≤ (q' : ℚ) := by linarith
  obtain ⟨hx1, hx2⟩ := abs_le.mp hmeas
  have hx'le : (p' : ℚ) / q' ≤ (p : ℚ) / q + 1 / (q' : ℚ) := by linarith
  have hx'ge : (p : ℚ) / q - 1 / (q' : ℚ) ≤ (p' : ℚ) / q' := by linarith
  have hxge : (1 : ℚ) / (q : ℚ) ≤ (p : ℚ) / q :=
    div_le_div_of_nonneg_right hp1 (le_of_lt hq)
  have hxx : (0 : ℚ) < (p : ℚ) / q - 1 / (q' : ℚ) := by
    have h2 : (1 : ℚ) / (q' : ℚ) < (1 : ℚ) / (q : ℚ) := by
      rw [one_div_lt_one_div hq'p hq]
      nlinarith [hq1]
    linarith

  have hposx : (0 : ℚ) < (p : ℚ) / q + 1 / (q' : ℚ) :=
    add_pos (div_pos hpp hq) (one_div_pos.mpr hq'p)
  have b1 : (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) + (q : ℚ)) ≤ (q' : ℚ) / p' := by
    have e : (q' : ℚ) / p' = 1 / ((p' : ℚ) / q') := (one_div_div _ _).symm
    have id1 : 1 / ((p : ℚ) / q + 1 / (q' : ℚ))
        = (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) + (q : ℚ)) := by field_simp
    rw [e, ← id1, one_div_le_one_div hposx (by positivity)]
    linarith
  have id2 : (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) + (q : ℚ))
        - ((q : ℚ) / p * (1 - 1 / (2 * (q : ℚ) * (p : ℚ))))
      = ((p : ℚ) * ((q' : ℚ) - 2 * (q : ℚ) * (q : ℚ)) + (q : ℚ))
          / (2 * (p : ℚ) * (p : ℚ) * ((p : ℚ) * (q' : ℚ) + (q : ℚ))) := by
    field_simp
    ring
  have hdif : (0 : ℚ) < (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) + (q : ℚ))
      - ((q : ℚ) / p * (1 - 1 / (2 * (q : ℚ) * (p : ℚ)))) := by
    rw [id2]
    have hn : (0 : ℚ) < (p : ℚ) * ((q' : ℚ) - 2 * (q : ℚ) * (q : ℚ)) + (q : ℚ) := by
      nlinarith [hqq'ℚ, hpp]
    have hdd : (0 : ℚ) < 2 * (p : ℚ) * (p : ℚ) * ((p : ℚ) * (q' : ℚ) + (q : ℚ)) :=
      mul_pos (by nlinarith [hpp]) (add_pos (mul_pos hpp hq'p) hq)
    exact div_pos hn hdd

  have b2 : (q' : ℚ) / p' ≤ (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) - (q : ℚ)) := by
    have e : (q' : ℚ) / p' = 1 / ((p' : ℚ) / q') := (one_div_div _ _).symm
    have id3 : 1 / ((p : ℚ) / q - 1 / (q' : ℚ))
        = (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) - (q : ℚ)) := by field_simp
    rw [e, ← id3, one_div_le_one_div (div_pos hpp' hq'p) hxx]
    linarith
  have hposqp : (0 : ℚ) < 2 * (q : ℚ) * (p : ℚ) - 1 := by nlinarith [hq, hpp, hq1, hp1]
  have hdenn2 : (0 : ℚ) < (p : ℚ) * (q' : ℚ) - (q : ℚ) := by
    nlinarith [hqq'ℚ, hp1, hq1]
  have e4q : (q : ℚ) / p * (2 * (q : ℚ) * (p : ℚ)) / (2 * (q : ℚ) * (p : ℚ) - 1)
      = 2 * (q : ℚ) * (q : ℚ) / (2 * (q : ℚ) * (p : ℚ) - 1) := by field_simp
  have hdif2 : (q : ℚ) * (q' : ℚ) / ((p : ℚ) * (q' : ℚ) - (q : ℚ))
      ≤ (q : ℚ) / p * (2 * (q : ℚ) * (p : ℚ)) / (2 * (q : ℚ) * (p : ℚ) - 1) := by
    rw [e4q, div_le_div_iff₀ hdenn2 hposqp]
    have hkey : (q : ℚ) * (2 * (q : ℚ) * (q : ℚ)) ≤ (q : ℚ) * (q' : ℚ) :=
      mul_le_mul_of_nonneg_left hqq'ℚ (le_of_lt hq)
    nlinarith [hkey]
  exact ⟨by linarith [b1, hdif], by linarith [b2, hdif2]⟩

set_option maxHeartbeats 1000000 in

theorem tailApprox_step {a b a' b' : ℕ} (hb : 0 < b) (hba : b < a) (hb' : 0 < b')
    (hba' : b' < a') (hr : 0 < a % b) (hinv : TailApprox a b a' b') :
    a' / b' = a / b ∧ 0 < a' % b' ∧ TailApprox b (a % b) b' (a' % b') := by
  obtain ⟨hl, hu⟩ := hinv
  have hbp : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hap : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show (0 : ℕ) < a by omega)
  have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ a by omega)
  have hb1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ b by omega)
  have hb'p : (0 : ℚ) < (b' : ℚ) := by exact_mod_cast hb'
  have ha'p : (0 : ℚ) < (a' : ℚ) := by exact_mod_cast (show (0 : ℕ) < a' by omega)
  have hrp : (0 : ℚ) < (a % b : ℕ) := by exact_mod_cast hr
  have hr1 : (1 : ℚ) ≤ (a % b : ℕ) := by exact_mod_cast (show (1 : ℕ) ≤ a % b by omega)
  have hden : (0 : ℚ) < 2 * (a : ℚ) * (b : ℚ) - 1 := by nlinarith [hap, hbp, ha1, hb1]
  have hden2 : (0 : ℚ) < 2 * (b : ℚ) * (a % b : ℕ) - 1 := by nlinarith [hbp, hrp, hb1, hr1]
  have hdm : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hdmℚ : (b : ℚ) * ((a / b : ℕ) : ℚ) + (a % b : ℕ) = (a : ℚ) := by exact_mod_cast hdm
  have hvk : (a : ℚ) / b = ((a / b : ℕ) : ℚ) + (a % b : ℕ) / (b : ℚ) := by
    rw [div_eq_iff (ne_of_gt hbp), add_mul, div_mul_cancel₀ _ (ne_of_gt hbp), mul_comm]
    exact hdmℚ.symm

  have hA : ((a / b : ℕ) : ℚ) < (a' : ℚ) / b' := by
    have hsub : ((a / b : ℕ) : ℚ) + ((a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ)))
        = (a : ℚ) / b * (1 - 1 / (2 * (a : ℚ) * (b : ℚ))) := by
      have h2 := hdmℚ
      field_simp
      nlinarith [h2]
    have hmin : (0 : ℚ) < (a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ)) := by
      have he : (a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ))
          = (2 * (b : ℚ) * (a % b : ℕ) - 1) / (2 * (b : ℚ) * (b : ℚ)) := by field_simp
      rw [he]
      exact div_pos hden2 (by nlinarith [hbp])
    linarith [hsub, hmin, hl]

  have hB : (a' : ℚ) / b' < ((a / b : ℕ) : ℚ) + 1 := by
    have hiden : (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) - 2 * (a : ℚ) * (a : ℚ)
        = 2 * (a : ℚ) * ((b : ℚ) - (a % b : ℕ)) - (((a / b : ℕ) : ℚ) + 1) := by
      linear_combination 2 * (a : ℚ) * hdmℚ
    have hrlt : a % b < b := Nat.mod_lt _ hb
    have hbr : (1 : ℚ) ≤ (b : ℚ) - (a % b : ℕ) := by
      have h1 : ((b - a % b : ℕ) : ℚ) = (b : ℚ) - (a % b : ℕ) :=
        Nat.cast_sub (Nat.le_of_lt hrlt)
      have h2 : (1 : ℚ) ≤ ((b - a % b : ℕ) : ℚ) := by
        have : (1 : ℕ) ≤ b - a % b := by omega
        exact_mod_cast this
      rwa [h1] at h2
    have hkle : ((a / b : ℕ) : ℚ) + 1 ≤ (a : ℚ) := by
      have hkkm : (a / b : ℕ) ≤ b * (a / b : ℕ) := Nat.le_mul_of_pos_left _ hb
      have : ((a / b : ℕ) : ℕ) + 1 ≤ a := by omega
      exact_mod_cast this
    have hpos2 : (0 : ℚ) < 2 * (a : ℚ) * ((b : ℚ) - (a % b : ℕ)) - (((a / b : ℕ) : ℚ) + 1) := by
      nlinarith [hbr, hap, hkle]
    have e4s : (a : ℚ) / b * (2 * (a : ℚ) * (b : ℚ)) / (2 * (a : ℚ) * (b : ℚ) - 1)
        = 2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) := by field_simp
    rw [e4s] at hu
    rw [div_lt_iff₀ hb'p]
    have hhu : (a' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1) ≤ 2 * (a : ℚ) * (a : ℚ) * (b' : ℚ) := by
      have h1 : (a' : ℚ) ≤ (2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1)) * (b' : ℚ) := by
        rwa [div_le_iff₀ hb'p] at hu
      have h2 : (a' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1)
          ≤ (2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1)) * (b' : ℚ)
            * (2 * (a : ℚ) * (b : ℚ) - 1) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hden)
      have h3 : (2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1)) * (b' : ℚ)
          * (2 * (a : ℚ) * (b : ℚ) - 1) = 2 * (a : ℚ) * (a : ℚ) * (b' : ℚ) := by
        field_simp
      rw [h3] at h2
      exact h2
    have hkey : 2 * (a : ℚ) * (a : ℚ)
        < (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) := by
      linarith [hiden, hpos2]
    have hfin : (2 * (a : ℚ) * (a : ℚ)) * (b' : ℚ)
        < (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) * (b' : ℚ) := by
      nlinarith [hkey, hb'p]
    have hfin2 : (a' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1)
        < (((a / b : ℕ) : ℚ) + 1) * (b' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1) := by
      nlinarith [hfin, hhu]
    exact lt_of_mul_lt_mul_right hfin2 (le_of_lt hden)

  have hq : a' / b' = a / b := by
    have hlo : (a / b : ℕ) * b' ≤ a' := by
      have h1 : ((a / b : ℕ) : ℚ) * (b' : ℚ) ≤ (a' : ℚ) := by
        rw [← le_div_iff₀ hb'p]
        exact le_of_lt hA
      exact_mod_cast h1
    have hhi : a' < ((a / b : ℕ) + 1) * b' := by
      have h2 : (a' : ℚ) < (((a / b : ℕ) : ℚ) + 1) * (b' : ℚ) := by
        rwa [div_lt_iff₀ hb'p] at hB
      exact_mod_cast h2
    exact Nat.div_eq_of_lt_le hlo hhi

  have hdm'0 : b' * (a' / b') + a' % b' = a' := Nat.div_add_mod a' b'
  rw [hq] at hdm'0
  have hdm'ℚ : (b' : ℚ) * ((a / b : ℕ) : ℚ) + (a' % b' : ℕ) = (a' : ℚ) := by exact_mod_cast hdm'0
  have hvk' : (a' : ℚ) / b' = ((a / b : ℕ) : ℚ) + (a' % b' : ℕ) / (b' : ℚ) := by
    rw [div_eq_iff (ne_of_gt hb'p), add_mul, div_mul_cancel₀ _ (ne_of_gt hb'p), mul_comm]
    exact hdm'ℚ.symm
  have eδ2 : (a : ℚ) / b * (1 - 1 / (2 * (a : ℚ) * (b : ℚ)))
      = (a : ℚ) / b - 1 / (2 * (b : ℚ) * (b : ℚ)) := by field_simp
  rw [eδ2] at hl
  have eδ3 : (a : ℚ) / b * (2 * (a : ℚ) * (b : ℚ)) / (2 * (a : ℚ) * (b : ℚ) - 1)
      = (a : ℚ) / b + (a : ℚ) / ((b : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1)) := by
    have hd : (a : ℚ) * (b : ℚ) * 2 - 1 ≠ 0 := by
      have := hden
      ring_nf at this ⊢
      linarith
    field_simp
    linarith
  rw [eδ3, hvk, hvk'] at hu
  rw [hvk, hvk'] at hl

  have hra : (a % b : ℕ) < (a : ℚ) := by
    exact_mod_cast (lt_trans (Nat.mod_lt _ hb) hba)
  have hcmp : (a : ℚ) / ((b : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1))
      < (a % b : ℕ) / ((b : ℚ) * (2 * (b : ℚ) * (a % b : ℕ) - 1)) := by
    have hdA : (0 : ℚ) < (b : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1) := by
      exact mul_pos hbp hden
    have hdB : (0 : ℚ) < (b : ℚ) * (2 * (b : ℚ) * (a % b : ℕ) - 1) := by
      exact mul_pos hbp hden2
    rw [div_lt_div_iff₀ hdA hdB]
    nlinarith [hra, hbp]
  have hmin2 : (0 : ℚ) < (a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ)) := by
    have he : (a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ))
        = (2 * (b : ℚ) * (a % b : ℕ) - 1) / (2 * (b : ℚ) * (b : ℚ)) := by field_simp
    rw [he]
    exact div_pos hden2 (by nlinarith [hbp])
  have hu'pos : (0 : ℚ) < (a' % b' : ℕ) / (b' : ℚ) := by linarith
  have hr'0 : 0 < a' % b' := by
    rcases Nat.eq_zero_or_pos (a' % b') with h0 | h0
    · rw [h0] at hu'pos
      simp at hu'pos
    · exact h0
  refine ⟨hq, hr'0, ?_⟩
  have hR2 : (0 : ℚ) < 2 * (a % b : ℕ) * (a % b : ℕ) := by nlinarith [hrp]
  have hB2 : (0 : ℚ) < 2 * (b : ℚ) * (b : ℚ) := by nlinarith [hbp]
  constructor
  · have eh : (a % b : ℕ) / (b : ℚ) + (a % b : ℕ) / ((b : ℚ) * (2 * (b : ℚ) * (a % b : ℕ) - 1))
        = 2 * (a % b : ℕ) * (a % b : ℕ) / (2 * (b : ℚ) * (a % b : ℕ) - 1) := by
      have hdr : (a % b : ℕ) * (b : ℚ) * 2 - 1 ≠ 0 := by
        have := hden2
        ring_nf at this ⊢
        linarith
      field_simp
      try rw [one_add_div hdr, div_left_inj' hdr]
      ring
    have hup2 : (a' % b' : ℕ) / (b' : ℚ)
        < 2 * (a % b : ℕ) * (a % b : ℕ) / (2 * (b : ℚ) * (a % b : ℕ) - 1) := by
      rw [← eh]
      linarith
    have e3s : (b : ℚ) / (a % b : ℕ) * (1 - 1 / (2 * (b : ℚ) * (a % b : ℕ)))
        = (2 * (b : ℚ) * (a % b : ℕ) - 1) / (2 * (a % b : ℕ) * (a % b : ℕ)) := by field_simp
    have hT : (0 : ℚ) < 2 * (a % b : ℕ) * (a % b : ℕ)
        / (2 * (b : ℚ) * (a % b : ℕ) - 1) := div_pos hR2 hden2
    have hr'p : (0 : ℚ) < (a' % b' : ℕ) := by exact_mod_cast hr'0
    rw [e3s, div_lt_div_iff₀ hR2 hr'p]
    rw [div_lt_div_iff₀ hb'p hden2] at hup2
    nlinarith [hup2]
  · have hr'p : (0 : ℚ) < (a' % b' : ℕ) := by exact_mod_cast hr'0
    have e4s2 : (b : ℚ) / (a % b : ℕ) * (2 * (b : ℚ) * (a % b : ℕ))
        / (2 * (b : ℚ) * (a % b : ℕ) - 1)
        = 2 * (b : ℚ) * (b : ℚ) / (2 * (b : ℚ) * (a % b : ℕ) - 1) := by field_simp
    have eδ2' : (a % b : ℕ) / (b : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ))
        = (2 * (b : ℚ) * (a % b : ℕ) - 1) / (2 * (b : ℚ) * (b : ℚ)) := by field_simp
    rw [e4s2, div_le_div_iff₀ hr'p hden2]
    have h8 : (2 * (b : ℚ) * (a % b : ℕ) - 1) / (2 * (b : ℚ) * (b : ℚ))
        ≤ (a' % b' : ℕ) / (b' : ℚ) := by
      rw [← eδ2']
      linarith
    rw [div_le_div_iff₀ hB2 hb'p] at h8
    nlinarith [h8]

theorem correctedIneq_shift (a b a' b' j : ℕ) :
    CorrectedIneq b (a % b) b' (a' % b') j ↔ CorrectedIneq a b a' b' (j + 1) := by
  simp only [CorrectedIneq]
  rw [euclidRem_shift, euclidRem_shift, euclidRem_shift, euclidRem_shift]

theorem div_eq_quot_add (a b : ℕ) (hb : 0 < b) :
    (a : ℚ) / b = ((a / b : ℕ) : ℚ) + (a % b : ℕ) / (b : ℚ) := by
  have hbp : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hdmℚ : (b : ℚ) * ((a / b : ℕ) : ℚ) + (a % b : ℕ) = (a : ℚ) := by
    exact_mod_cast (Nat.div_add_mod a b)
  rw [div_eq_iff (ne_of_gt hbp), add_mul, div_mul_cancel₀ _ (ne_of_gt hbp), mul_comm]
  exact hdmℚ.symm

set_option maxHeartbeats 1000000 in

theorem tail_approx_master : ∀ (a b a' b' : ℕ), 0 < b → b < a → Nat.Coprime a b →
    0 < b' → b' < a' → TailApprox a b a' b' →
    (∀ j, j < euclidLen a b → 0 < euclidRem a' b' (j + 1) ∧ CorrectedIneq a b a' b' j) ∧
    (∀ j, j + 1 < euclidLen a b →
      euclidRem a' b' j / euclidRem a' b' (j + 1) = euclidRem a b j / euclidRem a b (j + 1)) ∧
    (euclidRem a' b' (euclidLen a b - 1) / euclidRem a' b' (euclidLen a b)
      = euclidRem a b (euclidLen a b - 1) / euclidRem a b (euclidLen a b)
    ∨ (euclidRem a' b' (euclidLen a b - 1) / euclidRem a' b' (euclidLen a b)
      = euclidRem a b (euclidLen a b - 1) / euclidRem a b (euclidLen a b) - 1
      ∧ euclidRem a' b' (euclidLen a b) / euclidRem a' b' (euclidLen a b + 1) = 1)) ∧
    (cfValue (0 :: (euclidQuotients a' b').take (euclidLen a b)) = (b : ℚ) / a
    ∨ cfValue (0 :: (euclidQuotients a' b').take (euclidLen a b + 1)) = (b : ℚ) / a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b a' b' hb hba hcop hb' hba' hinv
    have hbp : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hap : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show (0 : ℕ) < a by omega)
    have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ a by omega)
    have hb1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast (show (1 : ℕ) ≤ b by omega)
    have hb'p : (0 : ℚ) < (b' : ℚ) := by exact_mod_cast hb'
    have hden : (0 : ℚ) < 2 * (a : ℚ) * (b : ℚ) - 1 := by nlinarith [hap, hbp, ha1, hb1]
    rcases Nat.eq_zero_or_pos (a % b) with hmod | hmod
    · have hL : euclidLen a b = 1 := euclidLen_mod_zero a b hb hmod
      have hdm : b * (a / b) = a := by
        have := Nat.div_add_mod a b
        omega
      have hdmℚ : (b : ℚ) * ((a / b : ℕ) : ℚ) = (a : ℚ) := by exact_mod_cast hdm
      have hk2 : (2 : ℕ) ≤ a / b := by
        rcases Nat.lt_or_ge (a / b) 2 with h | h
        · exfalso
          have h5 : a / b ≤ 1 := by omega
          have h4 : b * (a / b) ≤ b * 1 := Nat.mul_le_mul_left b h5
          omega
        · exact h
      have hk2ℚ : (2 : ℚ) ≤ ((a / b : ℕ) : ℚ) := by exact_mod_cast hk2
      have hkne : ((a / b : ℕ) : ℚ) ≠ 0 := by
        have : (0 : ℕ) < a / b := Nat.div_pos (Nat.le_of_lt hba) hb
        exact_mod_cast (show (a / b : ℕ) ≠ 0 by omega)
      have hfin : (1 : ℚ) / ((a / b : ℕ) : ℚ) = (b : ℚ) / a := by
        rw [div_eq_div_iff hkne hap.ne']
        nlinarith [hdmℚ]
      have hkey : ((a / b : ℕ) : ℚ) * (1 / (2 * (a : ℚ) * (b : ℚ)))
          = 1 / (2 * (b : ℚ) * (b : ℚ)) := by
        rw [mul_one_div, div_eq_div_iff (by nlinarith [hap]) (by nlinarith [hbp])]
        have h16 : ((a / b : ℕ) : ℚ) * ((b : ℚ) * (b : ℚ)) = (a : ℚ) * (b : ℚ) := by
          nlinarith [hdmℚ]
        nlinarith [h16]
      have ev1 : (a : ℚ) / b * (1 - 1 / (2 * (a : ℚ) * (b : ℚ)))
          = ((a / b : ℕ) : ℚ) - 1 / (2 * (b : ℚ) * (b : ℚ)) := by
        rw [div_eq_quot_add a b hb, hmod, Nat.cast_zero, zero_div, add_zero, mul_sub, mul_one,
          hkey]
      obtain ⟨hl, hu⟩ := id hinv
      rw [ev1] at hl
      have part1 : ∀ j, j < euclidLen a b →
          0 < euclidRem a' b' (j + 1) ∧ CorrectedIneq a b a' b' j := by
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        exact ⟨hb', (tailApprox_iff_correctedIneq hb hba hb' hba').mp hinv⟩
      have part2 : ∀ j, j + 1 < euclidLen a b →
          euclidRem a' b' j / euclidRem a' b' (j + 1) = euclidRem a b j / euclidRem a b (j + 1) := by
        intro j hj
        omega

      have hhalf : ((a / b : ℕ) : ℚ) - 1 / 2 < (a' : ℚ) / b' := by
        have h2 : (1 : ℚ) / (2 * (b : ℚ) * (b : ℚ)) ≤ 1 / 2 := by
          rw [one_div_le_one_div (by nlinarith [hbp]) (by norm_num)]
          nlinarith [hb1]
        linarith [hl, h2]
      have hup : (a' : ℚ) / b' < ((a / b : ℕ) : ℚ) + 1 := by
        have hiden : (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) - 2 * (a : ℚ) * (a : ℚ)
            = ((a / b : ℕ) : ℚ) * (2 * (b : ℚ) * (b : ℚ) - 1) - 1 := by
          linear_combination 2 * ((a : ℚ) - (b : ℚ)) * hdmℚ
        have hpos2 : (0 : ℚ) < ((a / b : ℕ) : ℚ) * (2 * (b : ℚ) * (b : ℚ) - 1) - 1 := by
          nlinarith [hk2ℚ, hb1]
        have e4b : (a : ℚ) / b * (2 * (a : ℚ) * (b : ℚ)) / (2 * (a : ℚ) * (b : ℚ) - 1)
            = 2 * (a : ℚ) * (a : ℚ) / (2 * (a : ℚ) * (b : ℚ) - 1) := by field_simp
        rw [e4b, div_le_div_iff₀ hb'p hden] at hu
        rw [div_lt_iff₀ hb'p]
        have hcross : 2 * (a : ℚ) * (a : ℚ)
            < (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) := by
          linarith [hiden, hpos2]
        have hfin2 : (2 * (a : ℚ) * (a : ℚ)) * (b' : ℚ)
            < (((a / b : ℕ) : ℚ) + 1) * (2 * (a : ℚ) * (b : ℚ) - 1) * (b' : ℚ) := by
          nlinarith [hcross, hb'p]
        have hfin3 : (a' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1)
            < (((a / b : ℕ) : ℚ) + 1) * (b' : ℚ) * (2 * (a : ℚ) * (b : ℚ) - 1) := by
          nlinarith [hfin2, hu]
        exact lt_of_mul_lt_mul_right hfin3 (le_of_lt hden)
      have hhi' : a' < ((a / b : ℕ) + 1) * b' := by
        have h8 : (((a / b : ℕ) + 1 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) + 1 := by push_cast; ring
        have h9 : (a' : ℚ) < (((a / b : ℕ) + 1 : ℕ) : ℚ) * (b' : ℚ) := by
          rw [h8, ← div_lt_iff₀ hb'p]
          exact hup
        exact_mod_cast h9
      have hq' : a' / b' = a / b ∨ a' / b' = a / b - 1 := by
        rcases Nat.lt_or_ge a' ((a / b : ℕ) * b') with hlt1 | hle1
        · refine Or.inr (Nat.div_eq_of_lt_le ?_ ?_)
          · have h10 : (((a / b : ℕ) - 1 : ℕ) : ℚ) * (b' : ℚ) < (a' : ℚ) := by
              have h11 : (((a / b : ℕ) - 1 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) - 1 := by
                rw [Nat.cast_sub (show (1 : ℕ) ≤ a / b by omega)]
                ring
              rw [h11, ← lt_div_iff₀ hb'p]
              linarith [hhalf]
            have h12 : (((a / b : ℕ) - 1 : ℕ) * b' : ℕ) < a' := by exact_mod_cast h10
            omega
          · rw [Nat.sub_add_cancel (show (1 : ℕ) ≤ a / b by omega)]
            exact hlt1
        · exact Or.inl (Nat.div_eq_of_lt_le hle1 hhi')
      rcases hq' with hq' | hq'
      · refine ⟨part1, part2, ?_, ?_⟩
        · rw [hL]
          norm_num [euclidRem_zero, euclidRem_one, euclidRem_two]
          exact Or.inl hq'
        · rw [hL, euclidQuotients_eq a' b' hb', hq']
          refine Or.inl ?_
          show cfValue (0 :: [(a / b : ℕ)]) = (b : ℚ) / a
          rw [cfValue_zero_cons, cfValue_single]
          exact hfin
      · have hr'p : 0 < a' % b' := by
          rcases Nat.eq_zero_or_pos (a' % b') with h0 | h0
          · exfalso
            have hdv : b' * (a' / b') + a' % b' = a' := Nat.div_add_mod a' b'
            rw [hq', h0, Nat.add_zero] at hdv
            have h13 : (a' : ℚ) = (b' : ℚ) * (((a / b : ℕ) - 1 : ℕ) : ℚ) := by
              exact_mod_cast hdv.symm
            have h14 : (a' : ℚ) / b' = (((a / b : ℕ) - 1 : ℕ) : ℚ) := by
              rw [div_eq_iff hb'p.ne', mul_comm]
              exact h13
            have h15 : (((a / b : ℕ) - 1 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) - 1 := by
              rw [Nat.cast_sub (show (1 : ℕ) ≤ a / b by omega)]
              ring
            rw [h15] at h14
            linarith [hhalf, h14]
          · exact h0
        have hnext : b' / (a' % b') = 1 := by
          have hvk' : (a' : ℚ) / b'
              = (((a / b : ℕ) - 1 : ℕ) : ℚ) + (a' % b' : ℕ) / (b' : ℚ) := by
            rw [div_eq_quot_add a' b' hb', hq']
          rw [hvk'] at hhalf
          have h11 : (((a / b : ℕ) - 1 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) - 1 := by
            rw [Nat.cast_sub (show (1 : ℕ) ≤ a / b by omega)]
            ring
          rw [h11] at hhalf
          have hu'gt : (1 : ℚ) / 2 < (a' % b' : ℕ) / (b' : ℚ) := by linarith
          have hu'gt' : (1 : ℚ) / 2 * (b' : ℚ) < (a' % b' : ℕ) := by
            rwa [lt_div_iff₀ hb'p] at hu'gt
          refine Nat.div_eq_of_lt_le ?_ ?_
          · simpa using (Nat.mod_lt _ hb').le
          · have h14 : (b' : ℚ) < 2 * (a' % b' : ℕ) := by nlinarith [hu'gt', hb'p]
            have h15 : b' < 2 * (a' % b' : ℕ) := by exact_mod_cast h14
            omega
        refine ⟨part1, part2, ?_, ?_⟩
        · rw [hL]
          norm_num [euclidRem_zero, euclidRem_one, euclidRem_two]
          exact Or.inr ⟨hq', hnext⟩
        · rw [hL, euclidQuotients_eq a' b' hb', hq', euclidQuotients_eq b' (a' % b') hr'p, hnext]
          refine Or.inr ?_
          show cfValue (0 :: [(a / b : ℕ) - 1, 1]) = (b : ℚ) / a
          have h15 : (((a / b : ℕ) - 1 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) - 1 := by
            rw [Nat.cast_sub (show (1 : ℕ) ≤ a / b by omega)]
            ring
          rw [cfValue_zero_cons, cfValue_cons, cfValue_single]
          norm_num1
          rw [h15, sub_add_cancel]
          exact hfin
    · obtain ⟨hq, hr'0, hinv'⟩ := tailApprox_step hb hba hb' hba' hmod hinv
      have hrlt : a % b < b := Nat.mod_lt _ hb
      have hcop' : Nat.Coprime b (a % b) := by
        have h1 : Nat.gcd b (a % b) = 1 := by
          rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
          exact Nat.Coprime.gcd_eq_one hcop
        exact h1
      have hL' : euclidLen a b = euclidLen b (a % b) + 1 := euclidLen_eq a b hb
      obtain ⟨P1, P2, P3, P4⟩ :=
        ih b (by omega) (a % b) b' (a' % b') hmod hrlt hcop' hr'0 (Nat.mod_lt _ hb') hinv'
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0]
          exact ⟨hb', (tailApprox_iff_correctedIneq hb hba hb' hba').mp hinv⟩
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' < euclidLen b (a % b) := by omega
          obtain ⟨hpos, hineq⟩ := P1 j' hj'
          refine ⟨?_, (correctedIneq_shift a b a' b' j').mp hineq⟩
          rw [euclidRem_shift] at hpos
          exact hpos
      · intro j hj
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0]
          simpa using hq
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' + 1 < euclidLen b (a % b) := by omega
          have h6 := P2 j' hj'
          rw [euclidRem_shift, euclidRem_shift, euclidRem_shift, euclidRem_shift] at h6
          exact h6
      · have hL'1 : (1 : ℕ) ≤ euclidLen b (a % b) := euclidLen_pos b (a % b) hmod
        have hidx : euclidLen b (a % b) - 1 + 1 = euclidLen b (a % b) := by omega
        obtain h3a | ⟨h3a, h3b⟩ := P3
        · refine Or.inl ?_
          rw [hL', Nat.add_sub_cancel]
          rw [euclidRem_shift a b (euclidLen b (a % b) - 1),
            euclidRem_shift a b (euclidLen b (a % b)),
            euclidRem_shift a' b' (euclidLen b (a % b) - 1),
            euclidRem_shift a' b' (euclidLen b (a % b)), hidx] at h3a
          exact h3a
        · refine Or.inr ⟨?_, ?_⟩
          · rw [hL', Nat.add_sub_cancel]
            rw [euclidRem_shift a b (euclidLen b (a % b) - 1),
              euclidRem_shift a b (euclidLen b (a % b)),
              euclidRem_shift a' b' (euclidLen b (a % b) - 1),
              euclidRem_shift a' b' (euclidLen b (a % b)), hidx] at h3a
            exact h3a
          · rw [hL']
            rw [euclidRem_shift a' b' (euclidLen b (a % b)),
              euclidRem_shift a' b' (euclidLen b (a % b) + 1)] at h3b
            exact h3b
      · have hsplit : euclidQuotients a' b' = (a / b) :: euclidQuotients b' (a' % b') := by
          rw [euclidQuotients_eq a' b' hb', hq]
        have hvk2 : (a : ℚ) / b = ((a / b : ℕ) : ℚ) + (a % b : ℕ) / (b : ℚ) :=
          div_eq_quot_add a b hb
        rw [hsplit, hL']
        change cfValue (0 :: ((a / b : ℕ) :: (euclidQuotients b' (a' % b')).take
            (euclidLen b (a % b)))) = (b : ℚ) / a ∨
          cfValue (0 :: ((a / b : ℕ) :: (euclidQuotients b' (a' % b')).take
            (euclidLen b (a % b) + 1))) = (b : ℚ) / a
        rcases P4 with h4 | h4
        · refine Or.inl ?_
          rw [cfValue_zero_cons, cfValue_cons, ← cfValue_zero_cons, h4, ← hvk2, one_div_div]
        · refine Or.inr ?_
          rw [cfValue_zero_cons, cfValue_cons, ← cfValue_zero_cons, h4, ← hvk2, one_div_div]

theorem two_mul_sq_le_of_meas {n q q' : ℕ} (hq : q ≤ 2 ^ n) (hq' : q' = 2 ^ (2 * n + 1)) :
    2 * q * q ≤ q' := by
  have hq2 : q * q ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hq hq
  have hq3 : (2 ^ n * 2 ^ n : ℕ) = 2 ^ (2 * n) := by
    calc 2 ^ n * 2 ^ n = 2 ^ (n + n) := (Nat.pow_add 2 n n).symm
      _ = 2 ^ (2 * n) := by congr 1; ring
  rw [hq', Nat.pow_succ]
  nlinarith [hq2, hq3]

theorem kitaev_cf_inequality_corrected {n p q p' q' : ℕ} (hq : q ≤ 2 ^ n)
    (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime q p) (hq' : q' = 2 ^ (2 * n + 1))
    (hp' : 0 < p') (hp'q' : p' < q')
    (hmeas : |(p' : ℚ) / q' - (p : ℚ) / q| ≤ 1 / (q' : ℚ)) :
    ∀ j, 1 ≤ j → j ≤ euclidLen q p →
      (euclidRem q p j : ℚ) / (euclidRem q p (j - 1) : ℚ)
          - 1 / (2 * (euclidRem q p (j - 1) : ℚ) ^ 2)
        ≤ (euclidRem q' p' j : ℚ) / (euclidRem q' p' (j - 1) : ℚ)
    ∧ (euclidRem q' p' j : ℚ) / (euclidRem q' p' (j - 1) : ℚ)
        < (euclidRem q p j : ℚ) / (euclidRem q p (j - 1) : ℚ)
          + 1 / ((2 * (euclidRem q p (j - 1) : ℚ)
              - 1 / (euclidRem q p j : ℚ)) * (euclidRem q p (j - 1) : ℚ)) := by
  have hbase : TailApprox q p q' p' :=
    tailApprox_of_measurement hp hpq hp' hp'q' (two_mul_sq_le_of_meas hq hq') hmeas
  obtain ⟨P1, P2, P3, P4⟩ := tail_approx_master q p q' p' hp hpq hcop hp' hp'q' hbase
  intro j hj1 hjL
  obtain ⟨hpos, hineq⟩ := P1 (j - 1) (by omega)
  simp only [CorrectedIneq] at hineq
  rw [show j - 1 + 1 = j from by omega] at hineq
  exact hineq

theorem kitaev_euclid_quotients_corrected {n p q p' q' : ℕ} (hq : q ≤ 2 ^ n)
    (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime q p) (hq' : q' = 2 ^ (2 * n + 1))
    (hp' : 0 < p') (hp'q' : p' < q')
    (hmeas : |(p' : ℚ) / q' - (p : ℚ) / q| ≤ 1 / (q' : ℚ)) :
    (∀ j, 1 ≤ j → j + 1 ≤ euclidLen q p →
       euclidRem q' p' (j - 1) / euclidRem q' p' j = euclidRem q p (j - 1) / euclidRem q p j)
    ∧ (euclidRem q' p' (euclidLen q p - 1) / euclidRem q' p' (euclidLen q p)
        = euclidRem q p (euclidLen q p - 1) / euclidRem q p (euclidLen q p)
      ∨ (euclidRem q' p' (euclidLen q p - 1) / euclidRem q' p' (euclidLen q p)
          = euclidRem q p (euclidLen q p - 1) / euclidRem q p (euclidLen q p) - 1
        ∧ euclidRem q' p' (euclidLen q p) / euclidRem q' p' (euclidLen q p + 1) = 1))
    ∧ (cfValue (0 :: (euclidQuotients q' p').take (euclidLen q p)) = (p : ℚ) / q
      ∨ cfValue (0 :: (euclidQuotients q' p').take (euclidLen q p + 1)) = (p : ℚ) / q) := by
  have hbase : TailApprox q p q' p' :=
    tailApprox_of_measurement hp hpq hp' hp'q' (two_mul_sq_le_of_meas hq hq') hmeas
  obtain ⟨P1, P2, P3, P4⟩ := tail_approx_master q p q' p' hp hpq hcop hp' hp'q' hbase
  refine ⟨?_, P3, P4⟩
  intro j hj1 hjL
  have h6 := P2 (j - 1) (by omega)
  rw [show j - 1 + 1 = j from by omega] at h6
  exact h6

theorem kitaev_separation_bounded_denominators {n p q r s : ℕ} (hn : 1 ≤ n)
    (hp : 0 < p) (hpq : p < q) (hq : q ≤ 2 ^ n) (hr : 0 < r) (hrs : r < s)
    (hs : s ≤ 2 ^ n) (hne : (p : ℚ) / q ≠ (r : ℚ) / s) :
    1 / ((2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1)) ≤ |(p : ℚ) / q - (r : ℚ) / s| := by
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show (0 : ℕ) < q by omega)
  have hs0 : (0 : ℚ) < (s : ℚ) := by exact_mod_cast (show (0 : ℕ) < s by omega)
  have h2n1' : (1 : ℚ) ≤ (2 ^ n : ℚ) := by exact_mod_cast (Nat.one_le_two_pow (n := n))
  have hca : ((2 ^ n : ℕ) : ℚ) = ((2 ^ n : ℚ)) := by push_cast; norm_num
  have hden : (0 : ℚ) < (q : ℚ) * (s : ℚ) := mul_pos hq0 hs0
  have hnum1 : ((p : ℤ) * s - (r : ℤ) * q) ≠ 0 := by
    intro h0
    refine hne ?_
    rw [div_eq_div_iff (ne_of_gt hq0) (ne_of_gt hs0)]
    have h2 := congrArg (Int.cast : ℤ → ℚ) h0
    push_cast at h2
    linarith
  have hnum : (1 : ℚ) ≤ |((p : ℚ) * s - (r : ℚ) * q)| := by
    have h3 : (1 : ℤ) ≤ |(p : ℤ) * s - (r : ℤ) * q| := Int.one_le_abs hnum1
    exact_mod_cast h3
  have hsplit : |(p : ℚ) / q - (r : ℚ) / s| = |((p : ℚ) * s - (r : ℚ) * q)| / ((q : ℚ) * s) := by
    rw [div_sub_div _ _ (ne_of_gt hq0) (ne_of_gt hs0), abs_div, abs_of_pos hden]
    congr 1
    ring
  by_cases hqs : q = s
  · have hpr : p ≠ r := by
      intro h9
      apply hne
      rw [h9, hqs]
    have hint : (1 : ℤ) ≤ |(p : ℤ) - (r : ℤ)| := Int.one_le_abs (by omega)
    have hcast : (1 : ℚ) ≤ |((p : ℚ) - (r : ℚ))| := by exact_mod_cast hint
    have hsplit2 : |(p : ℚ) / q - (r : ℚ) / q| = |((p : ℚ) - (r : ℚ))| / ((q : ℚ)) := by
      have hstep : (p : ℚ) / q - (r : ℚ) / q = ((p : ℚ) - (r : ℚ)) / q := by
        rw [div_sub_div _ _ (ne_of_gt hq0) (ne_of_gt hq0),
            div_eq_div_iff (ne_of_gt (mul_pos hq0 hq0)) (ne_of_gt hq0)]
        ring
      rw [hstep, abs_div, abs_of_pos hq0]
    have hqle : (q : ℚ) ≤ (2 ^ n : ℚ) := by
      have h6 : ((q : ℕ) : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast hq
      rw [hca] at h6
      exact h6
    subst hqs
    rw [hsplit2]
    have h2n2' : (2 : ℚ) ≤ (2 ^ n : ℚ) := by
      have h10 : (2 : ℕ) ≤ 2 ^ n := by
        cases n
        · omega
        · simp only [Nat.pow_succ]
          omega
      exact_mod_cast h10
    have hbb : ((q : ℚ)) ≤ (2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1) := by nlinarith [hqle, h2n2']
    have hkey2 : (1 : ℚ) / ((2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1)) ≤ |((p : ℚ) - (r : ℚ))| / ((q : ℚ)) := by
      have hB0 : (0 : ℚ) ≤ (2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1) := by nlinarith [h2n2']
      rw [div_le_div_iff₀ (by nlinarith [h2n2']) hq0]
      nlinarith [hcast, hbb, hB0]
    exact hkey2
  · have hdenmax : (q : ℚ) * (s : ℚ) ≤ (2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1) := by
      rcases Nat.lt_or_ge q s with hlt | hge
      · have hq2 : (q : ℕ) ≤ 2 ^ n - 1 := by omega
        have hq2' : ((q : ℚ)) ≤ (2 ^ n : ℚ) - 1 := by
          have h7 : ((q : ℕ) : ℚ) ≤ (((2 ^ n : ℕ) - 1 : ℕ) : ℚ) := by exact_mod_cast hq2
          have h8 : (((2 ^ n : ℕ) - 1 : ℕ) : ℚ) = ((2 ^ n : ℚ)) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_two_pow (n := n))]
            push_cast
            norm_num
          exact h7.trans (le_of_eq h8)
        have hs' : ((s : ℚ)) ≤ (2 ^ n : ℚ) := by
          have h6 : ((s : ℕ) : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast hs
          rw [hca] at h6
          exact h6
        calc ((q : ℚ)) * ((s : ℚ)) ≤ (((2 ^ n : ℚ)) - 1) * ((s : ℚ)) :=
              mul_le_mul_of_nonneg_right hq2' (le_of_lt hs0)
          _ ≤ (((2 ^ n : ℚ)) - 1) * ((2 ^ n : ℚ)) :=
              mul_le_mul_of_nonneg_left hs' (by linarith)
          _ ≤ ((2 ^ n : ℚ)) * (((2 ^ n : ℚ)) - 1) := le_of_eq (by ring)
      · have hlt2 : s < q := by omega
        have hs2 : (s : ℕ) ≤ 2 ^ n - 1 := by omega
        have hs2' : ((s : ℚ)) ≤ (2 ^ n : ℚ) - 1 := by
          have h7 : ((s : ℕ) : ℚ) ≤ (((2 ^ n : ℕ) - 1 : ℕ) : ℚ) := by exact_mod_cast hs2
          have h8 : (((2 ^ n : ℕ) - 1 : ℕ) : ℚ) = ((2 ^ n : ℚ)) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_two_pow (n := n))]
            push_cast
            norm_num
          exact h7.trans (le_of_eq h8)
        have hq' : ((q : ℚ)) ≤ (2 ^ n : ℚ) := by
          have h6 : ((q : ℕ) : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast hq
          rw [hca] at h6
          exact h6
        calc ((q : ℚ)) * ((s : ℚ)) ≤ ((2 ^ n : ℚ)) * ((s : ℚ)) :=
              mul_le_mul_of_nonneg_right hq' (le_of_lt hs0)
          _ ≤ ((2 ^ n : ℚ)) * (((2 ^ n : ℚ)) - 1) :=
              mul_le_mul_of_nonneg_left hs2' (by linarith)
    have hsep : (1 : ℚ) / ((q : ℚ) * (s : ℚ)) ≤ |(p : ℚ) / q - (r : ℚ) / s| := by
      rw [hsplit]
      exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
    have hmono : (1 : ℚ) / ((2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1)) ≤ (1 : ℚ) / ((q : ℚ) * (s : ℚ)) := by
      rw [one_div_le_one_div (by nlinarith) hden]
      exact hdenmax
    linarith

theorem kitaev_measurement_identifies_phase {n p q r s p' q' : ℕ} (hn : 1 ≤ n)
    (hp : 0 < p) (hpq : p < q) (hq : q ≤ 2 ^ n) (hr : 0 < r) (hrs : r < s)
    (hs : s ≤ 2 ^ n) (hp' : 0 < p') (hp'q' : p' < q') (hq' : q' = 2 ^ (2 * n + 1))
    (hm1 : |(p' : ℚ) / q' - (p : ℚ) / q| ≤ 1 / (q' : ℚ))
    (hm2 : |(p' : ℚ) / q' - (r : ℚ) / s| ≤ 1 / (q' : ℚ)) :
    (p : ℚ) / q = (r : ℚ) / s := by
  by_contra hne
  have hsep := kitaev_separation_bounded_denominators hn hp hpq hq hr hrs hs hne
  have htriangle : |(p : ℚ) / q - (r : ℚ) / s| ≤ 2 / (q' : ℚ) := by
    have h1 : |(p : ℚ) / q - (r : ℚ) / s|
        ≤ |(p : ℚ) / q - (p' : ℚ) / q'| + |(p' : ℚ) / q' - (r : ℚ) / s| := by
      have heq : ((p : ℚ) / q - (r : ℚ) / s)
          = ((p : ℚ) / q - (p' : ℚ) / q') + ((p' : ℚ) / q' - (r : ℚ) / s) := by ring
      rw [heq]
      exact abs_add_le _ _
    have h2 : |(p : ℚ) / q - (p' : ℚ) / q'| = |(p' : ℚ) / q' - (p : ℚ) / q| :=
      (abs_sub_comm _ _).symm
    rw [h2] at h1
    have h3 : |(p' : ℚ) / q' - (p : ℚ) / q| ≤ 1 / (q' : ℚ) := hm1
    have h4 : |(p' : ℚ) / q' - (r : ℚ) / s| ≤ 1 / (q' : ℚ) := hm2
    have hAB : |(p' : ℚ) / q' - (p : ℚ) / q| + |(p' : ℚ) / q' - (r : ℚ) / s|
        ≤ 1 / (q' : ℚ) + 1 / (q' : ℚ) := add_le_add h3 h4
    have hfin : |(p : ℚ) / q - (r : ℚ) / s| ≤ 1 / (q' : ℚ) + 1 / (q' : ℚ) := h1.trans hAB
    have htwo : 1 / (q' : ℚ) + 1 / (q' : ℚ) = 2 / (q' : ℚ) := by ring
    rw [htwo] at hfin
    exact hfin
  have hstrict : (2 : ℚ) / ((q' : ℚ)) < 1 / ((2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1)) := by
    have h2n : (2 : ℕ) ≤ 2 ^ n := by
      cases n
      · omega
      · simp only [Nat.pow_succ]
        omega
    have hca2 : ((2 ^ n : ℕ) : ℚ) = ((2 ^ n : ℚ)) := by push_cast; norm_num
    have h2n' : (2 : ℚ) ≤ (2 ^ n : ℚ) := by
      have h11 : ((2 ^ n : ℕ) : ℚ) ≥ ((2 : ℕ) : ℚ) := by exact_mod_cast h2n
      rw [hca2] at h11
      exact_mod_cast h11
    have hq'0 : 0 < q' := by omega
    have hq'pos : (0 : ℚ) < ((q' : ℕ) : ℚ) := by exact_mod_cast hq'0
    have haden : (0 : ℚ) < (2 ^ n : ℚ) * ((2 ^ n : ℚ) - 1) := by nlinarith [h2n']
    have hqq : (q' : ℕ) = 2 * (2 ^ n : ℕ) * (2 ^ n : ℕ) := by
      rw [hq', show 2 * n + 1 = n + n + 1 from by omega, pow_add, pow_add, pow_one]
      ring
    have hqq' : ((q' : ℕ) : ℚ) = 2 * ((2 ^ n : ℚ)) * ((2 ^ n : ℚ)) := by
      rw [hqq]
      push_cast
      norm_num
    rw [hqq']
    rw [div_lt_div_iff₀ (by nlinarith [h2n'] : (0 : ℚ) < 2 * ((2 ^ n : ℚ)) * ((2 ^ n : ℚ)))
      haden]
    nlinarith [h2n']
  linarith

theorem kitaev_cf_inequality_as_printed_false :
    (7 : ℕ) ≤ 2 ^ 3 ∧ (3 : ℕ) < 7 ∧ Nat.Coprime 7 3 ∧ (128 : ℕ) = 2 ^ (2 * 3 + 1)
      ∧ (55 : ℕ) < 128 ∧ |(55 : ℚ) / 128 - (3 : ℚ) / 7| ≤ 1 / 128
      ∧ 1 ≤ euclidLen 7 3
      ∧ ¬ ((euclidRem 128 55 0 : ℚ) / (euclidRem 128 55 1 : ℚ)
            < (euclidRem 7 3 1 : ℚ) / (euclidRem 7 3 0 : ℚ)
              + 1 / ((2 * (euclidRem 7 3 0 : ℚ) - 1 / (euclidRem 7 3 1 : ℚ))
                * (euclidRem 7 3 0 : ℚ))) := by
  refine ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, ?_,
    euclidLen_pos 7 3 (by norm_num), ?_⟩
  · norm_num
  · simp only [euclidRem_zero, euclidRem_one]
    norm_num

example : ¬ ((128 : ℚ) / 55 < (3 : ℚ) / 7 + 1 / ((2 * 7 - 1 / 3) * 7)) := by norm_num

theorem kitaev_kprime_succ_as_printed_false :
    euclidLen 7 3 = 2
      ∧ euclidRem 128 55 1 / euclidRem 128 55 2 = euclidRem 7 3 1 / euclidRem 7 3 2
      ∧ euclidRem 128 55 2 / euclidRem 128 55 3 = 18 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [euclidLen_eq 7 3 (by norm_num)]
    norm_num [euclidLen]
  · decide
  · decide

example : (euclidRem 128 55 2 / euclidRem 128 55 3 : ℕ) = 18
    ∧ (euclidRem 128 55 1 / euclidRem 128 55 2 : ℕ) = (euclidRem 7 3 1 / euclidRem 7 3 2 : ℕ) := by
  decide

end Qatlib.Concepts.HspRecovery.AbelianSampling
