/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Logarithmic fermion encoding

`sourceLe` specifies the binary-block relation used to accumulate occupations in `sourceParity`;
reducing these counts modulo two gives `sourceEncoding`. The module proves bijectivity and
bounds the number of encoded bits changed by one occupation flip by `t + 1` on `2 ^ t` modes.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `source_encode_diff_log_many`: a single input flip changes at most `t + 1` output bits.
* `source_encoding_bijective`: the encoding is bijective.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.LogEncoding

/-- The binary-block relation in which `b` is obtained from `a` by replacing its lowest `l0`
bits by ones for some `l0 ≤ t`. -/
def sourceLe (t a b : ℕ) : Prop :=
  ∃ l0, l0 ≤ t ∧ b = (a / 2 ^ l0) * 2 ^ l0 + (2 ^ l0 - 1)

/-- The binary-block relation is reflexive. -/
theorem sourceLe_refl (t a : ℕ) : sourceLe t a a :=
  ⟨0, Nat.zero_le t, by simp⟩

/-- For fixed `a`, at most `t + 1` values below `2 ^ t` are related to `a` by `sourceLe`. -/
theorem sourceLe_count (t a : ℕ) :
    ((Finset.range (2 ^ t)).filter (fun b => sourceLe t a b)).card ≤ t + 1 := by
  have hsub : (Finset.range (2 ^ t)).filter (fun b => sourceLe t a b) ⊆
      (Finset.range (t + 1)).image (fun l0 => (a / 2 ^ l0) * 2 ^ l0 + (2 ^ l0 - 1)) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, sourceLe] at hb
    obtain ⟨-, l0, hl0, rfl⟩ := hb
    exact Finset.mem_image.mpr ⟨l0, Finset.mem_range.mpr (Nat.lt_succ_of_le hl0), rfl⟩
  calc
    ((Finset.range (2 ^ t)).filter (fun b => sourceLe t a b)).card
        ≤ ((Finset.range (t + 1)).image
            (fun l0 => (a / 2 ^ l0) * 2 ^ l0 + (2 ^ l0 - 1))).card :=
          Finset.card_le_card hsub
    _ ≤ (Finset.range (t + 1)).card := Finset.card_image_le
    _ = t + 1 := Finset.card_range (t + 1)

/-- At most `t + 1` finite register indices are related to a fixed index by `sourceLe`. -/
theorem sourceLe_fin_count {t : ℕ} (s : Fin (2 ^ t)) :
    ((Finset.univ : Finset (Fin (2 ^ t))).filter
        (fun j => sourceLe t s.val j.val)).card ≤ t + 1 := by
  have himg : ((Finset.univ : Finset (Fin (2 ^ t))).filter
        (fun j => sourceLe t s.val j.val)).image Fin.val ⊆
      (Finset.range (2 ^ t)).filter (fun b => sourceLe t s.val b) := by
    intro b hb
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range] at hb ⊢
    obtain ⟨j, hj, rfl⟩ := hb
    exact ⟨j.isLt, hj⟩
  calc
    ((Finset.univ : Finset (Fin (2 ^ t))).filter
        (fun j => sourceLe t s.val j.val)).card
        = (((Finset.univ : Finset (Fin (2 ^ t))).filter
            (fun j => sourceLe t s.val j.val)).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ ((Finset.range (2 ^ t)).filter (fun b => sourceLe t s.val b)).card :=
          Finset.card_le_card himg
    _ ≤ t + 1 := sourceLe_count t s.val

/-- The number of occupied indices related to `j` by `sourceLe`. -/
def sourceParity (t : ℕ) (n : Reg (2 ^ t)) (j : Fin (2 ^ t)) : ℕ :=
  ∑ s ∈ (Finset.univ.filter (fun s : Fin (2 ^ t) => sourceLe t s.val j.val)),
    (if n s then 1 else 0)

/-- The register whose bit at `j` records whether `sourceParity t n j` is odd. -/
def sourceEncoding (t : ℕ) (n : Reg (2 ^ t)) : Reg (2 ^ t) :=
  fun j => sourceParity t n j % 2 == 1

/-- Distinct indices related by `sourceLe` are strictly increasing. -/
theorem sourceLe_lt {t a b : ℕ} (h : sourceLe t a b) (hne : a ≠ b) : a < b := by
  obtain ⟨l0, -, hb⟩ := h
  have hdiv : a = (a / 2 ^ l0) * 2 ^ l0 + a % 2 ^ l0 := by
    have hdm := Nat.div_add_mod a (2 ^ l0)
    rw [Nat.mul_comm] at hdm
    exact hdm.symm
  have hmod : a % 2 ^ l0 < 2 ^ l0 := Nat.mod_lt _ (pow_pos (by norm_num) _)
  have hp : 0 < 2 ^ l0 := pow_pos (by norm_num) l0
  set q := (a / 2 ^ l0) * 2 ^ l0 with hq
  have hdiv' : a = q + a % 2 ^ l0 := by rw [hq]; exact hdiv
  have hb' : b = q + (2 ^ l0 - 1) := by rw [hq]; exact hb
  have hle : a ≤ b := by
    rw [hdiv', hb']
    have : a % 2 ^ l0 ≤ 2 ^ l0 - 1 := by omega
    omega
  exact lt_of_le_of_ne hle hne

/-- If `s` contributes to the parity count at `j`, that count splits into the contribution of
`s` and the sum over all remaining indices. -/
private lemma sourceParity_split {t : ℕ} (n : Reg (2 ^ t)) (s j : Fin (2 ^ t))
    (hs : sourceLe t s.val j.val) :
    sourceParity t n j =
      (∑ x ∈ (Finset.univ.filter (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase s,
          (if n x then 1 else 0)) + (if n s then 1 else 0) := by
  rw [sourceParity,
    ← Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)]
  exact Nat.add_comm _ _

/-- After flipping a contributing bit `s`, the parity count splits into the unchanged sum over
other indices and the new contribution at `s`. -/
private lemma sourceParity_update_split {t : ℕ} (n : Reg (2 ^ t)) (s j : Fin (2 ^ t))
    (hs : sourceLe t s.val j.val) :
    sourceParity t (Function.update n s (!(n s))) j =
      (∑ x ∈ (Finset.univ.filter (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase s,
          (if n x then 1 else 0)) + (if (!(n s)) then 1 else 0) := by
  rw [sourceParity,
    ← Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)]
  have hsum :
      (∑ x ∈ (Finset.univ.filter (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase s,
          (if Function.update n s (!(n s)) x then 1 else 0)) =
      ∑ x ∈ (Finset.univ.filter (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase s,
          (if n x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hsum, Function.update_self]
  exact Nat.add_comm _ _

/-- Flipping an index unrelated to `j` leaves its parity count unchanged. -/
private lemma sourceParity_update_of_notMem {t : ℕ} (n : Reg (2 ^ t)) (s j : Fin (2 ^ t))
    (h : ¬ sourceLe t s.val j.val) :
    sourceParity t (Function.update n s (!(n s))) j = sourceParity t n j := by
  have hnot : s ∉ (Finset.univ.filter (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)) := by
    simp [h]
  rw [sourceParity, sourceParity]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Function.update_of_ne]
  intro hxs
  subst hxs
  exact hnot hx

/-- The Boolean tests for oddness of two natural numbers agree exactly when their residues
modulo two agree. -/
private lemma enc_eq_iff (a b : ℕ) : ((a % 2 == 1) = (b % 2 == 1)) ↔ a % 2 = b % 2 := by
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        simp [ha, hb] at h ⊢
  · intro h
    rw [h]

/-- Distinct residues modulo two give distinct Boolean oddness tests. -/
private lemma enc_bit_ne_of_mod_ne {a b : ℕ} (h : a % 2 ≠ b % 2) :
    (a % 2 == 1) ≠ (b % 2 == 1) := by
  intro he
  exact h ((enc_eq_iff a b).mp he)

/-- Adding one changes the residue of a natural number modulo two. -/
private lemma mod_two_add_one_ne (a : ℕ) : (a + 1) % 2 ≠ a % 2 := by
  intro h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  rw [Nat.add_mod] at h
  omega

/-- Flipping the occupation at `s` changes the encoded bit at `j` exactly when `sourceLe`
relates their indices. -/
private lemma update_flip_iff {t : ℕ} (n : Reg (2 ^ t)) (s j : Fin (2 ^ t)) :
    sourceEncoding t (Function.update n s (!(n s))) j ≠ sourceEncoding t n j ↔
      sourceLe t s.val j.val := by
  by_cases h : sourceLe t s.val j.val
  · refine ⟨fun _ => h, fun _ => ?_⟩
    rw [sourceEncoding, sourceEncoding,
      sourceParity_update_split n s j h, sourceParity_split n s j h]
    cases hn : n s with
    | false =>
        simp only [Bool.not_false, if_true]
        exact enc_bit_ne_of_mod_ne (mod_two_add_one_ne _)
    | true =>
        simp only [if_true]
        exact (enc_bit_ne_of_mod_ne (mod_two_add_one_ne _)).symm
  · refine ⟨fun hc => ?_, fun hh => absurd hh h⟩
    exfalso
    apply hc
    have hp := sourceParity_update_of_notMem n s j h
    simp only [sourceEncoding, hp]

/-- Flipping one occupation in a register of size `2 ^ t` changes at most `t + 1` encoded bits.
[BravyiKitaev2002] -/
theorem source_encode_diff_log_many {t : ℕ} (n : Reg (2 ^ t)) (s : Fin (2 ^ t)) :
    ((Finset.univ : Finset (Fin (2 ^ t))).filter
        (fun j => sourceEncoding t (Function.update n s (!(n s))) j ≠ sourceEncoding t n j)).card
      ≤ t + 1 := by
  have hset :
      ((Finset.univ : Finset (Fin (2 ^ t))).filter
          (fun j => sourceEncoding t (Function.update n s (!(n s))) j ≠ sourceEncoding t n j)) =
        ((Finset.univ : Finset (Fin (2 ^ t))).filter (fun j => sourceLe t s.val j.val)) := by
    apply Finset.filter_congr
    intro j _
    exact update_flip_iff n s j
  rw [hset]
  exact sourceLe_fin_count s

/-- The binary-block parity encoding is a bijection on registers of size `2 ^ t`.
[BravyiKitaev2002] -/
theorem source_encoding_bijective (t : ℕ) : Function.Bijective (sourceEncoding t) := by
  have hinj : Function.Injective (sourceEncoding t) := by
    intro n m h

    have key : ∀ J : ℕ, ∀ j : Fin (2 ^ t), j.val < J → n j = m j := by
      intro J
      induction J with
      | zero => intro j hj; omega
      | succ J ih =>
          intro j hj
          have hmem : sourceLe t j.val j.val := sourceLe_refl t j.val
          have hpar : sourceParity t n j % 2 = sourceParity t m j % 2 := by
            have he : sourceEncoding t n j = sourceEncoding t m j := congrFun h j
            exact (enc_eq_iff _ _).mp he
          have hR :
              (∑ x ∈ (Finset.univ.filter
                  (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                (if n x then 1 else 0)) =
              (∑ x ∈ (Finset.univ.filter
                  (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                (if m x then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxmem : x ∈ (Finset.univ.filter
                (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)) := Finset.mem_of_mem_erase hx
            have hle : sourceLe t x.val j.val := (Finset.mem_filter.mp hxmem).2
            have hxne : x ≠ j := Finset.ne_of_mem_erase hx
            have hlt : x.val < j.val := sourceLe_lt hle (fun hh => hxne (Fin.ext hh))
            rw [ih x (by omega)]
          have hpar' :
              ((∑ x ∈ (Finset.univ.filter
                  (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                (if n x then 1 else 0)) + (if n j then 1 else 0)) % 2 =
              ((∑ x ∈ (Finset.univ.filter
                  (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                (if n x then 1 else 0)) + (if m j then 1 else 0)) % 2 := by
            have := hpar
            rw [sourceParity_split n j j hmem, sourceParity_split m j j hmem, ← hR] at this
            exact this
          cases hnj : n j with
          | false =>
              cases hmj : m j with
              | false => rfl
              | true =>
                  exfalso
                  simp only [hnj, hmj, Bool.false_eq_true, if_true, if_false, Nat.add_zero]
                    at hpar'
                  exact (mod_two_add_one_ne
                    (∑ x ∈ (Finset.univ.filter
                        (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                      (if n x then 1 else 0))) hpar'.symm
          | true =>
              cases hmj : m j with
              | false =>
                  exfalso
                  simp only [hnj, hmj, Bool.false_eq_true, if_true, if_false, Nat.add_zero]
                    at hpar'
                  exact (mod_two_add_one_ne
                    (∑ x ∈ (Finset.univ.filter
                        (fun x : Fin (2 ^ t) => sourceLe t x.val j.val)).erase j,
                      (if n x then 1 else 0))) hpar'
              | true => rfl
    funext j
    exact key j.val.succ j (Nat.lt_succ_self _)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

end Qatlib.Papers.FermionicComp00.MainResults.LogEncoding
