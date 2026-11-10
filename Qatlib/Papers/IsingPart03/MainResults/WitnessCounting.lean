/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPart03.MainResults.SharpPWitness
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

abbrev FreeColour (y : ℕ) (b : E → ZMod 2) : Type _ := {e : E // b e = 0} → Fin y

def zeroParity (ends : E → V × V) : Finset (E → ZMod 2) :=
  Finset.univ.filter (fun b => parity ends b = 0)

def witnesses (x y : ℕ) (ends : E → V × V) :
    Finset (Σ b : E → ZMod 2, Colour (E := E) x b × FreeColour (E := E) y b) :=
  (zeroParity ends).sigma (fun _ => Finset.univ)

def posWitnesses (x y : ℕ) (ends : E → V × V) (w : E → ZMod 2) :
    Finset (Σ b : E → ZMod 2, Colour (E := E) x b × FreeColour (E := E) y b) :=
  (zeroParity ends).sigma (fun b => if bDotW b w = 0 then Finset.univ else ∅)

def negWitnesses (x y : ℕ) (ends : E → V × V) (w : E → ZMod 2) :
    Finset (Σ b : E → ZMod 2, Colour (E := E) x b × FreeColour (E := E) y b) :=
  (zeroParity ends).sigma (fun b => if bDotW b w = 1 then Finset.univ else ∅)

lemma card_colour_nat (x : ℕ) (b : E → ZMod 2) :
    Fintype.card (Colour (E := E) x b) = x ^ suppCard b := by
  classical
  rw [Fintype.card_fun, card_colourDomain, Fintype.card_fin]

omit [DecidableEq E] in

lemma card_zeroDomain (b : E → ZMod 2) :
    Fintype.card {e : E // b e = 0} = Fintype.card E - suppCard b := by
  classical
  have h := Fintype.card_subtype_compl (fun e : E => b e ≠ 0)
  rw [card_colourDomain] at h
  simpa only [ne_eq, not_not] using h

lemma card_freeColour (y : ℕ) (b : E → ZMod 2) :
    Fintype.card (FreeColour (E := E) y b) = y ^ (Fintype.card E - suppCard b) := by
  classical
  rw [Fintype.card_fun, card_zeroDomain, Fintype.card_fin]

lemma card_witnesses (x y : ℕ) (ends : E → V × V) :
    (witnesses (E := E) (V := V) x y ends).card
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 then x ^ suppCard b * y ^ (Fintype.card E - suppCard b) else 0 := by
  classical
  rw [witnesses, Finset.card_sigma, zeroParity, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : parity ends b = 0
  · rw [if_pos hp, if_pos hp, Finset.card_univ, Fintype.card_prod, card_colour_nat,
      card_freeColour]
  · rw [if_neg hp, if_neg hp]

lemma card_posWitnesses (x y : ℕ) (ends : E → V × V) (w : E → ZMod 2) :
    (posWitnesses (E := E) (V := V) x y ends w).card
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 ∧ bDotW b w = 0 then
            x ^ suppCard b * y ^ (Fintype.card E - suppCard b) else 0 := by
  classical
  rw [posWitnesses, Finset.card_sigma, zeroParity, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : parity ends b = 0
  · by_cases hw : bDotW b w = 0
    · rw [if_pos hp, if_pos hw, if_pos ⟨hp, hw⟩, Finset.card_univ, Fintype.card_prod,
        card_colour_nat, card_freeColour]
    · rw [if_pos hp, if_neg hw, if_neg (fun h => hw h.2)]
      simp
  · rw [if_neg hp, if_neg (fun h => hp h.1)]

lemma card_negWitnesses (x y : ℕ) (ends : E → V × V) (w : E → ZMod 2) :
    (negWitnesses (E := E) (V := V) x y ends w).card
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 ∧ bDotW b w = 1 then
            x ^ suppCard b * y ^ (Fintype.card E - suppCard b) else 0 := by
  classical
  rw [negWitnesses, Finset.card_sigma, zeroParity, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : parity ends b = 0
  · by_cases hw : bDotW b w = 1
    · rw [if_pos hp, if_pos hw, if_pos ⟨hp, hw⟩, Finset.card_univ, Fintype.card_prod,
        card_colour_nat, card_freeColour]
    · rw [if_pos hp, if_neg hw, if_neg (fun h => hw h.2)]
      simp
  · rw [if_neg hp, if_neg (fun h => hp h.1)]

def sgnZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

@[simp] lemma sgnZ_zero : sgnZ (0 : ZMod 2) = 1 := by simp [sgnZ]

@[simp] lemma sgnZ_one : sgnZ (1 : ZMod 2) = -1 := by rw [sgnZ]; exact if_neg (by decide)

lemma sgnZ_cast (z : ZMod 2) : ((sgnZ z : ℤ) : ℂ) = sgn z := by
  rcases eq_zero_or_one z with h | h <;> simp [sgnZ, sgn, h]

def qwgtInt (A : Matrix V E (ZMod 2)) (B : Matrix E E (ZMod 2)) (x y : ℕ) : ℤ :=
  ∑ b : E → ZMod 2,
    if A.mulVec b = 0 then
      sgnZ (∑ e, b e * (B.mulVec b) e) *
        ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ)
    else 0

omit [DecidableEq V] in

theorem qwgtInt_cast (A : Matrix V E (ZMod 2)) (B : Matrix E E (ZMod 2)) (x y : ℕ) :
    ((qwgtInt A B x y : ℤ) : ℂ) = qwgt A B (x : ℂ) (y : ℂ) := by
  classical
  rw [qwgtInt, qwgt, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : A.mulVec b = 0
  · rw [if_pos h, if_pos h]
    push_cast
    rw [sgnZ_cast]
    ring
  · rw [if_neg h, if_neg h]
    simp

lemma qwgtInt_incidence_dg (ends : E → V × V) (w : E → ZMod 2) (x y : ℕ) :
    qwgtInt (incidence ends) (dg w) x y
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 then
            sgnZ (bDotW b w) *
              ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ)
          else 0 := by
  classical
  unfold qwgtInt dg parity
  apply Finset.sum_congr rfl
  intro b _
  have hb : ∀ e : E, b e * ((Matrix.diagonal w).mulVec b) e = b e * w e := by
    intro e
    rw [Matrix.mulVec_diagonal]
    calc b e * (w e * b e) = (b e * b e) * w e := by ring
      _ = b e * w e := by rw [mul_self]
  have hsum : (∑ e, b e * ((Matrix.diagonal w).mulVec b) e) = bDotW b w := by
    rw [bDotW]
    exact Finset.sum_congr rfl (fun e _ => hb e)
  by_cases hp : (incidence ends).mulVec b = 0
  · rw [if_pos hp, if_pos hp, hsum]
  · rw [if_neg hp, if_neg hp]

theorem source_corollary1_qwgt_signed_counts (ends : E → V × V) (w : E → ZMod 2)
    (x y : ℕ) :
    qwgt (incidence ends) (dg w) (x : ℂ) (y : ℂ)
      = ((posWitnesses (E := E) (V := V) x y ends w).card : ℂ)
        - ((negWitnesses (E := E) (V := V) x y ends w).card : ℂ) := by
  classical
  have hZ : qwgtInt (incidence ends) (dg w) x y
      = ((posWitnesses (E := E) (V := V) x y ends w).card : ℤ)
        - ((negWitnesses (E := E) (V := V) x y ends w).card : ℤ) := by
    have hpos : ((posWitnesses (E := E) (V := V) x y ends w).card : ℤ)
        = ∑ b : E → ZMod 2,
            if parity ends b = 0 ∧ bDotW b w = 0 then
              ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0 := by
      rw [card_posWitnesses, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hp : parity ends b = 0 ∧ bDotW b w = 0 <;> simp [hp]
    have hneg : ((negWitnesses (E := E) (V := V) x y ends w).card : ℤ)
        = ∑ b : E → ZMod 2,
            if parity ends b = 0 ∧ bDotW b w = 1 then
              ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0 := by
      rw [card_negWitnesses, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hp : parity ends b = 0 ∧ bDotW b w = 1 <;> simp [hp]
    rw [qwgtInt_incidence_dg, hpos, hneg, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hp : parity ends b = 0
    · by_cases h0 : bDotW b w = 0
      · have h1 : ¬ (bDotW b w = 1) := by rw [h0]; decide
        rw [if_pos hp, if_pos ⟨hp, h0⟩, if_neg (fun h => h1 h.2), h0, sgnZ_zero]
        ring
      · by_cases h1 : bDotW b w = 1
        · rw [if_pos hp, if_neg (fun h => h0 h.2), if_pos ⟨hp, h1⟩, h1, sgnZ_one]
          ring
        · have hz : bDotW b w = 1 := by
            rcases eq_zero_or_one (bDotW b w) with h | h
            · exact absurd h h0
            · exact h
          exact absurd hz h1
    · rw [if_neg hp, if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
      ring
  rw [← qwgtInt_cast (incidence ends) (dg w) x y, hZ]
  push_cast
  ring

theorem source_corollary1_witness_balance (ends : E → V × V) (w : E → ZMod 2)
    (x y : ℕ) :
    (posWitnesses (E := E) (V := V) x y ends w).card
        + (negWitnesses (E := E) (V := V) x y ends w).card
      = (witnesses (E := E) (V := V) x y ends).card := by
  classical
  rw [card_posWitnesses, card_negWitnesses, card_witnesses, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : parity ends b = 0
  · by_cases h0 : bDotW b w = 0
    · have h1 : ¬ (bDotW b w = 1) := by rw [h0]; decide
      rw [if_pos ⟨hp, h0⟩, if_neg (fun h => h1 h.2), if_pos hp]
      ring
    · by_cases h1 : bDotW b w = 1
      · rw [if_neg (fun h => h0 h.2), if_pos ⟨hp, h1⟩, if_pos hp]
        ring
      · have hz : bDotW b w = 1 := by
          rcases eq_zero_or_one (bDotW b w) with h | h
          · exact absurd h h0
          · exact h
        exact absurd hz h1
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1), if_neg hp]

omit [DecidableEq E] in

lemma prod_weight (x y : ℕ) (b : E → ZMod 2) :
    (∏ e : E, (if b e = 0 then y else x))
      = x ^ suppCard b * y ^ (Fintype.card E - suppCard b) := by
  classical
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset E) (fun e => b e = 0) (fun e => if b e = 0 then y else x)
  have hpos : (Finset.univ.filter (fun e : E => b e = 0)).prod
      (fun e => if b e = 0 then y else x) = y ^ (Fintype.card E - suppCard b) := by
    have hconst : (Finset.univ.filter (fun e : E => b e = 0)).prod
        (fun e => if b e = 0 then y else x)
          = (Finset.univ.filter (fun e : E => b e = 0)).prod (fun _ => y) := by
      apply Finset.prod_congr rfl
      intro e he
      rw [if_pos (Finset.mem_filter.mp he).2]
    rw [hconst, Finset.prod_const, ← Fintype.card_subtype, card_zeroDomain]
  have hneg : (Finset.univ.filter (fun e : E => ¬ b e = 0)).prod
      (fun e => if b e = 0 then y else x) = x ^ suppCard b := by
    have hconst : (Finset.univ.filter (fun e : E => ¬ b e = 0)).prod
        (fun e => if b e = 0 then y else x)
          = (Finset.univ.filter (fun e : E => ¬ b e = 0)).prod (fun _ => x) := by
      apply Finset.prod_congr rfl
      intro e he
      rw [if_neg (Finset.mem_filter.mp he).2]
    rw [hconst, Finset.prod_const]
    have hcard : Fintype.card {e : E // ¬ b e = 0} = suppCard b := by
      simpa only [ne_eq] using card_colourDomain b
    rw [← Fintype.card_subtype, hcard]
  rw [← hsplit, hpos, hneg, mul_comm]

theorem sum_weight_eq_add_pow (x y : ℕ) :
    (∑ b : E → ZMod 2, x ^ suppCard b * y ^ (Fintype.card E - suppCard b))
      = (x + y) ^ Fintype.card E := by
  classical
  have hprod : (∏ e : E, (x + y))
      = ∑ b : E → ZMod 2, ∏ e : E, (if b e = 0 then y else x) := by
    have hstep : (∏ e : E, (x + y))
        = ∏ e : E, ∑ t : ZMod 2, (if t = 0 then y else x) := by
      apply Finset.prod_congr rfl
      intro e _
      have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      rw [huniv, Finset.sum_pair (by decide)]
      simp [add_comm]
    rw [hstep, Finset.prod_univ_sum, Fintype.piFinset_univ]
  calc (∑ b : E → ZMod 2, x ^ suppCard b * y ^ (Fintype.card E - suppCard b))
      = ∑ b : E → ZMod 2, ∏ e : E, (if b e = 0 then y else x) :=
        Finset.sum_congr rfl (fun b _ => (prod_weight x y b).symm)
    _ = ∏ e : E, (x + y) := hprod.symm
    _ = (x + y) ^ Fintype.card E := by rw [Finset.prod_const, Finset.card_univ]

omit [DecidableEq V] in

theorem qwgtInt_abs_le (A : Matrix V E (ZMod 2)) (B : Matrix E E (ZMod 2)) (x y : ℕ) :
    |qwgtInt A B x y| ≤ (((x + y) ^ Fintype.card E : ℕ) : ℤ) := by
  classical
  have hterm : ∀ b : E → ZMod 2,
      |if A.mulVec b = 0 then
        sgnZ (∑ e, b e * (B.mulVec b) e) *
          ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0|
        = (if A.mulVec b = 0 then
            ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0) := by
    intro b
    by_cases h : A.mulVec b = 0
    · rw [if_pos h, if_pos h]
      have hs : |sgnZ (∑ e, b e * (B.mulVec b) e)| = 1 := by
        rcases eq_zero_or_one (∑ e, b e * (B.mulVec b) e) with hz | hz <;>
          simp [sgnZ, hz]
      rw [abs_mul, hs, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    · rw [if_neg h, if_neg h]
      simp
  have hsum : (∑ b : E → ZMod 2,
        (if A.mulVec b = 0 then
          ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0))
      ≤ ∑ b : E → ZMod 2,
          ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro b _
    by_cases h : A.mulVec b = 0
    · rw [if_pos h]
    · rw [if_neg h]
      positivity
  have hcast : (∑ b : E → ZMod 2,
        ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ))
      = (((x + y) ^ Fintype.card E : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, sum_weight_eq_add_pow]
  calc |qwgtInt A B x y|
      ≤ ∑ b : E → ZMod 2,
          |if A.mulVec b = 0 then
            sgnZ (∑ e, b e * (B.mulVec b) e) *
              ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0| := by
          rw [qwgtInt]
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : E → ZMod 2,
          (if A.mulVec b = 0 then
            ((x ^ suppCard b * y ^ (Fintype.card E - suppCard b) : ℕ) : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hterm b]
    _ ≤ _ := hsum
    _ = (((x + y) ^ Fintype.card E : ℕ) : ℤ) := hcast

theorem source_corollary1_partition_witness (ends : E → V × V)
    (hLoop : ∀ e, (ends e).1 ≠ (ends e).2) (w : E → ZMod 2) (Θ μ : ℂ) (m : ℕ)
    (hΘ : Θ * μ ^ Fintype.card E = 1) :
    μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V * partition ends w Θ (m : ℂ)
      = ((posWitnesses (E := E) (V := V) m 1 ends w).card : ℂ)
        - ((negWitnesses (E := E) (V := V) m 1 ends w).card : ℂ) := by
  rw [source_theorem2_qwgt ends hLoop w Θ (m : ℂ) μ hΘ]
  simpa using source_corollary1_qwgt_signed_counts ends w m 1

end Qatlib.Papers.IsingPart03.MainResults
