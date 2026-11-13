/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodPairCountingStat
import Mathlib.Algebra.Order.Round
import Mathlib.Combinatorics.Pigeonhole

/-!
# Counting good discrete-logarithm pairs

Shows that every small-residue first coordinate extends to a good pair and bounds the number of
such first coordinates. These finite counting estimates prove `dlogGoodPairCounting`, supplying
the combinatorial input for the discrete-logarithm probability analysis associated with
[Shor1997].

## Main statements

* `dlog_extend_small_residue`: Extends a small-residue first coordinate to a good pair.
* `dlog_small_residue_real_count`: Gives the real lower bound `q / 12` on the number of small
  residues.
* `dlogGoodPairCounting`: Proves the counting contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open scoped Classical BigOperators
set_option autoImplicit false

/-- Every small-residue first coordinate extends to a good pair when `q > 0`. -/
theorem dlog_extend_small_residue (p q r : ℕ) (hq : 0 < q) (c : Fin q)
    (hc : dlogSmallResidue p q c) : ∃ d : Fin q, dlogGoodPair p q r c d := by
  let u : ℝ := (r : ℝ)*(c : ℕ) - (r : ℝ)/((p-1 : ℕ) : ℝ)*
    (centeredResidue (q : ℤ) ((c : ℕ)*(p-1) : ℤ) : ℝ)
  let D : ℤ := (-round u) % (q : ℤ)
  let Q : ℤ := (-round u) / (q : ℤ)
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hd0 : 0 ≤ D := Int.emod_nonneg _ (ne_of_gt hqz)
  have hdq : D < q := Int.emod_lt_of_pos _ hqz
  let d : Fin q := ⟨D.toNat, by omega⟩
  have hv : ((d : ℕ) : ℤ) = D := Int.toNat_of_nonneg hd0
  have hvr : (d : ℕ) = (D : ℝ) := by exact_mod_cast hv
  have he : D + (q : ℤ)*Q = -round u := Int.emod_add_mul_ediv _ _
  have her : (D : ℝ)+(q : ℝ)*(Q : ℝ) = -(round u : ℝ) := by exact_mod_cast he
  have hs : dlogT p q r c d - ((-Q : ℤ) : ℝ)*(q : ℝ) = u-(round u : ℝ) := by
    dsimp [dlogT, u]
    push_cast
    rw [hvr]
    nlinarith only [her]
  refine ⟨d, ⟨⟨-Q, ?_⟩, hc⟩⟩
  rw [hs]
  exact abs_sub_round u

/-- The number of good pairs is at least the number of small-residue first coordinates when `q >
0`. -/
theorem dlog_good_pairs_ge_small (p q r : ℕ) (hq : 0 < q) :
    (Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card ≤
      (Finset.univ.filter fun cd : Fin q × Fin q => dlogGoodPair p q r cd.1 cd.2).card := by
  letI : NeZero q := ⟨ne_of_gt hq⟩
  let S := Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c
  let f : Fin q → Fin q × Fin q := fun c =>
    (c, if hc : dlogSmallResidue p q c then
      Classical.choose (dlog_extend_small_residue p q r hq c hc) else 0)
  have hf : Function.Injective f := by
    intro a b h
    exact congrArg Prod.fst h
  have hsub : S.image f ⊆ Finset.univ.filter fun cd : Fin q × Fin q =>
      dlogGoodPair p q r cd.1 cd.2 := by
    intro cd hcd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hcd
    have hs : dlogSmallResidue p q c := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [f]
    rw [dif_pos hs]
    exact Classical.choose_spec (dlog_extend_small_residue p q r hq c hs)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hh
  exact hh

/-- If `z` and `w` are congruent modulo a positive `q` and `-q < 2 * w ≤ q`, then the centered
residue of `z` is `w`. -/
private theorem dlog_centered_eq (q z w : ℤ) (_hq : 0 < q)
    (hmod : z % q = w % q) (hw : -q < 2*w ∧ 2*w ≤ q) : centeredResidue q z = w := by
  unfold centeredResidue
  (try dsimp only)
  rw [hmod]
  by_cases h0 : 0 ≤ w
  · rw [Int.emod_eq_of_lt h0 (by omega : w < q), if_pos (by omega : w ≤ q/2)]
  · have hr : w%q = w+q := by
      have hh := Int.emod_eq_of_lt (by omega : 0 ≤ w+q) (by omega : w+q < q)
      simpa using! hh
    rw [hr, if_neg (by omega : ¬w+q ≤ q/2)]
    ring

/-- For positive `q`, at least `q / 12` first coordinates satisfy the small-residue condition,
with natural-number division in the bound. -/
theorem dlog_small_residue_count (p q : ℕ) (hq : 0 < q) :
    q/12 ≤ (Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card := by
  by_cases hq12 : q < 12
  · rw [Nat.div_eq_of_lt hq12]
    exact Nat.zero_le _
  letI : NeZero q := ⟨ne_of_gt hq⟩
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  let m : ℤ := (p : ℤ)-1
  let z : Fin q → ℤ := fun c => ((c : ℕ) : ℤ)*m
  let R : Fin q → ℤ := fun c => z c % (q : ℤ)
  have hR0 (c : Fin q) : 0 ≤ R c := Int.emod_nonneg _ (ne_of_gt hqz)
  have hRq (c : Fin q) : R c < q := Int.emod_lt_of_pos _ hqz
  have hRn (c : Fin q) : (R c).toNat < q := by
    have h0 := hR0 c
    have h1 := hRq c
    omega
  let B : Fin q → Fin 12 := fun c =>
    ⟨12*(R c).toNat/q, (Nat.div_lt_iff_lt_mul hq).2
      (by simpa only [mul_comm] using! Nat.mul_lt_mul_of_pos_left (hRn c) (by decide : 0 < 12))⟩
  have hcard : Fintype.card (Fin 12)*(q/12) ≤ Fintype.card (Fin q) := by
    simpa only [Fintype.card_fin, mul_comm] using! Nat.div_mul_le_self q 12
  obtain ⟨b, hb⟩ := Fintype.exists_le_card_fiber_of_mul_le_card B hcard
  let S := Finset.univ.filter fun c : Fin q => B c = b
  have hne : S.Nonempty := by
    apply Finset.card_pos.mp
    have hh : 0 < q/12 := Nat.div_pos (by omega : 12 ≤ q) (by decide)
    exact hh.trans_le hb
  obtain ⟨c₀, hc₀⟩ := hne
  have hB₀ : B c₀ = b := (Finset.mem_filter.mp hc₀).2
  have hRN (c : Fin q) : ((R c).toNat : ℤ) = R c := Int.toNat_of_nonneg (hR0 c)
  have hlow (c : Fin q) : ((B c).val : ℤ)*(q : ℤ) ≤ 12*R c := by
    have hn : (B c).val*q ≤ 12*(R c).toNat := Nat.div_mul_le_self _ _
    have hi : ((B c).val : ℤ)*(q : ℤ) ≤ 12*((R c).toNat : ℤ) := by exact_mod_cast hn
    simpa only [hRN] using! hi
  have hhigh (c : Fin q) : 12*R c < (((B c).val : ℤ)+1)*(q : ℤ) := by
    have hn : 12*(R c).toNat < ((B c).val+1)*q :=
      (Nat.div_lt_iff_lt_mul hq).1 (Nat.lt_succ_self _)
    have hi : 12*((R c).toNat : ℤ) < (((B c).val : ℤ)+1)*(q : ℤ) := by exact_mod_cast hn
    simpa only [hRN] using! hi
  let e : Fin q → Fin q := fun c => c-c₀
  have he : Function.Injective e := by
    intro a b h
    exact sub_left_injective h
  have hsub : S.image e ⊆ Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
    have hB : B c = B c₀ := (Finset.mem_filter.mp hc).2.trans hB₀.symm
    have hv : (B c).val = (B c₀).val := congrArg Fin.val hB
    have hl := hlow c
    have hh := hhigh c
    rw [hv] at hl hh
    have hlo := hlow c₀
    have hhi := hhigh c₀
    have hd : -(q : ℤ) < 12*(R c-R c₀) ∧ 12*(R c-R c₀) < (q : ℤ) := by
      constructor <;> linarith
    have hshift : (q : ℤ) ∣ z (e c)-(z c-z c₀) := by
      dsimp [z, e]
      rw [Fin.intCast_val_sub_eq_sub_add_ite]
      split_ifs
      · exact ⟨0, by ring⟩
      · exact ⟨m, by ring⟩
    have hraw (x : Fin q) : (q : ℤ) ∣ z x-R x := by
      refine ⟨z x/(q : ℤ), ?_⟩
      have hi := Int.emod_add_mul_ediv (z x) (q : ℤ)
      dsimp [R]
      linarith
    have hdiv : (q : ℤ) ∣ z (e c)-(R c-R c₀) := by
      have hi := dvd_add hshift (dvd_sub (hraw c) (hraw c₀))
      convert! hi using 1
      ring
    have hmod : z (e c)%(q : ℤ) = (R c-R c₀)%(q : ℤ) :=
      (Int.modEq_iff_dvd.mpr hdiv).symm
    have hcenter : centeredResidue (q : ℤ) (z (e c)) = R c-R c₀ :=
      dlog_centered_eq _ _ _ hqz hmod (by constructor <;> omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change ((|centeredResidue (q : ℤ) (z (e c))| : ℤ) : ℝ) ≤ (q : ℝ)/12
    rw [hcenter]
    have hd0 : -(q : ℝ) < 12*((R c-R c₀ : ℤ) : ℝ) := by exact_mod_cast hd.1
    have hd1 : 12*((R c-R c₀ : ℤ) : ℝ) < (q : ℝ) := by exact_mod_cast hd.2
    have hab : |((R c-R c₀ : ℤ) : ℝ)| ≤ (q : ℝ)/12 := by
      apply abs_le.mpr
      constructor <;> linarith
    simpa using! hab
  have himg := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ he] at himg
  exact hb.trans himg

/-- For positive `q`, the real cardinality of the small-residue first coordinates is at least
`(q : ℝ) / 12`. -/
theorem dlog_small_residue_real_count (p q : ℕ) (hq : 0 < q) :
    (q : ℝ)/12 ≤ ((Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card : ℝ) := by
  letI : NeZero q := ⟨ne_of_gt hq⟩
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  let m : ℤ := (p : ℤ)-1
  let z : Fin q → ℤ := fun c => ((c : ℕ) : ℤ)*m
  let R : Fin q → ℤ := fun c => z c % (q : ℤ)
  have hR0 (c : Fin q) : 0 ≤ R c := Int.emod_nonneg _ (ne_of_gt hqz)
  have hRq (c : Fin q) : R c < q := Int.emod_lt_of_pos _ hqz
  have hRn (c : Fin q) : (R c).toNat < q := by
    have h0 := hR0 c
    have h1 := hRq c
    omega
  let B : Fin q → Fin 12 := fun c =>
    ⟨12*(R c).toNat/q, (Nat.div_lt_iff_lt_mul hq).2
      (by simpa only [mul_comm] using! Nat.mul_lt_mul_of_pos_left (hRn c) (by decide : 0 < 12))⟩
  let n := (q-1)/12
  have hcard : Fintype.card (Fin 12)*n < Fintype.card (Fin q) := by
    have h := Nat.div_mul_le_self (q-1) 12
    simp only [Fintype.card_fin]
    dsimp [n]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card B hcard
  let S := Finset.univ.filter fun c : Fin q => B c = b
  have hne : S.Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_le_of_lt (Nat.zero_le n) hb
  obtain ⟨c₀, hc₀⟩ := hne
  have hB₀ : B c₀ = b := (Finset.mem_filter.mp hc₀).2
  have hRN (c : Fin q) : ((R c).toNat : ℤ) = R c := Int.toNat_of_nonneg (hR0 c)
  have hlow (c : Fin q) : ((B c).val : ℤ)*(q : ℤ) ≤ 12*R c := by
    have hn : (B c).val*q ≤ 12*(R c).toNat := Nat.div_mul_le_self _ _
    have hi : ((B c).val : ℤ)*(q : ℤ) ≤ 12*((R c).toNat : ℤ) := by exact_mod_cast hn
    simpa only [hRN] using! hi
  have hhigh (c : Fin q) : 12*R c < (((B c).val : ℤ)+1)*(q : ℤ) := by
    have hn : 12*(R c).toNat < ((B c).val+1)*q :=
      (Nat.div_lt_iff_lt_mul hq).1 (Nat.lt_succ_self _)
    have hi : 12*((R c).toNat : ℤ) < (((B c).val : ℤ)+1)*(q : ℤ) := by exact_mod_cast hn
    simpa only [hRN] using! hi
  let e : Fin q → Fin q := fun c => c-c₀
  have he : Function.Injective e := by
    intro a b h
    exact sub_left_injective h
  have hsub : S.image e ⊆ Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
    have hB : B c = B c₀ := (Finset.mem_filter.mp hc).2.trans hB₀.symm
    have hv : (B c).val = (B c₀).val := congrArg Fin.val hB
    have hl := hlow c
    have hh := hhigh c
    rw [hv] at hl hh
    have hlo := hlow c₀
    have hhi := hhigh c₀
    have hd : -(q : ℤ) < 12*(R c-R c₀) ∧ 12*(R c-R c₀) < (q : ℤ) := by
      constructor <;> linarith
    have hshift : (q : ℤ) ∣ z (e c)-(z c-z c₀) := by
      dsimp [z, e]
      rw [Fin.intCast_val_sub_eq_sub_add_ite]
      split_ifs
      · exact ⟨0, by ring⟩
      · exact ⟨m, by ring⟩
    have hraw (x : Fin q) : (q : ℤ) ∣ z x-R x := by
      refine ⟨z x/(q : ℤ), ?_⟩
      have hi := Int.emod_add_mul_ediv (z x) (q : ℤ)
      dsimp [R]
      linarith
    have hdiv : (q : ℤ) ∣ z (e c)-(R c-R c₀) := by
      have hi := dvd_add hshift (dvd_sub (hraw c) (hraw c₀))
      convert! hi using 1
      ring
    have hmod : z (e c)%(q : ℤ) = (R c-R c₀)%(q : ℤ) :=
      (Int.modEq_iff_dvd.mpr hdiv).symm
    have hcenter : centeredResidue (q : ℤ) (z (e c)) = R c-R c₀ :=
      dlog_centered_eq _ _ _ hqz hmod (by constructor <;> omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change ((|centeredResidue (q : ℤ) (z (e c))| : ℤ) : ℝ) ≤ (q : ℝ)/12
    rw [hcenter]
    have hd0 : -(q : ℝ) < 12*((R c-R c₀ : ℤ) : ℝ) := by exact_mod_cast hd.1
    have hd1 : 12*((R c-R c₀ : ℤ) : ℝ) < (q : ℝ) := by exact_mod_cast hd.2
    have hab : |((R c-R c₀ : ℤ) : ℝ)| ≤ (q : ℝ)/12 := by
      apply abs_le.mpr
      constructor <;> linarith
    simpa using! hab
  have himg := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ he] at himg
  have hceil : q ≤ 12*(n+1) := by
    have h := Nat.mod_lt (q-1) (by norm_num : 0 < 12)
    have he := Nat.mod_add_div (q-1) 12
    dsimp [n]
    omega
  have hbS : n < S.card := hb
  have hlarge : n+1 ≤ (Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card :=
    (Nat.succ_le_of_lt hbS).trans himg
  have hcount : q ≤ 12*(Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card :=
    hceil.trans (Nat.mul_le_mul_left 12 hlarge)
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
  exact_mod_cast (by simpa only [mul_comm] using! hcount)

/-- Establishes the lower bounds on small-residue coordinates and good pairs used in the
discrete-logarithm counting analysis associated with [Shor1997]. -/
theorem dlogGoodPairCounting : DlogGoodPairCounting := by
  intro p q r _ _hprime hp hpq
  have hq : 0 < q := by omega
  have hc := dlog_small_residue_count p q hq
  exact ⟨hc, hc.trans (dlog_good_pairs_ge_small p q r hq)⟩

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
