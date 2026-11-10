/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralHSP04.MainResults.CombinationProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

open scoped BigOperators

def nonzeroMasks (l : ℕ) : Finset (Mask l) := Finset.univ.erase (zeroMask l)

theorem card_nonzeroMasks (l : ℕ) :
    (nonzeroMasks l).card = 2 ^ (l + 4) - 1 := by
  unfold nonzeroMasks
  rw [Finset.card_erase_of_mem (Finset.mem_univ (zeroMask l)), Finset.card_univ]
  simp [Mask]

def matchIndicator (l : ℕ) (z : ZMod (2 ^ l)) (b : Mask l)
    (y : SampleSpace l) : ℝ :=
  if dotMod l b y = z then 1 else 0

def matchStat (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) : ℝ :=
  ∑ b ∈ nonzeroMasks l, matchIndicator l z b y

theorem uniformProb_match {l : ℕ} {b : Mask l} (hb : b ≠ zeroMask l)
    (z : ZMod (2 ^ l)) :
    uniformProb (fun y : SampleSpace l => dotMod l b y = z) =
      ((2 : ℝ) ^ l)⁻¹ := by
  rw [uniformProb_eq_filter]
  rw [linForm_fiber_card hb z, natCard_sampleSpace]
  have hA : (((2 ^ l) ^ (l + 3) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 3) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hB : (((2 ^ l) ^ (l + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 4) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hA, hB]
  have hexp : ((2 : ℝ) ^ l) ^ (l + 4) = ((2 : ℝ) ^ l) ^ (l + 3) * (((2 : ℝ) ^ l) ^ 1) := by
    rw [show (l : ℕ) + 4 = (l + 3) + 1 by omega, pow_add]
  rw [hexp, pow_one]
  have hq : ((2 : ℝ) ^ l) ≠ 0 := by positivity
  have hq3 : (((2 : ℝ) ^ l) ^ (l + 3)) ≠ 0 := by positivity
  field_simp

theorem sum_indicator_gen {Ω : Type} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] :
    (∑ y : Ω, (if p y then (1 : ℝ) else 0)) =
      ((Finset.univ.filter p).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp

theorem uniformProb_mono {Ω : Type} [Fintype Ω] {p q : Ω → Prop}
    (h : ∀ x, p x → q x) : uniformProb p ≤ uniformProb q := by
  classical
  rw [uniformProb_eq_filter p, uniformProb_eq_filter q]
  have hc : (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card :=
    Finset.card_le_card (Finset.monotone_filter_right _ (fun x _ hx => h x hx))
  have hN : (0 : ℝ) ≤ (Nat.card Ω : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) hN

theorem uniformProb_not {Ω : Type} [Fintype Ω] [Nonempty Ω] (p : Ω → Prop) :
    uniformProb (fun x => ¬ p x) = 1 - uniformProb p := by
  classical
  rw [uniformProb_eq_filter (fun x => ¬ p x), uniformProb_eq_filter p]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) p
  have hN : (Nat.card Ω : ℝ) = ((Finset.univ : Finset Ω).card : ℝ) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hcast : ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ)
      + ((Finset.univ.filter p).card : ℝ) = (Nat.card Ω : ℝ) := by
    have h2 := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at h2
    rw [hN]
    linarith
  rw [hN]
  field_simp
  linarith

lemma sum_sq_sub {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (μ : ℝ) :
    (∑ x, (f x - μ) ^ 2) =
      (∑ x, (f x) ^ 2) - 2 * μ * (∑ x, f x) + (Nat.card Ω : ℝ) * μ ^ 2 := by
  have hconst : (∑ x : Ω, μ ^ 2) = (Nat.card Ω : ℝ) * μ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  calc (∑ x, (f x - μ) ^ 2)
      = ∑ x, ((f x) ^ 2 - 2 * μ * f x + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = (∑ x, (f x) ^ 2) - (∑ x, 2 * μ * f x) + (∑ x, μ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ x, (f x) ^ 2) - 2 * μ * (∑ x, f x) + (Nat.card Ω : ℝ) * μ ^ 2 := by
        rw [hconst, Finset.mul_sum]

theorem finite_chebyshev {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {μ t : ℝ} (ht : 0 < t)
    (hμ : μ = (∑ x, f x) / (Nat.card Ω : ℝ)) :
    uniformProb (fun x => t ≤ |f x - μ|) ≤
      ((∑ x, (f x) ^ 2) / (Nat.card Ω : ℝ) - μ ^ 2) / t ^ 2 := by
  classical
  set N : ℝ := (Nat.card Ω : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < Nat.card Ω := Nat.card_pos
    simpa [hNdef] using (by exact_mod_cast this : (0 : ℝ) < (Nat.card Ω : ℝ))
  have hN : N ≠ 0 := hNpos.ne'
  have hterm : ∀ x, (if t ≤ |f x - μ| then (1 : ℝ) else 0) ≤ (f x - μ) ^ 2 / t ^ 2 := by
    intro x
    by_cases h : t ≤ |f x - μ|
    · rw [if_pos h, le_div_iff₀ (by positivity), one_mul]
      nlinarith [sq_abs (f x - μ), abs_nonneg (f x - μ), ht, h]
    · rw [if_neg h]
      positivity
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hterm x)
  rw [sum_indicator_gen (fun x => t ≤ |f x - μ|)] at hsum
  have hsumf : (∑ x, f x) = N * μ := by
    rw [hμ]
    field_simp
  have hvar : (∑ x, (f x - μ) ^ 2) / N = (∑ x, (f x) ^ 2) / N - μ ^ 2 := by
    rw [sum_sq_sub, hsumf]
    field_simp
    ring
  have h1 : ((∑ x, (f x - μ) ^ 2) / t ^ 2) / N =
      ((∑ x, (f x - μ) ^ 2) / N) / t ^ 2 := by
    rw [div_div, div_div, mul_comm]
  rw [uniformProb_eq_filter]
  have hdiv : ((Finset.univ.filter (fun x => t ≤ |f x - μ|)).card : ℝ) / N
      ≤ (∑ x, (f x - μ) ^ 2 / t ^ 2) / N :=
    div_le_div_of_nonneg_right hsum hNpos.le
  have heq : (∑ x, (f x - μ) ^ 2 / t ^ 2) / N =
      ((∑ x, (f x) ^ 2) / N - μ ^ 2) / t ^ 2 := by
    rw [← Finset.sum_div, h1, hvar]
  exact le_trans hdiv (le_of_eq heq)

lemma card_filter_erase_add {α : Type} [Fintype α] [DecidableEq α] (a : α)
    (p : α → Prop) [DecidablePred p] (ha : p a) :
    (Finset.univ.filter p).card = ((Finset.univ.erase a).filter p).card + 1 := by
  have hset : Finset.univ.filter p = insert a ((Finset.univ.erase a).filter p) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
    simp only [Finset.mem_univ, true_and, and_true]
    constructor
    · intro hx
      by_cases h : x = a
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | ⟨_, hx⟩)
      · exact ha
      · exact hx
  rw [hset, Finset.card_insert_of_notMem (by simp)]

lemma card_filter_erase_eq {α : Type} [Fintype α] [DecidableEq α] (a : α)
    (p : α → Prop) [DecidablePred p] (ha : ¬ p a) :
    (Finset.univ.filter p).card = ((Finset.univ.erase a).filter p).card := by
  have hset : Finset.univ.filter p = (Finset.univ.erase a).filter p := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    simp only [Finset.mem_univ, true_and, and_true]
    constructor
    · intro hx; exact ⟨fun h => ha (h ▸ hx), hx⟩
    · intro hx; exact hx.2
  rw [hset]

theorem first_moment (l : ℕ) (z : ZMod (2 ^ l)) :
    (∑ y : SampleSpace l, matchStat l y z) / (Nat.card (SampleSpace l) : ℝ) =
      16 - ((2 : ℝ) ^ l)⁻¹ := by
  classical
  have hswap : (∑ y : SampleSpace l, matchStat l y z)
      = ∑ b ∈ nonzeroMasks l,
          (∑ y : SampleSpace l, (if dotMod l b y = z then (1 : ℝ) else 0)) := by
    unfold matchStat matchIndicator
    rw [Finset.sum_comm]
  rw [hswap]
  have hstep : ∀ b ∈ nonzeroMasks l,
      (∑ y : SampleSpace l, (if dotMod l b y = z then (1 : ℝ) else 0))
        = (((2 ^ l) ^ (l + 3) : ℕ) : ℝ) := by
    intro b hb
    rw [sum_indicator_gen, linForm_fiber_card (Finset.ne_of_mem_erase hb) z]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul, card_nonzeroMasks]
  rw [natCard_sampleSpace]
  rw [show ((2 ^ (l + 4) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (l + 4) - 1 by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num]
  rw [show (((2 ^ l) ^ (l + 3) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 3) by
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  rw [show (((2 ^ l) ^ (l + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 4) by
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  rw [show (2 : ℝ) ^ (l + 4) = 16 * (2 : ℝ) ^ l by
        rw [pow_add]; norm_num; ring]
  have hq : (2 : ℝ) ^ l ≠ 0 := by positivity
  field_simp
  ring

theorem sum_indicator_mul (l : ℕ) (z : ZMod (2 ^ l)) (b b' : Mask l) :
    (∑ y : SampleSpace l, matchIndicator l z b y * matchIndicator l z b' y)
      = ((Finset.univ.filter
          (fun y : SampleSpace l => dotMod l b y = z ∧ dotMod l b' y = z)).card : ℝ) := by
  classical
  have h : ∀ y : SampleSpace l,
      matchIndicator l z b y * matchIndicator l z b' y
        = (if (dotMod l b y = z ∧ dotMod l b' y = z) then (1 : ℝ) else 0) := by
    intro y
    unfold matchIndicator
    by_cases hp : dotMod l b y = z <;> by_cases hq : dotMod l b' y = z <;> simp [hp, hq]
  rw [Finset.sum_congr rfl (fun y _ => h y), sum_indicator_gen]

theorem second_moment (l : ℕ) (z : ZMod (2 ^ l)) :
    (∑ y : SampleSpace l, (matchStat l y z) ^ 2) / (Nat.card (SampleSpace l) : ℝ) =
      272 - 49 * ((2 : ℝ) ^ l)⁻¹ + 2 * (((2 : ℝ) ^ l)⁻¹) ^ 2 := by
  classical
  set S := nonzeroMasks l with hS
  set A : ℝ := (((2 ^ l) ^ (l + 3) : ℕ) : ℝ) with hA
  set B : ℝ := (((2 ^ l) ^ (l + 2) : ℕ) : ℝ) with hB
  have hexp : (∑ y : SampleSpace l, (matchStat l y z) ^ 2)
      = ∑ b ∈ S, ∑ b' ∈ S,
          (∑ y : SampleSpace l, matchIndicator l z b y * matchIndicator l z b' y) := by
    have hone : ∀ y : SampleSpace l, (matchStat l y z) ^ 2
        = ∑ b ∈ S, ∑ b' ∈ S, matchIndicator l z b y * matchIndicator l z b' y := by
      intro y
      unfold matchStat
      rw [pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun y _ => hone y)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  have hG : ∀ b ∈ S, ∀ b' ∈ S,
      (∑ y : SampleSpace l, matchIndicator l z b y * matchIndicator l z b' y)
        = if b = b' then A else B := by
    intro b hb b' hb'
    rw [sum_indicator_mul]
    by_cases hbb : b = b'
    · rw [if_pos hbb]
      subst hbb
      rw [show (Finset.univ.filter (fun y : SampleSpace l => dotMod l b y = z ∧ dotMod l b y = z))
            = (Finset.univ.filter (fun y : SampleSpace l => dotMod l b y = z)) by
          apply Finset.filter_congr
          intro y _
          exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩]
      rw [linForm_fiber_card (Finset.ne_of_mem_erase (hS ▸ hb)) z, hA]
    · rw [if_neg hbb]
      rw [pairForm_fiber_card (Finset.ne_of_mem_erase (hS ▸ hb))
            (Finset.ne_of_mem_erase (hS ▸ hb')) hbb z z, hB]
  have hinner : ∀ b ∈ S,
      (∑ b' ∈ S, (∑ y : SampleSpace l, matchIndicator l z b y * matchIndicator l z b' y))
        = A + ((S.card - 1 : ℕ) : ℝ) * B := by
    intro b hb
    rw [Finset.sum_congr rfl (fun b' hb' => hG b hb b' hb')]
    rw [← Finset.add_sum_erase S (fun b' => if b = b' then A else B) hb]
    rw [if_pos rfl]
    have hrest : (∑ x ∈ S.erase b, (if b = x then A else B)) = ∑ _x ∈ S.erase b, B := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg]
      exact (Finset.ne_of_mem_erase hx).symm
    rw [hrest, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hb]
  rw [hexp, Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, card_nonzeroMasks]
  rw [natCard_sampleSpace]
  simp only [hA, hB]
  have hc1 : ((2 ^ (l + 4) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (l + 4) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
  have hc2 : ((2 ^ (l + 4) - 2 : ℕ) : ℝ) = (2 : ℝ) ^ (l + 4) - 2 := by
    have h2 : (2 : ℕ) ≤ 2 ^ (l + 4) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (l + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub h2, Nat.cast_pow]; norm_num
  rw [show (2 ^ (l + 4) - 1 - 1 : ℕ) = (2 ^ (l + 4) - 2) by omega, hc2, hc1]
  rw [show (((2 ^ l) ^ (l + 3) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 3) by
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  rw [show (((2 ^ l) ^ (l + 2) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 2) by
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  rw [show (((2 ^ l) ^ (l + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 4) by
        simp only [Nat.cast_pow, Nat.cast_ofNat]]
  rw [show (2 : ℝ) ^ (l + 4) = 16 * (2 : ℝ) ^ l by
        rw [pow_add]; norm_num; ring]
  have hq : (2 : ℝ) ^ l ≠ 0 := by positivity
  field_simp
  ring

theorem variance_eq (l : ℕ) (z : ZMod (2 ^ l)) :
    (∑ y : SampleSpace l, (matchStat l y z) ^ 2) / (Nat.card (SampleSpace l) : ℝ) -
        ((∑ y : SampleSpace l, matchStat l y z) / (Nat.card (SampleSpace l) : ℝ)) ^ 2 =
      16 - 17 * ((2 : ℝ) ^ l)⁻¹ + (((2 : ℝ) ^ l)⁻¹) ^ 2 := by
  rw [second_moment, first_moment]
  ring

theorem matchStat_eq_card (l : ℕ) (y : SampleSpace l) (z : ZMod (2 ^ l)) :
    matchStat l y z =
      (((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card : ℝ) := by
  classical
  unfold matchStat matchIndicator
  rw [← Finset.sum_filter]
  simp

lemma matchCount_zero (l : ℕ) (y : SampleSpace l) :
    matchCount l y 0 =
      ((nonzeroMasks l).filter (fun b => dotMod l b y = 0)).card + 1 := by
  unfold matchCount matchSet nonzeroMasks
  exact card_filter_erase_add (zeroMask l) (fun b => dotMod l b y = 0)
    (by simpa using! dotMod_zero_mask l y)

lemma matchCount_ne_zero {l : ℕ} (y : SampleSpace l) {z : ZMod (2 ^ l)} (hz : z ≠ 0) :
    matchCount l y z =
      ((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card := by
  unfold matchCount matchSet nonzeroMasks
  exact card_filter_erase_eq (zeroMask l) (fun b => dotMod l b y = z)
    (by have h0 : dotMod l (zeroMask l) y = 0 := dotMod_zero_mask l y
        intro h; exact hz (h.symm.trans h0))

theorem chebyshev_matchStat (l : ℕ) (z : ZMod (2 ^ l)) :
    uniformProb (fun y : SampleSpace l =>
        14 ≤ |matchStat l y z - (16 - ((2 : ℝ) ^ l)⁻¹)|) ≤
      (16 - 17 * ((2 : ℝ) ^ l)⁻¹ + (((2 : ℝ) ^ l)⁻¹) ^ 2) / 196 := by
  have h := finite_chebyshev (fun y : SampleSpace l => matchStat l y z)
    (μ := 16 - ((2 : ℝ) ^ l)⁻¹) (t := 14) (by norm_num) (first_moment l z).symm
  have hvar : ((∑ y : SampleSpace l, (matchStat l y z) ^ 2) / (Nat.card (SampleSpace l) : ℝ)
        - (16 - ((2 : ℝ) ^ l)⁻¹) ^ 2)
      = 16 - 17 * ((2 : ℝ) ^ l)⁻¹ + (((2 : ℝ) ^ l)⁻¹) ^ 2 := by
    rw [← first_moment l z]
    exact variance_eq l z
  rw [hvar] at h
  have h14 : ((14 : ℝ) ^ 2) = 196 := by norm_num
  rw [h14] at h
  exact h

lemma failure_imp_cheb (l : ℕ) (z : ZMod (2 ^ l)) (y : SampleSpace l)
    (hfail : ¬ combinationSucceeds l y z) :
    14 ≤ |matchStat l y z - (16 - ((2 : ℝ) ^ l)⁻¹)| := by
  classical
  set x : ℝ := ((2 : ℝ) ^ l)⁻¹ with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 := by
    rw [hxdef]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hY : matchStat l y z =
      (((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card : ℝ) :=
    matchStat_eq_card l y z
  by_cases hz : z = 0
  · subst hz
    unfold combinationSucceeds at hfail
    rw [matchCount_zero l y] at hfail
    have hcases : ((nonzeroMasks l).filter (fun b => dotMod l b y = 0)).card = 0 ∨
        32 ≤ ((nonzeroMasks l).filter (fun b => dotMod l b y = 0)).card := by omega
    rw [hY]
    rcases hcases with hc | hc
    · rw [hc]
      simp only [Nat.cast_zero]
      rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
      linarith
    · have hcR : (32 : ℝ) ≤
          (((nonzeroMasks l).filter (fun b => dotMod l b y = 0)).card : ℝ) := by
        exact_mod_cast hc
      rw [abs_of_pos (by linarith)]
      linarith
  · unfold combinationSucceeds at hfail
    rw [matchCount_ne_zero y hz] at hfail
    have hcases : ((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card ≤ 1 ∨
        33 ≤ ((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card := by omega
    rw [hY]
    rcases hcases with hc | hc
    · have hcR : (((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card : ℝ) ≤ 1 := by
        exact_mod_cast hc
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hcR : (33 : ℝ) ≤
          (((nonzeroMasks l).filter (fun b => dotMod l b y = z)).card : ℝ) := by
        exact_mod_cast hc
      rw [abs_of_pos (by linarith)]
      linarith

theorem combination_success_probability (l : ℕ) (_hl : 0 < l)
    (z : ZMod (2 ^ l)) :
    (1 : ℝ) / 2 ≤ uniformProb (fun y : SampleSpace l => combinationSucceeds l y z) := by
  classical
  set x : ℝ := ((2 : ℝ) ^ l)⁻¹ with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 := by
    rw [hxdef]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hVle : 16 - 17 * x + x ^ 2 ≤ 16 := by
    have hx2 : x ^ 2 ≤ x := by nlinarith [hxpos, hxle]
    linarith
  have hcheb := chebyshev_matchStat l z
  have hbound : (16 - 17 * ((2 : ℝ) ^ l)⁻¹ + (((2 : ℝ) ^ l)⁻¹) ^ 2) / 196 ≤ 16 / 196 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa [hxdef] using hVle
  have hmono : uniformProb (fun y : SampleSpace l => ¬ combinationSucceeds l y z) ≤
      uniformProb (fun y : SampleSpace l =>
        14 ≤ |matchStat l y z - (16 - ((2 : ℝ) ^ l)⁻¹)|) :=
    uniformProb_mono (fun y hy => failure_imp_cheb l z y hy)
  haveI : Nonempty (SampleSpace l) := ⟨0⟩
  have hcompl : uniformProb (fun y : SampleSpace l => ¬ combinationSucceeds l y z) =
      1 - uniformProb (fun y : SampleSpace l => combinationSucceeds l y z) :=
    uniformProb_not _
  have hfail_le : uniformProb (fun y : SampleSpace l => ¬ combinationSucceeds l y z) ≤ 16 / 196 :=
    le_trans hmono (le_trans hcheb hbound)
  rw [hcompl] at hfail_le
  linarith

end Qatlib.Papers.DihedralHSP04.MainResults
