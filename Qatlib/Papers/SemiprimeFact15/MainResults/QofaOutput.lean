/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiprimeFact15.MainResults.CoreObservation

set_option backward.isDefEq.respectTransparency false

/-!
# The QOFA output distribution for safe semiprimes

This file formalizes Lemma 1(2) of [Grosshans et al., 2015][GrosshansEtAl2015] (§III.C, p. 5):

> QOFA yields `d ∈ {q₁, q₂, q₁q₂, 2q₁, 2q₂, 2q₁q₂}` with probability
> `1 - 1/(q₁q₂) ∼ 1 - 4/N`; otherwise, `d ∈ {1, 2}`.

Specifically:

* the ideal QOFA output is `d = ord_N(2)/gcd(t, ord_N(2))` for `t` uniform in `{1, …, ord_N(2)}`
  (`qofaOutput`);
* for `r ∈ {q₁q₂, 2q₁q₂}`, `d` divides `2q₁q₂` (`qofaOutput_dvd_two_q1_q2`), so `d` lies in
  `usefulSet q₁ q₂ ∪ badSet`;
* `d ∈ {1, 2}` holds for `1` phase when `r = q₁q₂` and `2` phases when `r = 2q₁q₂`, giving
  exact failure probability `1/(q₁q₂)` (`bad_probability`);
* `4/N < 1/(q₁q₂)` since `N = (2q₁+1)(2q₂+1) > 4q₁q₂` (`four_div_N_lt_inv_q1q2`).

## Main statements

* `qofaOutput_mem_useful_or_bad`: every QOFA output lies in `usefulSet cs.q1 cs.q2 ∪ badSet`.
* `bad_probability`: the fraction of bad phases is `1 / (q₁ q₂)` for both possible orders.
* `four_div_N_lt_inv_q1q2`: strict bound `4 / N < 1 / (q₁ q₂)`.
* `lemma1_part2`: combined Lemma 1(2) statement.

## References

* [Grosshans et al., 2015][GrosshansEtAl2015]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SemiprimeFact15.MainResults

/-! ## The bad count `#{t ∈ {1,…,r} : qofaOutput r t ∈ {1,2}}` -/

/-- Number of "bad" phases `t ∈ {1,…,r}` at which the ideal QOFA output is `1` or `2`
([Grosshans et al., 2015][GrosshansEtAl2015], §III.C, proof of Lemma 1). -/
def badTCount (r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun t => qofaOutput r t ∈ badSet)).card

/-- `qofaOutput r r = 1` (the continued-fraction numerator `t = r` gives the trivial output). -/
theorem qofaOutput_self {r : ℕ} (hr : 0 < r) : qofaOutput r r = 1 := by
  unfold qofaOutput
  rw [Nat.gcd_eq_right (dvd_refl r)]
  exact Nat.div_self hr

/-! ## Part (a): every output is useful or bad -/

/-- **Lemma 1(2), first half** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C, Lemma 1,
p. 5): every ideal QOFA output for a true order `r ∈ {q₁q₂, 2q₁q₂}` lies in
`{q₁, q₂, q₁q₂, 2q₁, 2q₂, 2q₁q₂} ∪ {1, 2}`. -/
theorem qofaOutput_mem_useful_or_bad (cs : SafeSemiprime) (r t : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2) :
    qofaOutput r t ∈ usefulSet cs.q1 cs.q2 ∪ badSet := by
  have hdvd : qofaOutput r t ∣ 2 * cs.q1 * cs.q2 :=
    qofaOutput_dvd_two_q1_q2 cs r t hr
  rcases dvd_two_mul_q1q2 cs hdvd with h | h | h | h | h | h | h | h <;>
    simp [usefulSet, badSet, h]

/-- **Lemma 1(2), "otherwise" clause** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C,
Lemma 1, p. 5): if the QOFA output is not one of the six useful values, it is in `{1, 2}`. -/
theorem qofaOutput_not_useful_mem_bad (cs : SafeSemiprime) (r t : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2)
    (h : qofaOutput r t ∉ usefulSet cs.q1 cs.q2) :
    qofaOutput r t ∈ badSet := by
  rcases Finset.mem_union.mp (qofaOutput_mem_useful_or_bad cs r t hr) with h' | h'
  · exact absurd h' h
  · exact h'

/-! ## Part (b): exactly `1/(q₁q₂)` of the phases are bad -/

/-- For `r = q₁q₂` the only bad phase is `t = r`. -/
theorem bad_filter_q1q2 (cs : SafeSemiprime) :
    (Finset.Icc 1 (cs.q1 * cs.q2)).filter
        (fun t => qofaOutput (cs.q1 * cs.q2) t ∈ badSet) = {cs.q1 * cs.q2} := by
  have he : 0 < cs.q1 * cs.q2 := Nat.mul_pos cs.q1_prime.pos cs.q2_prime.pos
  have hodd : ¬ 2 ∣ cs.q1 * cs.q2 := (cs.q1_odd.mul cs.q2_odd).not_two_dvd_nat
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, badSet,
    Finset.mem_insert]
  constructor
  · rintro ⟨⟨_, ht2⟩, h1 | h2⟩
    · have hdvd : cs.q1 * cs.q2 ∣ t := (qofaOutput_eq_one_iff he t).mp h1
      exact Nat.le_antisymm ht2 (Nat.le_of_dvd (by omega) hdvd)
    · have hd : 2 ∣ cs.q1 * cs.q2 := h2 ▸ qofaOutput_dvd _ _
      exact absurd hd hodd
  · rintro rfl
    exact ⟨⟨by omega, le_refl _⟩, Or.inl (qofaOutput_self he)⟩

/-- For `r = 2q₁q₂` the bad phases are `t = q₁q₂` (output `2`) and `t = r` (output `1`). -/
theorem bad_filter_two_q1q2 (cs : SafeSemiprime) :
    (Finset.Icc 1 (2 * cs.q1 * cs.q2)).filter
        (fun t => qofaOutput (2 * cs.q1 * cs.q2) t ∈ badSet)
      = {cs.q1 * cs.q2, 2 * cs.q1 * cs.q2} := by
  have he : 0 < cs.q1 * cs.q2 := Nat.mul_pos cs.q1_prime.pos cs.q2_prime.pos
  have hr : 0 < 2 * cs.q1 * cs.q2 :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) cs.q1_prime.pos) cs.q2_prime.pos
  have heven : 2 ∣ 2 * cs.q1 * cs.q2 := ⟨cs.q1 * cs.q2, by ring⟩
  have hr2 : (2 * cs.q1 * cs.q2) / 2 = cs.q1 * cs.q2 := by
    have h : 2 * cs.q1 * cs.q2 = 2 * (cs.q1 * cs.q2) := by ring
    rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, Finset.mem_insert,
    badSet]
  constructor
  · rintro ⟨⟨ht1, ht2⟩, h1 | h2⟩
    · have hdvd : 2 * cs.q1 * cs.q2 ∣ t := (qofaOutput_eq_one_iff hr t).mp h1
      exact Or.inr (Nat.le_antisymm ht2 (Nat.le_of_dvd (by omega) hdvd))
    · have hg : Nat.gcd t (2 * cs.q1 * cs.q2) = cs.q1 * cs.q2 := by
        have h := (qofaOutput_eq_two_iff hr heven t).mp h2
        rwa [hr2] at h
      have hedvd : cs.q1 * cs.q2 ∣ t := hg ▸ Nat.gcd_dvd_left t (2 * cs.q1 * cs.q2)
      obtain ⟨k, hk⟩ := hedvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · rw [h0, mul_zero] at hk; omega
        · exact hpos
      have hk2 : k ≤ 2 := by
        have hmul : cs.q1 * cs.q2 * k ≤ cs.q1 * cs.q2 * 2 := by
          rw [← hk]
          have : cs.q1 * cs.q2 * 2 = 2 * cs.q1 * cs.q2 := by ring
          rw [this]
          exact ht2
        exact Nat.le_of_mul_le_mul_left hmul he
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with hk1' | hk2'
      · left
        rw [hk, hk1', mul_one]
      · exfalso
        have ht' : t = 2 * cs.q1 * cs.q2 := by rw [hk, hk2']; ring
        have hgcd : Nat.gcd t (2 * cs.q1 * cs.q2) = 2 * cs.q1 * cs.q2 := by
          rw [ht', Nat.gcd_eq_right (dvd_refl _)]
        rw [hg] at hgcd
        have h2e : 2 * cs.q1 * cs.q2 = cs.q1 * cs.q2 * 2 := by ring
        rw [h2e] at hgcd
        omega
  · rintro (rfl | rfl)
    · refine ⟨⟨by omega, by omega⟩, Or.inr ?_⟩
      refine (qofaOutput_eq_two_iff hr heven (cs.q1 * cs.q2)).mpr ?_
      have hg : Nat.gcd (cs.q1 * cs.q2) (2 * cs.q1 * cs.q2) = cs.q1 * cs.q2 :=
        Nat.gcd_eq_left ⟨2, by ring⟩
      rw [hg, hr2]
    · exact ⟨⟨by omega, le_refl _⟩, Or.inl (qofaOutput_self hr)⟩

/-- `badTCount (q₁q₂) = 1`: one phase fails when `ord_N(2) = q₁q₂`. -/
theorem badTCount_q1q2 (cs : SafeSemiprime) :
    badTCount (cs.q1 * cs.q2) = 1 := by
  unfold badTCount
  rw [bad_filter_q1q2, Finset.card_singleton]

/-- `badTCount (2q₁q₂) = 2`: two phases fail when `ord_N(2) = 2q₁q₂`. -/
theorem badTCount_two_q1q2 (cs : SafeSemiprime) :
    badTCount (2 * cs.q1 * cs.q2) = 2 := by
  unfold badTCount
  rw [bad_filter_two_q1q2]
  have he : 0 < cs.q1 * cs.q2 := Nat.mul_pos cs.q1_prime.pos cs.q2_prime.pos
  have hlt : cs.q1 * cs.q2 < 2 * cs.q1 * cs.q2 := by
    have h : 2 * cs.q1 * cs.q2 = cs.q1 * cs.q2 * 2 := by ring
    rw [h]; omega
  exact Finset.card_pair hlt.ne

/-! ## The failure probability `1/(q₁q₂)`, uniformly in the order -/

/-- **Lemma 1(2): failure probability** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C,
Lemma 1, p. 5): whatever the true order `r ∈ {q₁q₂, 2q₁q₂}`, the probability over the uniform
phase `t ∈ {1, …, r}` of a bad output `d ∈ {1, 2}` is `1 / (q₁q₂)`. -/
theorem bad_probability (cs : SafeSemiprime) (r : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2) :
    (badTCount r : ℚ) / (r : ℚ) = 1 / ((cs.q1 : ℚ) * cs.q2) := by
  have hq1 : (0 : ℚ) < cs.q1 := by exact_mod_cast cs.q1_prime.pos
  have hq2 : (0 : ℚ) < cs.q2 := by exact_mod_cast cs.q2_prime.pos
  rcases hr with rfl | rfl
  · rw [badTCount_q1q2]; push_cast; rfl
  · rw [badTCount_two_q1q2]; push_cast; field_simp

/-- **Lemma 1(2): success probability** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C,
Lemma 1, p. 5): the probability of a useful output is `1 - 1 / (q₁q₂)`. -/
theorem useful_probability (cs : SafeSemiprime) (r : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2) :
    1 - (badTCount r : ℚ) / (r : ℚ) = 1 - 1 / ((cs.q1 : ℚ) * cs.q2) := by
  rw [bad_probability cs r hr]

/-- **Asymptotic comparison**: `4 / N < 1 / (q₁q₂)`, since `N = (2q₁ + 1)(2q₂ + 1) > 4q₁q₂`. -/
theorem four_div_N_lt_inv_q1q2 (cs : SafeSemiprime) :
    (4 : ℚ) / (cs.N : ℚ) < 1 / ((cs.q1 : ℚ) * cs.q2) := by
  have hN : (cs.N : ℚ) = (2 * (cs.q1 : ℚ) + 1) * (2 * (cs.q2 : ℚ) + 1) := by
    rw [cs.N_eq, cs.p1_eq, cs.p2_eq]; push_cast; ring
  have hq1 : (0 : ℚ) < cs.q1 := by exact_mod_cast cs.q1_prime.pos
  have hq2 : (0 : ℚ) < cs.q2 := by exact_mod_cast cs.q2_prime.pos
  have hNpos : (0 : ℚ) < (cs.N : ℚ) := by rw [hN]; positivity
  have hden : (0 : ℚ) < (cs.q1 : ℚ) * cs.q2 := by positivity
  rw [div_lt_div_iff₀ hNpos hden, hN]
  nlinarith [hq1, hq2]

/-! ## The headline statement of Lemma 1(2) -/

/-- **Lemma 1(2)** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C, Lemma 1, p. 5): for a
safe semiprime and any true order `r ∈ {q₁q₂, 2q₁q₂}`, every ideal QOFA output lies in the six
useful values or in `{1, 2}`, and the bad probability is `1 / (q₁q₂)`. -/
theorem lemma1_part2 (cs : SafeSemiprime) (r : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2) :
    (∀ t, qofaOutput r t ∈ usefulSet cs.q1 cs.q2 ∪ badSet) ∧
      (badTCount r : ℚ) / (r : ℚ) = 1 / ((cs.q1 : ℚ) * cs.q2) :=
  ⟨fun t => qofaOutput_mem_useful_or_bad cs r t hr, bad_probability cs r hr⟩

end Qatlib.Papers.SemiprimeFact15.MainResults
