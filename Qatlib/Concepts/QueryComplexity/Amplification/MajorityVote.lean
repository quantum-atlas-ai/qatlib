/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.ParallelCopies

/-!
# Majority voting on tensor copies

This module defines `MajorityCount` and `MajorityBit` and bounds majority failure for identical
tensor copies. If each copy has failure probability at most 1/3, the probability that at most
`r` of 2r + 1 copies succeed is at most (8/9)ʳ, providing the estimate used in the amplification
argument of [BennettEtAl1997].

## Main statements

* `majorityBit_eq_true_iff`: characterize a true majority for an odd number of bits.
* `majority_copies_fail_mass`: bound the probability of a failed majority of independent copies.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The number of true bits in a finite Boolean word. -/
def MajorityCount {k : ℕ} (w : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun j => w j = true).card

/-- The Boolean value that is true exactly when more than half of the word's bits are true. -/
def MajorityBit {k : ℕ} (w : Fin k → Bool) : Bool :=
  decide (k / 2 < MajorityCount w)

/-- For a word of length 2r + 1, the majority bit is true exactly when more than `r` bits are
true. -/
theorem majorityBit_eq_true_iff (r : ℕ) (w : Fin (2 * r + 1) → Bool) :
    MajorityBit w = true ↔ r < MajorityCount w := by
  have hdiv : (2 * r + 1) / 2 = r := by omega
  simp only [MajorityBit, decide_eq_true_eq, hdiv]

/-- For a word of length 2r + 1, the majority bit is false exactly when at most `r` bits are
true. -/
theorem majorityBit_eq_false_iff (r : ℕ) (w : Fin (2 * r + 1) → Bool) :
    MajorityBit w = false ↔ MajorityCount w ≤ r := by
  have hdiv : (2 * r + 1) / 2 = r := by omega
  simp only [MajorityBit, decide_eq_false_iff_not, hdiv]
  exact Nat.not_lt

/-- For 2r + 1 identical tensor copies of a normalized state with failure probability at most
1/3, the probability of at most `r` successful copies is at most (8/9)ʳ. This gives the
majority estimate used for [Bennett et al., Theorem 4.13][BennettEtAl1997]. -/
theorem majority_copies_fail_mass {I : Type*} [Fintype I] [DecidableEq I] (r : ℕ)
    (φ : QState I) (hφ : Normalized φ) (S : Finset I)
    (hq : MeasureProb φ Sᶜ ≤ 1 / 3) :
    MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => φ)
      (Finset.univ.filter fun ω => (Finset.univ.filter fun j => ω j ∈ S).card ≤ r)
      ≤ (8 / 9 : ℝ) ^ r := by
  classical
  set fail : Finset (Fin (2 * r + 1) → I) :=
    Finset.univ.filter fun ω : Fin (2 * r + 1) → I =>
      (Finset.univ.filter fun j => ω j ∈ S).card ≤ r
  set good : (Fin (2 * r + 1) → I) → Finset (Fin (2 * r + 1)) :=
    fun ω => Finset.univ.filter fun j => ω j ∈ S

  have hdisj : Disjoint Sᶜ S := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy heq
    rw [Finset.mem_compl] at hx
    exact hx (heq ▸ hy)
  have hqs : MeasureProb φ Sᶜ + MeasureProb φ S = 1 := by
    unfold MeasureProb
    rw [← Finset.sum_union hdisj, Finset.union_comm, Finset.union_compl,
      bornProb_sum_eq_one hφ]
  have hq0 : 0 ≤ MeasureProb φ Sᶜ := measureProb_nonneg φ Sᶜ
  have hs0 : 0 ≤ MeasureProb φ S := measureProb_nonneg φ S
  have hq_le_s : MeasureProb φ Sᶜ ≤ MeasureProb φ S := by linarith
  have hqs29 : MeasureProb φ Sᶜ * MeasureProb φ S ≤ 2 / 9 := by
    have h2 : MeasureProb φ S = 1 - MeasureProb φ Sᶜ := by linarith
    rw [h2, mul_sub, mul_one]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 3 - MeasureProb φ Sᶜ)
      (by linarith : (0 : ℝ) ≤ 2 / 3 - MeasureProb φ Sᶜ)]

  have h2pow : (2 : ℝ) ^ (2 * r + 1) * (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (3 * r) := by
    rw [← pow_add, show 2 * r + 1 + r = 3 * r + 1 from by omega, pow_succ]
    ring
  have h8pow : ((8 : ℝ)) ^ r = ((2 : ℝ)) ^ (3 * r) := by
    rw [show ((8 : ℝ)) = ((2 : ℝ) ^ (3 : ℕ)) from by norm_num, ← pow_mul]
  have hfinal : ((1 / 3 : ℝ) * ((2 : ℝ) / 9) ^ r) * ((2 : ℝ) ^ (2 * r + 1))
      ≤ ((8 : ℝ) / 9) ^ r := by
    rw [div_pow, div_pow, ← mul_div_assoc, div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity : (0 : ℝ) < (9 : ℝ) ^ r)
        (by positivity : (0 : ℝ) < (9 : ℝ) ^ r)]
    calc ((1 / 3 : ℝ) * (2 : ℝ) ^ r) * (2 : ℝ) ^ (2 * r + 1) * (9 : ℝ) ^ r
        = (1 / 3 : ℝ) * ((2 : ℝ) ^ (2 * r + 1) * (2 : ℝ) ^ r) * (9 : ℝ) ^ r := by ring
      _ = (1 / 3 : ℝ) * (2 * (2 : ℝ) ^ (3 * r)) * (9 : ℝ) ^ r := by rw [h2pow]
      _ = (2 / 3 : ℝ) * ((2 : ℝ) ^ (3 * r) * (9 : ℝ) ^ r) := by ring
      _ ≤ 1 * ((2 : ℝ) ^ (3 * r) * (9 : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = ((8 : ℝ) ^ r) * (9 : ℝ) ^ r := by rw [← h8pow]; ring

  have hsum : MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => φ) fail
      = ∑ ω ∈ fail, ∏ j, BornProb φ (ω j) := by
    unfold MeasureProb
    exact Finset.sum_congr rfl fun ω _ =>
      bornProb_piTensorState (fun _ : Fin (2 * r + 1) => φ) ω

  have hfib : ∑ ω ∈ fail, ∏ j, BornProb φ (ω j)
      = ∑ G ∈ Finset.univ, ∑ ω ∈ fail.filter (fun ω => good ω = G),
          ∏ j, BornProb φ (ω j) :=
    (Finset.sum_fiberwise_of_maps_to
      (g := good) (f := fun ω => ∏ j, BornProb φ (ω j)) (t := Finset.univ) (s := fail)
      (by intro ω _; exact Finset.mem_univ _)).symm

  have hinner : ∀ G : Finset (Fin (2 * r + 1)),
      ∑ ω ∈ fail.filter (fun ω => good ω = G), ∏ j, BornProb φ (ω j)
      ≤ (1 / 3 : ℝ) * (2 / 9 : ℝ) ^ r := by
    intro G
    by_cases hG : G.card ≤ r
    · have hcyl : fail.filter (fun ω => good ω = G)
          ⊆ Fintype.piFinset (fun j => if j ∈ G then S else Sᶜ) := by
        intro ω hω
        have hge : good ω = G := (Finset.mem_filter.mp hω).2
        simp only [Fintype.mem_piFinset]
        intro j
        by_cases hj : j ∈ G
        · rw [if_pos hj]
          have hjmem : j ∈ good ω := by
            rw [hge]; exact hj
          exact (Finset.mem_filter.mp hjmem).2
        · rw [if_neg hj, Finset.mem_compl]
          intro hmem
          have hmem2 : j ∈ good ω :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩
          rw [hge] at hmem2
          exact hj hmem2

      have hprod : ∑ ω ∈ Fintype.piFinset (fun j => if j ∈ G then S else Sᶜ),
          ∏ j, BornProb φ (ω j)
          = (MeasureProb φ S) ^ G.card
            * (MeasureProb φ Sᶜ) ^ (Fintype.card (Fin (2 * r + 1)) - G.card) := by
        have h1 : ∑ ω ∈ Fintype.piFinset (fun j => if j ∈ G then S else Sᶜ),
                ∏ j, BornProb φ (ω j)
            = ∏ j : Fin (2 * r + 1), ∑ a ∈ (if j ∈ G then S else Sᶜ), BornProb φ a :=
          (Finset.prod_univ_sum (fun j : Fin (2 * r + 1) => if j ∈ G then S else Sᶜ)
            (fun (_ : Fin (2 * r + 1)) (a : I) => BornProb φ a)).symm
        have hmemG : (Finset.univ : Finset (Fin (2 * r + 1))).filter (fun j => j ∈ G) = G := by
          ext j; simp
        have hcard : (Finset.univ.filter (fun j => ¬j ∈ G) : Finset (Fin (2 * r + 1))).card
            = Fintype.card (Fin (2 * r + 1)) - G.card := by
          have h2 := Finset.card_filter_add_card_filter_not (fun j => j ∈ G)
            (s := (Finset.univ : Finset (Fin (2 * r + 1))))
          rw [hmemG, Finset.card_univ] at h2
          omega
        have hper : ∀ j : Fin (2 * r + 1), ∑ a ∈ (if j ∈ G then S else Sᶜ), BornProb φ a
            = if j ∈ G then MeasureProb φ S else MeasureProb φ Sᶜ := by
          intro j
          by_cases hj : j ∈ G
          · simp only [hj, if_true]
            rfl
          · simp only [hj, if_false]
            rfl
        rw [h1, Finset.prod_congr rfl fun j _ => hper j]
        simp only [Finset.prod_ite]
        rw [hmemG, Finset.prod_const, Finset.prod_const, hcard]

      have hN : Fintype.card (Fin (2 * r + 1)) = 2 * r + 1 := Fintype.card_fin _
      have hnum : (MeasureProb φ S) ^ G.card
          * (MeasureProb φ Sᶜ) ^ (Fintype.card (Fin (2 * r + 1)) - G.card)
          ≤ (1 / 3 : ℝ) * (2 / 9 : ℝ) ^ r := by
        have hd : Fintype.card (Fin (2 * r + 1)) - G.card = (r + 1) + (r - G.card) := by
          rw [hN]; omega
        have hqsplit : (MeasureProb φ Sᶜ) ^ (Fintype.card (Fin (2 * r + 1)) - G.card)
            = (MeasureProb φ Sᶜ) ^ (r + 1) * (MeasureProb φ Sᶜ) ^ (r - G.card) := by
          rw [hd, pow_add]
        have hqmono : (MeasureProb φ Sᶜ) ^ (r - G.card) ≤ (MeasureProb φ S) ^ (r - G.card) :=
          pow_le_pow_left₀ hq0 hq_le_s _
        have hssplit : (MeasureProb φ S) ^ G.card * (MeasureProb φ S) ^ (r - G.card)
            = (MeasureProb φ S) ^ r := by
          rw [← pow_add]
          congr 1
          omega
        calc (MeasureProb φ S) ^ G.card
              * (MeasureProb φ Sᶜ) ^ (Fintype.card (Fin (2 * r + 1)) - G.card)
            = (MeasureProb φ S) ^ G.card
                * ((MeasureProb φ Sᶜ) ^ (r + 1) * (MeasureProb φ Sᶜ) ^ (r - G.card)) := by
              rw [hqsplit]
          _ ≤ (MeasureProb φ S) ^ G.card
                * ((MeasureProb φ Sᶜ) ^ (r + 1) * (MeasureProb φ S) ^ (r - G.card)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hqmono (pow_nonneg hq0 _)) (pow_nonneg hs0 _)
          _ = (MeasureProb φ Sᶜ) ^ (r + 1) * ((MeasureProb φ S) ^ r) := by
              linear_combination (MeasureProb φ Sᶜ) ^ (r + 1) * hssplit
          _ = MeasureProb φ Sᶜ * ((MeasureProb φ Sᶜ * MeasureProb φ S) ^ r) := by
              rw [pow_succ, mul_pow]
              ring
          _ ≤ (1 / 3 : ℝ) * ((2 / 9 : ℝ) ^ r) :=
              mul_le_mul hq (pow_le_pow_left₀ (mul_nonneg hq0 hs0) hqs29 r)
                (pow_nonneg (mul_nonneg hq0 hs0) r) (by norm_num)
      calc ∑ ω ∈ fail.filter (fun ω => good ω = G), ∏ j, BornProb φ (ω j)
          ≤ ∑ ω ∈ Fintype.piFinset (fun j => if j ∈ G then S else Sᶜ),
              ∏ j, BornProb φ (ω j) :=
            Finset.sum_le_sum_of_subset_of_nonneg hcyl
              (fun ω _ _ => Finset.prod_nonneg fun j _ => bornProb_nonneg φ (ω j))
        _ = (MeasureProb φ S) ^ G.card
              * (MeasureProb φ Sᶜ) ^ (Fintype.card (Fin (2 * r + 1)) - G.card) := hprod
        _ ≤ (1 / 3 : ℝ) * (2 / 9 : ℝ) ^ r := hnum
    · have hempty : fail.filter (fun ω => good ω = G) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun ω hω => ?_
        have hcard : (good ω).card ≤ r := (Finset.mem_filter.mp hω).2
        intro hgood
        rw [hgood] at hcard
        exact hG hcard
      rw [hempty, Finset.sum_empty]
      positivity
  rw [hsum, hfib]

  calc ∑ G ∈ Finset.univ, ∑ ω ∈ fail.filter (fun ω => good ω = G),
          ∏ j, BornProb φ (ω j)
      ≤ ∑ _g ∈ Finset.univ, ((1 / 3 : ℝ) * (2 / 9 : ℝ) ^ r) :=
        Finset.sum_le_sum fun G _ => hinner G
    _ = (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).card • ((1 / 3 : ℝ) * (2 / 9 : ℝ) ^ r) :=
        Finset.sum_const _
    _ = ((1 / 3 : ℝ) * ((2 : ℝ) / 9) ^ r) * ((2 : ℝ) ^ (2 * r + 1)) := by
        rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]
        ring
    _ ≤ ((8 : ℝ) / 9) ^ r := hfinal

end Qatlib.Concepts.QueryComplexity.Amplification
