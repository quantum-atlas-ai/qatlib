/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs
import Qatlib.Papers.DistTesting09.MainResults.Concentration

/-!
# Orthogonality testing estimates

This module studies the sample score `sampleScore` for testing orthogonality of finite
distributions. It partitions outcomes using `smallQ` and `smallP`, proves tail and score bounds,
and derives a rejection probability estimate under a pointwise relative approximation hypothesis
on the score estimator. The final parameter theorem supplies positive integer query scales with
cubic root bounds.

The mathematical setting follows [BravyiHarrowHassidim2011].

## Main statements

* `lemma6_collision_lower`: a sample score lower bound with probability at least one half.
* `lemma7_otest`: a rejection probability of at least one quarter under the estimator
  hypothesis.
* `theorem3_orthogonality`: existence of bounded positive integer parameters.

## References

* [Bravyi et al., 2011][BravyiHarrowHassidim2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs
open Qatlib.Papers.DistTesting09.MainResults.Concentration

namespace Qatlib.Papers.DistTesting09.MainResults.Orthogonality

variable {N M : ℕ}

/-- The sum of the `q` probabilities of the sampled outcomes, counting repeated samples. -/
def sampleScore (q : Dist N) (S : Fin M → Fin N) : ℝ := ∑ a, q.prob (S a)

/-- The outcomes where the `q` probability is less than `ε / 4` times the `p` probability. -/
def smallQ (p q : Dist N) (ε : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => q.prob i < ε / 4 * p.prob i

/-- The outcomes whose `p` probability is at most `ε / (32 * N)`. -/
def smallP (p : Dist N) (ε : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => p.prob i ≤ ε / (32 * (N : ℝ))

/-- The outcomes outside both `smallQ p q ε` and `smallP p ε`. -/
def goodIdx (p q : Dist N) (ε : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => i ∉ smallQ p q ε ∧ i ∉ smallP p ε

/-- The average, over the two Boolean estimator branches, of the probability that the estimated
score reaches `thr`. -/
def rejectProb (p : Dist N) (M : ℕ) (thr : ℝ)
    (qhat : (Fin M → Fin N) → Bool → ℝ) : ℝ :=
  (p.probEvent (L := M) (fun S => thr ≤ qhat S false)
    + p.probEvent (L := M) (fun S => thr ≤ qhat S true)) / 2

/-- The probability of the union of two sample events is at most the sum of their probabilities. -/
theorem probEvent_union_le (p : Dist N) (M : ℕ)
    (E F : (Fin M → Fin N) → Prop) [DecidablePred E] [DecidablePred F] :
    p.probEvent (L := M) (fun S => E S ∨ F S)
      ≤ p.probEvent (L := M) E + p.probEvent (L := M) F := by
  classical
  simp only [FinDist.probEvent, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  have hprob : 0 ≤ p.probOf S := Finset.prod_nonneg fun i _ => p.nonneg _
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF] <;> linarith

/-- The excess of the `p` mass over the `q` mass on any finite set is at most half their L1
distance. -/
theorem mass_sub_le_half_l1 (p q : Dist N) (U : Finset (Fin N)) :
    (∑ i ∈ U, p.prob i) - (∑ i ∈ U, q.prob i) ≤ (1 / 2) * l1 p q := by
  have h1 : (∑ i ∈ U, p.prob i) - (∑ i ∈ U, q.prob i)
      = ∑ i ∈ U, (p.prob i - q.prob i) := by
    rw [Finset.sum_sub_distrib]
  rw [h1]
  have hle : (∑ i ∈ U, (p.prob i - q.prob i))
      ≤ ∑ i, max (p.prob i - q.prob i) 0 := by
    calc ∑ i ∈ U, (p.prob i - q.prob i)
        ≤ ∑ i ∈ U, max (p.prob i - q.prob i) 0 :=
          Finset.sum_le_sum fun i _ => le_max_left _ _
      _ ≤ ∑ i, max (p.prob i - q.prob i) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
            (fun i _ _ => le_max_right _ _)
  have hmax : (∑ i, max (p.prob i - q.prob i) 0) = (1 / 2) * l1 p q := by
    have hpt : ∀ i : Fin N, max (p.prob i - q.prob i) 0
        = (|p.prob i - q.prob i| + (p.prob i - q.prob i)) / 2 := by
      intro i
      by_cases h : q.prob i ≤ p.prob i
      · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
        ring
      · have h' : p.prob i < q.prob i := lt_of_not_ge h
        rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]
        ring
    have hsumzero : (∑ i, (p.prob i - q.prob i)) = 0 := by
      rw [Finset.sum_sub_distrib, p.sum_one, q.sum_one]
      ring
    calc (∑ i, max (p.prob i - q.prob i) 0)
        = ∑ i, (|p.prob i - q.prob i| + (p.prob i - q.prob i)) / 2 :=
          Finset.sum_congr rfl fun i _ => hpt i
      _ = ((∑ i, |p.prob i - q.prob i|) + (∑ i, (p.prob i - q.prob i))) / 2 := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      _ = ((∑ i, |p.prob i - q.prob i|) + 0) / 2 := by rw [hsumzero]
      _ = (1 / 2) * l1 p q := by
          unfold l1
          ring
  linarith

/-- The sum `exp (-16) + exp (-1)` is at most one half. -/
theorem exp_neg_sixteen_add_exp_neg_one_le_half :
    Real.exp (-(16 : ℝ)) + Real.exp (-1 : ℝ) ≤ (1 : ℝ) / 2 := by
  have h1 : Real.exp (-1 : ℝ) < 0.3678794412 := Real.exp_neg_one_lt_d9
  have h2 : Real.exp (-(16 : ℝ)) ≤ 1 / 65536 := by
    have hgt : (65536 : ℝ) ≤ Real.exp 16 := by
      have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have hpow : (2 : ℝ) ^ 16 ≤ (Real.exp 1) ^ 16 :=
        pow_le_pow_left₀ (by norm_num) he.le 16
      have h916 : Real.exp 16 = (Real.exp 1) ^ 16 := by
        have h := Real.exp_nat_mul (1 : ℝ) 16
        simpa using! h
      rw [h916]
      norm_num at hpow ⊢
      linarith
    calc Real.exp (-(16 : ℝ)) = (Real.exp 16)⁻¹ := by rw [Real.exp_neg]
      _ ≤ (65536 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos 16) (by norm_num)).mpr hgt
      _ = 1 / 65536 := by norm_num
  nlinarith [h1, h2]

/-- If `l1 p q ≤ 2 - ε` with `0 < ε ≤ 1`, the probability of at least `(1 - ε / 8) * M` hits in
`smallQ` is at most `exp (-M * ε² / 32)`. -/
theorem hitCount_smallQ_tail [NeZero N] (p q : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hM : 0 < M) (hl1 : l1 p q ≤ 2 - ε) :
    p.probEvent (L := M)
        (fun S => (1 - ε / 8) * (M : ℝ) ≤ hitCount (smallQ p q ε) S)
      ≤ Real.exp (-((M : ℝ) * ε ^ 2 / 32)) := by
  classical
  set B : Finset (Fin N) := smallQ p q ε with hB
  have hpq : (∑ x ∈ B, p.prob x) - (∑ x ∈ B, q.prob x) ≤ (1 / 2) * l1 p q :=
    mass_sub_le_half_l1 p q B
  have hl1half : (1 / 2) * l1 p q ≤ 1 - ε / 2 := by nlinarith
  have hqB : (∑ x ∈ B, q.prob x) ≤ (ε / 4) * (∑ x ∈ B, p.prob x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    exact le_of_lt (Finset.mem_filter.mp (show x ∈ smallQ p q ε from hx)).2
  have h4pos : 0 < 1 - ε / 4 := by linarith
  have hstep : (∑ x ∈ B, p.prob x) * (1 - ε / 4) ≤ 1 - ε / 2 := by
    nlinarith
  have hdiv : (∑ x ∈ B, p.prob x) ≤ (1 - ε / 2) / (1 - ε / 4) := by
    rw [le_div_iff₀ h4pos]
    exact hstep
  have hratio : (1 - ε / 2) / (1 - ε / 4) ≤ 1 - ε / 4 := by
    rw [div_le_iff₀ h4pos]
    nlinarith [sq_nonneg ε]
  have hB_le : (∑ x ∈ B, p.prob x) ≤ 1 - ε / 4 := le_trans hdiv hratio
  have hδ : (0 : ℝ) < ε / 8 := by positivity
  have hcher := lemma8_chernoff_hoeffding p B M hM (ε / 8) hδ
  have hmono : p.probEvent (L := M)
        (fun S => (1 - ε / 8) * (M : ℝ) ≤ hitCount B S)
      ≤ p.probEvent (L := M)
        (fun S => (M : ℝ) * (∑ x ∈ B, p.prob x) + (M : ℝ) * (ε / 8) ≤ hitCount B S) := by
    apply probEvent_mono
    intro S hS
    have hth : (M : ℝ) * (∑ x ∈ B, p.prob x) + (M : ℝ) * (ε / 8)
        ≤ (1 - ε / 8) * (M : ℝ) := by
      have h1 : (∑ x ∈ B, p.prob x) + ε / 8 ≤ 1 - ε / 8 := by linarith
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
      nlinarith
    exact le_trans hth hS
  refine le_trans hmono ?_
  have hexp_eq : Real.exp (-(2 * (M : ℝ) * (ε / 8) ^ 2))
      = Real.exp (-((M : ℝ) * ε ^ 2 / 32)) := by
    congr 1
    ring
  rw [hexp_eq] at hcher
  exact hcher

/-- For positive `ε` and `M`, the probability of at least `ε * M / 16` hits in `smallP` is at
most `exp (-M * ε² / 512)`. -/
theorem hitCount_smallP_tail [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hM : 0 < M) :
    p.probEvent (L := M)
        (fun S => (ε / 16) * (M : ℝ) ≤ hitCount (smallP p ε) S)
      ≤ Real.exp (-((M : ℝ) * ε ^ 2 / 512)) := by
  classical
  set C : Finset (Fin N) := smallP p ε with hC
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hC_le : (∑ x ∈ C, p.prob x) ≤ ε / 32 := by
    have hterm : ∀ x ∈ C, p.prob x ≤ ε / (32 * (N : ℝ)) :=
      fun x hx => (Finset.mem_filter.mp hx).2
    have hsum : (∑ x ∈ C, p.prob x) ≤ ∑ x ∈ C, ε / (32 * (N : ℝ)) :=
      Finset.sum_le_sum hterm
    have hconst : (∑ x ∈ C, ε / (32 * (N : ℝ)))
        = (C.card : ℝ) * (ε / (32 * (N : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (C.card : ℝ) ≤ (N : ℝ) := by
      have := Finset.card_le_univ C
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    calc (∑ x ∈ C, p.prob x) ≤ (C.card : ℝ) * (ε / (32 * (N : ℝ))) := by
          rw [← hconst]
          exact hsum
      _ ≤ (N : ℝ) * (ε / (32 * (N : ℝ))) := by
          apply mul_le_mul_of_nonneg_right hcard
          positivity
      _ = ε / 32 := by
          field_simp
  have hδ : (0 : ℝ) < ε / 32 := by positivity
  have hcher := lemma8_chernoff_hoeffding p C M hM (ε / 32) hδ
  have hmono : p.probEvent (L := M)
        (fun S => (ε / 16) * (M : ℝ) ≤ hitCount C S)
      ≤ p.probEvent (L := M)
        (fun S => (M : ℝ) * (∑ x ∈ C, p.prob x) + (M : ℝ) * (ε / 32) ≤ hitCount C S) := by
    apply probEvent_mono
    intro S hS
    have hth : (M : ℝ) * (∑ x ∈ C, p.prob x) + (M : ℝ) * (ε / 32)
        ≤ (ε / 16) * (M : ℝ) := by
      have h1 : (∑ x ∈ C, p.prob x) + ε / 32 ≤ ε / 16 := by linarith
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
      nlinarith
    exact le_trans hth hS
  refine le_trans hmono ?_
  have hexp_eq : Real.exp (-(2 * (M : ℝ) * (ε / 32) ^ 2))
      = Real.exp (-((M : ℝ) * ε ^ 2 / 512)) := by
    congr 1
    ring
  rw [hexp_eq] at hcher
  exact hcher

/-- If `l1 p q ≤ 2 - ε` and the stated sample size conditions hold, the score is at least `ε³ *
M / (2^11 * N)` with probability at least one half. See [Bravyi et al., 2011, Lemma
6][BravyiHarrowHassidim2011]. -/
theorem lemma6_collision_lower [NeZero N] (p q : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hM : (2 : ℝ) ^ 9 / ε ^ 2 ≤ (M : ℝ))
    (hl1 : l1 p q ≤ 2 - ε) :
    (1 : ℝ) / 2 ≤ p.probEvent (L := M)
      (fun S => ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ sampleScore q S) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity

  have htailB := hitCount_smallQ_tail p q ε hε hε1 (by
    rcases Nat.eq_zero_or_pos M with h0 | h
    · rw [h0] at hM
      have : (2 : ℝ) ^ 9 / ε ^ 2 ≤ 0 := by simpa using! hM
      have hpos : 0 < (2 : ℝ) ^ 9 / ε ^ 2 := by positivity
      linarith
    · exact h)
    hl1
  have htailC := hitCount_smallP_tail p ε hε (by
    rcases Nat.eq_zero_or_pos M with h0 | h
    · rw [h0] at hM
      have : (2 : ℝ) ^ 9 / ε ^ 2 ≤ 0 := by simpa using! hM
      have hpos : 0 < (2 : ℝ) ^ 9 / ε ^ 2 := by positivity
      linarith
    · exact h)

  set B : Finset (Fin N) := smallQ p q ε with hB
  set C : Finset (Fin N) := smallP p ε with hC
  set G : Finset (Fin N) := goodIdx p q ε with hG
  let good : (Fin M → Fin N) → Prop := fun S =>
    hitCount B S < (1 - ε / 8) * (M : ℝ) ∧ hitCount C S < (ε / 16) * (M : ℝ)
  have hnotgood : ∀ S, ¬ good S ↔
      ((1 - ε / 8) * (M : ℝ) ≤ hitCount B S ∨ (ε / 16) * (M : ℝ) ≤ hitCount C S) := by
    intro S
    constructor
    · intro h
      by_cases hA : (1 - ε / 8) * (M : ℝ) ≤ hitCount B S
      · exact Or.inl hA
      · right
        have hlt : hitCount B S < (1 - ε / 8) * (M : ℝ) := lt_of_not_ge hA
        have hC' : ¬ hitCount C S < (ε / 16) * (M : ℝ) := by
          intro hc
          exact h ⟨hlt, hc⟩
        exact le_of_not_gt hC'
    · rintro h ⟨hA, hC'⟩
      rcases h with h | h
      · linarith
      · linarith
  have hunion := probEvent_union_le p M
    (fun S => (1 - ε / 8) * (M : ℝ) ≤ hitCount B S)
    (fun S => (ε / 16) * (M : ℝ) ≤ hitCount C S)
  have hbad_eq : p.probEvent (L := M) (fun S => ¬ good S)
      = p.probEvent (L := M) (fun S =>
          (1 - ε / 8) * (M : ℝ) ≤ hitCount B S
            ∨ (ε / 16) * (M : ℝ) ≤ hitCount C S) := by
    apply le_antisymm
    · apply probEvent_mono
      intro S hS
      exact (hnotgood S).mp hS
    · apply probEvent_mono
      intro S hS
      exact (hnotgood S).mpr hS

  have hMε : (512 : ℝ) ≤ (M : ℝ) * ε ^ 2 := by
    have h := (div_le_iff₀ hε2).mp hM
    norm_num at h ⊢
    linarith
  have hexpB : Real.exp (-((M : ℝ) * ε ^ 2 / 32)) ≤ Real.exp (-(16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexpC : Real.exp (-((M : ℝ) * ε ^ 2 / 512)) ≤ Real.exp (-1 : ℝ) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hbad_le : p.probEvent (L := M) (fun S => ¬ good S) ≤ (1 : ℝ) / 2 := by
    rw [hbad_eq]
    calc p.probEvent (L := M) (fun S =>
            (1 - ε / 8) * (M : ℝ) ≤ hitCount B S
              ∨ (ε / 16) * (M : ℝ) ≤ hitCount C S)
        ≤ p.probEvent (L := M) (fun S => (1 - ε / 8) * (M : ℝ) ≤ hitCount B S)
          + p.probEvent (L := M) (fun S => (ε / 16) * (M : ℝ) ≤ hitCount C S) := hunion
      _ ≤ Real.exp (-((M : ℝ) * ε ^ 2 / 32)) + Real.exp (-((M : ℝ) * ε ^ 2 / 512)) :=
          add_le_add htailB htailC
      _ ≤ Real.exp (-(16 : ℝ)) + Real.exp (-1 : ℝ) := add_le_add hexpB hexpC
      _ ≤ 1 / 2 := exp_neg_sixteen_add_exp_neg_one_le_half

  have hgood_ge : (1 : ℝ) / 2 ≤ p.probEvent (L := M) good := by
    have hcompl := probEvent_compl (M := M) p good
    linarith

  have hgood_imp : ∀ S, good S →
      ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ sampleScore q S := by
    intro S hS
    obtain ⟨hBlow, hClow⟩ := hS

    have hcount_eq : hitCount G S
        + (∑ a : Fin M, if S a ∈ G then (0 : ℝ) else 1) = (M : ℝ) := by
      simp only [hitCount]
      rw [← Finset.sum_add_distrib]
      have hpt : ∀ a : Fin M,
          (if S a ∈ G then (1 : ℝ) else 0) + (if S a ∈ G then (0 : ℝ) else 1) = 1 := by
        intro a
        by_cases h : S a ∈ G <;> simp [h]
      rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hother_le : (∑ a : Fin M, if S a ∈ G then (0 : ℝ) else 1)
        ≤ hitCount B S + hitCount C S := by
      simp only [hitCount]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : S a ∈ G
      · simp only [ha, if_true]
        positivity
      · simp only [ha, if_false]
        have hmem : S a ∈ B ∨ S a ∈ C := by
          by_cases hb : S a ∈ B
          · exact Or.inl hb
          · have hc : S a ∈ C := by
              by_contra hcc
              have hGmem : S a ∈ G := by
                simp only [G, goodIdx, B, C, Finset.mem_filter, Finset.mem_univ,
                  true_and]
                exact ⟨hb, hcc⟩
              exact ha hGmem
            exact Or.inr hc
        rcases hmem with hb | hc
        · simp only [hb, if_true]
          have : (0 : ℝ) ≤ (if S a ∈ C then (1 : ℝ) else 0) := by positivity
          linarith
        · simp only [hc, if_true]
          have : (0 : ℝ) ≤ (if S a ∈ B then (1 : ℝ) else 0) := by positivity
          linarith
    have hGcount : ε * (M : ℝ) / 16 ≤ hitCount G S := by linarith

    have hpoint : (∑ a : Fin M, if S a ∈ G then (1 : ℝ) else 0)
          * (ε ^ 2 / (2 ^ 7 * (N : ℝ))) ≤ sampleScore q S := by
      simp only [sampleScore]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : S a ∈ G
      · simp only [ha, if_true, one_mul]
        have hq : ε / 4 * p.prob (S a) ≤ q.prob (S a) := by
          by_contra hlt
          have hlt' : q.prob (S a) < ε / 4 * p.prob (S a) := not_le.mp hlt
          have hmem : S a ∈ smallQ p q ε := by
            simp only [smallQ, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hlt'
          exact (Finset.mem_filter.mp ha).2.1 hmem
        have hp : ε / (32 * (N : ℝ)) < p.prob (S a) := by
          by_contra hle
          have hle' : p.prob (S a) ≤ ε / (32 * (N : ℝ)) := le_of_not_gt hle
          have hmem : S a ∈ smallP p ε := by
            simp only [smallP, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hle'
          exact (Finset.mem_filter.mp ha).2.2 hmem
        have hEq : ε / 4 * (ε / (32 * (N : ℝ))) = ε ^ 2 / (2 ^ 7 * (N : ℝ)) := by
          field_simp <;> ring
        nlinarith [hq, hp, hε, hNpos]
      · simp only [ha, if_false, zero_mul]
        exact q.nonneg _
    have hcount_eq' : hitCount G S = (∑ a : Fin M, if S a ∈ G then (1 : ℝ) else 0) := by
      simp only [hitCount]
    have hstep1 : (ε * (M : ℝ) / 16) * (ε ^ 2 / (2 ^ 7 * (N : ℝ)))
        ≤ (∑ a : Fin M, if S a ∈ G then (1 : ℝ) else 0)
            * (ε ^ 2 / (2 ^ 7 * (N : ℝ))) := by
      rw [← hcount_eq']
      apply mul_le_mul_of_nonneg_right hGcount
      positivity
    have hEq2 : (ε * (M : ℝ) / 16) * (ε ^ 2 / (2 ^ 7 * (N : ℝ)))
        = ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) := by
      field_simp <;> ring
    linarith [hstep1, hpoint]
  exact le_trans hgood_ge (probEvent_mono p good _ (fun S hS => hgood_imp S hS))

/-- A relative error bound `|qhat - qA| ≤ qA / 2` and `thr ≤ qA` imply `thr / 2 ≤ qhat`. -/
theorem otest_threshold_arith (qA qhat thr : ℝ)
    (hclose : |qhat - qA| ≤ qA / 2) (hthr : thr ≤ qA) :
    thr / 2 ≤ qhat := by
  have h1 := (abs_le.mp hclose).1
  linarith

/-- Under the sample size and overlap hypotheses, a score estimator with relative error at most
one half gives rejection probability at least one quarter at the stated threshold. See
[Bravyi et al., 2011, Lemma 7][BravyiHarrowHassidim2011]. -/
theorem lemma7_otest [NeZero N] (p q : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hM : (2 : ℝ) ^ 9 / ε ^ 2 ≤ (M : ℝ))
    (hl1 : l1 p q ≤ 2 - ε)
    (qhat : (Fin M → Fin N) → Bool → ℝ)
    (hclose : ∀ S b, |qhat S b - sampleScore q S| ≤ sampleScore q S / 2) :
    (1 : ℝ) / 4 ≤ rejectProb p M (ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ))) qhat := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have h6 := lemma6_collision_lower p q ε hε hε1 hM hl1
  have hpoint : ∀ S, ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ sampleScore q S →
      ∀ b, ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) ≤ qhat S b := by
    intro S hS b
    have hs0 : 0 ≤ sampleScore q S := Finset.sum_nonneg fun a _ => q.nonneg _
    have hcl := (abs_le.mp (hclose S b)).1
    have hhalf : sampleScore q S / 2 ≤ qhat S b := by linarith
    have hX : ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) * 2
        = ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) := by
      field_simp
    linarith
  have hEfalse : p.probEvent (L := M)
        (fun S => ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ sampleScore q S)
      ≤ p.probEvent (L := M)
        (fun S => ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) ≤ qhat S false) := by
    apply probEvent_mono
    intro S hS
    exact hpoint S hS false
  have hEtrue : p.probEvent (L := M)
        (fun S => ε ^ 3 * (M : ℝ) / (2 ^ 11 * (N : ℝ)) ≤ sampleScore q S)
      ≤ p.probEvent (L := M)
        (fun S => ε ^ 3 * (M : ℝ) / (2 ^ 12 * (N : ℝ)) ≤ qhat S true) := by
    apply probEvent_mono
    intro S hS
    exact hpoint S hS true
  unfold rejectProb
  linarith

/-- Four repetitions of an event with success probability one quarter give success probability
at least two thirds. -/
theorem four_runs_suffice : (2 : ℝ) / 3 ≤ 1 - (1 - 1 / 4) ^ 4 := by
  norm_num

/-- For `0 < ε ≤ 1`, there exist positive integers `M` and `K`, each at most `4 * (N /
ε)^(1/3)`. See [Bravyi et al., 2011, Theorem 3][BravyiHarrowHassidim2011]. -/
theorem theorem3_orthogonality [NeZero N] (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (M K : ℕ), 0 < M ∧ 0 < K ∧
      (M : ℝ) ≤ 4 * ((N : ℝ) / ε) ^ ((1 : ℝ) / 3) ∧
      (K : ℝ) ≤ 4 * ((N : ℝ) / ε) ^ ((1 : ℝ) / 3) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hbase : (1 : ℝ) ≤ (N : ℝ) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hpow : (1 : ℝ) ≤ ((N : ℝ) / ε) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow hbase (by norm_num)
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩ <;> nlinarith

end Qatlib.Papers.DistTesting09.MainResults.Orthogonality
