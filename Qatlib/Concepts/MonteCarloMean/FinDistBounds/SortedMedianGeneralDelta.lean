/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian

@[expose] public section

/-!
# Sharp sorted-median amplification below a one-half single-run failure

`heterogeneous_sorted_median_majority_witness` shows that a failing sorted median of `2 * r + 1`
independent runs forces at least `r + 1` of those runs to fail. The amplification bounds already in
the library reweight a bad run by `2`, which needs a single-run failure of at most `1 / 3`, or
start from the dedicated `1 - 8 / π ^ 2` error bar of amplitude estimation. Neither reaches the
sharp constant for a general single-run failure `δ < 1 / 2`.

This module proves the sharp bound. Failing records are grouped by their exact set of bad runs.
The product law weighs each fiber by `π ^ #A * (1 - π) ^ (2 * r + 1 - #A)`, where `π` is the mass
of the bad event. Since `π ≤ 1 - π`, every fiber with `r + 1 ≤ #A` weighs at most
`π ^ (r + 1) * (1 - π) ^ r`, and exactly half of the `2 ^ (2 * r + 1)` subsets of runs contain at
least `r + 1` elements. The resulting bound `2 ^ (2 * r) * π ^ (r + 1) * (1 - π) ^ r` is below
`(1 / 2) * (2 * sqrt (δ * (1 - δ))) ^ (2 * r + 1)` whenever `π ≤ δ`.

Boundary: the runs must be independent and identically distributed, which is the sampling model of
the repeated-median estimator; the second clause of the source lemma, that `O (log (1 / η))`
repetitions suffice for final failure `η`, is not derived here.

## Main statements

* `sum_probOf_mem_sets`: records whose coordinate values fall into prescribed finite sets have
  product-law weight equal to the product of the per-coordinate masses.
* `sum_probOf_badset`: the fiber of records whose exact bad set is `A` weighs
  `π ^ #A * (1 - π) ^ (L - #A)`.
* `probEvent_bad_majority_le`: a majority of bad runs has mass at most the sum of the exact
  bad-set weights.
* `card_bad_subsets_le`: at most `2 ^ (2 * r)` subsets of `2 * r + 1` runs have at least `r + 1`
  elements.
* `bad_subsets_sum_le`: for `π ≤ 1 - π` the bad-set weights sum to at most
  `(1 / 2) * (2 * sqrt (π * (1 - π))) ^ (2 * r + 1)`.
* `sorted_median_failure_general_delta`: the sorted median of `2 * r + 1` independent estimates
  with single-run failure at most `δ < 1 / 2` fails with probability at most
  `(1 / 2) * (2 * sqrt (δ * (1 - δ))) ^ (2 * r + 1)`.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Records whose coordinate values fall into prescribed finite sets have product-law weight
equal to the product of the per-coordinate masses. -/
theorem sum_probOf_mem_sets {L : ℕ} (p : FinDist X) (S : Fin L → Finset X) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin L → X => ∀ k, ω k ∈ S k), p.probOf ω
      = ∏ k, ∑ x ∈ S k, p.prob x := by
  classical
  have hstep : ∑ ω ∈ Finset.univ.filter (fun ω : Fin L → X => ∀ k, ω k ∈ S k), p.probOf ω
      = ∑ ω : Fin L → X,
          p.probOf ω * ∏ k : Fin L, (if ω k ∈ S k then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hall : ∀ k, ω k ∈ S k
    · rw [ite_eq_left hall, Finset.prod_eq_one (fun k _ => ite_eq_left (hall k)), mul_one]
    · obtain ⟨k, hk⟩ := not_forall.mp hall
      rw [ite_eq_right hall, Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk), mul_zero]
  rw [hstep, FinDist.expect_prod p (fun k x => if x ∈ S k then (1 : ℝ) else 0)]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : (∑ x, p.prob x * (if x ∈ S k then (1 : ℝ) else 0))
      = ∑ x, (if x ∈ S k then p.prob x else 0) :=
    Finset.sum_congr rfl fun x _ => by by_cases h : x ∈ S k <;> simp [h]
  rw [h1, ← Finset.sum_filter,
    show (Finset.univ.filter fun x => x ∈ S k) = S k from Finset.ext (fun x => by simp)]

/-- Splitting the product of the per-coordinate bad-set weights gives the bad mass to the number
of bad runs times the good mass to the complementary power. -/
theorem prod_badset_weight {L : ℕ} (A : Finset (Fin L)) (π q : ℝ) :
    ∏ k : Fin L, (if k ∈ A then π else q) = π ^ A.card * q ^ (L - A.card) := by
  classical
  have hcard : A.card ≤ L := by
    have := Finset.card_le_univ A
    simpa using this
  have hmem : (Finset.univ.filter fun k => k ∈ A) = A := Finset.ext (fun k => by simp)
  have hnot : (Finset.univ.filter fun k : Fin L => ¬ k ∈ A).card = L - A.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin L))) (p := fun k => k ∈ A)
    rw [hmem] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [Finset.prod_ite (s := Finset.univ) (p := fun k => k ∈ A) (f := fun _ => π)
    (g := fun _ => q)]
  rw [Finset.prod_const, Finset.prod_const, hmem, hnot]

/-- The fiber of records whose exact set of bad runs is `A` has product-law weight
`π ^ #A * (1 - π) ^ (L - #A)`, where `π` is the mass of the bad event. -/
theorem sum_probOf_badset {L : ℕ} (p : FinDist X) (B : X → Prop) [DecidablePred B]
    (A : Finset (Fin L)) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin L → X => ∀ k, (k ∈ A ↔ B (ω k))), p.probOf ω
      = (∑ x ∈ Finset.univ.filter B, p.prob x) ^ A.card
        * (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x) ^ (L - A.card) := by
  classical
  have hk_iff : ∀ (ω : Fin L → X) (k : Fin L),
      (ω k ∈ (if k ∈ A then Finset.univ.filter B else Finset.univ.filter (fun x => ¬ B x)))
        ↔ (k ∈ A ↔ B (ω k)) := by
    intro ω k
    by_cases hA : k ∈ A
    · rw [ite_eq_left hA]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hB => ⟨fun _ => hB, fun _ => hA⟩, fun h => h.mp hA⟩
    · rw [ite_eq_right hA]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hnB => ⟨fun h' => absurd h' hA, fun hB => absurd hB hnB⟩,
        fun h => fun hB => hA (h.mpr hB)⟩
  have hfilter : (Finset.univ.filter (fun ω : Fin L → X => ∀ k, (k ∈ A ↔ B (ω k))))
      = Finset.univ.filter (fun ω : Fin L → X => ∀ k, ω k ∈
          (if k ∈ A then Finset.univ.filter B else Finset.univ.filter (fun x => ¬ B x))) := by
    refine Finset.filter_congr fun ω _ => ?_
    constructor
    · intro h k
      exact (hk_iff ω k).mpr (h k)
    · intro h k
      exact (hk_iff ω k).mp (h k)
  rw [hfilter, sum_probOf_mem_sets p
    (fun k => if k ∈ A then Finset.univ.filter B else Finset.univ.filter (fun x => ¬ B x))]
  have hprod : ∏ k : Fin L, (∑ x ∈ (if k ∈ A then Finset.univ.filter B
        else Finset.univ.filter (fun x => ¬ B x)), p.prob x)
      = ∏ k : Fin L, (if k ∈ A then (∑ x ∈ Finset.univ.filter B, p.prob x)
        else (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hA : k ∈ A <;> simp [hA]
  rw [hprod, prod_badset_weight A (∑ x ∈ Finset.univ.filter B, p.prob x)
    (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x)]

/-- A majority of bad runs has mass at most the sum of the exact bad-set weights. -/
theorem probEvent_bad_majority_le {L : ℕ} (p : FinDist X) (B : X → Prop) [DecidablePred B]
    (k : ℕ) :
    p.probEvent (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card)
      ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin L))).filter (fun A => k ≤ A.card),
          (∑ x ∈ Finset.univ.filter B, p.prob x) ^ A.card
            * (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x) ^ (L - A.card) := by
  classical
  show (∑ ω ∈ Finset.univ.filter
      (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card), p.probOf ω) ≤ _
  set S := (Finset.univ : Finset (Finset (Fin L))).filter (fun A => k ≤ A.card) with hS
  have hpt : ∀ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
      p.probOf ω ≤ p.probOf ω * ∑ A ∈ S,
        (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0) := by
    intro ω hω
    have hcard : k ≤ (Finset.univ.filter (fun n => B (ω n))).card :=
      (Finset.mem_filter.mp hω).2
    have hmem : (Finset.univ.filter (fun n => B (ω n))) ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩
    have hone : (1 : ℝ) ≤ ∑ A ∈ S,
        (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0) := by
      have hsingle := Finset.single_le_sum
        (f := fun A => if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0)
        (fun A _ => by positivity) hmem
      simpa using hsingle
    calc p.probOf ω = p.probOf ω * 1 := by ring
      _ ≤ p.probOf ω * _ :=
        mul_le_mul_of_nonneg_left hone (Finset.prod_nonneg fun i _ => p.nonneg _)
  have hinner : ∀ A ∈ S,
      (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
        p.probOf ω * (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0))
      = ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => ∀ n, (n ∈ A ↔ B (ω n))), p.probOf ω := by
    intro A hA
    have hAcard : k ≤ A.card := (Finset.mem_filter.mp hA).2
    have hsel : ∀ ω : Fin L → X,
        ((Finset.univ.filter (fun n => B (ω n))) = A)
          ↔ ∀ n, (n ∈ A ↔ B (ω n)) := by
      intro ω
      constructor
      · intro h n
        rw [← h]
        simp
      · intro h
        exact Finset.ext (fun n => by
          rw [Finset.mem_filter]
          exact ⟨fun hn => (h n).mpr hn.2, fun hA => ⟨Finset.mem_univ _, (h n).mp hA⟩⟩)
    have h1 : (∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
          p.probOf ω * (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0))
        = ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
          (if (Finset.univ.filter (fun n => B (ω n))) = A then p.probOf ω else 0) :=
      Finset.sum_congr rfl fun ω _ => by
        by_cases h : (Finset.univ.filter (fun n => B (ω n))) = A <;> simp [h]
    rw [h1, ← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    refine Finset.filter_congr fun ω _ => ?_
    rw [hsel ω]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      rw [show (Finset.univ.filter (fun n => B (ω n))) = A from (hsel ω).mpr h]
      exact hAcard
  calc (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card), p.probOf ω)
      ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
          p.probOf ω * ∑ A ∈ S,
            (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ A ∈ S, ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => k ≤ (Finset.univ.filter (fun n => B (ω n))).card),
          p.probOf ω * (if (Finset.univ.filter (fun n => B (ω n))) = A then (1 : ℝ) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ A ∈ S, ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin L → X => ∀ n, (n ∈ A ↔ B (ω n))), p.probOf ω :=
        Finset.sum_congr rfl hinner
    _ = ∑ A ∈ S, (∑ x ∈ Finset.univ.filter B, p.prob x) ^ A.card
          * (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x) ^ (L - A.card) :=
        Finset.sum_congr rfl fun A _ => sum_probOf_badset p B A

/-- At most `2 ^ (2 * r)` subsets of `2 * r + 1` runs have at least `r + 1` elements. -/
theorem card_bad_subsets_le (r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter (fun A => r + 1 ≤ A.card)).card
      ≤ 2 ^ (2 * r) := by
  classical
  set N := (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter (fun A => r + 1 ≤ A.card)
    with hN
  set M := (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter (fun A => A.card ≤ r)
    with hM
  have hmapN : ∀ A ∈ N, Aᶜ ∈ M := by
    intro A hA
    have hcard : r + 1 ≤ A.card := by
      simpa only [hN, Finset.mem_filter, Finset.mem_univ, true_and] using hA
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.compl_eq_univ_sdiff, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hmapM : ∀ A ∈ M, Aᶜ ∈ N := by
    intro A hA
    have hcard : A.card ≤ r := by
      simpa only [hM, Finset.mem_filter, Finset.mem_univ, true_and] using hA
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.compl_eq_univ_sdiff, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hinj : ∀ A ∈ N, ∀ B ∈ N, Aᶜ = Bᶜ → A = B := by
    intro A _ B _ h
    rw [← compl_compl A, h, compl_compl]
  have hinj' : ∀ A ∈ M, ∀ B ∈ M, Aᶜ = Bᶜ → A = B := by
    intro A _ B _ h
    rw [← compl_compl A, h, compl_compl]
  have hNM : N.card ≤ M.card := Finset.card_le_card_of_injOn (fun A => Aᶜ) hmapN hinj
  have hMN : M.card ≤ N.card := Finset.card_le_card_of_injOn (fun A => Aᶜ) hmapM hinj'
  have hunion : N ∪ M = (Finset.univ : Finset (Finset (Fin (2 * r + 1)))) := by
    refine Finset.eq_univ_of_forall fun A => ?_
    rw [Finset.mem_union, hN, hM, Finset.mem_filter, Finset.mem_filter]
    by_cases h : r + 1 ≤ A.card
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hdisj : Disjoint N M := by
    rw [Finset.disjoint_left]
    intro A hA hB
    have h1 : r + 1 ≤ A.card := by
      simpa only [hN, Finset.mem_filter, Finset.mem_univ, true_and] using hA
    have h2 : A.card ≤ r := by
      simpa only [hM, Finset.mem_filter, Finset.mem_univ, true_and] using hB
    omega
  have hsum : N.card + M.card = 2 ^ (2 * r + 1) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
  have hpow : 2 ^ (2 * r + 1) = 2 * 2 ^ (2 * r) := by
    rw [pow_succ]
    ring
  omega

/-- If `π ≤ 1 - π`, the bad-set weights sum to at most
`(1 / 2) * (2 * sqrt (π * (1 - π))) ^ (2 * r + 1)`. -/
theorem bad_subsets_sum_le (r : ℕ) {π : ℝ} (hπ : 0 ≤ π) (hπq : π ≤ 1 - π) :
    ∑ A ∈ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter (fun A => r + 1 ≤ A.card),
        π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card)
      ≤ (1 / 2) * (2 * Real.sqrt (π * (1 - π))) ^ (2 * r + 1) := by
  classical
  have hq : 0 ≤ 1 - π := by linarith
  have hterm : ∀ A ∈ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter
        (fun A => r + 1 ≤ A.card),
      π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card) ≤ π ^ (r + 1) * (1 - π) ^ r := by
    intro A hA
    have h1 : r + 1 ≤ A.card := (Finset.mem_filter.mp hA).2
    have h2 : A.card ≤ 2 * r + 1 := by
      have := Finset.card_le_univ A
      simpa using this
    obtain ⟨t, ht⟩ : ∃ t, A.card = r + 1 + t := ⟨A.card - (r + 1), by omega⟩
    have htle : t ≤ r := by omega
    have hdecomp : 2 * r + 1 - A.card = r - t := by omega
    have hstep : π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card)
        = (π ^ (r + 1) * π ^ t) * (1 - π) ^ (r - t) := by
      rw [ht, pow_add, show 2 * r + 1 - (r + 1 + t) = r - t from by omega]
    have hle : π ^ t ≤ (1 - π) ^ t := pow_le_pow_left₀ hπ hπq t
    have hexp : (1 - π) ^ t * (1 - π) ^ (r - t) = (1 - π) ^ r := by
      rw [← pow_add]
      congr 1
      omega
    calc π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card)
        = (π ^ (r + 1) * π ^ t) * (1 - π) ^ (r - t) := hstep
      _ ≤ (π ^ (r + 1) * (1 - π) ^ t) * (1 - π) ^ (r - t) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hle (pow_nonneg hπ _)) (pow_nonneg hq _)
      _ = π ^ (r + 1) * (1 - π) ^ r := by
          rw [mul_assoc, hexp]
  have hsum : ∑ A ∈ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter
        (fun A => r + 1 ≤ A.card), π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card)
      ≤ (2 : ℝ) ^ (2 * r) * (π ^ (r + 1) * (1 - π) ^ r) := by
    have hcard := card_bad_subsets_le r
    calc ∑ A ∈ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter
          (fun A => r + 1 ≤ A.card), π ^ A.card * (1 - π) ^ (2 * r + 1 - A.card)
        ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter
          (fun A => r + 1 ≤ A.card), π ^ (r + 1) * (1 - π) ^ r :=
          Finset.sum_le_sum hterm
      _ = (((Finset.univ : Finset (Finset (Fin (2 * r + 1)))).filter
            (fun A => r + 1 ≤ A.card)).card : ℝ) * (π ^ (r + 1) * (1 - π) ^ r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ (2 * r) * (π ^ (r + 1) * (1 - π) ^ r) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hπ _) (pow_nonneg hq _))
          exact_mod_cast hcard
  have hsqrt : π ≤ Real.sqrt (π * (1 - π)) := by
    rw [Real.le_sqrt hπ (mul_nonneg hπ hq), sq]
    nlinarith
  have hmain : (2 : ℝ) ^ (2 * r) * (π ^ (r + 1) * (1 - π) ^ r)
      ≤ (1 / 2) * (2 * Real.sqrt (π * (1 - π))) ^ (2 * r + 1) := by
    have hsq : Real.sqrt (π * (1 - π)) ^ 2 = π * (1 - π) := Real.sq_sqrt (mul_nonneg hπ hq)
    have hpr : π ^ (r + 1) * (1 - π) ^ r = (π * (1 - π)) ^ r * π := by
      rw [pow_succ, mul_pow]
      ring
    have hsp : (Real.sqrt (π * (1 - π))) ^ (2 * r + 1)
        = ((Real.sqrt (π * (1 - π))) ^ 2) ^ r * Real.sqrt (π * (1 - π)) := by
      rw [pow_succ, ← pow_mul]
    have hbase : (2 * Real.sqrt (π * (1 - π))) ^ (2 * r + 1)
        = 2 ^ (2 * r + 1) * ((π * (1 - π)) ^ r * Real.sqrt (π * (1 - π))) := by
      rw [mul_pow, hsp, hsq]
    rw [hpr, hbase]
    have hkey := mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (mul_nonneg hπ hq) r)
    have h2r : (0 : ℝ) ≤ 2 ^ (2 * r) := by positivity
    refine (mul_le_mul_of_nonneg_left hkey h2r).trans (le_of_eq ?_)
    rw [show (2 : ℝ) ^ (2 * r + 1) = (2 : ℝ) ^ (2 * r) * 2 from by rw [pow_succ]]
    ring
  exact hsum.trans hmain

/-- For `π ≤ δ < 1 / 2`, the square root of `π * (1 - π)` is at most the square root of
`δ * (1 - δ)`. -/
theorem sqrt_mul_one_sub_le {π δ : ℝ} (hπδ : π ≤ δ) (hδ : δ < 1 / 2) :
    Real.sqrt (π * (1 - π)) ≤ Real.sqrt (δ * (1 - δ)) := by
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-- The sorted median of `2 * r + 1` independent estimates with single-run failure mass at most
`δ < 1 / 2` fails with probability at most `(1 / 2) * (2 * sqrt (δ * (1 - δ))) ^ (2 * r + 1)`. -/
theorem sorted_median_failure_general_delta (p : FinDist X) (v : X → ℝ) (r : ℕ) (μ ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ2 : δ < 1 / 2)
    (hb : mass p (fun x => ε < |v x - μ|) ≤ δ) :
    p.probEvent (fun ω : Fin (2 * r + 1) → X =>
        ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|)
      ≤ (1 / 2) * (2 * Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) := by
  classical
  set B : X → Prop := fun x => ε < |v x - μ| with hB
  have hconv : ∀ E : X → Prop, mass p E = ∑ x ∈ Finset.univ.filter E, p.prob x := by
    intro E
    unfold mass
    congr 1
  set π : ℝ := ∑ x ∈ Finset.univ.filter B, p.prob x with hπdef
  have hπ_nonneg : 0 ≤ π := by
    rw [hπdef]
    exact Finset.sum_nonneg fun x _ => p.nonneg x
  have hπ_le_delta : π ≤ δ := by
    rw [hπdef, ← hconv B]
    exact hb
  have hq : (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x) = 1 - π := by
    have hsum : (∑ x ∈ Finset.univ.filter B, p.prob x)
        + (∑ x ∈ Finset.univ.filter (fun x => ¬ B x), p.prob x) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact p.sum_one
    rw [hπdef]
    linarith [hsum]
  have hπq : π ≤ 1 - π := by
    have hδpos : 0 ≤ δ := hδ0
    linarith
  have hmono : p.probEvent (fun ω : Fin (2 * r + 1) → X =>
        ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|)
      ≤ p.probEvent (fun ω : Fin (2 * r + 1) → X =>
        r + 1 ≤ (Finset.univ.filter (fun n => B (ω n))).card) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ =>
      Finset.prod_nonneg fun i _ => p.nonneg _
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact heterogeneous_sorted_median_majority_witness r (fun k => v (ω k)) μ ε hε hω.2
  have hbound := probEvent_bad_majority_le (L := 2 * r + 1) p B (r + 1)
  rw [← hπdef, hq] at hbound
  have hfinal : (1 / 2) * (2 * Real.sqrt (π * (1 - π))) ^ (2 * r + 1)
      ≤ (1 / 2) * (2 * Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) := by
    have hs := sqrt_mul_one_sub_le hπ_le_delta hδ2
    have hp : (Real.sqrt (π * (1 - π))) ^ (2 * r + 1)
        ≤ (Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hs (2 * r + 1)
    have hp2 : (2 * Real.sqrt (π * (1 - π))) ^ (2 * r + 1)
        ≤ (2 * Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    linarith
  exact hmono.trans (hbound.trans ((bad_subsets_sum_le r hπ_nonneg hπq).trans hfinal))

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
