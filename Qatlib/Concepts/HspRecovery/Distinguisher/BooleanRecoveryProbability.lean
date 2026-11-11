/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanSamplingProbability

/-!
# Probability bounds for Boolean subgroup recovery

Decodes character samples into Boolean vectors and relates subgroup recovery to spanning the
orthogonal complement. Supported samples always produce a candidate containing the hidden
subgroup; failure is equivalent, in probability, to the existence of a vector outside the
subgroup orthogonal to every sample.

A halfspace probability and a finite union bound give failure at most `|Hᶜ| * (1 / 2) ^ m`, both
for independent finite-distribution records and for fresh circuit measurements. These estimates
formalize the sampling analysis behind Simon-type recovery [Simon1997].

## Main statements

* `booleanSampleCandidate_eq_iff_span_eq_orthogonal`: characterizes exact recovery by spanning.
* `hiddenSubgroupFreshSamples_boolean_no_false_exclusion`: proves zero probability of excluding
  a hidden element.
* `hiddenSubgroupSampleDist_boolean_recovery_failure_le`: bounds recovery failure.
* `hiddenSubgroupFreshSamples_boolean_recovery_success_ge`: bounds success for fresh
  measurements.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.Distinguisher

open scoped Classical

/-- Converts each Boolean-group character sample to its vector index using the inverse of
`booleanCharacterEquiv`. -/
noncomputable def booleanDecodedSamples {n m : ℕ}
    (xs : Fin m → AddChar (BooleanVec n) ℂ) : Fin m → BooleanVec n :=
  fun i => (booleanCharacterEquiv n).symm (xs i)

/-- The decoded sample at index `i` is the inverse-character-equivalence image of `xs i`. -/
@[simp] theorem booleanDecodedSamples_apply {n m : ℕ}
    (xs : Fin m → AddChar (BooleanVec n) ℂ) (i : Fin m) :
    booleanDecodedSamples xs i = (booleanCharacterEquiv n).symm (xs i) := rfl

/-- A decoded sample belongs to the Boolean orthogonal complement of `H` exactly when its
character annihilates `H`. -/
@[simp] theorem booleanDecodedSamples_mem_orthogonal_iff {n m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ) (i : Fin m) :
    booleanDecodedSamples xs i ∈ booleanOrthogonal H ↔
      xs i ∈ characterAnnihilator H := by
  change (booleanCharacterEquiv n).symm (xs i) ∈ booleanOrthogonal H ↔ _
  simpa only [(booleanCharacterEquiv n).apply_symm_apply] using
    (booleanCharacterEquiv_mem_characterAnnihilator_iff H
      ((booleanCharacterEquiv n).symm (xs i))).symm

/-- The sample candidate equals `H` exactly when the sample span equals the Boolean orthogonal
complement of `H`. -/
theorem booleanSampleCandidate_eq_iff_span_eq_orthogonal {n m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (samples : Fin m → BooleanVec n) :
    booleanSampleCandidate samples = H ↔
      booleanSampleSpan samples = booleanOrthogonal H := by
  constructor
  · intro hcand
    rw [booleanSampleCandidate_eq_booleanOrthogonal_span] at hcand
    have horth := congrArg booleanOrthogonal hcand
    rwa [booleanOrthogonal_booleanOrthogonal_eq] at horth
  · exact booleanSampleCandidate_eq_of_span_eq_orthogonal H samples

/-- The sample candidate contains `H` exactly when every sample belongs to the Boolean
orthogonal complement of `H`. -/
theorem le_booleanSampleCandidate_iff {n m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (samples : Fin m → BooleanVec n) :
    H ≤ booleanSampleCandidate samples ↔ ∀ i, samples i ∈ booleanOrthogonal H := by
  constructor
  · intro h i
    rw [mem_booleanOrthogonal]
    intro x
    exact (mem_booleanSampleCandidate samples (x : BooleanVec n)).1 (h x.property) i
  · intro h x hx
    rw [mem_booleanSampleCandidate]
    intro i
    exact (mem_booleanOrthogonal H (samples i)).1 (h i) ⟨x, hx⟩

/-- With no samples, the candidate subgroup is the entire Boolean vector group. -/
@[simp] theorem booleanSampleCandidate_empty {n : ℕ}
    (samples : Fin 0 → BooleanVec n) :
    booleanSampleCandidate samples = ⊤ := by
  ext x
  simp only [mem_booleanSampleCandidate, AddSubgroup.mem_top, iff_true]
  intro i
  exact Fin.elim0 i

/-- The event that every decoded sample lies in the orthogonal complement of `H` but their
additive span is a proper subgroup of that complement. -/
noncomputable def booleanSpanFailureEvent {n m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ) : Prop :=
  (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) ∧
    booleanSampleSpan (booleanDecodedSamples xs) ≠ booleanOrthogonal H

/-- The Boolean dot product is symmetric. -/
private theorem booleanDot_comm_recoveryProbability {n : ℕ}
    (a x : BooleanVec n) : booleanDot a x = booleanDot x a := by
  simp only [booleanDot]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Failure to span the orthogonal complement yields a vector outside `H` orthogonal to every
decoded sample. -/
theorem booleanSpanFailureEvent_exists_separator {n m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hfail : booleanSpanFailureEvent H xs) :
    ∃ x : BooleanVec n, x ∉ H ∧
      ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0 := by
  classical
  have hHle : H ≤ booleanSampleCandidate (booleanDecodedSamples xs) :=
    (le_booleanSampleCandidate_iff H _).2 hfail.1
  have hcand_ne : booleanSampleCandidate (booleanDecodedSamples xs) ≠ H := by
    intro hcand
    exact hfail.2 ((booleanSampleCandidate_eq_iff_span_eq_orthogonal H _).1 hcand)
  have hex : ∃ x : BooleanVec n,
      x ∈ booleanSampleCandidate (booleanDecodedSamples xs) ∧ x ∉ H := by
    by_contra hno
    push Not at hno
    have hcand_le : booleanSampleCandidate (booleanDecodedSamples xs) ≤ H := by
      intro x hx
      exact hno x hx
    exact hcand_ne (le_antisymm hcand_le hHle)
  obtain ⟨x, hxcand, hxH⟩ := hex
  refine ⟨x, hxH, ?_⟩
  intro i
  have hi := (mem_booleanSampleCandidate (booleanDecodedSamples xs) x).1 hxcand i
  rw [booleanDot_comm_recoveryProbability]
  exact hi

/-- Span failure is equivalent to orthogonal support of all decoded samples together with a
vector outside `H` orthogonal to every sample. -/
theorem booleanSpanFailureEvent_iff_supported_exists_separator {n m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ) :
    booleanSpanFailureEvent H xs ↔
      (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) ∧
        ∃ x : BooleanVec n, x ∉ H ∧
          ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0 := by
  constructor
  · intro hfail
    exact ⟨hfail.1, booleanSpanFailureEvent_exists_separator H xs hfail⟩
  · rintro ⟨hs, x, hx, hmiss⟩
    refine ⟨hs, ?_⟩
    intro hspan
    have hcand := booleanSampleCandidate_eq_of_span_eq_orthogonal H
      (booleanDecodedSamples xs) hspan
    have hxcand : x ∈ booleanSampleCandidate (booleanDecodedSamples xs) := by
      rw [mem_booleanSampleCandidate]
      intro i
      rw [booleanDot_comm_recoveryProbability]
      exact hmiss i
    rw [hcand] at hxcand
    exact hx hxcand

/-- Inclusion of events implies the corresponding inequality of independent-sample event
probabilities. -/
private theorem probEvent_mono {X : Type*} [Fintype X] [DecidableEq X]
    {L : ℕ} (p : FinDist X)
    (E F : (Fin L → X) → Prop) [DecidablePred E] [DecidablePred F]
    (hEF : ∀ xs, E xs → F xs) : p.probEvent E ≤ p.probEvent F := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro xs hxs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxs ⊢
    exact hEF xs hxs
  · intro xs _ _
    exact Finset.prod_nonneg (fun i _ => p.nonneg (xs i))

/-- The probability that at least one event in a finite indexed family occurs is at most the sum
of their probabilities. -/
private theorem union_bound_fintype {X I : Type*}
    [Fintype X] [DecidableEq X] [Fintype I]
    {L : ℕ} (p : FinDist X) (E : I → (Fin L → X) → Prop)
    [∀ i, DecidablePred (E i)]
    [DecidablePred (fun xs : Fin L → X => ∃ i, E i xs)] :
    p.probEvent (fun xs => ∃ i, E i xs) ≤ ∑ i : I, p.probEvent (E i) := by
  classical
  let e := Fintype.equivFin I
  have hpred : ∀ xs : Fin L → X,
      (∃ i : I, E i xs) ↔ ∃ j : Fin (Fintype.card I), E (e.symm j) xs := by
    intro xs
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e.symm j, hj⟩
  have hrewrite :
      p.probEvent (fun xs => ∃ i : I, E i xs) =
        p.probEvent (fun xs => ∃ j : Fin (Fintype.card I), E (e.symm j) xs) := by
    unfold FinDist.probEvent
    apply Finset.sum_congr
    · ext xs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred xs
    · intro xs _
      rfl
  calc
    p.probEvent (fun xs => ∃ i : I, E i xs) =
        p.probEvent (fun xs => ∃ j : Fin (Fintype.card I), E (e.symm j) xs) := hrewrite
    _ ≤ ∑ j : Fin (Fintype.card I), p.probEvent (E (e.symm j)) :=
      FinDist.union_bound p (fun j : Fin (Fintype.card I) => E (e.symm j))
    _ = ∑ i : I, p.probEvent (E i) :=
      e.symm.sum_comp (fun i : I => p.probEvent (E i))

variable {n : ℕ} {R : Type*}
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- If `f` hides `H` and `x ∉ H`, the probability that all `m` decoded samples are orthogonal to
`x` is `(1 / 2) ^ m`. -/
theorem hiddenSubgroupSampleDist_boolean_halfspace_event
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    (x : BooleanVec n) (hx : x ∉ H) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0) =
      (1 / 2 : ℝ) ^ m := by
  classical
  have h := hiddenSubgroupFreshSamples_boolean_halfspace f H hf e x hx m
  rw [hiddenSubgroupFreshSamples_event] at h
  have hnonneg : 0 ≤ (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0) :=
    Finset.sum_nonneg (fun xs _ =>
      Finset.prod_nonneg (fun i _ => (hiddenSubgroupSampleDist f e).nonneg (xs i)))
  exact (ENNReal.ofReal_eq_ofReal_iff hnonneg
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m)).1 h

/-- For a function hiding `H`, the probability of supported span failure is at most the number
of vectors outside `H` times `(1 / 2) ^ m`. -/
theorem hiddenSubgroupSampleDist_boolean_span_failure_le
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent (booleanSpanFailureEvent (m := m) H) ≤
      (Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m := by
  classical
  let p := hiddenSubgroupSampleDist f e
  let E : {x : BooleanVec n // x ∉ H} →
      (Fin m → AddChar (BooleanVec n) ℂ) → Prop := fun x xs =>
    ∀ i, booleanDot x.1 (booleanDecodedSamples xs i) = 0
  have hmono : p.probEvent (booleanSpanFailureEvent (m := m) H) ≤
      p.probEvent (fun xs => ∃ x : {x : BooleanVec n // x ∉ H}, E x xs) := by
    apply probEvent_mono
    intro xs hfail
    obtain ⟨x, hxH, hxmiss⟩ := booleanSpanFailureEvent_exists_separator H xs hfail
    exact ⟨⟨x, hxH⟩, hxmiss⟩
  have hunion : p.probEvent (fun xs => ∃ x : {x : BooleanVec n // x ∉ H}, E x xs) ≤
      ∑ x : {x : BooleanVec n // x ∉ H}, p.probEvent (E x) :=
    union_bound_fintype p E
  calc
    (hiddenSubgroupSampleDist f e).probEvent (booleanSpanFailureEvent (m := m) H) =
        p.probEvent (booleanSpanFailureEvent (m := m) H) := rfl
    _ ≤ p.probEvent (fun xs => ∃ x : {x : BooleanVec n // x ∉ H}, E x xs) := hmono
    _ ≤ ∑ x : {x : BooleanVec n // x ∉ H}, p.probEvent (E x) := hunion
    _ = ∑ _x : {x : BooleanVec n // x ∉ H}, (1 / 2 : ℝ) ^ m := by
      apply Finset.sum_congr rfl
      intro x _
      exact hiddenSubgroupSampleDist_boolean_halfspace_event f H hf e x.1 x.2 m
    _ = (Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- For a function hiding `H`, the fresh-measurement probability of supported span failure is at
most `ENNReal.ofReal (|Hᶜ| * (1 / 2) ^ m)`. -/
theorem hiddenSubgroupFreshSamples_boolean_span_failure_le
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (booleanSpanFailureEvent (m := m) H),
      hiddenSubgroupFreshSamples f e m xs) ≤
      ENNReal.ofReal
        ((Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m) := by
  rw [hiddenSubgroupFreshSamples_event]
  apply ENNReal.ofReal_le_ofReal
  exact hiddenSubgroupSampleDist_boolean_span_failure_le f H hf e m

/-- If every decoded sample lies in the orthogonal complement of `H` and span failure does not
occur, the candidate subgroup equals `H`. -/
theorem booleanSampleCandidate_eq_of_supported_not_span_failure {n m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hsupported : ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H)
    (hnot : ¬ booleanSpanFailureEvent H xs) :
    booleanSampleCandidate (booleanDecodedSamples xs) = H := by
  apply booleanSampleCandidate_eq_of_span_eq_orthogonal H
  by_contra hspan
  exact hnot ⟨hsupported, hspan⟩

/-- For a function hiding `H`, a sample sequence with a decoded vector outside the orthogonal
complement of `H` has product probability zero. -/
theorem hiddenSubgroupSampleDist_boolean_probOf_eq_zero_of_not_supported
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hnot : ¬ ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) :
    (hiddenSubgroupSampleDist f e).probOf xs = 0 := by
  classical
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hχ : xs i ∉ characterAnnihilator H := by
    intro hχ
    exact hi ((booleanDecodedSamples_mem_orthogonal_iff H xs i).2 hχ)
  unfold FinDist.probOf
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hiddenSubgroupSampleDist_prob f H hf e, if_neg hχ]

/-- Every decoded sample in a fresh sequence of nonzero mass belongs to the orthogonal
complement of the hidden subgroup. -/
theorem hiddenSubgroupFreshSamples_boolean_supported_of_ne_zero
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hprob : hiddenSubgroupFreshSamples f e m xs ≠ 0) :
    ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H := by
  by_contra hnot
  apply hprob
  rw [hiddenSubgroupFreshSamples_apply,
    hiddenSubgroupSampleDist_boolean_probOf_eq_zero_of_not_supported f H hf e xs hnot,
    ENNReal.ofReal_zero]

/-- For a function hiding `H`, a length-`m` sequence has probability the reciprocal annihilator
cardinality to the power `m` if all decoded samples are orthogonally supported, and zero
otherwise. -/
theorem hiddenSubgroupSampleDist_boolean_probOf
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ) :
    (hiddenSubgroupSampleDist f e).probOf xs =
      if (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) then
        (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m else 0 := by
  classical
  by_cases hs : ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H
  · rw [if_pos hs]
    unfold FinDist.probOf
    calc
      _ = ∏ _i : Fin m, (1 / (Fintype.card (characterAnnihilator H) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hiddenSubgroupSampleDist_prob f H hf e,
          if_pos ((booleanDecodedSamples_mem_orthogonal_iff H xs i).1 (hs i))]
      _ = _ := by simp
  · rw [if_neg hs]
    exact hiddenSubgroupSampleDist_boolean_probOf_eq_zero_of_not_supported f H hf e xs hs

/-- For a function hiding `H`, a sequence has positive product probability exactly when every
decoded sample lies in the orthogonal complement of `H`. -/
theorem hiddenSubgroupSampleDist_boolean_probOf_pos_iff
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ) :
    0 < (hiddenSubgroupSampleDist f e).probOf xs ↔
      ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H := by
  rw [hiddenSubgroupSampleDist_boolean_probOf f H hf e xs]
  have hmass : 0 < (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m := by
    apply pow_pos
    exact div_pos zero_lt_one (by exact_mod_cast Fintype.card_pos)
  by_cases hs : ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H
  · rw [if_pos hs]
    exact iff_of_true hmass hs
  · rw [if_neg hs]
    exact iff_of_false (lt_irrefl 0) hs

/-- A fresh sample sequence has nonzero mass exactly when all its decoded samples belong to the
orthogonal complement of the hidden subgroup. -/
theorem hiddenSubgroupFreshSamples_boolean_ne_zero_iff
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ) :
    hiddenSubgroupFreshSamples f e m xs ≠ 0 ↔
      ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H := by
  rw [hiddenSubgroupFreshSamples_apply, ENNReal.ofReal_ne_zero_iff]
  exact hiddenSubgroupSampleDist_boolean_probOf_pos_iff f H hf e xs

/-- For a function hiding `H`, every fresh sequence of nonzero mass produces a candidate
subgroup containing `H`. -/
theorem hiddenSubgroupFreshSamples_boolean_le_candidate_of_ne_zero
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    {m : ℕ} (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hprob : hiddenSubgroupFreshSamples f e m xs ≠ 0) :
    H ≤ booleanSampleCandidate (booleanDecodedSamples xs) :=
  (le_booleanSampleCandidate_iff H _).2
    ((hiddenSubgroupFreshSamples_boolean_ne_zero_iff f H hf e xs).1 hprob)

/-- For a function hiding `H`, an event probability equals the number of supported satisfying
sequences times the reciprocal annihilator cardinality to the power `m`. -/
theorem hiddenSubgroupSampleDist_boolean_event_eq_card
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ)
    (E : (Fin m → AddChar (BooleanVec n) ℂ) → Prop) [DecidablePred E] :
    (hiddenSubgroupSampleDist f e).probEvent E =
      ((Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) ∧ E xs)).card : ℝ) *
        (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m := by
  classical
  calc
    _ = ∑ _xs ∈ Finset.univ.filter
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) ∧ E xs),
          (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m := by
      simp only [FinDist.probEvent, Finset.sum_filter,
        hiddenSubgroupSampleDist_boolean_probOf f H hf e]
      apply Finset.sum_congr rfl
      intro xs _
      by_cases hE : E xs <;> simp [hE]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- For a function hiding `H`, a fresh-measurement event probability is the `ENNReal.ofReal`
conversion of its supported satisfying-sequence count times the reciprocal annihilator
cardinality to the power `m`. -/
theorem hiddenSubgroupFreshSamples_boolean_event_eq_card
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ)
    (E : (Fin m → AddChar (BooleanVec n) ℂ) → Prop) [DecidablePred E] :
    (∑ xs ∈ Finset.univ.filter E, hiddenSubgroupFreshSamples f e m xs) =
      ENNReal.ofReal
        (((Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) ∧ E xs)).card : ℝ) *
          (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m) := by
  rw [hiddenSubgroupFreshSamples_event,
    hiddenSubgroupSampleDist_boolean_event_eq_card f H hf e m E]

/-- For a function hiding `H`, events agreeing on orthogonally supported decoded sequences have
equal independent-sample probabilities. -/
theorem hiddenSubgroupSampleDist_boolean_event_congr
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ)
    (E F : (Fin m → AddChar (BooleanVec n) ℂ) → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ xs, (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) →
      (E xs ↔ F xs)) :
    (hiddenSubgroupSampleDist f e).probEvent E =
      (hiddenSubgroupSampleDist f e).probEvent F := by
  rw [hiddenSubgroupSampleDist_boolean_event_eq_card f H hf e m E,
    hiddenSubgroupSampleDist_boolean_event_eq_card f H hf e m F]
  apply congrArg (fun S : Finset (Fin m → AddChar (BooleanVec n) ℂ) =>
    (S.card : ℝ) * (1 / (Fintype.card (characterAnnihilator H) : ℝ)) ^ m)
  ext xs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hE⟩
    exact ⟨hs, (hEF xs hs).1 hE⟩
  · rintro ⟨hs, hF⟩
    exact ⟨hs, (hEF xs hs).2 hF⟩

/-- For a function hiding `H`, events agreeing on orthogonally supported decoded sequences have
equal fresh-measurement probabilities. -/
theorem hiddenSubgroupFreshSamples_boolean_event_congr
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ)
    (E F : (Fin m → AddChar (BooleanVec n) ℂ) → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ xs, (∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) →
      (E xs ↔ F xs)) :
    (∑ xs ∈ Finset.univ.filter E, hiddenSubgroupFreshSamples f e m xs) =
      ∑ xs ∈ Finset.univ.filter F, hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_event, hiddenSubgroupFreshSamples_event]
  exact congrArg ENNReal.ofReal
    (hiddenSubgroupSampleDist_boolean_event_congr f H hf e m E F hEF)

/-- For a function hiding `H`, the probability that the sample candidate fails to contain `H` is
zero. -/
theorem hiddenSubgroupFreshSamples_boolean_no_false_exclusion
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        ¬ H ≤ booleanSampleCandidate (booleanDecodedSamples xs)),
      hiddenSubgroupFreshSamples f e m xs) = 0 := by
  have heq := hiddenSubgroupFreshSamples_boolean_event_congr f H hf e m
    (fun xs => ¬ H ≤ booleanSampleCandidate (booleanDecodedSamples xs))
    (fun _ => False) (by
      intro xs hs
      have hle := (le_booleanSampleCandidate_iff H (booleanDecodedSamples xs)).2 hs
      simp only [hle, not_true_eq_false])
  simpa only [Finset.filter_false, Finset.sum_empty] using heq

/-- For a function hiding `H`, recovery failure has the same probability as the existence of a
vector outside `H` orthogonal to every decoded sample. -/
theorem hiddenSubgroupSampleDist_boolean_recovery_failure_eq_separator_event
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) =
      (hiddenSubgroupSampleDist f e).probEvent
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∃ x : BooleanVec n, x ∉ H ∧
            ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0) := by
  apply hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
  intro xs hs
  have h := booleanSpanFailureEvent_iff_supported_exists_separator H xs
  rw [booleanSpanFailureEvent, and_iff_right hs, and_iff_right hs] at h
  exact (not_congr (booleanSampleCandidate_eq_iff_span_eq_orthogonal H _)).trans h

/-- For a function hiding `H`, fresh-measurement recovery failure has the same probability as a
vector outside `H` being orthogonal to every decoded sample. -/
theorem hiddenSubgroupFreshSamples_boolean_recovery_failure_eq_separator_event
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e m xs) =
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∃ x : BooleanVec n, x ∉ H ∧
            ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0),
        hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_event, hiddenSubgroupFreshSamples_event,
    hiddenSubgroupSampleDist_boolean_recovery_failure_eq_separator_event f H hf e m]

/-- For a function hiding `H`, the probability that the candidate differs from `H` equals the
probability of supported span failure. -/
theorem hiddenSubgroupSampleDist_boolean_recovery_failure_eq_span_failure
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) =
      (hiddenSubgroupSampleDist f e).probEvent (booleanSpanFailureEvent (m := m) H) := by
  apply hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
  intro xs hs
  rw [booleanSpanFailureEvent, and_iff_right hs]
  exact not_congr (booleanSampleCandidate_eq_iff_span_eq_orthogonal H _)

/-- For a function hiding `H`, the probability that the sample candidate differs from `H` is at
most `|Hᶜ| * (1 / 2) ^ m`. -/
theorem hiddenSubgroupSampleDist_boolean_recovery_failure_le
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) ≤
      (Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m := by
  rw [hiddenSubgroupSampleDist_boolean_recovery_failure_eq_span_failure f H hf e m]
  exact hiddenSubgroupSampleDist_boolean_span_failure_le f H hf e m

/-- For a function hiding `H`, the fresh-measurement recovery failure probability is at most the
`ENNReal.ofReal` conversion of `|Hᶜ| * (1 / 2) ^ m`. -/
theorem hiddenSubgroupFreshSamples_boolean_recovery_failure_le
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e m xs) ≤
      ENNReal.ofReal
        ((Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m) := by
  rw [hiddenSubgroupFreshSamples_event]
  exact ENNReal.ofReal_le_ofReal
    (hiddenSubgroupSampleDist_boolean_recovery_failure_le f H hf e m)

/-- For a function hiding `H`, the sample candidate equals `H` with probability at least `1 -
|Hᶜ| * (1 / 2) ^ m`. -/
theorem hiddenSubgroupSampleDist_boolean_recovery_success_ge
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    1 - (Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m ≤
      (hiddenSubgroupSampleDist f e).probEvent
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H) := by
  classical
  let p := hiddenSubgroupSampleDist f e
  let E : (Fin m → AddChar (BooleanVec n) ℂ) → Prop := fun xs =>
    booleanSampleCandidate (booleanDecodedSamples xs) = H
  have hsplit : p.probEvent (fun xs => ¬ E xs) + p.probEvent E = 1 := by
    simp only [FinDist.probEvent, Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      _ = ∑ xs : Fin m → AddChar (BooleanVec n) ℂ, p.probOf xs := by
        apply Finset.sum_congr rfl
        intro xs _
        by_cases hE : E xs <;> simp [hE]
      _ = 1 := FinDist.sum_probOf p m
  have hfail := hiddenSubgroupSampleDist_boolean_recovery_failure_le f H hf e m
  change p.probEvent (fun xs => ¬ E xs) ≤ _ at hfail
  change _ ≤ p.probEvent E
  linarith

/-- For a function hiding `H`, the fresh-measurement recovery success probability is at least
the `ENNReal.ofReal` conversion of `1 - |Hᶜ| * (1 / 2) ^ m`. -/
theorem hiddenSubgroupFreshSamples_boolean_recovery_success_ge
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    ENNReal.ofReal
      (1 - (Fintype.card {x : BooleanVec n // x ∉ H} : ℝ) * (1 / 2 : ℝ) ^ m) ≤
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H),
        hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_event]
  exact ENNReal.ofReal_le_ofReal
    (hiddenSubgroupSampleDist_boolean_recovery_success_ge f H hf e m)

end Qatlib.Concepts.HspRecovery.Distinguisher
