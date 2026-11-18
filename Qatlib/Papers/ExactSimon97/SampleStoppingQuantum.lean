/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.SampleStoppingInf
public import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupRepetition
public import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality

@[expose] public section

/-!
# Executable Fourier-sampler semantics for the uniform stopping process

The stopping modules construct the finite-window and infinite-process stopping laws for
independent draws from the idealized distribution `unifOnSub`. This module identifies that
per-draw interface with the public coherent hidden-subgroup sampling program.

For an oracle `f` hiding `H`, `hiddenSubgroupSamplingCircuit` executes one additive-oracle
query followed by the Fourier gate on the first register. Its first-register measurement is
therefore indexed by `AddChar G ℂ`; the uniform subgroup in the stopping theorem is the
character annihilator `characterAnnihilator H`, as required by Fourier sampling. The public
`hiddenSubgroupSampleDist` packages precisely this Born marginal as a `FinDist`.

The main bridges are:

* `sampleDist_prob_eq_unifOnSub`: the executable Born probability of every character equals
  the idealized `unifOnSub (characterAnnihilator H)` mass. Thus uniformity is proved from the
  circuit semantics, not assumed as a sampling interface.
* `freshSamples_probOf_eq_unifOnSub` and `freshSamples_event_eq_unifOnSub`: the public fresh-run
  PMF has exactly the independent product masses and event probabilities used in the finite-window stopping law.
* `freshSamples_stopGen_tail`: the quantum fresh-run probability of the first-generation tail
  event is exactly `failProbAt (characterAnnihilator H) k`, directly instantiating the earlier
  stopping-law identification without changing its expectation proof.
* `samplingCircuit_queryCount`: the actual composed query-then-QFT word contains exactly one
  oracle query per draw. `freshSchedule_queryCount_stopGen` consequently charges exactly
  `stopGen K ω` queries to the fresh-run schedule stopped on a record `ω`.

No new quantum state, oracle model, independence assumption, or abstract query cost is
introduced: all semantic and resource statements reuse the public circuit, Born, fresh-run,
and `QueryCount` definitions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open scoped BigOperators Classical ENNReal

namespace Qatlib.Papers.ExactSimon97.SampleStoppingQuantum

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.ExactSimon97.SampleStopping
open Qatlib.Papers.NoncommHSP98.MainResults

/-! ## The coherent query-then-Fourier word and its Born law -/

section Sampler

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [DecidableEq G] [AddCommGroup R] [Fintype R] in
/-- The public hidden-subgroup sampler is the composed word consisting of one oracle-query
segment followed by one first-register Fourier-gate segment. -/
theorem samplingCircuit_eq_query_append_qft (e : G ≃ AddChar G ℂ) :
    hiddenSubgroupSamplingCircuit (R := R) e =
      [Step.query] ++ [Step.gate (TensorGate (fourierGate e) 1)] :=
  rfl

omit [DecidableEq G] [AddCommGroup R] [Fintype R] in
/-- The actual composed sampling word makes exactly one oracle query per draw; the Fourier
segment contributes no query. This is a count of instructions in the executable word, not an
abstract per-history cost assignment. -/
theorem samplingCircuit_queryCount (e : G ≃ AddChar G ℂ) :
    QueryCount (hiddenSubgroupSamplingCircuit (R := R) e) = 1 := by
  rw [samplingCircuit_eq_query_append_qft, queryCount_append]
  rfl

/-- Born-probability uniformity for the coherent sampler. If `f` hides `H`, the probability of
measuring a character after the query-then-QFT word is exactly the idealized uniform mass on
`characterAnnihilator H`, including zero mass outside that subgroup. -/
theorem sampleDist_prob_eq_unifOnSub (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (χ : AddChar G ℂ) :
    (hiddenSubgroupSampleDist f e).prob χ =
      (unifOnSub (characterAnnihilator H)).prob χ := by
  rw [hiddenSubgroupSampleDist_prob f H hf]
  rfl

/-- Independent record masses under the executable one-draw Born law agree with the idealized
uniform-subgroup product law coordinate by coordinate. -/
theorem sampleDist_probOf_eq_unifOnSub (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) {L : ℕ}
    (ω : Fin L → AddChar G ℂ) :
    (hiddenSubgroupSampleDist f e).probOf ω =
      (unifOnSub (characterAnnihilator H)).probOf ω := by
  unfold FinDist.probOf
  exact Finset.prod_congr rfl
    (fun i _ => sampleDist_prob_eq_unifOnSub f H hf e (ω i))

/-- Every finite-window event has the same probability under the executable Born law and the
idealized uniform-subgroup law. -/
theorem sampleDist_probEvent_eq_unifOnSub (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) {L : ℕ}
    (E : (Fin L → AddChar G ℂ) → Prop) [DecidablePred E] :
    (hiddenSubgroupSampleDist f e).probEvent E =
      (unifOnSub (characterAnnihilator H)).probEvent E :=
  probEventCongrLaw (fun χ => sampleDist_prob_eq_unifOnSub f H hf e χ) E

end Sampler

/-! ## Fresh quantum runs instantiate the stopping process -/

section FreshRuns

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- The PMF mass of a record of fresh coherent sampling runs is the `ENNReal` image of the
idealized independent uniform-subgroup record mass. -/
theorem freshSamples_probOf_eq_unifOnSub (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (L : ℕ)
    (ω : Fin L → AddChar G ℂ) :
    hiddenSubgroupFreshSamples f e L ω =
      ENNReal.ofReal ((unifOnSub (characterAnnihilator H)).probOf ω) := by
  rw [hiddenSubgroupFreshSamples_apply, sampleDist_probOf_eq_unifOnSub f H hf]

/-- The fresh-run quantum probability of any decidable finite-record event equals the `ENNReal`
image of its probability under the idealized uniform-subgroup window law. -/
theorem freshSamples_event_eq_unifOnSub (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (L : ℕ)
    (E : (Fin L → AddChar G ℂ) → Prop) [DecidablePred E] :
    (∑ ω ∈ Finset.univ.filter E, hiddenSubgroupFreshSamples f e L ω) =
      ENNReal.ofReal ((unifOnSub (characterAnnihilator H)).probEvent E) := by
  rw [hiddenSubgroupFreshSamples_event,
    sampleDist_probEvent_eq_unifOnSub f H hf]

/-- The executable stopping-law bridge: among fresh query-then-QFT sampling runs, the
probability that the first-generation time exceeds `k` is exactly the generation-failure
probability from the finite-window stopping law. No separate or idealized quantum stopping distribution is used. -/
theorem freshSamples_stopGen_tail (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) {L k : ℕ} (hk : k < L) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin L → AddChar G ℂ => k < stopGen (characterAnnihilator H) ω),
        hiddenSubgroupFreshSamples f e L ω) =
      ENNReal.ofReal (failProbAt (characterAnnihilator H) k) := by
  rw [freshSamples_event_eq_unifOnSub f H hf,
    probEvent_stopGen_gt (characterAnnihilator H) hk]

omit [DecidableEq G] [AddCommGroup R] [Fintype R] in
/-- Query accounting at the stopping time: the fresh schedule containing one composed sampling
word for each draw up to `stopGen K ω` uses exactly `stopGen K ω` oracle queries. The statement
is for an arbitrary target character subgroup `K`, independent of the stopping expectation
bound, which remains the uncensored infinite-process result. -/
theorem freshSchedule_queryCount_stopGen (e : G ≃ AddChar G ℂ)
    (K : AddSubgroup (AddChar G ℂ)) {L : ℕ} (ω : Fin L → AddChar G ℂ) :
    ((List.replicate (stopGen K ω)
        (hiddenSubgroupSamplingCircuit (R := R) e)).map QueryCount).sum = stopGen K ω := by
  exact (hiddenSubgroupFreshSchedule_resources (R := R) e (stopGen K ω)).1

end FreshRuns

/-! ## Infinite repetition, recovery, and total executed query cost -/

section InfiniteRuns

open MeasureTheory Qatlib.Papers.ExactSimon97.SampleStoppingInf
open Qatlib.Concepts.HspRecovery.BackendAudit

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]
  [MeasurableSpace (AddChar G ℂ)] [DiscreteMeasurableSpace (AddChar G ℂ)]

/-- The discrete measure obtained from the actual one-run Born probabilities. -/
noncomputable def bornMeasure (f : G → R) (e : G ≃ AddChar G ℂ) :
    Measure (AddChar G ℂ) :=
  Measure.sum fun χ => ENNReal.ofReal ((hiddenSubgroupSampleDist f e).prob χ) •
    Measure.dirac χ

/-- Fresh coherent runs form the infinite product of their actual Born measures. -/
noncomputable def bornSeq (f : G → R) (e : G ≃ AddChar G ℂ) :
    Measure (ℕ → AddChar G ℂ) :=
  Measure.infinitePi fun _ : ℕ => bornMeasure f e

omit [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- A hiding oracle identifies the actual Born measure with the uniform annihilator measure. -/
theorem bornMeasure_eq (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (e : G ≃ AddChar G ℂ) : bornMeasure f e = unifSubMeasure (characterAnnihilator H) := by
  unfold bornMeasure unifSubMeasure
  congr 1
  funext χ
  rw [sampleDist_prob_eq_unifOnSub f H hf e χ]

omit [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- The repeated quantum sampling process has exactly the infinite iid stopping law. -/
theorem bornSeq_eq (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (e : G ≃ AddChar G ℂ) : bornSeq f e = unifSubSeq (characterAnnihilator H) := by
  unfold bornSeq unifSubSeq
  simp only [bornMeasure_eq f H hf e]

/-- The repeated Born process has total mass one for a hiding oracle, so its
almost-sure and expected-query statements concern a genuine probability law. -/
theorem bornSeq_isProbabilityMeasure (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) :
    IsProbabilityMeasure (bornSeq f e) := by
  rw [bornSeq_eq f H hf e]
  unfold unifSubSeq
  let : ∀ _ : ℕ, IsProbabilityMeasure (unifSubMeasure (characterAnnihilator H)) :=
    fun _ => isProbabilityMeasure_unifSubMeasure (characterAnnihilator H)
  infer_instance

/-- Total queries are the monotone limit of actual stopped finite-window schedule counts.
Each schedule uses fresh query-then-Fourier words; divergence is charged infinite cost. -/
noncomputable def totalQueries (e : G ≃ AddChar G ℂ)
    (K : AddSubgroup (AddChar G ℂ)) (ω : ℕ → AddChar G ℂ) : ℝ≥0∞ :=
  ⨆ L : ℕ, ((((List.replicate (stopGen K (windowOf L ω))
    (hiddenSubgroupSamplingCircuit (R := R) e)).map QueryCount).sum : ℕ) : ℝ≥0∞)

omit [DecidableEq G] [AddCommGroup R] [Fintype R]
  [MeasurableSpace (AddChar G ℂ)] [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- The uncensored quantum query bill equals the first generation time pointwise. -/
theorem totalQueries_eq (e : G ≃ AddChar G ℂ)
    (K : AddSubgroup (AddChar G ℂ)) (ω : ℕ → AddChar G ℂ) :
    totalQueries (R := R) e K ω = stopGenInf K ω := by
  unfold totalQueries
  simp only [freshSchedule_queryCount_stopGen]
  exact (stopGenInf_eq_iSup_windowOf K ω).symm

/-- The subgroup recovered from a prefix is its character annihilator transported
back through the canonical double-dual embedding. This is mathematical recovery,
without a claim about the classical cost of computing its basis. -/
noncomputable def recoveredPrefix (ω : ℕ → AddChar G ℂ) (k : ℕ) : AddSubgroup G :=
  (characterAnnihilator (spanInf ω k)).comap AddChar.doubleDualEmb

omit [DecidableEq G] [MeasurableSpace (AddChar G ℂ)]
  [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- Generating the full annihilator suffices to recover the hidden subgroup exactly. -/
theorem recoveredPrefix_eq (H : AddSubgroup G) (ω : ℕ → AddChar G ℂ) (k : ℕ)
    (hspan : spanInf ω k = characterAnnihilator H) : recoveredPrefix ω k = H := by
  unfold recoveredPrefix
  rw [hspan]
  exact doubleCharacterAnnihilator_eq H

/-- Repeated coherent sampling reaches a prefix recovering the hidden subgroup
almost surely. Independence comes from fresh runs, and recovery uses finite abelian duality. -/
theorem bornSeq_recovery_null (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) :
    bornSeq f e {ω | ¬ ∃ k, recoveredPrefix ω k = H} = 0 := by
  rw [bornSeq_eq f H hf e]
  apply measure_mono_null _ (measure_stopGenInf_top (characterAnnihilator H))
  intro ω hω
  have hnone : ¬ ∃ k, spanInf ω k = characterAnnihilator H := by
    rintro ⟨k, hk⟩
    exact hω ⟨k, recoveredPrefix_eq H ω k hk⟩
  simp only [Set.mem_ofPred_eq, stopGenInf, dite_eq_right hnone]

/-- End-to-end expected query bound for fresh coherent sampling until the observed
characters generate the annihilator: at most `2 log₂ |H⊥|` oracle calls. The target
annihilator has at least two elements. The stopping rule is relative to that target;
no oracle-free certificate of its unknown rank or classical runtime is asserted. -/
theorem expected_totalQueries_le (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ)
    (hcard : 2 ≤ Fintype.card (characterAnnihilator H)) :
    ∫⁻ ω, totalQueries (R := R) e (characterAnnihilator H) ω ∂(bornSeq f e) ≤
      ENNReal.ofReal (2 * Real.logb 2 (Fintype.card (characterAnnihilator H) : ℝ)) := by
  simp only [totalQueries_eq, bornSeq_eq f H hf e]
  exact stopGenInf_lintegral_le (characterAnnihilator H) hcard

/-- The actual total quantum query bill is finite almost surely. -/
theorem totalQueries_infinite_null (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) :
    bornSeq f e {ω | totalQueries (R := R) e (characterAnnihilator H) ω = ⊤} = 0 := by
  simp only [totalQueries_eq, bornSeq_eq f H hf e]
  exact measure_stopGenInf_top (characterAnnihilator H)

end InfiniteRuns

/-! ## Stopping by an observed rank when the target size is known -/

section ObservedRank

open MeasureTheory Qatlib.Papers.ExactSimon97.SampleStoppingInf

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]
  [MeasurableSpace (AddChar G ℂ)] [DiscreteMeasurableSpace (AddChar G ℂ)]

/-- Stop as soon as the observed character span has the prescribed cardinality.
For a known rank `d` over two elements, the prescribed size is `2^d`.
This rule inspects the observed span and a size, rather than a hidden subgroup. -/
noncomputable def observedStop (N : ℕ) (ω : ℕ → AddChar G ℂ) : ℝ≥0∞ :=
  if hex : ∃ k, Fintype.card (spanInf ω k) = N then (Nat.find hex : ℝ≥0∞) else ⊤

omit [DecidableEq G] [MeasurableSpace (AddChar G ℂ)]
  [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- On a record supported in a subgroup of known size, reaching that size is
equivalent to spanning the entire subgroup. -/
theorem observed_card_iff (K : AddSubgroup (AddChar G ℂ)) (N : ℕ)
    (hN : Fintype.card K = N) (ω : ℕ → AddChar G ℂ)
    (hmem : ∀ i, ω i ∈ K) (k : ℕ) :
    Fintype.card (spanInf ω k) = N ↔ spanInf ω k = K := by
  constructor
  · intro hk
    apply AddSubgroup.eq_of_le_of_card_ge (spanInf_le ω k K (fun i => hmem i))
    simp only [Nat.card_eq_fintype_card]
    exact (hk.trans hN.symm).ge
  · intro hk
    rw [hk, hN]

omit [DecidableEq G] [MeasurableSpace (AddChar G ℂ)]
  [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- On supported records the observable size stopping rule is exactly the
first full-generation time, including the divergent branch. -/
theorem observedStop_eq (K : AddSubgroup (AddChar G ℂ)) (N : ℕ)
    (hN : Fintype.card K = N) (ω : ℕ → AddChar G ℂ)
    (hmem : ∀ i, ω i ∈ K) : observedStop N ω = stopGenInf K ω := by
  have hi := observed_card_iff K N hN ω hmem
  by_cases hex : ∃ k, spanInf ω k = K
  · have hobs : ∃ k, Fintype.card (spanInf ω k) = N := by
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, (hi k).mpr hk⟩
    simp only [observedStop, stopGenInf, dite_eq_left hobs, dite_eq_left hex]
    congr 1
    exact Nat.le_antisymm
      (Nat.find_min' hobs ((hi _).mpr (Nat.find_spec hex)))
      (Nat.find_min' hex ((hi _).mp (Nat.find_spec hobs)))
  · have hobs : ¬ ∃ k, Fintype.card (spanInf ω k) = N := by
      rintro ⟨k, hk⟩
      exact hex ⟨k, (hi k).mp hk⟩
    simp only [observedStop, stopGenInf, dite_eq_right hobs, dite_eq_right hex]

/-- The observable known-size stopping rule agrees almost surely with the
quantum full-generation stopping rule. All samples stay in the annihilator
almost surely, by the genuine Born product measure. -/
theorem observedStop_eq_ae (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (N : ℕ)
    (hN : Fintype.card (characterAnnihilator H) = N) :
    (fun ω => observedStop N ω) =ᵐ[bornSeq f e]
      (fun ω => stopGenInf (characterAnnihilator H) ω) := by
  rw [bornSeq_eq f H hf e]
  have hs : ∀ k : ℕ, ∀ᵐ ω ∂unifSubSeq (characterAnnihilator H),
      ω k ∈ characterAnnihilator H := by
    intro k
    apply ae_iff.mpr
    apply measure_mono_null ?_ (measure_escape_null (characterAnnihilator H) (k + 1))
    intro ω hω
    exact ⟨⟨k, Nat.lt_succ_self k⟩, hω⟩
  exact (ae_all_iff.mpr hs).mono fun ω hω =>
    observedStop_eq (characterAnnihilator H) N hN ω hω

/-- The query bill for the observable stopping rule: each fresh coherent
query-then-Fourier trial pays its actual word query count. -/
noncomputable def observedQueries (e : G ≃ AddChar G ℂ) (N : ℕ)
    (ω : ℕ → AddChar G ℂ) : ℝ≥0∞ :=
  (QueryCount (hiddenSubgroupSamplingCircuit (R := R) e) : ℝ≥0∞) * observedStop N ω

omit [DecidableEq G] [AddCommGroup R] [Fintype R]
  [MeasurableSpace (AddChar G ℂ)] [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- Each observed-rank trial uses one query, so the query bill equals the
observable stopping time even on divergent records. -/
theorem observedQueries_eq (e : G ≃ AddChar G ℂ) (N : ℕ)
    (ω : ℕ → AddChar G ℂ) : observedQueries (R := R) e N ω = observedStop N ω := by
  simp only [observedQueries, samplingCircuit_queryCount, Nat.cast_one, one_mul]

/-- The known-size query bill is almost surely the monotone limit of actual
stopped finite-window circuit-query counts, tying the observable rule to the
same executed-word ledger as the uncensored quantum process. -/
theorem observedQueries_eq_totalQueries_ae (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (N : ℕ)
    (hN : Fintype.card (characterAnnihilator H) = N) :
    (fun ω => observedQueries (R := R) e N ω) =ᵐ[bornSeq f e]
      (fun ω => totalQueries (R := R) e (characterAnnihilator H) ω) := by
  exact (observedStop_eq_ae f H hf e N hN).mono fun ω hω => by
    simpa only [observedQueries_eq, totalQueries_eq] using hω

/-- Repeated coherent sampling until a prescribed known target size is reached
uses at most `2 log₂ N` oracle queries in complete expectation. This covers
known-rank Simon targets via `N = 2^d`; it makes no worst-case runtime claim. -/
theorem expected_observedQueries_le (f : G → R) (H : AddSubgroup G)
    (hf : HidesSubgroup f H) (e : G ≃ AddChar G ℂ) (N : ℕ)
    (hN : Fintype.card (characterAnnihilator H) = N) (hsize : 2 ≤ N) :
    ∫⁻ ω, observedQueries (R := R) e N ω ∂(bornSeq f e) ≤
      ENNReal.ofReal (2 * Real.logb 2 (N : ℝ)) := by
  simp only [observedQueries_eq]
  rw [lintegral_congr_ae (observedStop_eq_ae f H hf e N hN), bornSeq_eq f H hf e]
  have h := stopGenInf_lintegral_le (characterAnnihilator H) (by rw [hN]; exact hsize)
  simpa only [hN] using h

omit [DecidableEq G] [MeasurableSpace (AddChar G ℂ)]
  [DiscreteMeasurableSpace (AddChar G ℂ)] in
/-- At an observed known-size stopping prefix, annihilator recovery gives the
hidden subgroup exactly on supported records. The premise supplies the known
target size and support, rather than the desired recovered subgroup. -/
theorem recovery_at_observed_stop (H : AddSubgroup G) (N : ℕ)
    (hN : Fintype.card (characterAnnihilator H) = N) (ω : ℕ → AddChar G ℂ)
    (hmem : ∀ i, ω i ∈ characterAnnihilator H)
    (hex : ∃ k, Fintype.card (spanInf ω k) = N) :
    recoveredPrefix ω (Nat.find hex) = H := by
  apply recoveredPrefix_eq
  exact (observed_card_iff (characterAnnihilator H) N hN ω hmem _).mp (Nat.find_spec hex)

end ObservedRank

end Qatlib.Papers.ExactSimon97.SampleStoppingQuantum
