/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomizedObservedExecution

/-!
# A mixed-state measurement feedback example

The Boolean-indexed family `mixedFeedbackProgram`, randomized using `mixedChoiceWeights` and
executed on `mixedFeedbackInput`, combines classical choice with a computational-basis
measurement and an outcome-dependent number of oracle queries. The input is the maximally mixed
qubit state, illustrating the density-operator and measurement formalism of [NielsenChuang2010].

For the identity oracle and choice weights `1 / 3` and `2 / 3`, the induced instrument has
expected query count `1` and acceptance probability `2 / 3`. Appending a continuation that makes
one further query after rejection gives expected query count `4 / 3`.

## Main statements

* `mixed_feedback_consumer_data`: validity and nonpurity of the input, well-formedness, and
  choice weights.
* `mixed_feedback_consumer_cost_and_output`: the instrument's expected query count and
  acceptance probability.
* `mixed_feedback_continuation_consumer`: the expected query count after the rejection
  continuation.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped ComplexOrder

/-- The identity operator on a qubit is unitary. -/
private theorem one_mem_unitary : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.one_mem _

/-- Conjugation by the identity leaves every operator unchanged. -/
private theorem conjBranch_one {D : ℕ} (X : Operator D) :
    conjBranch (1 : Operator D) X = X := by
  simp

/-- The list generated from a function on `Fin 2` consists of its values at `0` and `1`, in that
order. -/
private theorem list_ofFn_two {α : Type*} (f : Fin 2 → α) : List.ofFn f = [f 0, f 1] := rfl

/-- The Boolean distribution assigning probability `1 / 3` to `false` and `2 / 3` to `true`. -/
noncomputable def mixedChoiceWeights : FinDist Bool where
  prob := fun b => if b then 2 / 3 else 1 / 3
  nonneg := by
    intro b
    cases b <;> norm_num
  sum_one := by
    rw [Fintype.univ_bool]
    norm_num

/-- The measurement continuation that makes one query and accepts on outcome `0`, or applies the
identity, makes two queries, and rejects on the other outcome. -/
private def feedbackNext (o : Fin 2) : ObservedCircuit (Fin 2) :=
  if o = 0 then .step .query (.halt true)
  else .step (.gate (1 : Operator 2)) (.step .query (.step .query (.halt false)))

/-- Outcome `0` selects the continuation that makes one query and accepts. -/
private theorem feedbackNext_zero :
    feedbackNext 0 = .step .query (.halt true) := by
  simp [feedbackNext]

/-- Outcome `1` selects the continuation that applies the identity, makes two queries, and
rejects. -/
private theorem feedbackNext_one :
    feedbackNext 1 = .step (.gate (1 : Operator 2)) (.step .query (.step .query (.halt false))) := by
  simp [feedbackNext]

/-- A Boolean-indexed family that accepts immediately on `false` and measures the qubit in the
computational basis before following `feedbackNext` on `true`. -/
def mixedFeedbackProgram : Bool → ObservedCircuit (Fin 2)
  | false => .halt true
  | true => .measure 2 (fun x => x) feedbackNext

/-- The maximally mixed qubit operator, equal to one half of the identity. -/
noncomputable def mixedFeedbackInput : Operator 2 := ((1 / 2 : ℝ) : ℂ) • (1 : Operator 2)

/-- The maximally mixed input operator is positive semidefinite. -/
private theorem input_psd : mixedFeedbackInput.PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one (RCLike.ofReal_nonneg.mpr one_half_pos.le)

/-- The mixed feedback input has trace one. -/
private theorem input_trace : Matrix.trace mixedFeedbackInput = 1 := by
  simp only [mixedFeedbackInput, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.sum_univ_two]
  norm_num

/-- The real part of the mixed feedback input's trace equals one. -/
private theorem input_trace_re : (Matrix.trace mixedFeedbackInput).re = 1 := by
  rw [input_trace]
  rfl

/-- The maximally mixed qubit input is not a pure density operator. -/
private theorem input_not_pure : ¬ IsPureDensityOperator mixedFeedbackInput := by
  intro hpure
  obtain ⟨_, hsq⟩ := hpure
  have htr := congrArg Matrix.trace hsq
  have h1 : Matrix.trace (mixedFeedbackInput * mixedFeedbackInput) = ((1 / 2 : ℝ) : ℂ) := by
    simp only [mixedFeedbackInput, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two]
    norm_num
  rw [h1, input_trace] at htr
  exact absurd (Complex.ofReal_inj.mp htr) (by norm_num)

/-- Both members of the mixed feedback program family are well formed. -/
private theorem program_wf : ∀ b, observedWellFormed (mixedFeedbackProgram b) := by
  intro b
  cases b with
  | false => exact trivial
  | true =>
    intro o
    by_cases ho : o = 0
    · rw [show (feedbackNext o) = (if o = 0 then (.step .query (.halt true) :
          ObservedCircuit (Fin 2)) else
          .step (.gate (1 : Operator 2)) (.step .query (.step .query (.halt false)))) from rfl,
        if_pos ho]
      exact trivial
    · rw [show (feedbackNext o) = (if o = 0 then (.step .query (.halt true) :
          ObservedCircuit (Fin 2)) else
          .step (.gate (1 : Operator 2)) (.step .query (.step .query (.halt false)))) from rfl,
        if_neg ho]
      exact ⟨Submonoid.one_mem _, trivial⟩

/-- The feedback input is a nonpure density operator, both program branches are well formed, and
their choice probabilities are `1 / 3` and `2 / 3`. -/
theorem mixed_feedback_consumer_data :
    IsDensityOperator mixedFeedbackInput ∧ ¬ IsPureDensityOperator mixedFeedbackInput ∧
    (∀ b, observedWellFormed (mixedFeedbackProgram b)) ∧
    mixedChoiceWeights.prob false = 1 / 3 ∧ mixedChoiceWeights.prob true = 2 / 3 := by
  refine ⟨⟨input_psd, input_trace⟩, input_not_pure, program_wf, ?_, ?_⟩
  · rfl
  · rfl

/-- With the identity oracle, the `false` program yields a single accepting trace with unchanged
input and no operations or outcomes. -/
private theorem traces_false :
    observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram false) mixedFeedbackInput
      = [⟨mixedFeedbackInput, true, 0, 0, 0, []⟩] := by
  simp [observedMixedTraces, mixedFeedbackProgram]

/-- With the identity oracle, the `true` program yields two projected traces: outcome `0`
accepts after one query, and outcome `1` rejects after two queries and one gate. Each trace
records one measurement and its outcome. -/
private theorem traces_true :
    observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram true) mixedFeedbackInput
      = [⟨conjBranch
            (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 0)) mixedFeedbackInput,
          true, 1, 0, 1, [(2, 0)]⟩,
         ⟨conjBranch
            (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 1)) mixedFeedbackInput,
          false, 2, 1, 1, [(2, 1)]⟩] := by
  simp only [observedMixedTraces, mixedFeedbackProgram, conjBranch_one, list_ofFn_two,
    List.flatten_cons, List.flatten_nil, List.append_nil, feedbackNext_zero, feedbackNext_one,
    List.map_cons, List.map_nil]
  rfl

/-- Projection of the mixed feedback input onto basis outcome `0` has mass `1 / 2`. -/
private theorem mass_branch_zero :
    (Matrix.trace (conjBranch
        (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 0)) mixedFeedbackInput)).re
      = 1 / 2 := by
  rw [mixedFeedbackInput, conjBranch_apply, projector_conjTranspose, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, projector_mul_self, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Projector]
  simp

/-- Projection of the mixed feedback input onto basis outcome `1` has mass `1 / 2`. -/
private theorem mass_branch_one :
    (Matrix.trace (conjBranch
        (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 1)) mixedFeedbackInput)).re
      = 1 / 2 := by
  rw [mixedFeedbackInput, conjBranch_apply, projector_conjTranspose, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, projector_mul_self, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Projector]
  simp

/-- The `false` program has expected query count zero for the identity oracle and mixed feedback
input. -/
private theorem eq_false : mixedExpectedQueries (1 : Operator 2) (mixedFeedbackProgram false)
    mixedFeedbackInput = 0 := by
  simp [mixedExpectedQueries, traces_false]

/-- The `true` program has expected query count `3 / 2` for the identity oracle and mixed
feedback input. -/
private theorem eq_true : mixedExpectedQueries (1 : Operator 2) (mixedFeedbackProgram true)
    mixedFeedbackInput = 3 / 2 := by
  simp only [mixedExpectedQueries, traces_true, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, mixedMass]
  rw [mass_branch_zero, mass_branch_one]
  norm_num

/-- The sum of branch masses weighted by the acceptance indicator is one for the `false` program
with the identity oracle and mixed feedback input. -/
private theorem accept_mass_false :
    ((observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram false) mixedFeedbackInput).map
        (fun t => mixedMass t * (if t.accepted then 1 else 0))).sum = 1 := by
  simp only [traces_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    mixedMass]
  rw [input_trace_re]
  norm_num

/-- The sum of branch masses weighted by the acceptance indicator is `1 / 2` for the `true`
program with the identity oracle and mixed feedback input. -/
private theorem accept_mass_true :
    ((observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram true) mixedFeedbackInput).map
        (fun t => mixedMass t * (if t.accepted then 1 else 0))).sum = 1 / 2 := by
  simp only [traces_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Bool.false_eq_true, if_false, mul_zero, mixedMass]
  rw [mass_branch_zero]
  norm_num

/-- Selecting the accepting branch masses gives total mass `1 / 2` for the `true` program with
the identity oracle and mixed feedback input. -/
private theorem accept_mass_true' :
    ((observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram true) mixedFeedbackInput).map
        (fun t => if t.accepted = true then mixedMass t else 0)).sum = 1 / 2 := by
  simpa only [mul_ite, mul_one, mul_zero] using accept_mass_true

/-- Selecting the accepting branch masses gives total mass one for the `false` program with the
identity oracle and mixed feedback input. -/
private theorem accept_mass_false' :
    ((observedMixedTraces (1 : Operator 2) (mixedFeedbackProgram false) mixedFeedbackInput).map
        (fun t => if t.accepted = true then mixedMass t else 0)).sum = 1 := by
  simpa only [mul_ite, mul_one, mul_zero] using accept_mass_false

/-- For the identity oracle and mixed feedback input, the randomized feedback instrument has
expected query count `1` and acceptance probability `2 / 3`. The weighted source expected
query count also equals `1`. -/
theorem mixed_feedback_consumer_cost_and_output
    (hP : ∀ b, observedWellFormed (mixedFeedbackProgram b)) :
    (∑ ji : Σ b, Fin (observedLeafCount (mixedFeedbackProgram b)),
      instrumentProb
        (randomizedObservedInstrument mixedChoiceWeights 1
          ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP) mixedFeedbackInput ji
        * (observedLeaf 1 (mixedFeedbackProgram ji.1) ji.2).queries) = 1 ∧
    (∑ ji : Σ b, Fin (observedLeafCount (mixedFeedbackProgram b)),
      instrumentProb
        (randomizedObservedInstrument mixedChoiceWeights 1
          ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP) mixedFeedbackInput ji
        * (if (observedLeaf 1 (mixedFeedbackProgram ji.1) ji.2).accepted then 1 else 0)) = 2 / 3 ∧
    (∑ b, mixedChoiceWeights.prob b
      * mixedExpectedQueries 1 (mixedFeedbackProgram b) mixedFeedbackInput) = 1 := by
  have hcost : (∑ b, mixedChoiceWeights.prob b
      * mixedExpectedQueries 1 (mixedFeedbackProgram b) mixedFeedbackInput) = 1 := by
    simp [mixedChoiceWeights, eq_true, eq_false]
  refine ⟨?_, ?_, hcost⟩
  · rw [randomized_observed_expected_cost mixedChoiceWeights 1
      ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP mixedFeedbackInput]
    exact hcost
  · have hsplit :
        (∑ ji : Σ b, Fin (observedLeafCount (mixedFeedbackProgram b)),
          instrumentProb
            (randomizedObservedInstrument mixedChoiceWeights 1
              ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
            mixedFeedbackInput ji
            * (if (observedLeaf 1 (mixedFeedbackProgram ji.1) ji.2).accepted then 1 else 0))
        = ∑ b : Bool,
            ∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
              instrumentProb
                (randomizedObservedInstrument mixedChoiceWeights 1
                  ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
                  mixedFeedbackInput ⟨b, i⟩
                * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0) :=
      Fintype.sum_sigma (fun ji =>
        instrumentProb
          (randomizedObservedInstrument mixedChoiceWeights 1
            ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
          mixedFeedbackInput ji
          * (if (observedLeaf 1 (mixedFeedbackProgram ji.1) ji.2).accepted then 1 else 0))
    rw [hsplit]
    have key : ∀ b : Bool,
        (∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
          instrumentProb
            (randomizedObservedInstrument mixedChoiceWeights 1
              ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
            mixedFeedbackInput ⟨b, i⟩
            * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0))
        = mixedChoiceWeights.prob b
          * ((observedMixedTraces 1 (mixedFeedbackProgram b) mixedFeedbackInput).map
              (fun t => mixedMass t * (if t.accepted then 1 else 0))).sum := by
      intro b
      have h1 :
          (∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
            instrumentProb
              (randomizedObservedInstrument mixedChoiceWeights 1
                ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
              mixedFeedbackInput ⟨b, i⟩
              * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0))
          = mixedChoiceWeights.prob b
            * ∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
                instrumentProb (observedInstrument 1
                  ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) (mixedFeedbackProgram b) (hP b))
                  mixedFeedbackInput i
                * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(randomized_observed_branch_law mixedChoiceWeights 1
          ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP mixedFeedbackInput b
          i).2]
        ring
      have h2 :
          (∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
            instrumentProb (observedInstrument 1
              ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) (mixedFeedbackProgram b) (hP b))
              mixedFeedbackInput i
            * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0))
          = ((observedMixedTraces 1 (mixedFeedbackProgram b) mixedFeedbackInput).map
              (fun t => mixedMass t * (if t.accepted then 1 else 0))).sum :=
        (observedMixedTraces_event_statistic 1
          ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) (mixedFeedbackProgram b) (hP b)
          mixedFeedbackInput (fun t => if t.accepted then 1 else 0)).1
      rw [h1, h2]
    have htotal :
        (∑ b : Bool,
            ∑ i : Fin (observedLeafCount (mixedFeedbackProgram b)),
              instrumentProb
                (randomizedObservedInstrument mixedChoiceWeights 1
                  ((Matrix.unitaryGroup (Fin 2) ℂ).one_mem) mixedFeedbackProgram hP)
                  mixedFeedbackInput ⟨b, i⟩
                * (if (observedLeaf 1 (mixedFeedbackProgram b) i).accepted then 1 else 0))
        = ∑ b : Bool,
            mixedChoiceWeights.prob b
              * ((observedMixedTraces 1 (mixedFeedbackProgram b) mixedFeedbackInput).map
                  (fun t => mixedMass t * (if t.accepted then 1 else 0))).sum :=
      Finset.sum_congr rfl fun b _ => key b
    rw [htotal]
    simp [mixedChoiceWeights, accept_mass_true', accept_mass_false']
    norm_num

/-- A continuation that accepts immediately after `true` and makes one query before accepting
after `false`. -/
private def retryK (b : Bool) : ObservedCircuit (Fin 2) :=
  if b then .halt true else .step .query (.halt true)

/-- Both rejection-retry continuations are well formed. -/
private theorem retryK_wf : ∀ b : Bool, observedWellFormed (retryK b) := by
  intro b
  cases b <;> exact trivial

/-- Appending an immediate accepting continuation after acceptance and a one-query accepting
continuation after rejection gives weighted expected query count `4 / 3` for the identity
oracle and mixed feedback input. -/
theorem mixed_feedback_continuation_consumer :
    (let k : Bool → ObservedCircuit (Fin 2) :=
        fun b => if b then .halt true else .step .query (.halt true);
      (∑ b, mixedChoiceWeights.prob b
        * mixedExpectedQueries 1 (continueObserved (mixedFeedbackProgram b) k)
          mixedFeedbackInput)) = 4 / 3 := by
  show (∑ b : Bool, mixedChoiceWeights.prob b
      * mixedExpectedQueries (1 : Operator 2)
        (continueObserved (mixedFeedbackProgram b)
          (fun b => if b then (.halt true : ObservedCircuit (Fin 2))
            else .step .query (.halt true)))
        mixedFeedbackInput) = 4 / 3
  rw [show (fun b : Bool => if b then (.halt true : ObservedCircuit (Fin 2))
      else .step .query (.halt true)) = retryK from rfl]
  have h0 : mixedExpectedQueries (1 : Operator 2)
      (continueObserved (mixedFeedbackProgram false) retryK) mixedFeedbackInput = 0 := by
    simp [mixedExpectedQueries, observedMixedTraces, mixedFeedbackProgram, continueObserved,
      retryK]
  have hstop : mixedExpectedQueries (1 : Operator 2) (retryK true)
      (conjBranch (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 0))
        mixedFeedbackInput) = 0 := by
    simp [mixedExpectedQueries, observedMixedTraces, retryK]
  have hretry : mixedExpectedQueries (1 : Operator 2) (retryK false)
      (conjBranch (Projector ((Finset.univ : Finset (Fin 2)).filter fun i => i = 1))
        mixedFeedbackInput) = 1 / 2 := by
    rw [show retryK false = (.step .query (.halt true) : ObservedCircuit (Fin 2)) from rfl,
      mixedExpectedQueries, observedMixedTraces, observedMixedTraces, conjBranch_one]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mixedMass,
      Nat.zero_add, Nat.cast_one, mul_one]
    exact mass_branch_one
  have h2 : mixedExpectedQueries (1 : Operator 2)
      (continueObserved (mixedFeedbackProgram true) retryK) mixedFeedbackInput = 2 := by
    rw [mixed_continuation_actual_cost 1 one_mem_unitary (mixedFeedbackProgram true)
      (program_wf true) retryK retryK_wf mixedFeedbackInput, eq_true, traces_true]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hstop, hretry]
    norm_num
  simp [mixedChoiceWeights, h0, h2]
  norm_num

end Qatlib.Concepts.AdversaryBounds.AdvDuality
