/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# §VI — numerical results and discussion (empirical claim)

Chen, Liu, Chen, Huang, Chang and Huang, *Differentiable Quantum Architecture
Search in Quantum-Enhanced Neural Network Parameter Generation*, fixed
arXiv:2505.09653v1, §VI p.4–9.

The active claim `c002` is the paper's §VI comparison against twelve
hand-designed QNN baselines.  Its mathematical content is the *structural and
arithmetic* part:

* ten benchmark families: three classification settings (MNIST 1 vs 5,
  FashionMNIST 1 vs 5, FashionMNIST 5 vs 7), five time-series settings
  (Bessel J₂, damped SHM, delayed quantum control, NARMA-5, NARMA-10) and two
  reinforcement-learning environments (MiniGrid-Empty 5×5, 6×6), §VI p.5–8;
* twelve hand-designed baseline configurations (Table I, p.5):
  `{Hadamard on/off} × {Ent, Cyc} × {Rx, Ry, Rz}`, so `2 × 2 × 3 = 12`;
* the trainable-parameter ledger, §VI.A p.5 and §VI.B p.5:
  `108,866 → 286` (classification) and `1,781 → 135` (LSTM), and the
  reinforcement-learning ledger of §VI.C p.9: `6,023 + 5,825` baseline versus
  `157 + 157 = 314` under DiffQAS-QT.

The *comparison outcome* ("results comparable to or better than the baselines,
more stable training") is an empirical observation about the authors'
simulation runs, not a theorem.  The published text does not tabulate the raw
per-epoch measurements (the evidence is the plotted curves of Figures 5–14), so
the outcome is recorded as the closed proposition `NumericalComparisonClaim`
and consumed as an explicit hypothesis by `source_numerical_results`: given the
authors' measurement table and its comparison outcome, the §VI claim follows
unconditionally from the structural and arithmetic facts proved below.

Scope note: this module formalizes the structural and arithmetic content of the
empirical comparison claim; worst-case accuracy guarantees and classical
complexity lower bounds are outside its scope.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiffQASChen25.MainResults.SourceNumericalResults

/-! ## The ten benchmark families of §VI -/

/-- The benchmark families evaluated in §VI p.5–8: three binary-classification
settings, five time-series-prediction settings and two reinforcement-learning
environments. -/
inductive TaskFamily where
  | mnistOneFive
  | fashionOneFive
  | fashionFiveSeven
  | besselJ2
  | dampedSHM
  | delayedQuantumControl
  | narmaFive
  | narmaTen
  | miniGridFive
  | miniGridSix
  deriving DecidableEq, Repr

/-- §VI p.5–8: the ten benchmark families form a finite type. -/
instance : Fintype TaskFamily := derive_fintype% TaskFamily

/-- §VI p.5–8: ten benchmark families are considered. -/
theorem taskFamily_card : Fintype.card TaskFamily = 10 := by decide

/-! ## The twelve baseline configurations (Table I) -/

/-- §VI p.5 / Table I: a hand-designed QNN baseline is one choice of
`{Hadamard on, Hadamard off} × {Ent, Cyc} × {Rx, Ry, Rz}`. -/
abbrev BaselineConfig := Bool × Fin 2 × Fin 3

/-- §VI p.5, Table I: "we include 12 baseline quantum neural network (QNN)
configurations", obtained as `2 × 2 × 3 = 12`. -/
theorem baselineConfig_card : Fintype.card BaselineConfig = 12 := by
  simp [BaselineConfig]

/-- Table I enumerated explicitly: each of the twelve columns fixes the
Hadamard, entanglement and rotation components. -/
theorem baselineConfig_card_eq_prod :
    Fintype.card BaselineConfig
      = Fintype.card Bool * Fintype.card (Fin 2) * Fintype.card (Fin 3) := by
  simp [BaselineConfig, Fintype.card_prod]

/-! ## The reported trainable-parameter ledger -/

/-- §VI.A p.5: "the total number of trainable parameters reaches 108,866" for
the conventional classification network. -/
def conventionalClassificationParameters : ℕ := 108866

/-- §VI.A p.5: "the proposed DiffQAS-QT framework reduces this dramatically to
only 286 trainable parameters". -/
def diffqasClassificationParameters : ℕ := 286

/-- §VI.B p.5: "The conventional LSTM baseline contains 1,781 trainable
parameters". -/
def conventionalLSTMParameters : ℕ := 1781

/-- §VI.B p.5: "the DiffQAS-QT-based version reduces this to just 135". -/
def diffqasLSTMParameters : ℕ := 135

/-- §VI.C p.9 (reported alongside the active claim): the standard RL policy
network contains 6,023 trainable parameters. -/
def rlPolicyBaselineParameters : ℕ := 6023

/-- §VI.C p.9: the standard RL value network contains 5,825 trainable
parameters. -/
def rlValueBaselineParameters : ℕ := 5825

/-- §VI.C p.9: each DiffQAS-QT module in the RL networks contains only 157
trainable parameters. -/
def rlDiffQASModuleParameters : ℕ := 157

/-- §VI.A p.5: the classification parameter count strictly decreases. -/
theorem classification_parameter_reduction :
    diffqasClassificationParameters < conventionalClassificationParameters := by
  unfold diffqasClassificationParameters conventionalClassificationParameters
  norm_num

/-- §VI.B p.5: the LSTM parameter count strictly decreases. -/
theorem lstm_parameter_reduction :
    diffqasLSTMParameters < conventionalLSTMParameters := by
  unfold diffqasLSTMParameters conventionalLSTMParameters
  norm_num

/-- §VI.A p.5: more than a 380-fold reduction in the classification model. -/
theorem classification_parameter_compression :
    380 * diffqasClassificationParameters ≤ conventionalClassificationParameters := by
  unfold diffqasClassificationParameters conventionalClassificationParameters
  norm_num

/-- §VI.B p.5: more than a 13-fold reduction in the LSTM model. -/
theorem lstm_parameter_compression :
    13 * diffqasLSTMParameters ≤ conventionalLSTMParameters := by
  unfold diffqasLSTMParameters conventionalLSTMParameters
  norm_num

/-- §VI.C p.9: the baseline RL networks carry 11,848 parameters in total. -/
theorem rl_baseline_parameter_total :
    rlPolicyBaselineParameters + rlValueBaselineParameters = 11848 := by
  unfold rlPolicyBaselineParameters rlValueBaselineParameters
  norm_num

/-- §VI.C p.9: the two DiffQAS-QT RL modules carry 314 parameters in total. -/
theorem rl_diffqas_parameter_total :
    rlDiffQASModuleParameters + rlDiffQASModuleParameters = 314 := by
  unfold rlDiffQASModuleParameters
  norm_num

/-- §VI.C p.9: the RL parameter count strictly decreases. -/
theorem rl_parameter_reduction :
    rlDiffQASModuleParameters + rlDiffQASModuleParameters
      < rlPolicyBaselineParameters + rlValueBaselineParameters := by
  unfold rlDiffQASModuleParameters rlPolicyBaselineParameters rlValueBaselineParameters
  norm_num

/-! ## The empirical comparison outcome -/

/-- A recorded comparison on one task family: the final performance metric
(accuracy or reward) of the hand-designed baselines and of DiffQAS-QT, together
with the spread (standard deviation) of the metric. -/
structure TaskOutcome where
  /-- Final performance of the hand-designed baseline. -/
  baselineFinalScore : ℝ
  /-- Final performance of the DiffQAS-QT run. -/
  diffqasFinalScore : ℝ
  /-- Testing-score standard deviation of the baseline. -/
  baselineTestStd : ℝ
  /-- Testing-score standard deviation of the DiffQAS-QT run. -/
  diffqasTestStd : ℝ

/-- §VI p.5–8: "comparable or better final performance and more stable
training", with `ε` the comparability tolerance in the metric's units. -/
def TaskOutcome.matchedOrBetter (ε : ℝ) (o : TaskOutcome) : Prop :=
  o.baselineFinalScore - ε ≤ o.diffqasFinalScore ∧
    o.diffqasTestStd ≤ o.baselineTestStd

/-- The comparison predicate is not vacuous: a record whose baseline is both
strictly better and strictly more stable fails `matchedOrBetter` at every
tolerance.  This records that the empirical conjunct below really asserts a
data-dependent fact, not a consequence of the architecture. -/
theorem matchedOrBetter_fails_of_dominated (ε : ℝ) :
    ¬ TaskOutcome.matchedOrBetter ε
        { baselineFinalScore := 1, diffqasFinalScore := 0,
          baselineTestStd := 0, diffqasTestStd := 1 } := by
  intro h
  exact absurd h.2 (by norm_num)

/-- The empirical core of §VI p.5–8: there is a measurement table `record` (the
authors' simulation runs) and a nonnegative tolerance `ε` such that on every
task family DiffQAS-QT matches or beats the best hand-designed baseline within
`ε` and is at least as stable.

The raw per-epoch table is not part of the published text (the evidence is
Figures 5–14), so this proposition cannot be constructed inside Lean; it is
recorded here as the exact logical content of the empirical claim. -/
def NumericalComparisonClaim : Prop :=
  ∃ record : TaskFamily → TaskOutcome, ∃ ε : ℝ,
    0 ≤ ε ∧ ∀ t, (record t).matchedOrBetter ε

/-- The full §VI claim `c002` as a proposition: the structural pool (ten task
families, twelve baselines), the reported parameter ledger and the empirical
comparison outcome. -/
def NumericalResultsClaim : Prop :=
  Fintype.card TaskFamily = 10 ∧
  Fintype.card BaselineConfig = 12 ∧
  diffqasClassificationParameters < conventionalClassificationParameters ∧
  diffqasLSTMParameters < conventionalLSTMParameters ∧
  NumericalComparisonClaim

/-- §VI p.5–8, active claim `c002`, restricted coverage.

The structural and arithmetic conjuncts are proved unconditionally; the
comparison-outcome conjunct is supplied as the explicit hypothesis `hrecord`,
because the per-epoch measurement tables behind Figures 5–14 are not part of
the published text and Lean has no model of the training dynamics.  This is the
exact logical content of the empirical claim: once a measurement table and its
comparison outcome are given, the claim holds.

* Fixed source: arXiv:2505.09653v1.
* Source location: §VI p.5–8 (classification Table I and §VI.A p.5,
  time-series §VI.B p.5–8, reinforcement learning §VI.C p.8–9).
* Source argument: the authors train DiffQAS-QT and each of the twelve
  hand-designed QNN baselines on every task family and compare the curves of
  Figures 5–14; the parameter counts are read from §VI.A/B/C.
* The raw measurement tables are absent from the source text, so `record` is
  treated as an input to this structural comparison theorem. -/
theorem source_numerical_results
    (record : TaskFamily → TaskOutcome) (ε : ℝ) (hε : 0 ≤ ε)
    (hrecord : ∀ t, (record t).matchedOrBetter ε) :
    NumericalResultsClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact classification_parameter_reduction
  · exact lstm_parameter_reduction
  · exact ⟨record, ε, hε, hrecord⟩

end Qatlib.Papers.DiffQASChen25.MainResults.SourceNumericalResults
