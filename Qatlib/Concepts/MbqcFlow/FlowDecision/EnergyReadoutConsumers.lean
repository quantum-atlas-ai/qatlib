/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.DegenerateEnergyInstrument
import Qatlib.Concepts.AdversaryBounds.AdvDuality.CountedEnergyReadout

/-!
# Degenerate energy readout on a coherent input

This module evaluates a two-outcome energy measurement on the three-dimensional pure state with
vector `(Ket 0 + Ket 1) / sqrt 2`. `degenerateLabel` places both occupied basis states in the
same energy fiber. `energy_degenerate_coherence_actual_consumer` proves that forgetting this
energy outcome preserves the input, whereas forgetting a full basis measurement changes it.
Quantum instruments and projective measurements provide the background in [Watrous2018].

The remaining statements connect this example to the actual energy-program branch pipeline and
its resource ledger. They identify outcome zero as certain and compute both individual trace
counts and probability-weighted costs.

## Main statements

* `energy_degenerate_instrument_branches`: identifies the two unnormalized instrument outputs.
* `energy_degenerate_actual_outcome_prob`: gives probability one for the actual outcome-zero
  leaf.
* `energy_degenerate_actual_traces`: gives three gates, zero queries, and one measurement for
  every observed trace.
* `energy_degenerate_actual_cost`: computes the corresponding expected costs.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped Classical BigOperators Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The pure-state density matrix of `(Ket 0 + Ket 1) / sqrt 2` in a three-dimensional register. -/
noncomputable def degenerateConsumerState : Operator 3 :=
  outerProduct (((Real.sqrt 2:ℂ)⁻¹) • (Ket (0:Fin 3)+Ket (1:Fin 3)))

/-- The two-valued energy label assigning zero to basis indices zero and one, and one to basis
index two. -/
def degenerateLabel : Fin 3 → Fin 2 := fun i => if i.val = 2 then (1:Fin 2) else 0

/-- For the identity eigenbasis, forgetting the degenerate energy outcome preserves
`degenerateConsumerState`, while forgetting a full basis measurement changes it. The energy
outcome zero has probability one. -/
theorem energy_degenerate_coherence_actual_consumer :
    ∀ (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ),
      let label : Fin 3 → Fin 2 := fun i => if i.val=2 then 1 else 0
      let V := (1:Operator 3)
      degenerateConsumerState = outerProduct (((Real.sqrt 2:ℂ)⁻¹) • (Ket (0:Fin 3)+Ket (1:Fin 3))) ∧
      (energyInstrument label V hV).forget.map degenerateConsumerState = degenerateConsumerState ∧
      (projectiveInstrument (D:=3)).forget.map degenerateConsumerState ≠ degenerateConsumerState ∧
      instrumentProb (energyInstrument label V hV) degenerateConsumerState 0 = 1 := by
  intro hV
  show degenerateConsumerState = outerProduct (((Real.sqrt 2:ℂ)⁻¹) • (Ket (0:Fin 3)+Ket (1:Fin 3))) ∧
      (energyInstrument (fun i => if i.val=2 then 1 else 0) (1:Operator 3) hV).forget.map
        degenerateConsumerState = degenerateConsumerState ∧
      (projectiveInstrument (D:=3)).forget.map degenerateConsumerState ≠ degenerateConsumerState ∧
      instrumentProb (energyInstrument (fun i => if i.val=2 then 1 else 0) (1:Operator 3) hV)
        degenerateConsumerState 0 = 1
  have hamp : ∀ i : Fin 3, (((Real.sqrt 2:ℂ)⁻¹) • (Ket (0:Fin 3)+Ket (1:Fin 3))) i
      = if i.val = 2 then 0 else (Real.sqrt 2:ℂ)⁻¹ := by
    intro i
    rcases i with ⟨i, hi⟩
    interval_cases i <;> simp [Qatlib.Foundations.PureStateMath.Ket]
  have hproj : ∀ a : Fin 2, energyProjector (fun i : Fin 3 => if i.val=2 then 1 else 0)
        (1:Operator 3) a
      = Matrix.diagonal (fun i => if (if i.val=2 then 1 else 0) = a then (1:ℂ) else 0) := by
    intro a
    show (1:Operator 3) * Matrix.diagonal
        (fun i => if (if i.val=2 then 1 else 0) = a then (1:ℂ) else 0)
        * (1:Operator 3).conjTranspose = _
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have hentry : ∀ i j : Fin 3, degenerateConsumerState i j
      = (if i.val = 2 then 0 else (Real.sqrt 2:ℂ)⁻¹)
        * (starRingEnd ℂ) (if j.val = 2 then 0 else ((Real.sqrt 2:ℂ)⁻¹)) := by
    intro i j
    rw [degenerateConsumerState, outerProduct_apply, hamp i, hamp j]

  have hmodsq : ∀ i : Fin 3, (if i.val = 2 then 0 else (Real.sqrt 2:ℂ)⁻¹)
        * (starRingEnd ℂ) (if i.val = 2 then 0 else (Real.sqrt 2:ℂ)⁻¹)
      = if i.val = 2 then 0 else (1/2 : ℂ) := by
    intro i
    have key : ((Real.sqrt 2:ℂ)⁻¹) * (starRingEnd ℂ) ((Real.sqrt 2:ℂ)⁻¹) = (1/2 : ℂ) := by
      rw [Complex.conj_inv, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      norm_num
    rcases i with ⟨i, hi⟩
    interval_cases i <;>
      simp [Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [Instrument.forget_apply]
    have hbr : ∀ a : Fin 2, (energyInstrument (fun i => if i.val=2 then 1 else 0)
          (1:Operator 3) hV).branch a degenerateConsumerState
        = energyProjector (fun i => if i.val=2 then 1 else 0) (1:Operator 3) a
          * degenerateConsumerState
          * energyProjector (fun i => if i.val=2 then 1 else 0) (1:Operator 3) a := by
      intro a
      rw [(energy_actual_instrument_projector_map 3 2
        (fun i => if i.val=2 then 1 else 0) (1:Operator 3) hV a _).1]
    rw [Finset.sum_congr rfl fun a _ => hbr a]
    rw [Finset.sum_congr rfl fun a _ => by rw [hproj a]]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.sum_apply, hentry]
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    interval_cases i <;> interval_cases j <;> simp
  · intro hcontra
    have h01 : ((projectiveInstrument (D:=3)).forget.map degenerateConsumerState) 0 1 = 0 := by
      rw [Instrument.forget_apply]
      simp only [Matrix.sum_apply, projectiveInstrument, conjBranch_projector_apply,
        Matrix.diagonal_apply]
      exact Finset.sum_eq_zero fun c _ => by
        rw [if_neg (show (0:Fin 3) ≠ 1 by decide)]
    rw [hcontra, hentry 0 1] at h01
    rw [if_neg (by decide), if_neg (by decide),
      Complex.conj_inv, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)] at h01
    norm_num at h01
  · rw [(energy_actual_instrument_projector_map 3 2 (fun i => if i.val=2 then 1 else 0)
      (1:Operator 3) hV 0 degenerateConsumerState).2]
    have htr : Matrix.trace (energyProjector (fun i : Fin 3 => if i.val = 2 then (1 : Fin 2) else 0)
        (1:Operator 3) 0 * degenerateConsumerState) = 1 := by
      rw [show energyProjector (fun i : Fin 3 => if i.val = 2 then (1 : Fin 2) else 0)
        (1:Operator 3) 0 = Matrix.diagonal
        (fun i : Fin 3 => if (if i.val = 2 then (1 : Fin 2) else 0) = 0 then (1:ℂ) else 0) from
        hproj 0]
      show ∑ i : Fin 3, (Matrix.diagonal
          (fun i : Fin 3 => if (if i.val = 2 then (1 : Fin 2) else 0) = 0 then (1:ℂ) else 0)
          * degenerateConsumerState) i i = 1
      simp only [Matrix.diagonal_mul, hentry, hmodsq]
      rw [Fin.sum_univ_three]
      norm_num
    rw [htr]
    rfl

/-- The consumer superposition has amplitude `1 / sqrt 2` at indices zero and one, and zero at
index two. -/
theorem degenerateConsumerAmplitude (i : Fin 3) :
    (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (0:Fin 3) + Ket (1:Fin 3))) i
      = if i.val = 2 then 0 else (Real.sqrt 2 : ℂ)⁻¹ := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> simp [Qatlib.Foundations.PureStateMath.Ket]

/-- Each entry of the consumer density matrix is the product of its row amplitude with the
conjugate of its column amplitude. -/
theorem degenerateConsumerState_apply (i j : Fin 3) :
    degenerateConsumerState i j
      = (if i.val = 2 then 0 else (Real.sqrt 2 : ℂ)⁻¹)
        * (starRingEnd ℂ) (if j.val = 2 then 0 else (Real.sqrt 2 : ℂ)⁻¹) := by
  rw [degenerateConsumerState, outerProduct_apply]
  simp only [degenerateConsumerAmplitude]

/-- The consumer amplitude has squared modulus one half at indices zero and one, and zero at
index two. -/
theorem degenerateConsumerModulusSq (i : Fin 3) :
    (if i.val = 2 then 0 else (Real.sqrt 2 : ℂ)⁻¹)
        * (starRingEnd ℂ) (if i.val = 2 then 0 else (Real.sqrt 2 : ℂ)⁻¹)
      = if i.val = 2 then 0 else (1 / 2 : ℂ) := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    simp [Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- In the identity eigenbasis, each consumer energy projector is the diagonal indicator matrix
of its energy-label fiber. -/
theorem degenerateConsumerProjector (a : Fin 2) :
    energyProjector (fun i : Fin 3 => if i.val = 2 then (1:Fin 2) else 0) (1:Operator 3) a
      = Matrix.diagonal
          (fun i : Fin 3 => if (if i.val = 2 then (1:Fin 2) else 0) = a then (1:ℂ) else 0) := by
  show (1:Operator 3) * Matrix.diagonal
      (fun i : Fin 3 => if (if i.val = 2 then (1:Fin 2) else 0) = a then (1:ℂ) else 0)
      * (1:Operator 3).conjTranspose = _
  rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

/-- On the consumer state, the degenerate energy instrument's outcome-zero branch equals the
input state and its outcome-one branch is zero. -/
theorem energy_degenerate_instrument_branches
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    (energyInstrument (fun i : Fin 3 => if i.val = 2 then (1:Fin 2) else 0) (1:Operator 3)
        hV).branch 0 degenerateConsumerState
      = degenerateConsumerState ∧
    (energyInstrument (fun i : Fin 3 => if i.val = 2 then (1:Fin 2) else 0) (1:Operator 3)
        hV).branch 1 degenerateConsumerState = 0 := by
  constructor
  · rw [(energy_actual_instrument_projector_map 3 2
        (fun i : Fin 3 => if i.val = 2 then (1:Fin 2) else 0) (1:Operator 3) hV 0 _).1,
      degenerateConsumerProjector 0]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, degenerateConsumerState_apply]
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    interval_cases i <;> interval_cases j <;> simp
  · rw [(energy_actual_instrument_projector_map 3 2
        (fun i : Fin 3 => if i.val = 2 then (1:Fin 2) else 0) (1:Operator 3) hV 1 _).1,
      degenerateConsumerProjector 1]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, degenerateConsumerState_apply]
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    interval_cases i <;> interval_cases j <;> simp

/-- The observed energy-program leaf probability on the transported frame embedding of the
consumer density matrix. -/
noncomputable def degenerateActualProb
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hM : 0 < 2)
    (i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3)))) : ℝ :=
  instrumentProb (observedInstrument (1 : Operator (2*3))
      (by rw [Matrix.mem_unitaryGroup_iff]; simp)
      (energyProgram degenerateLabel (1:Operator 3))
      (energyProgram_observedWellFormed 3 2 hM degenerateLabel (1:Operator 3) hV))
      (energyTransportGate (energyEmbedFrame hM degenerateConsumerState)) i

/-- The actual energy branch pipeline preserves the consumer state at outcome zero and gives
zero at outcome one. -/
theorem energy_degenerate_actual_branches
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hM : 0 < 2) :
    energyActualBranchPipeline degenerateLabel (1:Operator 3) 0 hM degenerateConsumerState
        = degenerateConsumerState ∧
    energyActualBranchPipeline degenerateLabel (1:Operator 3) 1 hM degenerateConsumerState
        = 0 := by
  rw [energy_program_branch_frame_measure_discard 3 2 hM degenerateLabel (1:Operator 3)
      hV 0 _ |>.1,
    energy_program_branch_frame_measure_discard 3 2 hM degenerateLabel (1:Operator 3)
      hV 1 _ |>.1]
  exact energy_degenerate_instrument_branches hV

/-- The actual energy-program leaf for outcome zero has probability one on the consumer input. -/
theorem energy_degenerate_actual_outcome_prob
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hM : 0 < 2) :
    degenerateActualProb hV hM
        (energyLeaf degenerateLabel (1:Operator 3) 0) = 1 := by
  show instrumentProb (observedInstrument (1 : Operator (2*3))
      (by rw [Matrix.mem_unitaryGroup_iff]; simp)
      (energyProgram degenerateLabel (1:Operator 3))
      (energyProgram_observedWellFormed 3 2 hM degenerateLabel (1:Operator 3) hV))
      (energyTransportGate (energyEmbedFrame hM degenerateConsumerState))
      (energyLeaf degenerateLabel (1:Operator 3) 0) = 1
  rw [energy_program_actual_outcome_prob 3 2 hM degenerateLabel (1:Operator 3) hV 0 _]
  exact (energy_degenerate_coherence_actual_consumer hV).2.2.2

/-- Each consumer energy leaf is accepted and records zero queries, three gates, one
measurement, and the single outcome `(2, a.val)`. -/
theorem energy_degenerate_actual_leaf_ledger
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    ∀ a : Fin 2,
      (energyActualLeaf degenerateLabel (1:Operator 3) a).accepted = true ∧
      (energyActualLeaf degenerateLabel (1:Operator 3) a).queries = 0 ∧
      (energyActualLeaf degenerateLabel (1:Operator 3) a).gates = 3 ∧
      (energyActualLeaf degenerateLabel (1:Operator 3) a).measurements = 1 ∧
      (energyActualLeaf degenerateLabel (1:Operator 3) a).outcomes = [(2, a.val)] := by
  intro a
  rw [energyActualLeaf_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The consumer superposition with a two-dimensional phase register initialized at zero,
reindexed onto a register of dimension six. -/
noncomputable def degenerateConsumerFrame (hM : 0 < 2) : QState (Fin (2*3)) :=
  (TensorState (Ket (⟨0, hM⟩ : Fin 2))
    (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (0:Fin 3) + Ket (1:Fin 3))))
    ∘ (energyRegisterEquiv 3 2).symm

/-- Every observed trace of the consumer energy program has three gates, zero queries, and one
measurement. -/
theorem energy_degenerate_actual_traces
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hM : 0 < 2)
    (t : BranchTrace (Fin (2*3)))
    (ht : t ∈ observedTraces (1:Operator (2*3))
        (energyProgram degenerateLabel (1:Operator 3)) (degenerateConsumerFrame hM)) :
    t.gates = 3 ∧ t.queries = 0 ∧ t.measurements = 1 :=
  (energy_program_legality_and_exact_macro_cost 3 2 hM degenerateLabel (1:Operator 3)
    hV).2.1 _ _ ht

/-- The frame embedding of the consumer density matrix has trace one. -/
theorem trace_energyEmbedFrame_degenerate (hM : 0 < 2) :
    Matrix.trace (energyEmbedFrame hM degenerateConsumerState) = 1 := by
  rw [energyEmbedFrame_eq, Matrix.trace_kronecker]
  have hframe : Matrix.trace (energyPhaseFrame hM) = 1 := by
    simp only [energyPhaseFrame, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply]
    rw [Fin.sum_univ_two]
    simp
  have hnorm : Normalized (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (0:Fin 3) + Ket (1:Fin 3))) := by
    simp only [Normalized]
    rw [Fin.sum_univ_three]
    simp only [degenerateConsumerAmplitude]
    norm_num
  have hrho : Matrix.trace degenerateConsumerState = 1 :=
    (isDensityOperator_outerProduct hnorm).2
  rw [hframe, hrho, mul_one]

/-- The consumer energy program's probability-weighted leaf costs are three gates, zero queries,
and one measurement. -/
theorem energy_degenerate_actual_cost
    (hV : (1:Operator 3) ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hM : 0 < 2) :
    (∑ i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3))),
        degenerateActualProb hV hM i
          * (observedLeaf (1 : Operator (2*3))
              (energyProgram degenerateLabel (1:Operator 3)) i).gates) = 3 ∧
    (∑ i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3))),
        degenerateActualProb hV hM i
          * (observedLeaf (1 : Operator (2*3))
              (energyProgram degenerateLabel (1:Operator 3)) i).queries) = 0 ∧
    (∑ i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3))),
        degenerateActualProb hV hM i
          * (observedLeaf (1 : Operator (2*3))
              (energyProgram degenerateLabel (1:Operator 3)) i).measurements) = 1 := by
  have hcount := observedLeafCount_energyProgram degenerateLabel (1:Operator 3)
  have hebij : Function.Bijective (Fin.cast hcount.symm) := by
    constructor
    · intro a b hab
      exact Fin.ext (by simpa [Fin.val_cast] using congrArg Fin.val hab)
    · intro b
      exact ⟨Fin.cast hcount b, Fin.ext (by simp)⟩
  have hprobsum : ∑ i : Fin (observedLeafCount
        (energyProgram degenerateLabel (1:Operator 3))), degenerateActualProb hV hM i = 1 := by
    show ∑ i : Fin (observedLeafCount
        (energyProgram degenerateLabel (1:Operator 3))),
      instrumentProb (observedInstrument (1 : Operator (2*3))
          (by rw [Matrix.mem_unitaryGroup_iff]; simp)
          (energyProgram degenerateLabel (1:Operator 3))
          (energyProgram_observedWellFormed 3 2 hM degenerateLabel (1:Operator 3) hV))
          (energyTransportGate (energyEmbedFrame hM degenerateConsumerState)) i = 1
    rw [sum_instrumentProb, energyTransportGate_trace,
      trace_energyEmbedFrame_degenerate hM]
    rfl
  have hprobsumleaf : ∑ a : Fin 2, degenerateActualProb hV hM
      (energyLeaf degenerateLabel (1:Operator 3) a) = 1 := by
    have hre : (∑ a : Fin 2, degenerateActualProb hV hM
          (energyLeaf degenerateLabel (1:Operator 3) a))
        = ∑ i : Fin (observedLeafCount
            (energyProgram degenerateLabel (1:Operator 3))), degenerateActualProb hV hM i := by
      simp only [energyLeaf]
      rw [← Function.Bijective.sum_comp hebij
        (fun i : Fin (observedLeafCount
            (energyProgram degenerateLabel (1:Operator 3))) => degenerateActualProb hV hM i)]
    rw [hre]
    exact hprobsum
  have hreindex : ∀ f : ObservedKrausLeaf (2*3) → ℕ,
      (∑ a : Fin 2, degenerateActualProb hV hM
            (energyLeaf degenerateLabel (1:Operator 3) a)
          * f (energyActualLeaf degenerateLabel (1:Operator 3) a))
        = ∑ i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3))),
          degenerateActualProb hV hM i
            * f (observedLeaf (1 : Operator (2*3))
              (energyProgram degenerateLabel (1:Operator 3)) i) := by
    intro f
    simp only [energyLeaf]
    rw [← Function.Bijective.sum_comp hebij
      (fun i : Fin (observedLeafCount (energyProgram degenerateLabel (1:Operator 3))) =>
        degenerateActualProb hV hM i
          * f (observedLeaf (1 : Operator (2*3))
            (energyProgram degenerateLabel (1:Operator 3)) i))]
    simp only [observedLeaf_cast]
  have hfieldgates : ∀ a : Fin 2,
      (energyActualLeaf degenerateLabel (1:Operator 3) a).gates = 3 := fun a => by
    rw [energyActualLeaf_eq]
  have hfieldqueries : ∀ a : Fin 2,
      (energyActualLeaf degenerateLabel (1:Operator 3) a).queries = 0 := fun a => by
    rw [energyActualLeaf_eq]
  have hfieldmeas : ∀ a : Fin 2,
      (energyActualLeaf degenerateLabel (1:Operator 3) a).measurements = 1 := fun a => by
    rw [energyActualLeaf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hreindex (fun leaf => leaf.gates)]
    rw [Finset.sum_congr rfl (fun a _ => by rw [hfieldgates a]), ← Finset.sum_mul,
      hprobsumleaf, one_mul, Nat.cast_ofNat]
  · rw [← hreindex (fun leaf => leaf.queries)]
    simp [hfieldqueries]
  · rw [← hreindex (fun leaf => leaf.measurements)]
    rw [Finset.sum_congr rfl (fun a _ => by rw [hfieldmeas a]), ← Finset.sum_mul,
      hprobsumleaf, one_mul, Nat.cast_one]

end Qatlib.Concepts.MbqcFlow.FlowDecision
