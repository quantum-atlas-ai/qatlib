/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.ThresholdFlag
public import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesis
public import Qatlib.Foundations.BornMetrics.EventProbability
public import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws

@[expose] public section

/-!
# The counting register after coherent threshold selection

In [KerenidisPrakash2017], Algorithm 5.2, the threshold flag is written
before inverse phase estimation. Restricted to a target eigenstate, the
executed phase word acts as a unitary on the counting register. The
successful component applies the adjoint of that unitary to the accepted
part of its counting state. Its clean amplitude is the acceptance
probability `p`, and its nonzero counting labels have total mass `p * (1 - p)`.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_union)
open Qatlib.Concepts.MatrixAccess.RitzPipeline (localProgramMatrix_mem_unitary)
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum (localProgramAdjoint localProgramMatrix)
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Restrict the actual phase word to a target eigenphase. Each controlled power then
contributes a scalar on its controlling counting basis state. -/
def phaseCountingGate (bits : ℕ) (phase : ℝ) : Matrix (Reg bits) (Reg bits) ℂ :=
  localProgramMatrix (localProgramAdjoint (localQFT bits)) *
    diagonal (fun z => Complex.exp (2 * Real.pi * Complex.I * (phase : ℂ)) ^ (bitVecEquiv bits z).val) *
    localProgramMatrix (localHadamard bits)

/-- The eigenphase restriction of the counting word is unitary. -/
theorem phase_counting_gate_unitary (bits : ℕ) (phase : ℝ) :
    phaseCountingGate bits phase ∈ Matrix.unitaryGroup (Reg bits) ℂ := by
  have hExponent : (2 * Real.pi * Complex.I * (phase : ℂ)) =
      ((2 * Real.pi * phase : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hPhase : ‖Complex.exp (2 * Real.pi * Complex.I * (phase : ℂ))‖ = 1 := by
    rw [hExponent, Complex.norm_exp_ofReal_mul_I]
  have hDiag := diagonal_mem_unitaryGroup
    (fun z : Reg bits => Complex.exp (2 * Real.pi * Complex.I * (phase : ℂ)) ^ (bitVecEquiv bits z).val)
    (fun z => by rw [norm_pow, hPhase, one_pow])
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem (localProgramMatrix_mem_unitary _) hDiag)
    (localProgramMatrix_mem_unitary _)

/-- With an eigenstate in the target, the phase word acts on an arbitrary counting state
by its restricted gate and leaves the target vector fixed. -/
theorem phase_counting_gate_apply (bits : ℕ) (U : Matrix I I ℂ) (phase : ℝ)
    (v : QState I) (hEigen : U *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * phase) • v)
    (a : QState (Reg bits)) :
    ApplyGate (poweredProgramMatrix U (PoweredProgram.word bits)) (TensorState a v) =
      TensorState (ApplyGate (phaseCountingGate bits phase) a) v := by
  rw [apply_powered_program_matrix, PoweredProgram.word, PoweredProgram.execute_append,
    PoweredProgram.execute_append, PoweredProgram.execute_local, PoweredProgram.execute_powers U _ v hEigen]
  simp_rw [PoweredProgram.selectedWeight_all]
  rw [PoweredProgram.execute_local, phaseCountingGate, applyGate_mul, applyGate_mul]
  let diagonalPhase (z : Reg bits) := Complex.exp (2 * Real.pi * Complex.I * (phase : ℂ)) ^ (bitVecEquiv bits z).val
  let prepared := localProgramMatrix (localHadamard bits) *ᵥ a
  have hDiagonal : diagonal diagonalPhase *ᵥ prepared = fun z => diagonalPhase z * prepared z :=
    funext (Matrix.mulVec_diagonal diagonalPhase prepared)
  exact congrArg (fun b => TensorState (localProgramMatrix (localProgramAdjoint (localQFT bits)) *ᵥ b) v) hDiagonal.symm

/-- A unitary applied after its adjoint cancels on every state. -/
private theorem apply_adjoint_cancel {X : Type} [Fintype X] [DecidableEq X]
    {W : Matrix X X ℂ} (hW : W ∈ Matrix.unitaryGroup X ℂ) (ψ : QState X) :
    ApplyGate W (ApplyGate Wᴴ ψ) = ψ := by
  have hInv : W * Wᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hW
  rw [← applyGate_mul, hInv, applyGate_one]

/-- The reversed phase word acts by the adjoint restriction on the same eigenspace,
including on a counting state already filtered by the threshold. -/
theorem phase_counting_gate_adjoint_apply (bits : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (phase : ℝ) (v : QState I)
    (hEigen : U *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * phase) • v)
    (a : QState (Reg bits)) :
    ApplyGate (poweredProgramMatrix U (PoweredProgram.word bits))ᴴ (TensorState a v) =
      TensorState (ApplyGate (phaseCountingGate bits phase)ᴴ a) v := by
  let W := poweredProgramMatrix U (PoweredProgram.word bits)
  have hW := powered_program_matrix_unitary hU (PoweredProgram.word bits)
  have hInv : Wᴴ * W = 1 := by
    simpa only [W, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hW
  have hForward : ApplyGate W (TensorState (ApplyGate (phaseCountingGate bits phase)ᴴ a) v) =
      TensorState a v := by
    rw [phase_counting_gate_apply bits U phase v hEigen,
      apply_adjoint_cancel (phase_counting_gate_unitary bits phase)]
  rw [← hForward, ← applyGate_mul, hInv, applyGate_one]

/-- The unnormalized counting state left on a successful eigenphase branch after uncomputation. -/
def acceptedCountingState (bits : ℕ) (phase : ℝ) (accepted : Finset (Reg bits)) : QState (Reg bits) :=
  let V := phaseCountingGate bits phase
  ApplyGate Vᴴ (Collapse (ApplyGate V (Ket (ZeroStr bits))) accepted)

/-- A successful eigenphase branch retains the target eigenstate and leaves the corresponding
unnormalized accepted counting state. -/
theorem execute_threshold_flag_eigenbranch (bits : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (phase : ℝ) (v : QState I)
    (hEigen : U *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * phase) • v)
    (accepted : Finset (Reg bits)) :
    (fun p => executeThresholdFlag bits U accepted v (true, p)) =
      TensorState (acceptedCountingState bits phase accepted) v := by
  rw [execute_threshold_flag_success, ← apply_powered_program_matrix,
    phase_counting_gate_apply bits U phase v hEigen]
  have hMask (a : QState (Reg bits)) : (fun p : Reg bits × I =>
      if p.1 ∈ accepted then TensorState a v p else 0) = TensorState (Collapse a accepted) v := by
    funext p
    by_cases h : p.1 ∈ accepted <;> simp [TensorState, collapse_apply, h]
  rw [hMask, phase_counting_gate_adjoint_apply bits U hU phase v hEigen, acceptedCountingState]

/-- The full successful output is a coherent sum over the input's eigenbranches, with the
counting state of each branch kept explicitly. -/
theorem execute_threshold_flag_spectral_success {J : Type} [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (accepted : Finset (Reg bits)) :
    (fun p => executeThresholdFlag bits U accepted (∑ j, c j • v j) (true, p)) =
      ∑ j, c j • TensorState (acceptedCountingState bits (phase j) accepted) (v j) := by
  have hInput : TensorState (Ket false) (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j)) =
      ∑ j, c j • TensorState (Ket false) (TensorState (Ket (ZeroStr bits)) (v j)) := by
    funext p
    simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hRun : executeThresholdFlag bits U accepted (∑ j, c j • v j) =
      ∑ j, c j • executeThresholdFlag bits U accepted (v j) := by
    simp_rw [← threshold_flag_gate_apply]
    rw [hInput]
    simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  rw [hRun]
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => c j * z)
    (congrFun (execute_threshold_flag_eigenbranch bits U hU (phase j) (v j) (hEigen j) accepted) p)

/-- The total successful mass is `p`, the clean counting amplitude is `p`, and the mass
on the other counting labels is `p * (1 - p)`. Here `p` is the acceptance probability before
uncomputation on the given eigenphase. -/
theorem accepted_counting_state_statistics (bits : ℕ) (phase : ℝ) (accepted : Finset (Reg bits)) :
    let V := phaseCountingGate bits phase
    let p := MeasureProb (ApplyGate V (Ket (ZeroStr bits))) accepted
    let out := acceptedCountingState bits phase accepted
    MeasureProb out Finset.univ = p ∧ out (ZeroStr bits) = (p : ℂ) ∧
      MeasureProb out (Finset.univ.erase (ZeroStr bits)) = p * (1 - p) := by
  intro V p out
  let K := ApplyGate V (Ket (ZeroStr bits))
  let selected := Collapse K accepted
  have hV := phase_counting_gate_unitary bits phase
  have hAdj : Vᴴ ∈ Matrix.unitaryGroup (Reg bits) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hV
  have hMass : MeasureProb out Finset.univ = p := by
    change (∑ i, ‖ApplyGate Vᴴ selected i‖ ^ 2) = _
    calc
      _ = ∑ i, ‖selected i‖ ^ 2 := by
        simpa only [ApplyGate, Complex.normSq_eq_norm_sq] using sum_normSq_mulVec_of_mem_unitaryGroup hAdj selected
      _ = p := sum_normSq_collapse K accepted
  have hInner : Inner K selected = (p : ℂ) := by
    have hProj : Inner K selected = Inner selected selected := by
      simp only [inner_apply, selected]
      exact Finset.sum_congr rfl fun i _ => by
        by_cases h : i ∈ accepted <;> simp [collapse_apply, h]
    rw [hProj, inner_self, ← Complex.ofReal_sum, sum_normSq_collapse]
  have hApply : ApplyGate V out = selected := apply_adjoint_cancel hV selected
  have hKet : Inner (Ket (ZeroStr bits)) out = out (ZeroStr bits) := by
    rw [inner_apply, Finset.sum_eq_single (ZeroStr bits)]
    · simp [Ket]
    · intro i _ hi
      simp [Ket, hi]
    · simp
  have hClean : out (ZeroStr bits) = (p : ℂ) := by
    have hi := inner_applyGate hV (Ket (ZeroStr bits)) out
    rw [hApply, show ApplyGate V (Ket (ZeroStr bits)) = K from rfl, hInner, hKet] at hi
    exact hi.symm
  have hSingle : MeasureProb out {ZeroStr bits} = p ^ 2 := by
    simp only [MeasureProb, Finset.sum_singleton, BornProb, hClean, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDisjoint : Disjoint (Finset.univ.erase (ZeroStr bits)) {ZeroStr bits} := by simp
  have hUnion : Finset.univ.erase (ZeroStr bits) ∪ {ZeroStr bits} = (Finset.univ : Finset (Reg bits)) := by
    ext z
    by_cases h : z = ZeroStr bits <;> simp [h]
  have hAdd := measureProb_union out hDisjoint
  rw [hUnion, hMass, hSingle] at hAdd
  exact ⟨hMass, hClean, by nlinarith only [hAdd]⟩

end Qatlib.Papers.QRecommender16.Recommendations
