/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.SpectralCombination
public import Qatlib.Foundations.InstrumentCore.Measurement.Basic

@[expose] public section

/-!
# Coherent threshold flag and uncomputation

[KerenidisPrakash2017], Algorithm 5.2, records a decision on the phase label
in a flag and reverses phase estimation before measuring that flag. The flag
operation here is a reversible basis permutation, followed by the adjoint
of the executed phase word. For an orthonormal eigenfamily, the squared
amplitude error of the unnormalized success branch is bounded by the
per-branch classification error. This treatment uses a supplied set of
accepted labels and does not count the gates for computing that predicate.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (relabelState)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse collapse_apply sum_normSq_collapse)
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern (conditionalGate conditionalGate_unitary)
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout (qpeKernel)
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I] {bits : ℕ}

/-- The ordered product of the gates applied by a powered program. -/
def poweredProgramMatrix (U : Matrix I I ℂ) :
    List (PoweredProgram.Instruction bits) → Matrix (Reg bits × I) (Reg bits × I) ℂ
  | [] => 1
  | gate :: rest => poweredProgramMatrix U rest * PoweredProgram.instructionMatrix U gate

/-- The program matrix acts by executing the supplied instruction list. -/
theorem apply_powered_program_matrix (U : Matrix I I ℂ) (word : List (PoweredProgram.Instruction bits))
    (ψ : QState (Reg bits × I)) :
    ApplyGate (poweredProgramMatrix U word) ψ = PoweredProgram.execute U word ψ := by
  induction word generalizing ψ with
  | nil => exact applyGate_one ψ
  | cons gate rest ih =>
    simp only [poweredProgramMatrix, PoweredProgram.execute, applyGate_mul, ih]

/-- The product of the instruction matrices is unitary for a unitary powered device. -/
theorem powered_program_matrix_unitary {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (word : List (PoweredProgram.Instruction bits)) :
    poweredProgramMatrix U word ∈ Matrix.unitaryGroup (Reg bits × I) ℂ := by
  induction word with
  | nil => exact (Matrix.unitaryGroup (Reg bits × I) ℂ).one_mem
  | cons gate rest ih =>
    exact (Matrix.unitaryGroup (Reg bits × I) ℂ).mul_mem ih (PoweredProgram.instruction_unitary hU gate)

/-- The conjugate transpose of a unitary powered program is unitary. -/
private theorem powered_program_matrix_adjoint_unitary {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (word : List (PoweredProgram.Instruction bits)) :
    (poweredProgramMatrix U word)ᴴ ∈ Matrix.unitaryGroup (Reg bits × I) ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem (powered_program_matrix_unitary hU word)

/-- Toggle the flag precisely on the accepted counting labels. -/
def toggleThresholdFlag (accepted : Finset (Reg bits)) (p : Bool × (Reg bits × I)) :
    Bool × (Reg bits × I) :=
  (if p.2.1 ∈ accepted then !p.1 else p.1, p.2)

omit [Fintype I] [DecidableEq I] in
/-- The basis flag operation is its own inverse. -/
theorem toggle_threshold_flag_involutive (accepted : Finset (Reg bits)) :
    Function.Involutive (toggleThresholdFlag (I := I) accepted) := by
  rintro ⟨flag, z, i⟩
  by_cases hz : z ∈ accepted <;> simp [toggleThresholdFlag, hz]

/-- Uncompute the phase word after writing its counting-register decision to a clean flag. -/
def executeThresholdFlag (bits : ℕ) (U : Matrix I I ℂ) (accepted : Finset (Reg bits)) (ψ : QState I) :
    QState (Bool × (Reg bits × I)) :=
  let W := poweredProgramMatrix U (PoweredProgram.word bits)
  ApplyGate (conditionalGate fun _ : Bool => Wᴴ)
    (ApplyGate (permMatrix (toggleThresholdFlag accepted))
      (TensorState (Ket false) (PoweredProgram.execute U (PoweredProgram.word bits)
        (TensorState (Ket (ZeroStr bits)) ψ))))

/-- The reversible matrix for estimating the phase, writing the decision, and undoing
the phase estimate on the entire flag and counting workspace. -/
def thresholdFlagGate (bits : ℕ) (U : Matrix I I ℂ) (accepted : Finset (Reg bits)) :
    Matrix (Bool × (Reg bits × I)) (Bool × (Reg bits × I)) ℂ :=
  let W := poweredProgramMatrix U (PoweredProgram.word bits)
  conditionalGate (fun _ : Bool => Wᴴ) * permMatrix (toggleThresholdFlag accepted) * TensorGate 1 W

/-- Each of the estimator, reversible decision and adjoint estimator is unitary. -/
theorem threshold_flag_gate_unitary (bits : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (accepted : Finset (Reg bits)) :
    thresholdFlagGate bits U accepted ∈ Matrix.unitaryGroup _ ℂ := by
  unfold thresholdFlagGate
  apply (Matrix.unitaryGroup _ ℂ).mul_mem
  · exact (Matrix.unitaryGroup _ ℂ).mul_mem
      (conditionalGate_unitary _ fun _ => powered_program_matrix_adjoint_unitary hU _)
      (permMatrix_unitary (toggle_threshold_flag_involutive accepted))
  · exact tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem (powered_program_matrix_unitary hU _)

/-- On clean flag and counting registers the reversible matrix realizes the threshold sampler. -/
theorem threshold_flag_gate_apply (bits : ℕ) (U : Matrix I I ℂ)
    (accepted : Finset (Reg bits)) (ψ : QState I) :
    ApplyGate (thresholdFlagGate bits U accepted) (TensorState (Ket false) (TensorState (Ket (ZeroStr bits)) ψ)) =
      executeThresholdFlag bits U accepted ψ := by
  rw [thresholdFlagGate, applyGate_mul, applyGate_mul, applyGate_tensorGate, applyGate_one,
    apply_powered_program_matrix, executeThresholdFlag]

/-- The complete flag circuit is normalized for a normalized input and unitary device. -/
theorem execute_threshold_flag_normalized (bits : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (accepted : Finset (Reg bits)) (ψ : QState I)
    (hψ : Normalized ψ) : Normalized (executeThresholdFlag bits U accepted ψ) := by
  exact normalized_applyGate (conditionalGate_unitary _
    (fun _ => powered_program_matrix_adjoint_unitary hU (PoweredProgram.word bits)))
    (normalized_applyGate (permMatrix_unitary (toggle_threshold_flag_involutive accepted))
      (normalized_tensorState (normalized_ket false) (PoweredProgram.execute_normalized hU _
        (normalized_tensorState (normalized_ket (ZeroStr bits)) hψ))))

/-- The success slice is the adjoint word applied to the projection onto accepted labels. -/
theorem execute_threshold_flag_success (bits : ℕ) (U : Matrix I I ℂ)
    (accepted : Finset (Reg bits)) (ψ : QState I) :
    (fun p => executeThresholdFlag bits U accepted ψ (true, p)) =
      ApplyGate (poweredProgramMatrix U (PoweredProgram.word bits))ᴴ
        (fun p => if p.1 ∈ accepted then PoweredProgram.execute U (PoweredProgram.word bits)
          (TensorState (Ket (ZeroStr bits)) ψ) p else 0) := by
  let W := poweredProgramMatrix U (PoweredProgram.word bits)
  let out := PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ)
  let marked := ApplyGate (permMatrix (toggleThresholdFlag accepted)) (TensorState (Ket false) out)
  have hMarked (p : Reg bits × I) : marked (true, p) = if p.1 ∈ accepted then out p else 0 := by
    unfold marked
    rw [applyGate_permMatrix (toggle_threshold_flag_involutive accepted)]
    by_cases hp : p.1 ∈ accepted <;> simp [TensorState, toggleThresholdFlag, hp, Ket]
  funext p
  change (∑ k : Bool × (Reg bits × I),
    (if true = k.1 then Wᴴ p k.2 else 0) * marked k) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [ApplyGate, Matrix.mulVec, dotProduct, W, hMarked, out]

/-- Measuring the success flag after inverse phase estimation has exactly the
probability of the accepted counting-register event before the inverse. -/
theorem execute_threshold_flag_probability (bits : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (accepted : Finset (Reg bits)) (ψ : QState I) :
    MeasureProb (executeThresholdFlag bits U accepted ψ)
      ({true} ×ˢ (Finset.univ : Finset (Reg bits × I))) =
    MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ))
      (accepted ×ˢ (Finset.univ : Finset I)) := by
  let out := PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ)
  let event := accepted ×ˢ (Finset.univ : Finset I)
  have hMask : (fun p : Reg bits × I => if p.1 ∈ accepted then out p else 0) = Collapse out event := by
    funext p
    rw [collapse_apply]
    simp [event, Finset.mem_product]
  calc
    _ = ∑ p : Reg bits × I, ‖(fun q => executeThresholdFlag bits U accepted ψ (true, q)) p‖ ^ 2 := by
      simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb]
    _ = ∑ p, ‖Collapse out event p‖ ^ 2 := by
      rw [execute_threshold_flag_success]
      change (∑ p, ‖ApplyGate (poweredProgramMatrix U (PoweredProgram.word bits))ᴴ
        (fun q => if q.1 ∈ accepted then out q else 0) p‖ ^ 2) = _
      rw [hMask]
      simpa only [ApplyGate, Complex.normSq_eq_norm_sq] using
        sum_normSq_mulVec_of_mem_unitaryGroup (powered_program_matrix_adjoint_unitary hU _) (Collapse out event)
    _ = _ := sum_normSq_collapse out event

/-- Before uncomputation, the squared error of the filtered spectral sum is bounded by
the branchwise decision errors weighted by the mass in each input direction. -/
theorem powered_counting_projection_error {J : Type} [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (accepted : Finset (Reg bits)) (keep : J → Prop) (error : J → ℝ)
    (hDecision : ∀ j, |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        (if keep j then 1 else 0)| ≤ error j) :
    let actual := PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j))
    let ideal := PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (∑ j, (if keep j then c j else 0) • v j))
    ∑ p : Reg bits × I, ‖(if p.1 ∈ accepted then actual p else 0) - ideal p‖ ^ 2 ≤
      ∑ j, ‖c j‖ ^ 2 * error j := by
  intro actual ideal
  let retained (j : J) := if keep j then c j else 0
  let kernel (j : J) := relabelState (bitVecEquiv bits).symm (qpeKernel (2 ^ bits) (phase j))
  let weight (z : Reg bits) (j : J) := (if z ∈ accepted then c j else 0) - retained j
  have hSlice (z : Reg bits) :
      (fun i => (if z ∈ accepted then actual (z, i) else 0) - ideal (z, i)) =
        ∑ j, (weight z j * kernel j z) • v j := by
    have hActual := powered_word_spectral_run bits U v c phase hEigen
    have hIdeal := powered_word_spectral_run bits U v retained phase hEigen
    change actual = _ at hActual
    change ideal = _ at hIdeal
    rw [hActual, hIdeal]
    funext i
    by_cases hz : z ∈ accepted
    · simp only [hz, ite_true, weight, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TensorState,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [hz, ite_false, weight, kernel, zero_sub, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        TensorState, neg_mul, Finset.sum_neg_distrib, mul_assoc]
  have hSquare (z : Reg bits) (j : J) :
      ‖weight z j * kernel j z‖ ^ 2 =
        ‖c j‖ ^ 2 * (if (z ∈ accepted ↔ keep j) then 0 else ‖kernel j z‖ ^ 2) := by
    by_cases hz : z ∈ accepted <;> by_cases hj : keep j <;>
      simp [weight, retained, hz, hj, mul_pow]
  have hMismatch (j : J) :
      ∑ z, (if (z ∈ accepted ↔ keep j) then 0 else ‖kernel j z‖ ^ 2) ≤ error j := by
    let out := PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (v j))
    have hn : Normalized (v j) := (normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)
    have hnOut := PoweredProgram.execute_normalized hU (PoweredProgram.word bits)
      (normalized_tensorState (normalized_ket (ZeroStr bits)) hn)
    have hMeasure (s : Finset (Reg bits)) : MeasureProb out (s ×ˢ (Finset.univ : Finset I)) =
        ∑ z ∈ s, ‖kernel j z‖ ^ 2 := by
      unfold out
      rw [PoweredProgram.word_run bits U (phase j) (v j) (hEigen j)]
      exact measureProb_tensorState_left hn _ _
    have hAll : ∑ z, ‖kernel j z‖ ^ 2 = 1 := by
      rw [← hMeasure Finset.univ, Finset.univ_product_univ]
      exact measureProb_univ hnOut
    have hDecision' := hDecision j
    change |MeasureProb out _ - _| ≤ error j at hDecision'
    by_cases hj : keep j
    · simp only [hj, iff_true, ite_true] at hDecision' ⊢
      have hSplit : (∑ z, ‖kernel j z‖ ^ 2) =
          (∑ z, if z ∈ accepted then ‖kernel j z‖ ^ 2 else 0) +
            (∑ z, if z ∈ accepted then 0 else ‖kernel j z‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z ∈ accepted <;> simp [hz]
      rw [hAll, Finset.sum_ite_mem, Finset.univ_inter, ← hMeasure accepted] at hSplit
      linarith only [hSplit, (neg_le_abs _).trans hDecision']
    · simp only [hj, iff_false, ite_false, ite_not, sub_zero] at hDecision' ⊢
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← hMeasure accepted]
      exact (le_abs_self _).trans hDecision'
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ z, ∑ j, ‖weight z j * kernel j z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      change (∑ i, ‖(fun i => (if z ∈ accepted then actual (z, i) else 0) - ideal (z, i)) i‖ ^ 2) = _
      rw [hSlice z, sum_norm_sq_orthonormal v _ hOrthogonal]
    _ = ∑ j, ‖c j‖ ^ 2 * ∑ z, (if (z ∈ accepted ↔ keep j) then 0 else ‖kernel j z‖ ^ 2) := by
      simp_rw [hSquare]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ j, ‖c j‖ ^ 2 * error j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hMismatch j) (sq_nonneg _)

/-- After uncomputation, the same input-weighted error bounds the squared distance from
the unnormalized success branch to the retained vector with a clean counting register. -/
theorem powered_threshold_flag_error {J : Type} [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (accepted : Finset (Reg bits)) (keep : J → Prop) (error : J → ℝ)
    (hDecision : ∀ j, |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        (if keep j then 1 else 0)| ≤ error j) :
    let result := executeThresholdFlag bits U accepted (∑ j, c j • v j)
    let ideal := TensorState (Ket (ZeroStr bits)) (∑ j, (if keep j then c j else 0) • v j)
    ∑ p : Reg bits × I, ‖result (true, p) - ideal p‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 * error j := by
  intro result ideal
  let W := poweredProgramMatrix U (PoweredProgram.word bits)
  let actual := PoweredProgram.execute U (PoweredProgram.word bits)
    (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j))
  let filtered : QState (Reg bits × I) := fun p => if p.1 ∈ accepted then actual p else 0
  have hUWord : W ∈ Matrix.unitaryGroup (Reg bits × I) ℂ := powered_program_matrix_unitary hU _
  have hAdj : Wᴴ ∈ Matrix.unitaryGroup (Reg bits × I) ℂ := powered_program_matrix_adjoint_unitary hU _
  have hInverse : Wᴴ * W = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hUWord
  have hResult : (fun p => result (true, p)) = ApplyGate Wᴴ filtered :=
    execute_threshold_flag_success bits U accepted (∑ j, c j • v j)
  have hDifference : (fun p => result (true, p) - ideal p) =
      ApplyGate Wᴴ (filtered - PoweredProgram.execute U (PoweredProgram.word bits) ideal) := by
    have hClean : ApplyGate Wᴴ (PoweredProgram.execute U (PoweredProgram.word bits) ideal) = ideal := by
      rw [← apply_powered_program_matrix]
      change ApplyGate Wᴴ (ApplyGate W ideal) = ideal
      rw [← applyGate_mul, hInverse, applyGate_one]
    calc
      _ = ApplyGate Wᴴ filtered - ApplyGate Wᴴ (PoweredProgram.execute U (PoweredProgram.word bits) ideal) := by
        rw [hClean]
        exact congrArg (fun u : QState (Reg bits × I) => u - ideal) hResult
      _ = _ := by simp only [ApplyGate, Matrix.mulVec_sub]
  change (∑ p, ‖(fun q => result (true, q) - ideal q) p‖ ^ 2) ≤ ∑ j, ‖c j‖ ^ 2 * error j
  rw [hDifference]
  have hNorm := sum_normSq_mulVec_of_mem_unitaryGroup hAdj
    (filtered - PoweredProgram.execute U (PoweredProgram.word bits) ideal)
  simp only [Complex.normSq_eq_norm_sq] at hNorm
  rw [show (∑ p, ‖ApplyGate Wᴴ (filtered - PoweredProgram.execute U (PoweredProgram.word bits) ideal) p‖ ^ 2) = _ from hNorm]
  exact powered_counting_projection_error bits U hU v c phase hOrthogonal hEigen
    accepted keep error hDecision

end Qatlib.Papers.QRecommender16.Recommendations
