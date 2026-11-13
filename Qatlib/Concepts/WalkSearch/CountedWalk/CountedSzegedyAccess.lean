/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation

/-!
# Counted access to Szegedy walk updates

`szegedyFrame` embeds a state with a fixed second-register anchor, and `szegedyZeroReflection`
reflects about its image. Conjugating this reflection by a preparation unitary gives the Szegedy
row reflection.

`countedSzegedyWord` implements one walk update with four forward or adjoint queries and four
gates. The module proves the semantics and resource counts of repetitions and a linear
operator-error bound for noisy unitary access. See [Szegedy2004] for the mathematical
background.

## Main statements

* `counted_szegedy_actual_walk_semantics`: evaluation of one update.
* `counted_szegedy_repetition_semantics_resources`: powers and resource counts.
* `counted_szegedy_noisy_update_operator_error`: the repeated-update error bound.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.WalkSearch.CountedWalk

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false

open scoped Classical BigOperators
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Applying a matrix to a basis ket extracts the corresponding matrix column. -/
theorem mulVec_ket_column {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (M : Matrix H K ℂ) (i : K) (p : H) : (M *ᵥ Ket i) p = M p i := by
  show (∑ k : K, M p k * Ket i k) = _
  rw [Finset.sum_eq_single i]
  · rw [ket_self, mul_one]
  · intro k _ hk; rw [ket_ne hk, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ i) hcon

/-- Two square matrices are equal if they act equally on every basis ket. -/
theorem matrix_eq_of_forall_mulVec_ket {H : Type*} [Fintype H] [DecidableEq H]
    {M N : Matrix H H ℂ} (h : ∀ q : H, M *ᵥ Ket q = N *ᵥ Ket q) : M = N := by
  ext r c
  rw [← mulVec_ket_column M c r, ← mulVec_ket_column N c r, h c]

/-- Applying a conjugate-transpose matrix to a basis ket extracts the conjugate of the
corresponding original row entry. -/
theorem conjTranspose_mulVec_ket_apply {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (M : Matrix H K ℂ) (i : H) (p : K) :
    ((M)ᴴ *ᵥ Ket i) p = (starRingEnd ℂ) (M i p) := by
  show (∑ k : H, (starRingEnd ℂ) (M k p) * Ket i k) = _
  rw [Finset.sum_eq_single i]
  · rw [ket_self, mul_one]
  · intro k _ hk; rw [ket_ne hk, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ i) hcon

/-- The matrix embedding the basis state indexed by `i` as the pair state `(i, j)`. -/
noncomputable def szegedyFrame (j : I) : Matrix (I × I) I ℂ :=
  Matrix.of fun p i => if p = (i, j) then 1 else 0

omit [Fintype I] in

/-- The frame entry is 1 exactly when the pair index is `(i, j)`, and is zero otherwise. -/
theorem szegedyFrame_apply (j : I) (p : I × I) (i : I) :
    szegedyFrame j p i = if p = (i, j) then (1 : ℂ) else 0 := rfl

/-- The tensor product of the identity on the first register with the reflection about the
anchor ket `Ket j` on the second register. -/
noncomputable def szegedyZeroReflection (j : I) : Matrix (I × I) (I × I) ℂ :=
  TensorGate (1 : Matrix I I ℂ) (ReflectionAbout (outerProduct (Ket j)))

/-- The anchor reflection equals twice the frame projector minus the identity. -/
theorem szegedyZeroReflection_eq (j : I) :
    szegedyZeroReflection j
      = (2 : ℂ) • (szegedyFrame j * (szegedyFrame j)ᴴ) - 1 := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [szegedyZeroReflection, tensorGate_apply, ReflectionAbout,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply,
    outerProduct_apply, Ket, RCLike.star_def, Matrix.mul_apply, Matrix.conjTranspose_apply, szegedyFrame_apply]
  have hstar : (starRingEnd ℂ) (if d = j then (1 : ℂ) else 0)
      = if d = j then (1 : ℂ) else 0 := by
    by_cases hdj : d = j <;> simp [hdj]
  rw [hstar]
  by_cases hac : a = c
  · by_cases hbj : b = j
    · rw [Finset.sum_eq_single a]
      · simp [hac, hbj, Prod.mk.injEq, eq_comm]
      · intro i _ hi
        have hne : ¬((a, b) = (i, j)) := by
          rw [Prod.mk.injEq]; exact fun e => hi e.1.symm
        rw [ite_eq_right hne, zero_mul]
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    · rw [Finset.sum_eq_zero]
      · simp [hbj, hac, Prod.mk.injEq]
      · intro i _
        have hne : ¬((a, b) = (i, j)) := by
          rw [Prod.mk.injEq]; exact fun e => hbj e.2
        rw [ite_eq_right hne, zero_mul]
  · rw [Finset.sum_eq_zero]
    · simp [hac, Prod.mk.injEq]
    · intro i _
      by_cases h1 : (a, b) = (i, j)
      · have h2 : ¬((c, d) = (i, j)) := by
          rw [Prod.mk.injEq] at h1 ⊢
          exact fun e => hac (h1.1.trans e.1.symm)
        rw [ite_eq_left h1, ite_eq_right h2, map_zero, mul_zero]
      · rw [ite_eq_right h1, zero_mul]

/-- The anchor reflection fixes a pair basis ket when its second coordinate is `j` and negates
it otherwise. -/
theorem szegedyZeroReflection_mulVec_ket (j a b : I) :
    szegedyZeroReflection j *ᵥ Ket (a, b)
      = if b = j then Ket (a, b) else -(Ket (a, b)) := by
  rw [show Ket (a, b) = TensorState (Ket a) (Ket b) from (tensorState_ket_ket a b).symm]
  show TensorGate (1 : Matrix I I ℂ) (ReflectionAbout (outerProduct (Ket j))) *ᵥ
    TensorState (Ket a) (Ket b) = _
  rw [mulVec_tensorGate, Matrix.one_mulVec]
  have hsecond : ApplyGate (ReflectionAbout (outerProduct (Ket j))) (Ket b)
      = if b = j then Ket b else -(Ket b) := by
    by_cases hb : b = j
    · rw [hb, applyGate_reflectionAbout_of_fixed
        (show ApplyGate (outerProduct (Ket j)) (Ket j) = Ket j from by
          show outerProduct (Ket j) *ᵥ Ket j = Ket j
          rw [outerProduct_mulVec, inner_ket_ket, ite_eq_left rfl, one_smul])]
      rw [ite_eq_left rfl]
    · rw [applyGate_reflectionAbout_of_zero
        (show ApplyGate (outerProduct (Ket j)) (Ket b) = 0 from by
          show outerProduct (Ket j) *ᵥ Ket b = 0
          rw [outerProduct_mulVec, inner_ket_ket, ite_eq_right (fun e : j = b => hb e.symm),
            zero_smul])]
      rw [ite_eq_right hb]
  show TensorState (Ket a) (ApplyGate (ReflectionAbout (outerProduct (Ket j))) (Ket b))
      = _
  rw [hsecond]
  by_cases hb : b = j
  · rw [ite_eq_left hb, tensorState_ket_ket, ite_eq_left hb]
  · rw [ite_eq_right hb]
    have hneg : TensorState (Ket a) (-(Ket b)) = -(TensorState (Ket a) (Ket b)) := by
      funext x; simp [TensorState]
    rw [hneg, tensorState_ket_ket, ite_eq_right hb]

/-- For every anchor, `szegedyZeroReflection` is the stated tensor-product reflection and is
unitary. -/
theorem counted_szegedy_actual_source_reflection : ∀ (j : I),
    szegedyZeroReflection j =
      TensorGate (1 : Matrix I I ℂ) (ReflectionAbout (outerProduct (Ket j))) ∧
    szegedyZeroReflection j ∈ Matrix.unitaryGroup (I × I) ℂ := by
  intro j
  exact ⟨rfl, tensorGate_unitary (Submonoid.one_mem _)
    (outerProduct_reflection_unitary (normalized_ket j))⟩

/-- If `U` prepares the Szegedy row states from anchor `j`, then `U * szegedyFrame j` equals
`SzegedyIsometry P`. -/
theorem szegedyPreparation_mul_frame {P : I → I → ℝ} {j : I}
    (U : Matrix (I × I) (I × I) ℂ)
    (h : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    U * szegedyFrame j = SzegedyIsometry P := by
  ext p i
  have h1 : (U * szegedyFrame j) p i = (U *ᵥ Ket (i, j)) p := by
    rw [mulVec_ket_column]
    show (∑ r : I × I, U p r * szegedyFrame j r i) = _
    rw [Finset.sum_eq_single (i, j)]
    · rw [szegedyFrame_apply, ite_eq_left rfl, mul_one]
    · intro r _ hr
      rw [szegedyFrame_apply, ite_eq_right hr, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  rw [h1, ← tensorState_ket_ket i j, h i, mulVec_ket_column]

/-- For a transition matrix and a unitary row preparation, conjugating the anchor reflection by
the preparation unitary yields `SzegedyReflection P`. -/
theorem counted_szegedy_prepare_frame_reflection :
    ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
    U * szegedyZeroReflection j * Uᴴ = SzegedyReflection P := by
  intro P j U hP hU h
  have hUF : U * szegedyFrame j = SzegedyIsometry P := szegedyPreparation_mul_frame U h
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hU
  have hprod : U * (szegedyFrame j * (szegedyFrame j)ᴴ) * Uᴴ
      = (U * szegedyFrame j) * (U * szegedyFrame j)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      ← Matrix.mul_assoc]
  rw [szegedyZeroReflection_eq j, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.mul_one, hprod, hUF, hUU]
  rfl

/-- The eight-instruction Szegedy update word containing two swaps, two anchor reflections, two
forward queries, and two adjoint queries. -/
noncomputable def countedSzegedyWord (j : I) : List (AdjointStep (I × I)) :=
  [.gate SwapGate, .forward, .gate (szegedyZeroReflection j), .backward,
   .gate SwapGate, .forward, .gate (szegedyZeroReflection j), .backward]

omit [Fintype I] in

/-- Expands the Szegedy update word and verifies that it contains four queries and four gates. -/
theorem counted_szegedy_actual_word_and_counts : ∀ (j : I),
    countedSzegedyWord j = [.gate SwapGate, .forward, .gate (szegedyZeroReflection j),
      .backward, .gate SwapGate, .forward, .gate (szegedyZeroReflection j),
      .backward] ∧
    adjointQueryCount (countedSzegedyWord j) = 4 ∧
    adjointGateCount (countedSzegedyWord j) = 4 := by
  intro j
  exact ⟨rfl, rfl, rfl⟩

/-- The counted Szegedy update word satisfies `WellFormedAdjointCircuit`. -/
theorem countedSzegedyWord_wellFormed (j : I) :
    WellFormedAdjointCircuit (countedSzegedyWord j) := by
  simp [countedSzegedyWord, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.forward_cons_iff, WellFormedAdjointCircuit.backward_cons_iff,
    WellFormedAdjointCircuit.nil, swapGate_unitary,
    (counted_szegedy_actual_source_reflection j).2]

/-- Given a transition matrix and a unitary row preparation, evaluating the counted update word
yields `SzegedyWalk P`. -/
theorem counted_szegedy_actual_walk_semantics :
    ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
    evaluate U (countedSzegedyWord j) = SzegedyWalk P := by
  intro P j U hP hU hprep
  have hR := counted_szegedy_prepare_frame_reflection P j U hP hU hprep
  simp only [countedSzegedyWord, evaluate, instructionMatrix, Matrix.mul_one]
  simp only [SzegedyWalk, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at hR
  rw [← hR]
  simp only [Matrix.mul_assoc]

/-- Under the preparation assumptions, `m` concatenated update words evaluate to `(SzegedyWalk
P) ^ m` and use `4 * m` queries and `4 * m` gates. -/
theorem counted_szegedy_repetition_semantics_resources :
    ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ) (m : ℕ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
    let cs := (List.replicate m (countedSzegedyWord j)).flatten
    evaluate U cs = (SzegedyWalk P)^m ∧
      adjointQueryCount cs = 4*m ∧ adjointGateCount cs = 4*m := by
  intro P j U m hP hU hprep
  have hc := counted_szegedy_actual_word_and_counts j
  induction m with
  | zero => simp [evaluate, adjointQueryCount, adjointGateCount]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, evaluate_append,
      adjointQueryCount_append, adjointGateCount_append]
    rw [counted_szegedy_actual_walk_semantics P j U hP hU hprep,
      ih.1, ih.2.1, ih.2.2, hc.2.1, hc.2.2, pow_succ']
    exact ⟨rfl, by omega, by omega⟩

/-- If unitary access `V` is within operator distance `δ` of the row preparation `U`, evaluating
`m` update words with `V` differs from the ideal walk power by at most `4 * m * δ`, for `δ ≥
0`. -/
theorem counted_szegedy_noisy_update_operator_error :
    ∀ (P : I → I → ℝ) (j : I) (U V : Matrix (I × I) (I × I) ℂ) (m : ℕ) (δ : ℝ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I × I) ℂ →
    V ∈ Matrix.unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
    0 ≤ δ → ‖V-U‖ ≤ δ →
    ‖evaluate V ((List.replicate m (countedSzegedyWord j)).flatten) - (SzegedyWalk P)^m‖
      ≤ (4*m : ℕ)*δ := by
  intro P j U V m δ hP hU hV hprep hδ hVU
  have hr := counted_szegedy_repetition_semantics_resources P j U m hP hU hprep
  have hw : WellFormedAdjointCircuit ((List.replicate m (countedSzegedyWord j)).flatten) := by
    clear hr
    induction m with
    | zero => exact WellFormedAdjointCircuit.nil
    | succ m ih =>
      simpa only [List.replicate_succ, List.flatten_cons] using
        (countedSzegedyWord_wellFormed j).append ih
  have he := evaluate_operator_error_le_queries
    ((List.replicate m (countedSzegedyWord j)).flatten) U V δ hw hU hV hδ hVU
  rwa [hr.1, hr.2.1] at he

end Qatlib.Concepts.WalkSearch.CountedWalk
