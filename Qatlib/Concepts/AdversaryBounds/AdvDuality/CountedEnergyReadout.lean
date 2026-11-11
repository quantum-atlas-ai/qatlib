/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.DegenerateEnergyInstrument
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument

/-!
# Counted implementation of energy readout

This module implements energy-label readout as an observed circuit with a phase register.
`energyProgram` applies three gates and measures the phase label; `energyActualBranchPipeline`
embeds a system operator, executes one actual leaf, and discards that register.

The resulting branches and outcome probabilities agree with `energyInstrument`. This realizes
the dilation and measurement description of quantum instruments used in [Watrous2018], while
retaining exact circuit resource counts.

## Main statements

* `energy_program_branch_frame_measure_discard`: each implemented branch equals the
  energy-instrument branch.
* `energy_program_actual_outcome_prob`: the implementation preserves outcome probabilities.
* `energy_program_legality_and_exact_macro_cost`: the program is well formed and every trace has
  three gates, zero queries, and one measurement.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Kronecker

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The standard equivalence flattening a phase-register index and a system index into `Fin (M *
D)`. -/
def energyRegisterEquiv (D M : ℕ) : Fin M × Fin D ≃ Fin (M*D) :=
  finProdFinEquiv

/-- Transport a matrix on the phase-system product register to the flattened register. -/
noncomputable def energyTransportGate {D M : ℕ}
    (W : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) : Matrix (Fin (M*D)) (Fin (M*D)) ℂ :=
  W.submatrix (energyRegisterEquiv D M).symm (energyRegisterEquiv D M).symm

/-- Transporting a gate and vector commutes with matrix-vector multiplication. -/
theorem energyTransportGate_mulVec {D M : ℕ}
    (W : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (v : QState (Fin M × Fin D)) :
    energyTransportGate W *ᵥ (v ∘ (energyRegisterEquiv D M).symm)
      = (W *ᵥ v) ∘ (energyRegisterEquiv D M).symm := by
  funext k
  show ∑ l : Fin (M*D), W ((energyRegisterEquiv D M).symm k)
      ((energyRegisterEquiv D M).symm l) * v ((energyRegisterEquiv D M).symm l) = _
  rw [Equiv.sum_comp (energyRegisterEquiv D M).symm
    (fun p => W ((energyRegisterEquiv D M).symm k) p * v p)]
  rfl

/-- Register transport preserves membership in the unitary group. -/
theorem energyTransportGate_unitary {D M : ℕ}
    (W : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) :
    energyTransportGate W ∈ Matrix.unitaryGroup (Fin (M*D)) ℂ := by
  have hWt : W.conjTranspose * W = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hW
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext k l
  show ∑ m : Fin (M*D), star (W ((energyRegisterEquiv D M).symm m)
      ((energyRegisterEquiv D M).symm k))
      * W ((energyRegisterEquiv D M).symm m) ((energyRegisterEquiv D M).symm l) = _
  rw [Equiv.sum_comp (energyRegisterEquiv D M).symm
    (fun p => star (W p ((energyRegisterEquiv D M).symm k))
      * W p ((energyRegisterEquiv D M).symm l))]
  have hentry := congrFun (congrFun hWt ((energyRegisterEquiv D M).symm k))
    ((energyRegisterEquiv D M).symm l)
  rw [Matrix.mul_apply] at hentry
  have hentry' : ∑ i : Fin M × Fin D, star (W i ((energyRegisterEquiv D M).symm k))
        * W i ((energyRegisterEquiv D M).symm l)
      = (1 : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
        ((energyRegisterEquiv D M).symm k) ((energyRegisterEquiv D M).symm l) := by
    rw [← hentry]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Matrix.conjTranspose_apply]
  rw [hentry']
  simp only [Matrix.one_apply]
  by_cases h : k = l
  · subst h
    simp
  · rw [if_neg h, if_neg (fun hh => h ((energyRegisterEquiv D M).symm.injective hh))]

/-- The observed energy-readout circuit, consisting of three transported gates followed by
measurement of the phase label. -/
noncomputable def energyProgram {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    ObservedCircuit (Fin (M*D)) :=
  .step (.gate (energyTransportGate (TensorGate (1 : Operator M) V.conjTranspose)))
    (.step (.gate (energyTransportGate (energyLabelPerm label)))
      (.step (.gate (energyTransportGate (TensorGate (1 : Operator M) V)))
        (.measure M (fun k => ((energyRegisterEquiv D M).symm k).1)
          (fun _ => .halt true))))

/-- The system Kraus block of the energy dilation from initial phase zero to outcome `a`. -/
noncomputable def energyKrausBlock {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) (hM : 0 < M) : Operator D :=
  Matrix.of fun i j => energyDilation label V (a, i) (⟨0, hM⟩, j)

/-- The conjugation branch associated with the energy Kraus block, with zero map when the phase
dimension is zero. -/
noncomputable def energyActualBranchMap {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) : Operator D →ₗ[ℂ] Operator D :=
  if hM : 0 < M then conjBranch (energyKrausBlock label V a hM) else 0

/-- For unitary `V`, the dilation's Kraus block equals the corresponding energy projector. -/
theorem energyKrausBlock_eq_projector (D M : ℕ) (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : Fin M) :
    energyKrausBlock label V a hM = energyProjector label V a := by
  ext i j
  have hG2 := (energy_readout_dilation_unitary_and_branch_amplitudes D M hM label V
    (Qatlib.Foundations.PureStateMath.Ket j) hV).2 a i

  have hcol : (energyDilation label V *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩:Fin M)) (Qatlib.Foundations.PureStateMath.Ket j)) (a, i)
      = energyDilation label V (a, i) (⟨0, hM⟩, j) := by
    show ∑ p : Fin M × Fin D, energyDilation label V (a, i) p
        * TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩:Fin M)) (Qatlib.Foundations.PureStateMath.Ket j) p = _
    rw [tensorState_ket_ket]
    rw [Finset.sum_eq_single (⟨0, hM⟩, j)]
    · rw [Qatlib.Foundations.PureStateMath.Ket, if_pos rfl, mul_one]
    · intro z _ hz
      rw [Qatlib.Foundations.PureStateMath.Ket, if_neg hz, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hcolR : (energyProjector label V a *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = energyProjector label V a i j := by
    show ∑ m :
        Fin D, energyProjector label V a i m * Qatlib.Foundations.PureStateMath.Ket j m = _
    rw [Finset.sum_eq_single j]
    · rw [Qatlib.Foundations.PureStateMath.Ket, if_pos rfl, mul_one]
    · intro z _ hz
      rw [Qatlib.Foundations.PureStateMath.Ket, if_neg hz, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show energyDilation label V (a, i) (⟨0, hM⟩, j) = energyProjector label V a i j
  rw [← hcol, hG2, hcolR]

/-- The phase-register projector onto basis state zero. -/
noncomputable def energyPhaseFrame {M : ℕ} (hM : 0 < M) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun p : Fin M => if p = ⟨0, hM⟩ then (1:ℂ) else 0)

/-- Embed a system operator into the phase-zero block of the phase-system register. -/
noncomputable def energyEmbedFrame {D M : ℕ} (hM : 0 < M) (X : Operator D) :
    Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ :=
  Matrix.of fun p q => (if p.1 = (⟨0, hM⟩ : Fin M) then (1:ℂ) else 0)
    * (if q.1 = (⟨0, hM⟩ : Fin M) then (1:ℂ) else 0) * X p.2 q.2

/-- The projector onto the phase-register label `a`, acting identically on the system index. -/
noncomputable def energyLabelProjector {D M : ℕ} (a : Fin M) :
    Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ :=
  Matrix.diagonal (fun p : Fin M × Fin D => if p.1 = a then (1:ℂ) else 0)

/-- The energy-dilation operator followed by projection onto phase outcome `a`. -/
noncomputable def energyLeafOperator {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ :=
  energyLabelProjector a * energyDilation label V

/-- Discard the phase register after undoing the flattened register indexing. -/
noncomputable def energyDiscardPhase {D M : ℕ} (Y : Matrix (Fin (M*D)) (Fin (M*D)) ℂ) :
    Operator D :=
  partialTraceFirst (Y.submatrix (energyRegisterEquiv D M) (energyRegisterEquiv D M))

/-- Transport of product-register matrices preserves multiplication. -/
theorem energyTransportGate_mul {D M : ℕ}
    (A B : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) :
    energyTransportGate A * energyTransportGate B = energyTransportGate (A * B) :=
  Matrix.submatrix_mul_equiv A B (energyRegisterEquiv D M).symm
    (energyRegisterEquiv D M).symm (energyRegisterEquiv D M).symm

/-- Transport of product-register matrices commutes with conjugate transpose. -/
theorem energyTransportGate_conjTranspose {D M : ℕ}
    (A : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) :
    (energyTransportGate A).conjTranspose = energyTransportGate A.conjTranspose := by
  ext k l
  simp only [Matrix.conjTranspose_apply, energyTransportGate, Matrix.submatrix_apply,
    Matrix.conjTranspose_apply]

/-- The flattened measurement projector is the transport of the corresponding phase-label
projector. -/
theorem energyTransportGate_labelProjector {D M : ℕ} (a : Fin M) :
    Projector (Finset.univ.filter (fun k : Fin (M*D) =>
        ((energyRegisterEquiv D M).symm k).1 = a))
      = energyTransportGate (energyLabelProjector a) := by
  ext k l
  simp only [Projector, Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and,
    energyTransportGate, Matrix.submatrix_apply, energyLabelProjector]
  by_cases hk : k = l
  · subst hk
    by_cases h : ((energyRegisterEquiv D M).symm k).1 = a <;> simp [h]
  · rw [if_neg hk,
      if_neg (fun hc => hk (Equiv.injective (energyRegisterEquiv D M).symm hc))]

/-- The energy program has exactly `M` observed leaves. -/
theorem observedLeafCount_energyProgram {D M : ℕ} (label : Fin D → Fin M)
    (V : Operator D) : observedLeafCount (energyProgram label V) = M := by
  simp [energyProgram, observedLeafCount]

/-- The observed-leaf index corresponding to an energy outcome `a`. -/
noncomputable def energyLeaf {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) (a : Fin M) :
    Fin (observedLeafCount (energyProgram label V)) :=
  Fin.cast (observedLeafCount_energyProgram label V).symm a

/-- The actual Kraus leaves obtained by executing the energy program from the identity operator. -/
noncomputable def energyActualLeaves {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    List (ObservedKrausLeaf (M*D)) :=
  observedKrausLeaves (1 : Operator (M*D)) (energyProgram label V)

/-- The list of actual energy-program Kraus leaves has length `M`. -/
theorem energyActualLeaves_length {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    (energyActualLeaves label V).length = M := by
  rw [energyActualLeaves, observedKrausLeaves_length, observedLeafCount_energyProgram]

/-- Flattening the list of singleton lists indexed by `Fin n` yields the original indexed list. -/
private theorem flatten_ofFn_singleton {α : Type*} {n : ℕ} (g : Fin n → α) :
    (List.ofFn (fun o : Fin n => [g o])).flatten = List.ofFn g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.singleton_append,
      ih (fun i => g i.succ), List.ofFn_succ (f := g)]

/-- The actual energy leaves are the transported leaf operators, each accepting with zero
queries, three gates, one measurement, and its phase outcome. -/
theorem energyActualLeaves_eq {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    energyActualLeaves label V
      = List.ofFn (fun a : Fin M =>
          ({ operator := energyTransportGate (energyLeafOperator label V a),
             accepted := true, queries := 0, gates := 3, measurements := 1,
             outcomes := [(M, a.val)] } : ObservedKrausLeaf (M*D))) := by
  simp only [energyActualLeaves, energyProgram, observedKrausLeaves, List.map_cons,
    List.map_nil, flatten_ofFn_singleton, ← List.ofFn_comp',
    ObservedKrausLeaf.prepend]
  congr 1
  funext a
  congr 1
  · have hinner : energyLabelProjector (D := D) a * TensorGate (1 : Operator M) V
        * energyLabelPerm label * TensorGate (1 : Operator M) V.conjTranspose
        = energyLeafOperator label V a := by
      simp only [energyLeafOperator, energyDilation]
      noncomm_ring
    rw [energyTransportGate_labelProjector, Matrix.one_mul,
      energyTransportGate_mul, energyTransportGate_mul, energyTransportGate_mul,
      hinner]

/-- The actual Kraus leaf at the given energy outcome. -/
noncomputable def energyActualLeaf {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) : ObservedKrausLeaf (M*D) :=
  (energyActualLeaves label V)[a.val]'(by rw [energyActualLeaves_length]; exact a.isLt)

/-- The actual energy leaf has the transported leaf operator and the stated acceptance,
resource, and measurement-outcome fields. -/
theorem energyActualLeaf_eq {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) (a : Fin M) :
    energyActualLeaf label V a
      = { operator := energyTransportGate (energyLeafOperator label V a),
          accepted := true, queries := 0, gates := 3, measurements := 1,
          outcomes := [(M, a.val)] } := by
  show (energyActualLeaves label V)[a.val]'(by rw [energyActualLeaves_length]; exact a.isLt)
      = _
  simp only [energyActualLeaves_eq, List.getElem_ofFn]

/-- The indexed observed leaf of the energy program equals its actual Kraus leaf. -/
theorem observedLeaf_energyActualLeaf {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) :
    observedLeaf (1 : Operator (M*D)) (energyProgram label V) (energyLeaf label V a)
      = energyActualLeaf label V a := rfl

/-- Casting an energy outcome to the observed-leaf index yields the corresponding actual Kraus
leaf. -/
theorem observedLeaf_cast {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (a : Fin M) :
    observedLeaf (1 : Operator (M*D)) (energyProgram label V)
        (Fin.cast (observedLeafCount_energyProgram label V).symm a)
      = energyActualLeaf label V a := rfl

/-- The phase-zero embedding is the Kronecker product of the phase-zero projector with the
system operator. -/
theorem energyEmbedFrame_eq {D M : ℕ} (hM : 0 < M) (X : Operator D) :
    energyEmbedFrame hM X = energyPhaseFrame hM ⊗ₖ X := by
  ext p q
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  simp only [energyEmbedFrame, Matrix.of_apply, Matrix.kronecker_apply, energyPhaseFrame,
    Matrix.diagonal_apply]
  by_cases hp0 : p₁ = (⟨0, hM⟩ : Fin M) <;> by_cases hq0 : q₁ = (⟨0, hM⟩ : Fin M) <;>
    by_cases hpq : p₁ = q₁ <;> simp_all

/-- An entry of the phase-zero embedding is the system entry multiplied by the two phase-zero
indicators. -/
theorem energyEmbedFrame_apply {D M : ℕ} (hM : 0 < M) (X : Operator D)
    (p q : Fin M) (i j : Fin D) :
    energyEmbedFrame hM X (p, i) (q, j)
      = (if p = (⟨0, hM⟩ : Fin M) then (1:ℂ) else 0) * (if q = (⟨0, hM⟩ : Fin M) then (1:ℂ) else 0)
        * X i j := rfl

/-- Sandwiching by the phase-label projector retains exactly the block with both phase indices
equal to `a`. -/
theorem energyLabelProjector_sandwich_apply {D M : ℕ} (a : Fin M)
    (W : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (p q : Fin M) (m m' : Fin D) :
    ((energyLabelProjector (D := D) a * W * energyLabelProjector (D := D) a :
        Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (p, m) (q, m')
      = if p = a ∧ q = a then W (a, m) (a, m') else 0) := by
  have hstep : energyLabelProjector (D := D) a * W * energyLabelProjector (D := D) a
      = Matrix.of (fun x y : Fin M × Fin D =>
          (if x.1 = a then (1:ℂ) else 0) * W x y * (if y.1 = a then (1:ℂ) else 0)) := by
    simp only [energyLabelProjector]
    ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hstep]
  simp only [Matrix.of_apply]
  by_cases hpa : p = a <;> by_cases hqa : q = a <;> simp [hpa, hqa]

set_option maxHeartbeats 1000000 in

/-- Tracing out the phase register after an energy leaf acts on a phase-zero embedding gives
conjugation by the associated Kraus block. -/
theorem partialTraceFirst_leaf_frame {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (a : Fin M) (X : Operator D) :
    partialTraceFirst (energyLeafOperator label V a * energyEmbedFrame hM X
          * (energyLeafOperator label V a).conjTranspose)
      = energyKrausBlock label V a hM * X
        * (energyKrausBlock label V a hM).conjTranspose := by
  ext m m'
  have hrebracket : energyLeafOperator label V a * energyEmbedFrame hM X
      * (energyLeafOperator label V a).conjTranspose
      = energyLabelProjector a * (energyDilation label V * energyEmbedFrame hM X
          * (energyDilation label V).conjTranspose) * energyLabelProjector a := by
    have hLP : (energyLabelProjector (D := D) a).conjTranspose
        = energyLabelProjector (D := D) a := by
      ext x y
      simp only [Matrix.conjTranspose_apply, energyLabelProjector, Matrix.diagonal_apply]
      by_cases hxy : x = y
      · subst hxy
        by_cases h : x.1 = a <;> simp [h]
      · rw [if_neg (Ne.symm hxy), if_neg hxy]
        simp
    simp only [energyLeafOperator, Matrix.conjTranspose_mul, hLP]
    calc ((energyLabelProjector a * energyDilation label V) * energyEmbedFrame hM X)
          * ((energyDilation label V).conjTranspose * energyLabelProjector a)
        = (energyLabelProjector a * energyDilation label V)
            * (energyEmbedFrame hM X
              * ((energyDilation label V).conjTranspose * energyLabelProjector a)) :=
          Matrix.mul_assoc _ _ _
      _ = energyLabelProjector a
            * (energyDilation label V
              * (energyEmbedFrame hM X
                * ((energyDilation label V).conjTranspose * energyLabelProjector a))) :=
          Matrix.mul_assoc _ _ _
      _ = energyLabelProjector a
            * ((energyDilation label V * energyEmbedFrame hM X)
              * ((energyDilation label V).conjTranspose * energyLabelProjector a)) := by
          congr 1
          rw [← Matrix.mul_assoc]
      _ = energyLabelProjector a
            * ((energyDilation label V * energyEmbedFrame hM X
              * (energyDilation label V).conjTranspose) * energyLabelProjector a) := by
          congr 1
          rw [← Matrix.mul_assoc]
      _ = (energyLabelProjector a
            * (energyDilation label V * energyEmbedFrame hM X
              * (energyDilation label V).conjTranspose)) * energyLabelProjector a :=
          (Matrix.mul_assoc _ _ _).symm

  have hDgZ : ∀ (u : Fin M) (v : Fin D),
      (energyDilation label V * energyEmbedFrame hM X) (a, m) (u, v)
        = (if u = (⟨0, hM⟩ : Fin M) then (1:ℂ) else 0)
          * ∑ s : Fin D, energyDilation label V (a, m) (⟨0, hM⟩, s) * X s v := by
    intro u v
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [energyEmbedFrame_apply]
    rw [Finset.sum_eq_single (⟨0, hM⟩ : Fin M)]
    · rw [if_pos rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    · intro r _ hr
      rw [if_neg hr]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [partialTraceFirst, Matrix.traceLeft, Matrix.of_apply]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · rw [hrebracket, energyLabelProjector_sandwich_apply,
      if_pos (show a = a ∧ a = a from ⟨rfl, rfl⟩), Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Fintype.sum_prod_type, hDgZ]
    rw [Finset.sum_eq_single_of_mem (⟨0, hM⟩ : Fin M) (Finset.mem_univ _)]
    · rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, reduceIte, one_mul,
        Finset.sum_mul, energyKrausBlock, Matrix.of_apply]
    · intro u _ hu
      simp [hu]
  · intro p _ hp
    rw [hrebracket, energyLabelProjector_sandwich_apply, if_neg (fun hh => hp hh.1)]

/-- Register transport preserves the matrix trace. -/
theorem energyTransportGate_trace {D M : ℕ}
    (Z : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) :
    Matrix.trace (energyTransportGate Z) = Matrix.trace Z := by
  simp only [Matrix.trace, Matrix.diag_apply, energyTransportGate, Matrix.submatrix_apply]
  exact Equiv.sum_comp (energyRegisterEquiv D M).symm
    (fun p : Fin M × Fin D => Z p p)

/-- The implemented energy branch obtained by phase-zero embedding, actual leaf execution, and
phase-register disposal. -/
noncomputable def energyActualBranchPipeline {D M : ℕ} (label : Fin D → Fin M)
    (V : Operator D) (a : Fin M) (hM : 0 < M) (X : Operator D) : Operator D :=
  energyDiscardPhase
    ((energyActualLeaf label V a).operator
      * energyTransportGate (energyEmbedFrame hM X)
      * (energyActualLeaf label V a).operator.conjTranspose)

/-- For unitary `V`, the implemented branch pipeline equals the energy-instrument branch, which
also equals `energyActualBranchMap`. -/
theorem energy_program_branch_frame_measure_discard (D M : ℕ) (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : Fin M) (X : Operator D) :
    energyActualBranchPipeline label V a hM X
        = (energyInstrument label V hV).branch a X ∧
      (energyInstrument label V hV).branch a X = energyActualBranchMap label V a X := by
  have hsand : (energyActualLeaf label V a).operator
      * energyTransportGate (energyEmbedFrame hM X)
      * (energyActualLeaf label V a).operator.conjTranspose
      = energyTransportGate (energyLeafOperator label V a * energyEmbedFrame hM X
          * (energyLeafOperator label V a).conjTranspose) := by
    simp only [energyActualLeaf_eq]
    rw [energyTransportGate_mul, energyTransportGate_conjTranspose,
      energyTransportGate_mul]
  have hcanc : ∀ W : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ,
      energyDiscardPhase (energyTransportGate W) = partialTraceFirst W := by
    intro W
    simp [energyDiscardPhase, partialTraceFirst, Matrix.traceLeft,
      energyTransportGate, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rw [energyActualBranchPipeline, hsand, hcanc, partialTraceFirst_leaf_frame,
      energyInstrument, Instrument.ofKraus_branch,
      energyKrausBlock_eq_projector D M hM label V hV a]
  · show (energyInstrument label V hV).branch a X
        = (if hM : 0 < M then conjBranch (energyKrausBlock label V a hM) else 0) X
    rw [dif_pos hM, energyInstrument, Instrument.ofKraus_branch, conjBranch_apply,
      energyKrausBlock_eq_projector D M hM label V hV a]

/-- The energy program is well formed when the phase dimension is positive and `V` is unitary. -/
theorem energyProgram_observedWellFormed (D M : ℕ) (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    observedWellFormed (energyProgram label V) := by
  simp only [energyProgram, observedWellFormed]
  exact ⟨energyTransportGate_unitary _ (tensorGate_unitary
      (by rw [Matrix.mem_unitaryGroup_iff]; simp) (energyConjTranspose_unitary hV)),
    ⟨energyTransportGate_unitary _ (energyLabelPerm_unitary label),
      ⟨energyTransportGate_unitary _ (tensorGate_unitary
        (by rw [Matrix.mem_unitaryGroup_iff]; simp) hV), fun _ => trivial⟩⟩⟩

/-- Taking the partial trace over the first register preserves the full trace. -/
theorem partialTraceFirst_trace {D M : ℕ}
    (A : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) :
    Matrix.trace (partialTraceFirst A) = Matrix.trace A := Matrix.traceLeft_trace A

/-- The observed circuit's outcome probability on an embedded system operator equals the
corresponding energy-instrument probability. -/
theorem energy_program_actual_outcome_prob (D M : ℕ) (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (a : Fin M) (X : Operator D) :
    instrumentProb (observedInstrument (1 : Operator (M*D))
        (by rw [Matrix.mem_unitaryGroup_iff]; simp)
        (energyProgram label V)
        (energyProgram_observedWellFormed D M hM label V hV))
        (energyTransportGate (energyEmbedFrame hM X)) (energyLeaf label V a)
      = instrumentProb (energyInstrument label V hV) X a := by
  show (Matrix.trace ((observedInstrument (1 : Operator (M*D)) _
        (energyProgram label V) _).branch (energyLeaf label V a)
        (energyTransportGate (energyEmbedFrame hM X)))).re
      = instrumentProb (energyInstrument label V hV) X a
  rw [observedInstrument, Instrument.ofKraus_branch]
  simp only [observedLeaf_energyActualLeaf, energyActualLeaf_eq]
  rw [energyTransportGate_mul, energyTransportGate_conjTranspose,
    energyTransportGate_mul, energyTransportGate_trace,
    ← partialTraceFirst_trace, partialTraceFirst_leaf_frame]
  rw [energyKrausBlock_eq_projector D M hM label V hV a]
  have hcycle : Matrix.trace (energyProjector label V a * X
        * (energyProjector label V a).conjTranspose)
      = Matrix.trace (energyProjector label V a * X) := by
    have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
    rw [Matrix.trace_mul_cycle, (hG1.2.1 a).1, (hG1.2.1 a).2]
  rw [hcycle, ← (energy_actual_instrument_projector_map D M label V hV a X).2]

/-- The energy circuit is well formed, each trace uses three gates, zero queries, and one
measurement, and its actual branches equal those of the energy instrument. -/
theorem energy_program_legality_and_exact_macro_cost (D M : ℕ) (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    observedWellFormed (energyProgram label V) ∧
    (∀ ψ t, t ∈ observedTraces (1:Operator (M*D)) (energyProgram label V) ψ →
      t.gates = 3 ∧ t.queries = 0 ∧ t.measurements = 1) ∧
    (∀ a X, energyActualBranchMap label V a X = (energyInstrument label V hV).branch a X) := by
  have hG1 := energy_projector_actual_orthogonal_resolution D M label V hV
  refine ⟨?_, ?_, ?_⟩
  · simp only [energyProgram, observedWellFormed]
    exact ⟨energyTransportGate_unitary _ (tensorGate_unitary
        (by rw [Matrix.mem_unitaryGroup_iff]; simp) (energyConjTranspose_unitary hV)),
      ⟨energyTransportGate_unitary _ (energyLabelPerm_unitary label),
        ⟨energyTransportGate_unitary _ (tensorGate_unitary
          (by rw [Matrix.mem_unitaryGroup_iff]; simp) hV),
          fun _ => trivial⟩⟩⟩
  · intro ψ t ht
    simp only [energyProgram, observedTraces] at ht
    rw [List.mem_map] at ht
    obtain ⟨t₂, ht₂, rfl⟩ := ht
    rw [List.mem_map] at ht₂
    obtain ⟨t₁, ht₁, rfl⟩ := ht₂
    rw [List.mem_map] at ht₁
    obtain ⟨t₀, ht₀, rfl⟩ := ht₁
    rw [List.mem_flatten] at ht₀
    obtain ⟨l, hl, htl⟩ := ht₀
    rw [List.mem_ofFn] at hl
    obtain ⟨o, rfl⟩ := hl
    simp only [List.mem_map, List.mem_singleton] at htl
    obtain ⟨t', rfl, rfl⟩ := htl
    simp
  · intro a X

    exact (energy_program_branch_frame_measure_discard D M hM label V hV a X).2.symm

end Qatlib.Concepts.AdversaryBounds.AdvDuality
