/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.ActivationSampling
public import Qatlib.Papers.QCNN20.Forward.MedianActivation
public import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError

@[expose] public section

/-!
# Coherently labelled median activation sampling

[KerenidisLandmanPrakash2020], Algorithm 1 and Sections D.1.2–D.1.5,
estimate the capped activations. To realize the probability law of
Section D.1.4, Eq. (12), this construction uses square-root activation
weights in the zero-flag amplitudes. A counter label whose decoded value
is the median records the activation in a finite register before the flag rotation. The
sampling law retains the full joint uncertainty of the repeated
estimates at each address. Reversing estimation on its workspaces after
writing the label preserves the address, label, and flag distribution.
Distinct estimated labels may still be entangled with those workspaces.
The median selection and rotations have exact matrix semantics.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
  (measureProb_relabelState norm_toEuclidean_fromVec_sq relabelState)
open Qatlib.Concepts.CircuitLang.QueryWords (Denote)
open Qatlib.Concepts.LchsSimulation.StaticLchs (norm_applyGate_of_mem_unitaryGroup)
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
  (insertionSortCounted insertionSortCounted_length insertionSortCounted_perm sortedBlockMedian)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open scoped BigOperators Classical

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- The matrix unitary group on a finite basis is independent of its equality decision procedure. -/
theorem unitary_with_decidable_eq {I : Type} [Fintype I] {d e : DecidableEq I} {U : Matrix I I ℂ}
    (h : letI := d; U ∈ Matrix.unitaryGroup I ℂ) : letI := e; U ∈ Matrix.unitaryGroup I ℂ := by
  have hde : d = e := Subsingleton.elim _ _
  subst e
  exact h

/-- The median is attained by at least one of the sampled counter labels. -/
theorem exists_convolution_median_label {R : Type} (patch filter : Tree ℝ window) (cap : ℝ)
    (M r : ℕ) (record : Fin (2 * r + 1) → Fin M × R) :
    ∃ z, convolutionCounterActivation patch filter cap M z = convolutionMedianActivation patch filter cap M r record := by
  let v (j : Fin (2 * r + 1)) := convolutionCounterActivation patch filter cap M (record j).1
  let sorted := (insertionSortCounted (List.ofFn v)).1
  have hr : r < sorted.length := by
    dsimp only [sorted]
    rw [insertionSortCounted_length, List.length_ofFn]
    omega
  have hm : sorted[r] ∈ List.ofFn v :=
    (insertionSortCounted_perm (List.ofFn v)).mem_iff.mp (List.getElem_mem hr)
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  refine ⟨(record j).1, ?_⟩
  change v j = sorted.getD r 0
  rw [List.getD_eq_getElem _ 0 hr]
  exact hj

/-- Pick a counter label whose clipped activation is the median of the decoded record. -/
def convolutionMedianLabel {R : Type} (patch filter : Tree ℝ window) (cap : ℝ)
    (M r : ℕ) (record : Fin (2 * r + 1) → Fin M × R) : Fin M :=
  Classical.choose (exists_convolution_median_label patch filter cap M r record)

/-- The median label decodes back to precisely the median used in the failure bound. -/
theorem convolution_median_label_value {R : Type} (patch filter : Tree ℝ window) (cap : ℝ)
    (M r : ℕ) (record : Fin (2 * r + 1) → Fin M × R) :
    convolutionCounterActivation patch filter cap M (convolutionMedianLabel patch filter cap M r record) =
      convolutionMedianActivation patch filter cap M r record :=
  Classical.choose_spec (exists_convolution_median_label patch filter cap M r record)

/-- Exchange the blank label with the label computed from a source coordinate. -/
def writeMedianActivationLabel {J : Type} {M : ℕ} (label : J → Fin M) (blank : Fin M) (p : J × Fin M) : J × Fin M :=
  (p.1, Equiv.swap blank (label p.1) p.2)

/-- The controlled label write is a reversible basis operation. -/
private theorem write_label_involutive {J : Type} {M : ℕ} (label : J → Fin M) (blank : Fin M) :
    Function.Involutive (writeMedianActivationLabel label blank) := by
  rintro ⟨j, z⟩
  change (j, ((Equiv.swap blank (label j)).trans (Equiv.swap blank (label j))) z) = (j, z)
  rw [Equiv.swap_swap]
  rfl

/-- Recording a median label is a unitary permutation of the source and label basis. -/
theorem write_median_label_unitary {J : Type} [Fintype J] [DecidableEq J] {M : ℕ}
    (label : J → Fin M) (blank : Fin M) :
    permMatrix (writeMedianActivationLabel label blank) ∈ Matrix.unitaryGroup (J × Fin M) ℂ :=
  permMatrix_unitary (write_label_involutive label blank)

/-- A label written into a clean register preserves each source amplitude at its assigned label. -/
private theorem write_label_amplitude {J : Type} [Fintype J] {M : ℕ}
    (label : J → Fin M) (blank : Fin M) (ψ : QState J) (j : J) (z : Fin M) :
    ApplyGate (permMatrix (writeMedianActivationLabel label blank)) (TensorState ψ (Ket blank)) (j, z) =
      if z = label j then ψ j else 0 := by
  rw [applyGate_permMatrix (write_label_involutive label blank)]
  have hLabel : Equiv.swap blank (label j) z = blank ↔ z = label j := by
    constructor
    · intro h
      apply (Equiv.swap blank (label j)).injective
      simpa only [Equiv.swap_apply_right] using h
    · rintro rfl
      exact Equiv.swap_apply_right _ _
  simp [writeMedianActivationLabel, TensorState, ket_apply, hLabel, mul_ite]

/-- One record holds the counter, mark flag and signal of every repeated estimate. -/
abbrev ConvolutionMedianRecord (window M r : ℕ) := Fin (2 * r + 1) → Fin M × (Bool × (Bool × Reg window))

/-- The finite label written for each addressed history. -/
def convolutionMedianLabelMap (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M r : ℕ) (p : (Address positions × Filter) × ConvolutionMedianRecord window M r) : Fin M :=
  convolutionMedianLabel (patchTree memory p.1.1) (filters p.1.2) cap M r p.2

/-- The flag weight is the activation decoded from the written label, divided by its cap. -/
def convolutionMedianFlagWeight (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M r : ℕ) (p : ((Address positions × Filter) × ConvolutionMedianRecord window M r) × Fin M) : ℝ :=
  convolutionCounterActivation (patchTree memory p.1.1.1) (filters p.1.1.2) cap M p.2 / cap

/-- The addressed repeated estimates before the median label and sampling flag are written. -/
def convolutionMedianCounters (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (M : ℕ) (hM : 0 < M) (r : ℕ) (α : QState (Address positions × Filter)) :
    QState ((Address positions × Filter) × ConvolutionMedianRecord window M r) :=
  addressedAERepeatedOutput (2 * r + 1) M hM
    (fun a => convolutionPreparation (patchTree memory a.1) (filters a.2)) (false, ZeroStr window)
    (fun _ => differenceOutcomes window) α

/-- Write the median label, then rotate the sampling flag using the labelled activation. -/
def convolutionMedianFlagOutput (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ) (α : QState (Address positions × Filter)) :
    QState ((((Address positions × Filter) × ConvolutionMedianRecord window M r) × Fin M) × Bool) :=
  let label := convolutionMedianLabelMap memory filters cap M r
  let blank : Fin M := ⟨0, hM⟩
  let labelled := ApplyGate (permMatrix (writeMedianActivationLabel label blank))
    (TensorState (convolutionMedianCounters memory filters M hM r α) (Ket blank))
  ApplyGate (activationFlagGate (convolutionMedianFlagWeight memory filters cap M r))
    (TensorState labelled (Ket false))

set_option maxHeartbeats 800000 in
/-- The median sampler preserves normalization for valid trees and a positive cap. -/
theorem convolution_median_flag_normalized [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (cap : ℝ) (hCap : 0 < cap)
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter)) (hα : Normalized α) :
    Normalized (convolutionMedianFlagOutput memory filters cap M (by omega) r α) := by
  unfold convolutionMedianFlagOutput
  apply normalized_applyGate
  · apply activation_flag_gate_unitary
    intro p
    unfold convolutionMedianFlagWeight
    refine ⟨div_nonneg (capped_relu_nonneg _ _) hCap.le, (div_le_one hCap).mpr ?_⟩
    exact max_le hCap.le (min_le_left _ _)
  apply normalized_tensorState _ (normalized_ket false)
  apply normalized_applyGate (permMatrix_unitary (write_label_involutive _ _))
  apply normalized_tensorState _ (normalized_ket _)
  unfold convolutionMedianCounters
  apply addressed_ae_repeated_output_normalized _ M hM _ _ _ _ α hα
  intro a
  exact convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)

/-- The activation-weighted mass of an event on the address and its written median label. -/
def convolutionMedianActivationMass (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ) (α : QState (Address positions × Filter))
    (event : (Address positions × Filter) → Fin M → Prop) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => event p.1
      (convolutionMedianLabel (patchTree memory p.1.1) (filters p.1.2) cap M r p.2)),
    convolutionMedianActivation (patchTree memory p.1.1) (filters p.1.2) cap M r p.2 *
      BornProb (convolutionMedianCounters memory filters M hM r α) p

set_option maxHeartbeats 800000 in
/-- The event on retained coordinates in the layout used for the flag rotation. -/
def medianFlagEvent {C R Z : Type} [Fintype C] [Fintype R] [Fintype Z]
    (event : C → Z → Bool → Prop) : Finset (((C × R) × Z) × Bool) :=
  Finset.univ.filter fun p => event p.1.1.1 p.1.2 p.2

/-- Joint measurement of the good flag, address and written label is weighted by the actual
median activation divided by the cap. -/
theorem convolution_median_flag_probability (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 0 < M) (r : ℕ)
    (α : QState (Address positions × Filter)) (event : (Address positions × Filter) → Fin M → Prop) :
    MeasureProb (convolutionMedianFlagOutput memory filters cap M hM r α)
      (medianFlagEvent (fun a z b => b = false ∧ event a z)) =
      convolutionMedianActivationMass memory filters cap M hM r α event / cap := by
  let J := (Address positions × Filter) × ConvolutionMedianRecord window M r
  let label (p : J) := convolutionMedianLabel (patchTree memory p.1.1) (filters p.1.2) cap M r p.2
  let blank : Fin M := ⟨0, hM⟩
  let counters := convolutionMedianCounters memory filters M hM r α
  let labelled := ApplyGate (permMatrix (writeMedianActivationLabel label blank)) (TensorState counters (Ket blank))
  let f (a : Address positions × Filter) := convolutionCounterActivation (patchTree memory a.1) (filters a.2) cap M
  let weight (p : J × Fin M) := f p.1.1 p.2 / cap
  have hFlag := activation_flag_event weight (fun p => div_nonneg (capped_relu_nonneg cap _) hCap.le)
    labelled (fun p => event p.1.1 p.2)
  have hEvent : medianFlagEvent (R := ConvolutionMedianRecord window M r) (fun a z b => b = false ∧ event a z) =
      Finset.univ.filter (fun p => p.2 = false ∧ event p.1.1.1 p.1.2) := by
    ext p
    simp [medianFlagEvent]
  unfold convolutionMedianFlagOutput convolutionMedianLabelMap convolutionMedianFlagWeight
  rw [hEvent, hFlag, Finset.sum_filter, Fintype.sum_prod_type]
  unfold convolutionMedianActivationMass
  rw [Finset.sum_div, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  have hLabelled (z : Fin M) : BornProb labelled (p, z) =
      (if z = label p then BornProb counters p else 0) := by
    unfold BornProb labelled
    rw [write_label_amplitude]
    split_ifs <;> simp
  calc
    _ = ∑ z : Fin M, if z = label p then
          (if event p.1 z then weight (p, z) * BornProb counters p else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      change (if event p.1 z then weight (p, z) * BornProb labelled (p, z) else 0) = _
      rw [hLabelled]
      by_cases hz : z = label p <;> simp [hz]
    _ = _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, weight, f, label, convolution_median_label_value]
      by_cases h : event p.1 (label p) <;> simp [counters, label, h, div_mul_eq_mul_div₀]

/-- Put the registers that will be measured next to each other. -/
def medianReadoutLayout (C R Z : Type) : (((C × R) × Z) × Bool) ≃ (((C × Z) × Bool) × R) where
  toFun p := (((p.1.1.1, p.1.2), p.2), p.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2), p.1.2)
  left_inv p := by rcases p with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl
  right_inv p := by rcases p with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

/-- The same event in the layout used for the reversed estimate. -/
def medianReadoutEvent {C R Z : Type} [Fintype C] [Fintype R] [Fintype Z]
    (event : C → Z → Bool → Prop) : Finset (((C × Z) × Bool) × R) :=
  Finset.univ.filter fun p => event p.1.1.1 p.1.1.2 p.1.2

/-- Reverse the actual repeated estimation on the history while preserving the written label
and flag at each address. -/
def convolutionMedianReverse (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (M r : ℕ) : Matrix ((((Address positions × Filter) × Fin M) × Bool) × ConvolutionMedianRecord window M r)
      ((((Address positions × Filter) × Fin M) × Bool) × ConvolutionMedianRecord window M r) ℂ :=
  blockDiagFirst fun kept => (Denote 1 (repeatedLocalAECircuit (2 * r + 1) M
    (convolutionPreparation (patchTree memory kept.1.1.1) (filters kept.1.1.2)) (false, ZeroStr window)
    (differenceOutcomes window)))ᴴ

omit [Fintype Filter] in
/-- Each controlled reverse block is the adjoint of the physical repeated estimate at its address. -/
private theorem convolution_median_reverse_block_unitary (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (a : Address positions × Filter) :
    (Denote 1 (repeatedLocalAECircuit (2 * r + 1) M
      (convolutionPreparation (patchTree memory a.1) (filters a.2)) (false, ZeroStr window)
      (differenceOutcomes window)))ᴴ ∈ Matrix.unitaryGroup (ConvolutionMedianRecord window M r) ℂ := by
  have hA := convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  have hAdj := Unitary.star_mem
    (repeated_local_ae_gate_unitary (2 * r + 1) M hM _ (false, ZeroStr window) (differenceOutcomes window) hA)
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff'] at hAdj
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at hAdj
  calc
    _ = _ := hAdj
    _ = _ := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]

set_option maxHeartbeats 800000 in
/-- All retained coordinates control unitary reverse operations on the estimation history. -/
theorem convolution_median_reverse_unitary [DecidableEq Filter] (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) :
    convolutionMedianReverse memory filters M r ∈
      Matrix.unitaryGroup ((((Address positions × Filter) × Fin M) × Bool) × ConvolutionMedianRecord window M r) ℂ := by
  let K := ((Address positions × Filter) × Fin M) × Bool
  let R := ConvolutionMedianRecord window M r
  let V (kept : K) : Matrix R R ℂ :=
    (Denote 1 (repeatedLocalAECircuit (2 * r + 1) M
      (convolutionPreparation (patchTree memory kept.1.1.1) (filters kept.1.1.2)) (false, ZeroStr window)
      (differenceOutcomes window)))ᴴ
  have hV (kept : K) : V kept ∈ Matrix.unitaryGroup R ℂ :=
    convolution_median_reverse_block_unitary memory filters hMemory hFilters M hM r kept.1.1
  exact unitary_with_decidable_eq (@blockDiagFirst_unitary K R inferInstance inferInstance inferInstance inferInstance V hV)

/-- The final median sampler runs the reversed estimator before measurement. -/
def convolutionMedianReadout (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (cap : ℝ) (M : ℕ) (hM : 0 < M) (r : ℕ) (α : QState (Address positions × Filter)) :
    QState ((((Address positions × Filter) × Fin M) × Bool) × ConvolutionMedianRecord window M r) :=
  ApplyGate (convolutionMedianReverse memory filters M r)
    (relabelState (medianReadoutLayout _ _ _) (convolutionMedianFlagOutput memory filters cap M hM r α))

/-- Unitary work inside each retained coordinate preserves every event that tests only
the retained coordinates. -/
private theorem block_diagonal_event_probability {K W : Type} [Fintype K] [Fintype W] [DecidableEq W]
    (V : K → Matrix W W ℂ) (hV : ∀ k, V k ∈ Matrix.unitaryGroup W ℂ) (ψ : QState (K × W))
    (event : K → Prop) :
    MeasureProb (ApplyGate (blockDiagFirst V) ψ) (Finset.univ.filter fun p => event p.1) =
      MeasureProb ψ (Finset.univ.filter fun p => event p.1) := by
  simp only [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : event k
  · simp only [hk, ite_true]
    have hNorm := congrArg (fun x : ℝ => x ^ 2)
      (norm_applyGate_of_mem_unitaryGroup (hV k) (fun w => ψ (k, w)))
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq] at hNorm
    simpa only [BornProb, applyGate_blockDiagFirst_slice] using hNorm
  · simp [hk]

/-- The joint readout law of address, median label and activation flag survives the
physical reversal of the estimation work. -/
theorem convolution_median_readout_event (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (cap : ℝ)
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter))
    (event : (Address positions × Filter) → Fin M → Bool → Prop) :
    MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r α)
      (medianReadoutEvent event) =
    MeasureProb (convolutionMedianFlagOutput memory filters cap M (by omega) r α)
      (medianFlagEvent event) := by
  let e := medianReadoutLayout (Address positions × Filter) (ConvolutionMedianRecord window M r) (Fin M)
  let out := convolutionMedianFlagOutput memory filters cap M (by omega) r α
  let before : Finset ((((Address positions × Filter) × ConvolutionMedianRecord window M r) × Fin M) × Bool) :=
    medianFlagEvent event
  let after : Finset ((((Address positions × Filter) × Fin M) × Bool) × ConvolutionMedianRecord window M r) :=
    medianReadoutEvent event
  let V (kept : ((Address positions × Filter) × Fin M) × Bool) :=
    (Denote 1 (repeatedLocalAECircuit (2 * r + 1) M
      (convolutionPreparation (patchTree memory kept.1.1.1) (filters kept.1.1.2)) (false, ZeroStr window)
      (differenceOutcomes window)))ᴴ
  have hV (kept : ((Address positions × Filter) × Fin M) × Bool) : V kept ∈ Matrix.unitaryGroup _ ℂ :=
    convolution_median_reverse_block_unitary memory filters hMemory hFilters M hM r kept.1.1
  have hMap : before.map e.toEmbedding = after := by
    unfold before after medianFlagEvent medianReadoutEvent
    rw [Finset.map_filter, Finset.map_univ_equiv]
    rfl
  change MeasureProb (ApplyGate (blockDiagFirst V) (relabelState e out)) after = MeasureProb out before
  rw [show MeasureProb (ApplyGate (blockDiagFirst V) (relabelState e out)) after =
    MeasureProb (relabelState e out) after from
    block_diagonal_event_probability V hV _ (fun k => event k.1.1 k.1.2 k.2)]
  rw [← hMap, measureProb_relabelState]

/-- The reversed estimator preserves normalization of the median sampler. -/
theorem convolution_median_readout_normalized [DecidableEq Filter]
    (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f)) (cap : ℝ) (hCap : 0 < cap)
    (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter)) (hα : Normalized α) :
    Normalized (convolutionMedianReadout memory filters cap M (by omega) r α) := by
  have hRead := convolution_median_readout_event memory filters hMemory hFilters cap M hM r α (fun _ _ _ => True)
  have hFlag := convolution_median_flag_normalized memory filters hMemory hFilters cap hCap M hM r α hα
  change MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r α) Finset.univ = 1
  have hEq : MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r α) Finset.univ =
      MeasureProb (convolutionMedianFlagOutput memory filters cap M (by omega) r α) Finset.univ := by
    simpa [medianReadoutEvent, medianFlagEvent] using hRead
  exact hEq.trans hFlag

/-- The final sampler's postselected address and activation label have the exact
median-activation-weighted law. -/
theorem convolution_median_readout_postselect (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (hCap : 0 < cap) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter))
    (event : (Address positions × Filter) → Fin M → Prop)
    (hMass : 0 < convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True)) :
    let out := convolutionMedianReadout memory filters cap M (by omega) r α
    let good := medianReadoutEvent (R := ConvolutionMedianRecord window M r) (Z := Fin M)
      (fun (_ : Address positions × Filter) _ b => b = false)
    0 < MeasureProb out good ∧
      MeasureProb (PostMeasure out good) (Finset.univ.filter fun p => event p.1.1.1 p.1.1.2) =
        convolutionMedianActivationMass memory filters cap M (by omega) r α event /
          convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True) := by
  dsimp only
  have hRead := convolution_median_readout_event memory filters hMemory hFilters cap M hM r α
  have hTotal : MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r α)
      (medianReadoutEvent (fun _ _ b => b = false)) =
      convolutionMedianActivationMass memory filters cap M (by omega) r α (fun _ _ => True) / cap := by
    rw [hRead (fun _ _ b => b = false)]
    simpa only [and_true] using convolution_median_flag_probability memory filters cap hCap M (by omega) r α
      (fun _ _ => True)
  have hPos : 0 < MeasureProb (convolutionMedianReadout memory filters cap M (by omega) r α)
      (medianReadoutEvent (fun _ _ b => b = false)) := by rw [hTotal]; exact div_pos hMass hCap
  refine ⟨hPos, ?_⟩
  rw [measureProb_postMeasure hPos, hTotal]
  have hIntersection : medianReadoutEvent (R := ConvolutionMedianRecord window M r) (Z := Fin M)
      (fun (_ : Address positions × Filter) _ b => b = false) ∩
      (Finset.univ.filter fun p => event p.1.1.1 p.1.1.2) =
      medianReadoutEvent (fun a z b => b = false ∧ event a z) := by
    ext p
    simp [medianReadoutEvent]
  rw [hIntersection, hRead (fun a z b => b = false ∧ event a z)]
  rw [show MeasureProb (convolutionMedianFlagOutput memory filters cap M (by omega) r α)
      (medianFlagEvent (fun a z b => b = false ∧ event a z)) = _ from
    convolution_median_flag_probability memory filters cap hCap M (by omega) r α event]
  exact div_div_div_cancel_right₀ hCap.ne' _ _

end Qatlib.Papers.QCNN20.Forward
