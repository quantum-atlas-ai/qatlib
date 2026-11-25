/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.CoherentPreparation
public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Foundations.BornMetrics.EventProbability

@[expose] public section

/-!
# Address-controlled prepared amplitude estimation

[KerenidisLandmanPrakash2020], Algorithm 1 and Section D.1.1, estimate
patch–filter interference in superposition. Each instruction in the
counted BHMT word is executed with a preserved address register. The
address chooses the preparation and marking matrices. The joint Born law
weights the exact local counter laws by the input address masses. The
ledger counts the addressed operations, with the cost of implementing
each addressed matrix left to its access model.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.QueryWords (InstMat run_denote)
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedMark prepared_aa_reflection_and_access)
open Qatlib.Concepts.LocalMachine.LocalTransport (controlOracle_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_smul)
open scoped BigOperators Classical

variable {C I : Type} [Fintype I] [DecidableEq I]

/-- Interpret an AE instruction with its preparation controlled by the address. -/
def addressedAEInstruction (M : ℕ) (A : C → Matrix I I ℂ) (seed : I) :
    AEAccessStep (Fin M × (Bool × I)) → Step (C × (Fin M × (Bool × I)))
  | .mark => .query
  | s => .gate (blockDiagFirst (fun c => InstMat 1 (aeAccessInstruction M (A c) seed s)))

/-- The counted AE word, with each operation executed coherently across all addresses. -/
def addressedAECircuit (M : ℕ) (A : C → Matrix I I ℂ) (seed : I) :
    Circuit (C × (Fin M × (Bool × I))) :=
  (aeAccessWord (I := I) M).map (addressedAEInstruction M A seed)

/-- The address selects the marked event without changing the address register. -/
def addressedAEMark (M : ℕ) (marked : C → Finset I) :
    Matrix (C × (Fin M × (Bool × I))) (C × (Fin M × (Bool × I))) ℂ :=
  blockDiagFirst (fun c => aeControlledGate M (preparedMark (marked c)))

/-- Every slice of the addressed run executes the local word for its address. -/
private theorem run_addressed_ae_word_slice [Fintype C] (M : ℕ) (A : C → Matrix I I ℂ)
    (seed : I) (marked : C → Finset I) (word : List (AEAccessStep (Fin M × (Bool × I))))
    (ψ : QState (C × (Fin M × (Bool × I)))) (c : C) :
    (fun p => Run (addressedAEMark M marked) (word.map (addressedAEInstruction M A seed)) ψ (c, p)) =
      Run (aeControlledGate M (preparedMark (marked c))) (word.map (aeAccessInstruction M (A c) seed))
        (fun p => ψ (c, p)) := by
  induction word generalizing ψ with
  | nil => rfl
  | cons s word ih =>
    cases s <;> simp only [List.map_cons, addressedAEInstruction, aeAccessInstruction, InstMat, Run] <;>
      rw [ih] <;> simp [addressedAEMark, applyGate_blockDiagFirst_slice]

omit [Fintype I] in
/-- The addressed word has the same number of queries and gates as any local instance. -/
private theorem addressed_ae_word_counts (M : ℕ) (A : C → Matrix I I ℂ) (V : Matrix I I ℂ)
    (seed : I) (word : List (AEAccessStep (Fin M × (Bool × I)))) :
    QueryCount (word.map (addressedAEInstruction M A seed)) = QueryCount (word.map (aeAccessInstruction M V seed)) ∧
    GateCount (word.map (addressedAEInstruction M A seed)) = GateCount (word.map (aeAccessInstruction M V seed)) := by
  induction word with
  | nil => simp
  | cons s word ih => cases s <;> simp [addressedAEInstruction, aeAccessInstruction, ih.1, ih.2]

/-- The counts of the addressed word are independent of the number of addresses. -/
theorem addressed_ae_counts (M : ℕ) (hM : 0 < M) (A : C → Matrix I I ℂ) (seed : I) :
    QueryCount (addressedAECircuit M A seed) = M - 1 ∧
      GateCount (addressedAECircuit M A seed) = 5 * (M - 1) + 3 := by
  have h := addressed_ae_word_counts M A (1 : Matrix I I ℂ) seed (aeAccessWord M)
  have hc := prepared_ae_access_ledger M hM (1 : Matrix I I ℂ) seed
  exact ⟨h.1.trans hc.1, h.2.trans hc.2.1⟩

/-- The addressed AE word consists of unitary gates for unitary local preparations. -/
theorem addressed_ae_circuit_unitary [Fintype C] [DecidableEq C] (M : ℕ) (hM : 2 ≤ M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I)
    (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ) : IsUnitaryCircuit (addressedAECircuit M A seed) := by
  have hLocal (c : C) : IsUnitaryCircuit (countedAECircuit M (A c) seed) :=
    (prepared_ae_expanded_access_and_output M hM (A c) seed (marked c) (hA c)).2.2.1
  intro U hU
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hU
  cases s <;> simp only [addressedAEInstruction, aeAccessInstruction, InstMat, Step.gate.injEq,
    reduceCtorEq] at he
  all_goals
    rw [← he]
    apply blockDiagFirst_unitary
    intro c
    apply hLocal c
    exact List.mem_map.mpr ⟨_, hs, rfl⟩

/-- The address-controlled marking operation is unitary. -/
theorem addressed_ae_mark_unitary [Fintype C] [DecidableEq C] (M : ℕ)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I)
    (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ) :
    addressedAEMark M marked ∈ Matrix.unitaryGroup (C × (Fin M × (Bool × I))) ℂ := by
  apply blockDiagFirst_unitary
  intro c
  exact tensorGate_unitary (Matrix.unitaryGroup (Fin M) ℂ).one_mem
    (controlOracle_unitary (prepared_aa_reflection_and_access (A c) seed (marked c) (hA c)).1)

/-- Run the controlled word with the counter, flag and local system initialized. -/
def addressedAEOutput [Fintype C] (M : ℕ) (hM : 0 < M) (A : C → Matrix I I ℂ)
    (seed : I) (marked : C → Finset I) (α : QState C) : QState (C × (Fin M × (Bool × I))) :=
  Run (addressedAEMark M marked) (addressedAECircuit M A seed)
    (TensorState α (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed))))

/-- The joint output is normalized for normalized address amplitudes. -/
theorem addressed_ae_output_normalized [Fintype C] [DecidableEq C] (M : ℕ) (hM : 2 ≤ M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ)
    (α : QState C) (hα : Normalized α) : Normalized (addressedAEOutput M (by omega) A seed marked α) :=
  (addressed_ae_circuit_unitary M hM A seed marked hA).normalized_run
    (addressed_ae_mark_unitary M A seed marked hA)
    (normalized_tensorState hα (normalized_tensorState (normalized_ket _)
      (normalized_tensorState (normalized_ket _) (normalized_ket _))))

/-- The joint output retains the input address amplitude coherently in every slice. -/
theorem addressed_ae_output_slice [Fintype C] (M : ℕ) (hM : 0 < M) (A : C → Matrix I I ℂ)
    (seed : I) (marked : C → Finset I) (α : QState C) (c : C) :
    (fun p => addressedAEOutput M hM A seed marked α (c, p)) =
      α c • Run (aeControlledGate M (preparedMark (marked c))) (countedAECircuit M (A c) seed)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed))) := by
  let input := TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed))
  let oracle := aeControlledGate M (preparedMark (marked c))
  let word := countedAECircuit M (A c) seed
  calc
    _ = Run oracle word (α c • input) :=
      run_addressed_ae_word_slice M A seed marked (aeAccessWord M) (TensorState α input) c
    _ = α c • Run oracle word input := by
      rw [run_denote, run_denote]
      simp only [ApplyGate, Matrix.mulVec_smul]

/-- The probability of any joint address and counter event is the weighted sum of the
corresponding local events. -/
theorem addressed_ae_event_probability [Fintype C] (M : ℕ) (hM : 2 ≤ M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ)
    (α : QState C) (event : C → Fin M → Prop) :
    MeasureProb (addressedAEOutput M (by omega) A seed marked α)
      (Finset.univ.filter fun p => event p.1 p.2.1) =
      ∑ c, ‖α c‖ ^ 2 * ∑ z ∈ Finset.univ.filter (event c), (aeLaw M (A c) seed (marked c) (hA c) hM).prob z := by
  let out := addressedAEOutput M (by omega) A seed marked α
  change MeasureProb out _ = _
  rw [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ p, if event c p.1 then BornProb (fun p => out (c, p)) p else 0) = _
  rw [← Finset.sum_filter, ← MeasureProb, addressed_ae_output_slice, measureProb_smul,
    ← aeLaw_event M hM (A c) seed (marked c) (hA c) (event c)]

/-- The counter circuit preserves each address's marginal probability. -/
theorem addressed_ae_address_probability [Fintype C] (M : ℕ) (hM : 2 ≤ M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ)
    (α : QState C) (address : C) :
    MeasureProb (addressedAEOutput M (by omega) A seed marked α)
      (Finset.univ.filter fun p => p.1 = address) = ‖α address‖ ^ 2 := by
  rw [addressed_ae_event_probability M hM A seed marked hA α (fun c _ => c = address)]
  have hTerm (c : C) :
      ‖α c‖ ^ 2 * (∑ z ∈ Finset.univ.filter (fun _ : Fin M => c = address),
        (aeLaw M (A c) seed (marked c) (hA c) hM).prob z) =
      if c = address then ‖α c‖ ^ 2 else 0 := by
    by_cases hc : c = address
    · simp [hc, (aeLaw M (A address) seed (marked address) (hA address) hM).sum_one]
    · simp [hc]
  simp_rw [hTerm]
  simp

/-- The inner AE flag is clean even when the preparation is coherently addressed. -/
theorem addressed_ae_clean_flag [Fintype C] (M : ℕ) (hM : 2 ≤ M) (A : C → Matrix I I ℂ)
    (seed : I) (marked : C → Finset I) (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ)
    (α : QState C) (c : C) (z : Fin M) (i : I) :
    addressedAEOutput M (by omega) A seed marked α (c, (z, (true, i))) = 0 := by
  let hPos : 0 < M := by omega
  have hs := congrFun (addressed_ae_output_slice M hPos A seed marked α c) (z, (true, i))
  have hZero : Run (aeControlledGate M (preparedMark (marked c))) (countedAECircuit M (A c) seed)
      (TensorState (Ket (⟨0, hPos⟩ : Fin M)) (TensorState (Ket false) (Ket seed))) (z, (true, i)) = 0 :=
    (prepared_ae_expanded_access_and_output M hM (A c) seed (marked c) (hA c)).2.2.2.2.2 z i
  change addressedAEOutput M hPos A seed marked α (c, (z, (true, i))) = 0
  rw [hs, Pi.smul_apply, hZero, smul_zero]

/-- The expectation of any real weight on the address and counter factors through
the exact local counter laws. -/
theorem addressed_ae_weighted_probability [Fintype C] (M : ℕ) (hM : 2 ≤ M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ)
    (α : QState C) (weight : C → Fin M → ℝ) :
    (∑ p, weight p.1 p.2.1 * BornProb (addressedAEOutput M (by omega) A seed marked α) p) =
      ∑ c, ‖α c‖ ^ 2 * ∑ z, weight c z * (aeLaw M (A c) seed (marked c) (hA c) hM).prob z := by
  let hPos : 0 < M := by omega
  let out := addressedAEOutput M hPos A seed marked α
  have hCell (c : C) (z : Fin M) : (∑ r : Bool × I, BornProb out (c, (z, r))) =
      ‖α c‖ ^ 2 * (aeLaw M (A c) seed (marked c) (hA c) hM).prob z := by
    let ψ := Run (aeControlledGate M (preparedMark (marked c))) (countedAECircuit M (A c) seed)
      (TensorState (Ket (⟨0, hPos⟩ : Fin M)) (TensorState (Ket false) (Ket seed)))
    have hAmp (r : Bool × I) : out (c, (z, r)) = α c * ψ (z, r) :=
      congrFun (addressed_ae_output_slice M hPos A seed marked α c) (z, r)
    have hLaw : (aeLaw M (A c) seed (marked c) (hA c) hM).prob z =
        MeasureProb ψ (Finset.univ.filter fun p => p.1 = z) := rfl
    have hEvent : (Finset.univ.filter fun p : Fin M × (Bool × I) => p.1 = z) =
        {z} ×ˢ (Finset.univ : Finset (Bool × I)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_singleton,
        true_and, and_true]
    simp_rw [BornProb, hAmp, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hLaw, hEvent, MeasureProb, Finset.sum_product, Finset.sum_singleton]
    rfl
  change (∑ p, weight p.1 p.2.1 * BornProb out p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ r : Bool × I, weight c z * BornProb out (c, (z, r))) = _
  rw [← Finset.mul_sum, hCell]
  ring

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- The actual coherently addressed convolution counter output on a superposition
of locations and filters. -/
def convolutionAEOutput (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (M : ℕ) (hM : 0 < M) (α : QState (Address positions × Filter)) :
    QState ((Address positions × Filter) × (Fin M × (Bool × (Bool × Address window)))) :=
  addressedAEOutput M hM (fun a => convolutionPreparation (patchTree memory a.1) (filters a.2))
    (false, ZeroStr window) (fun _ => differenceOutcomes window) α

/-- The rescaled BHMT radius for the capped activation of a patch and a filter. -/
def convolutionActivationRadius (patch filter : Tree ℝ window) (M : ℕ) : ℝ :=
  let a := differenceWeight patch filter
  2 * (Real.sqrt (mass patch) * Real.sqrt (mass filter)) *
    (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2)

/-- Reconstruct and clip the activation at a particular counter label. -/
def convolutionCounterActivation (patch filter : Tree ℝ window) (cap : ℝ) (M : ℕ) (z : Fin M) : ℝ :=
  cappedRelu cap (estimateFromDifferenceWeight patch filter (aeEstimate M z))

/-- A label gives an accurate capped activation when its reconstructed convolution
is within the rescaled BHMT error. -/
def convolutionCounterAccurate (patch filter : Tree ℝ window) (cap : ℝ) (M : ℕ) (label : Fin M) : Prop :=
  |convolutionCounterActivation patch filter cap M label -
    cappedRelu cap (convolutionEntry patch filter)| ≤ convolutionActivationRadius patch filter M

/-- The coherent counter circuit yields an accurate capped activation with the BHMT
probability for any normalized superposition of patch–filter addresses. Zero-mass
inputs are included because their rescaled activations are exact. -/
theorem convolution_ae_activation_success (memory : Tree ℝ (window + positions)) (filters : Filter → Tree ℝ window)
    (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (M : ℕ) (hM : 2 ≤ M) (α : QState (Address positions × Filter)) (hα : Normalized α) :
    8 / Real.pi ^ 2 ≤
      MeasureProb (convolutionAEOutput memory filters M (by omega) α)
        (Finset.univ.filter fun p =>
          convolutionCounterAccurate (patchTree memory p.1.1) (filters p.1.2) cap M p.2.1) := by
  let A (a : Address positions × Filter) := convolutionPreparation (patchTree memory a.1) (filters a.2)
  let S : Address positions × Filter → Finset (Bool × Address window) := fun _ => differenceOutcomes window
  let event (a : Address positions × Filter) :=
    convolutionCounterAccurate (patchTree memory a.1) (filters a.2) cap M
  have hA (a : Address positions × Filter) : A a ∈ Matrix.unitaryGroup (Bool × Address window) ℂ :=
    convolution_preparation_unitary _ _ (valid_subtree positions memory a.1 hMemory) (hFilters a.2)
  change 8 / Real.pi ^ 2 ≤ MeasureProb (addressedAEOutput M (by omega) A (false, ZeroStr window) S α)
    (Finset.univ.filter fun p => event p.1 p.2.1)
  rw [addressed_ae_event_probability M hM A (false, ZeroStr window) S hA α event]
  calc
    _ = ∑ a : Address positions × Filter, ‖α a‖ ^ 2 * (8 / Real.pi ^ 2) := by
      have hSum : ∑ a, ‖α a‖ ^ 2 = 1 := hα
      rw [← Finset.sum_mul, hSum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (qram_convolution_estimation_success _ _ (valid_subtree positions memory a.1 hMemory)
          (hFilters a.2) cap M hM) (sq_nonneg _)

end Qatlib.Papers.QCNN20.Forward
