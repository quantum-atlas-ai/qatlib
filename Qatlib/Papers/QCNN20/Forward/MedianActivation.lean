/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCNN20.Forward.AddressedAmplitudeEstimation
public import Qatlib.Concepts.QueryComplexity.Amplification.ParallelCopies
public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Coherent convolution median

[KerenidisLandmanPrakash2020], Section D.1.1 and Appendix F, use median
estimation in superposition. Repeat the actual prepared AE word on fresh
workspaces while preserving the address. The median is applied to decoded
and clipped real activations. The error analysis uses the product law only
within each fixed address. The computation of the real median and its
finite-word implementation are separate.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCNN20.Forward

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.QueryWords (Denote InstMat denote_unitary run_denote)
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean (mass_complement sorted_median_failure)
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LchsSimulation.StaticLchs (preparedMark prepared_aa_reflection_and_access)
open Qatlib.Concepts.LocalMachine.LocalTransport (controlOracle_unitary)
open Qatlib.Concepts.QsvtCore.PhaseExistence (blockDiagFirst blockDiagFirst_unitary)
open Qatlib.Concepts.QRAM.AmplitudeAccess (applyGate_blockDiagFirst_slice)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass valid_subtree)
open Qatlib.Papers.QCNN20.PatchMemory (patchTree)
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_smul)
open scoped BigOperators Classical

variable {C I : Type} [Fintype I] [DecidableEq I]

/-- Resolve a word's marking instruction to the actual local marking matrix. -/
def resolveMark {R : Type} (O : Matrix R R ℂ) (word : Circuit R) : Circuit R :=
  word.map (fun s => Step.gate (InstMat O s))

/-- The resolved word has no unresolved calls and has one gate per original instruction. -/
private theorem resolve_mark_counts {R : Type} (O : Matrix R R ℂ) (word : Circuit R) :
    QueryCount (resolveMark O word) = 0 ∧
      GateCount (resolveMark O word) = GateCount word + QueryCount word := by
  induction word with
  | nil => simp [resolveMark]
  | cons s word ih =>
    cases s <;> simp [resolveMark] at ih ⊢ <;> omega

/-- Running the resolved word applies exactly the original gates and marking calls. -/
private theorem run_resolve_mark {R : Type} [Fintype R]
    (O O' : Matrix R R ℂ) (word : Circuit R) (ψ : QState R) :
    Run O' (resolveMark O word) ψ = Run O word ψ := by
  induction word generalizing ψ with
  | nil => rfl
  | cons s word ih =>
    cases s <;> simp only [resolveMark, List.map_cons, InstMat, run_gate, run_query] <;> exact ih _

/-- Every resolved instruction is unitary when the underlying word and its mark are unitary. -/
private theorem isUnitaryCircuit_resolve_mark {R : Type} [Fintype R] [DecidableEq R]
    (O : Matrix R R ℂ) (word : Circuit R) (hO : O ∈ Matrix.unitaryGroup R ℂ) (hw : IsUnitaryCircuit word) :
    IsUnitaryCircuit (resolveMark O word) := by
  intro U hU
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hU
  have hGate : InstMat O s = U := Step.gate.inj he
  rw [← hGate]
  cases s with
  | gate V => exact hw V hs
  | query => exact hO

/-- Execute the local counted AE word on one fresh counter and signal workspace. -/
def localCounterOutput (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (seed : I) (marked : Finset I) :
    QState (Fin M × (Bool × I)) :=
  Run (aeControlledGate M (preparedMark marked)) (countedAECircuit M A seed)
    (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed)))

/-- Resolve the marking matrices and route each instruction to its own copy's workspace. -/
def repeatedLocalAECircuit (n M : ℕ) (A : Matrix I I ℂ) (seed : I) (marked : Finset I) :
    Circuit (Fin n → Fin M × (Bool × I)) :=
  SeqCopiesCircuit n (resolveMark (aeControlledGate M (preparedMark marked)) (countedAECircuit M A seed))

/-- Each repeated workspace uses all explicit instructions and marking calls of one AE word. -/
theorem repeated_local_ae_counts (n M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (seed : I) (marked : Finset I) :
    QueryCount (repeatedLocalAECircuit n M A seed marked) = 0 ∧
      GateCount (repeatedLocalAECircuit n M A seed marked) = n * (6 * (M - 1) + 3) := by
  let O := aeControlledGate M (preparedMark marked)
  let word := countedAECircuit M A seed
  have h := resolve_mark_counts O word
  have hAE := prepared_ae_access_ledger M hM A seed
  have hCount : 5 * (M - 1) + 3 + (M - 1) = 6 * (M - 1) + 3 := by omega
  unfold repeatedLocalAECircuit
  rw [queryCount_seqCopiesCircuit, gateCount_seqCopiesCircuit, h.1, h.2, hAE.1, hAE.2.1, hCount, mul_zero]
  exact ⟨rfl, rfl⟩

/-- Repeat the counted AE word on distinct workspaces, controlled by a common address. -/
def addressedAERepeatedGate (n M : ℕ) (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) :
    Matrix (C × (Fin n → Fin M × (Bool × I))) (C × (Fin n → Fin M × (Bool × I))) ℂ :=
  blockDiagFirst fun c => Denote 1 (repeatedLocalAECircuit n M (A c) seed (marked c))

/-- The local sequence on fresh workspaces is unitary for a unitary preparation. -/
theorem repeated_local_ae_gate_unitary (n M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (seed : I) (marked : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Denote 1 (repeatedLocalAECircuit n M A seed marked) ∈
      Matrix.unitaryGroup (Fin n → Fin M × (Bool × I)) ℂ := by
  apply denote_unitary 1 (Submonoid.one_mem _)
  apply isUnitaryCircuit_seqCopiesCircuit
  apply isUnitaryCircuit_resolve_mark
  · exact tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (prepared_aa_reflection_and_access A seed marked hA).1)
  · exact (prepared_ae_expanded_access_and_output M hM A seed marked hA).2.2.1

/-- The controlled repetition is unitary for unitary preparations. -/
theorem addressed_ae_repeated_gate_unitary [Fintype C] [DecidableEq C]
    (n M : ℕ) (hM : 2 ≤ M) (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I)
    (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ) :
    addressedAERepeatedGate n M A seed marked ∈ Matrix.unitaryGroup (C × (Fin n → Fin M × (Bool × I))) ℂ :=
  blockDiagFirst_unitary _ (fun c => repeated_local_ae_gate_unitary n M hM (A c) seed (marked c) (hA c))

/-- Apply the repeated word with all workspaces initialized and a coherent address input. -/
def addressedAERepeatedOutput [Fintype C] (n M : ℕ) (hM : 0 < M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (α : QState C) :
    QState (C × (Fin n → Fin M × (Bool × I))) :=
  ApplyGate (addressedAERepeatedGate n M A seed marked)
    (TensorState α (PiTensorState (fun _ : Fin n =>
      TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed)))))

/-- A normalized address input gives a normalized repeated output. -/
theorem addressed_ae_repeated_output_normalized [Fintype C] [DecidableEq C]
    (n M : ℕ) (hM : 2 ≤ M) (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I)
    (hA : ∀ c, A c ∈ Matrix.unitaryGroup I ℂ) (α : QState C) (hα : Normalized α) :
    Normalized (addressedAERepeatedOutput n M (by omega) A seed marked α) := by
  apply normalized_applyGate (addressed_ae_repeated_gate_unitary n M hM A seed marked hA)
  exact normalized_tensorState hα (normalized_piTensorState fun _ =>
    normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) (normalized_ket _)))

/-- Each address slice is the original address amplitude times the tensor product of its runs. -/
private theorem addressed_ae_repeated_output_slice [Fintype C] (n M : ℕ) (hM : 0 < M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (α : QState C) (c : C) :
    (fun y => addressedAERepeatedOutput n M hM A seed marked α (c, y)) =
      α c • PiTensorState (fun _ : Fin n => localCounterOutput M hM (A c) seed (marked c)) := by
  let input := TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket seed))
  let O := aeControlledGate M (preparedMark (marked c))
  let word := countedAECircuit M (A c) seed
  let copies := repeatedLocalAECircuit n M (A c) seed (marked c)
  have hRun : ApplyGate (Denote 1 copies) (PiTensorState (fun _ : Fin n => input)) =
      PiTensorState (fun _ : Fin n => localCounterOutput M hM (A c) seed (marked c)) := by
    rw [← run_denote]
    change Run 1 (SeqCopiesCircuit n (resolveMark O word)) (PiTensorState (fun _ : Fin n => input)) = _
    rw [run_seqCopiesCircuit_piTensorState _ _ (resolve_mark_counts O word).1]
    apply congrArg PiTensorState
    funext j
    exact run_resolve_mark O 1 word input
  funext y
  unfold addressedAERepeatedOutput addressedAERepeatedGate
  rw [applyGate_blockDiagFirst_slice]
  change (Denote 1 copies *ᵥ (α c • PiTensorState (fun _ : Fin n => input))) y = _
  rw [Matrix.mulVec_smul]
  change (α c • ApplyGate (Denote 1 copies) (PiTensorState (fun _ : Fin n => input))) y = _
  rw [hRun]

/-- The repeated output weights each local record's product probability by its address mass. -/
theorem addressed_ae_repeated_event_probability [Fintype C] (n M : ℕ) (hM : 0 < M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (α : QState C)
    (event : C → (Fin n → Fin M × (Bool × I)) → Prop) :
    MeasureProb (addressedAERepeatedOutput n M hM A seed marked α)
      (Finset.univ.filter fun p => event p.1 p.2) =
      ∑ c, ‖α c‖ ^ 2 *
        MeasureProb (PiTensorState (fun _ : Fin n => localCounterOutput M hM (A c) seed (marked c)))
          (Finset.univ.filter (event c)) := by
  rw [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ p, if event c p then BornProb
    (fun q => addressedAERepeatedOutput n M hM A seed marked α (c, q)) p else 0) = _
  rw [← Finset.sum_filter, ← MeasureProb, addressed_ae_repeated_output_slice, measureProb_smul]

/-- A weight on the address and repeated record averages over the product state at each address. -/
theorem addressed_ae_repeated_weighted_probability [Fintype C] (n M : ℕ) (hM : 0 < M)
    (A : C → Matrix I I ℂ) (seed : I) (marked : C → Finset I) (α : QState C)
    (weight : C → (Fin n → Fin M × (Bool × I)) → ℝ) :
    (∑ p, weight p.1 p.2 * BornProb (addressedAERepeatedOutput n M hM A seed marked α) p) =
      ∑ c, ‖α c‖ ^ 2 * ∑ record, weight c record *
        BornProb (PiTensorState (fun _ : Fin n => localCounterOutput M hM (A c) seed (marked c))) record := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro record _
  have hBorn : BornProb (addressedAERepeatedOutput n M hM A seed marked α) (c, record) =
      ‖α c‖ ^ 2 * BornProb (PiTensorState (fun _ : Fin n => localCounterOutput M hM (A c) seed (marked c))) record := by
    unfold BornProb
    rw [congrFun (addressed_ae_repeated_output_slice n M hM A seed marked α c) record,
      Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hBorn]
  ring

variable {positions window : ℕ} {Filter : Type} [Fintype Filter]

/-- Decode and clip each counter result before taking the median of the activations. -/
def convolutionMedianActivation {R : Type} (patch filter : Tree ℝ window) (cap : ℝ) (M r : ℕ)
    (record : Fin (2 * r + 1) → Fin M × R) : ℝ :=
  sortedBlockMedian r (fun j => convolutionCounterActivation patch filter cap M (record j).1)

/-- For one patch and filter, taking the median of decoded counter results suppresses
the probability of exceeding the same rescaled radius as the single-run estimate. -/
private theorem convolution_local_median_failure (patch filter : Tree ℝ window)
    (hp : Valid patch) (hf : Valid filter) (cap : ℝ) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) :
    MeasureProb (PiTensorState (fun _ : Fin (2 * r + 1) =>
      localCounterOutput M (by omega) (convolutionPreparation patch filter)
        (false, ZeroStr window) (differenceOutcomes window)))
      (Finset.univ.filter fun record =>
        convolutionActivationRadius patch filter M <
          |convolutionMedianActivation patch filter cap M r record -
            cappedRelu cap (convolutionEntry patch filter)|) ≤ (8 / 9 : ℝ) ^ r := by
  let A := convolutionPreparation patch filter
  let seed := (false, ZeroStr window)
  let S := differenceOutcomes window
  let ψ := localCounterOutput M (by omega) A seed S
  let decode (x : Fin M × (Bool × (Bool × Address window))) :=
    convolutionCounterActivation patch filter cap M x.1
  let μ := cappedRelu cap (convolutionEntry patch filter)
  let ε := convolutionActivationRadius patch filter M
  have hA := convolution_preparation_unitary patch filter hp hf
  have hψ : Normalized ψ := (prepared_ae_expanded_access_and_output M hM A seed S hA).2.2.2.1
  let p : FinDist (Fin M × (Bool × (Bool × Address window))) :=
    ⟨BornProb ψ, bornProb_nonneg ψ, hψ⟩
  have hGood : 8 / Real.pi ^ 2 ≤
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun x => |decode x - μ| ≤ ε) := by
    change _ ≤ MeasureProb (localCounterOutput M (by omega) A seed S)
      (Finset.univ.filter fun x => |convolutionCounterActivation patch filter cap M x.1 - μ| ≤ ε)
    unfold localCounterOutput
    rw [← aeLaw_event M hM A seed S hA (fun z => |convolutionCounterActivation patch filter cap M z - μ| ≤ ε)]
    exact qram_convolution_estimation_success patch filter hp hf cap M hM
  have hConstant : (2 / 3 : ℝ) ≤ 8 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    have hPi := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
    nlinarith
  have hc := mass_complement p (fun x => |decode x - μ| ≤ ε)
  simp only [not_le] at hc
  have hε : 0 ≤ ε := by
    dsimp [ε, convolutionActivationRadius]
    positivity
  have hBad : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun x => ε < |decode x - μ|) ≤ 1 / 3 := by
    linarith [hConstant.trans hGood]
  have hMedian := sorted_median_failure p decode r μ ε hε hBad
  change MeasureProb (PiTensorState (fun _ : Fin (2 * r + 1) => ψ))
    (Finset.univ.filter fun record => ε < |sortedBlockMedian r (fun j => decode (record j)) - μ|) ≤ _
  simp_rw [MeasureProb, bornProb_piTensorState]
  exact hMedian

/-- Failure of the capped-activation median is exponentially small for any normalized
coherent superposition of patch–filter addresses. -/
theorem convolution_ae_median_failure (memory : Tree ℝ (window + positions))
    (filters : Filter → Tree ℝ window) (hMemory : Valid memory) (hFilters : ∀ f, Valid (filters f))
    (cap : ℝ) (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (α : QState (Address positions × Filter)) (hα : Normalized α) :
    let patch (a : Address positions × Filter) := patchTree memory a.1
    let A (a : Address positions × Filter) := convolutionPreparation (patch a) (filters a.2)
    let out := addressedAERepeatedOutput (2 * r + 1) M (by omega) A
      (false, ZeroStr window) (fun _ => differenceOutcomes window) α
    MeasureProb out (Finset.univ.filter fun p =>
      convolutionActivationRadius (patch p.1) (filters p.1.2) M <
        |convolutionMedianActivation (patch p.1) (filters p.1.2) cap M r p.2 -
          cappedRelu cap (convolutionEntry (patch p.1) (filters p.1.2))|) ≤ (8 / 9 : ℝ) ^ r := by
  intro patch A out
  let failed (a : Address positions × Filter) (record : Fin (2 * r + 1) → Fin M × (Bool × (Bool × Address window))) :=
    convolutionActivationRadius (patch a) (filters a.2) M <
      |convolutionMedianActivation (patch a) (filters a.2) cap M r record -
        cappedRelu cap (convolutionEntry (patch a) (filters a.2))|
  change MeasureProb out (Finset.univ.filter fun p => failed p.1 p.2) ≤ _
  dsimp only [out]
  rw [addressed_ae_repeated_event_probability (2 * r + 1) M (by omega) A
    (false, ZeroStr window) (fun _ => differenceOutcomes window) α failed]
  calc
    _ ≤ ∑ a : Address positions × Filter, ‖α a‖ ^ 2 * (8 / 9 : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (convolution_local_median_failure (patch a) (filters a.2)
          (valid_subtree positions memory a.1 hMemory) (hFilters a.2) cap M hM r) (sq_nonneg _)
    _ = _ := by
      have hSum : ∑ a, ‖α a‖ ^ 2 = 1 := hα
      rw [← Finset.sum_mul, hSum, one_mul]

end Qatlib.Papers.QCNN20.Forward
