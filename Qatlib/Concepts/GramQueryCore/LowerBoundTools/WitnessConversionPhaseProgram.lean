/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionGeometry
import Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter

/-!
# Phase reflection programs for witness conversion

Constructs a two-query matching-phase circuit and proves error estimates for phase reflection
applied to witness walks. Exact residual identities express the error through the zero outcome
of phase detection, linking the circuit analysis to the state conversion method of
[LeeEtAl2011].

The module derives single-pass conversion bounds from fixed and forbidden witnesses, and bounds
the explicit phase clock sizes, repetition counts, and expanded circuit costs.

## Main statements

* `conversionMatchingWord_run`: computes the two-query matching phase action.
* `conversion_phase_actual_error_norm`: identifies reflection error with twice the zero-event
  norm.
* `conversion_onepass_witness_error`: gives a conversion error of at most `2*η`.
* `conversion_onepass_cost_bounds`: bounds the selected implementation's resource expressions.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- The conjugate transpose of a unitary matrix is unitary. -/
private theorem conversion_adjoint_unitary {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup I ℂ := by
  simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU

/-- The phase equal to minus one when the workspace is active and the answer bit matches its
selected bit, and one otherwise. -/
def conversionMatchingPhase {I K : Type} (active bit : K → Bool)
    (p : (I × Bool) × K) : ℂ :=
  if active p.2 then (if p.1.2 = bit p.2 then -1 else 1) else 1

/-- The circuit consisting of a query, the diagonal matching phase gate, and a second query. -/
def conversionMatchingWord {I K : Type} [DecidableEq I] [DecidableEq K]
    (active bit : K → Bool) : Circuit ((I × Bool) × K) :=
  [.query, .gate (Matrix.diagonal (conversionMatchingPhase active bit)), .query]

/-- The diagonal matching phase gate is unitary. -/
theorem conversionMatchingGate_unitary {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (active bit : K → Bool) :
    Matrix.diagonal (conversionMatchingPhase (I := I) active bit) ∈
      Matrix.unitaryGroup ((I × Bool) × K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h : (fun p : (I × Bool) × K =>
      star (conversionMatchingPhase active bit p) * conversionMatchingPhase active bit p) =
      fun _ => (1 : ℂ) := by
    funext p
    dsimp [conversionMatchingPhase]
    split_ifs <;> norm_num
  simp only [Pi.star_apply]
  rw [h]
  exact Matrix.diagonal_one

/-- The matching phase circuit is unitary and uses exactly two queries and one gate. -/
theorem conversionMatchingWord_resources {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (active bit : K → Bool) :
    IsUnitaryCircuit (conversionMatchingWord (I := I) active bit) ∧
      QueryCount (conversionMatchingWord (I := I) active bit) = 2 ∧
      GateCount (conversionMatchingWord (I := I) active bit) = 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [conversionMatchingWord, isUnitaryCircuit_query, isUnitaryCircuit_gate,
    isUnitaryCircuit_nil, and_true]
  exact conversionMatchingGate_unitary active bit

/-- The matching phase circuit multiplies each amplitude by minus one exactly when its workspace
is active and the queried answer bit matches the selected workspace bit. -/
theorem conversionMatchingWord_run {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (f : I → Bool) (active bit : K → Bool)
    (ψ : QState ((I × Bool) × K)) (i : I) (t : Bool) (w : K) :
    Run (workspaceBitOracle (W := K) f) (conversionMatchingWord active bit) ψ ((i,t),w) =
      (if active w then (if t ^^ f i = bit w then (-1 : ℂ) else 1) else 1) * ψ ((i,t),w) := by
  simp only [conversionMatchingWord, Run]
  rw [applyGate_workspaceBitOracle_mk]
  change ((Matrix.diagonal (conversionMatchingPhase active bit)) *ᵥ
    ApplyGate (workspaceBitOracle (W := K) f) ψ) ((i, t ^^ f i), w) = _
  rw [Matrix.mulVec_diagonal, applyGate_workspaceBitOracle_mk]
  cases t <;> cases f i <;> simp [conversionMatchingPhase]

/-- On a false answer bit, the matching circuit applies minus one exactly when the workspace is
active and the input bit matches its selected bit. -/
theorem conversionMatchingWord_clean_sector {I K : Type} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (f : I → Bool) (active bit : K → Bool)
    (ψ : QState ((I × Bool) × K)) (i : I) (w : K) :
    Run (workspaceBitOracle (W := K) f) (conversionMatchingWord active bit) ψ ((i,false),w) =
      (if active w then (if f i = bit w then (-1 : ℂ) else 1) else 1) * ψ ((i,false),w) := by
  simpa using conversionMatchingWord_run f active bit ψ i false w

/-- For a packet of eigenvectors, the phase reflection residual is the inverse detection circuit
applied to twice the embedded packet weighted by the zero-outcome phase kernel raised to the
repetition count. -/
theorem conversion_phase_packet_residual
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, ApplyGate W (v j) = Complex.exp (2 * Real.pi * Complex.I * φ j) • v j) :
    phaseReflectionState W M k (∑ j, c j • v j) +
        phaseReflectionEmbed M k (∑ j, c j • v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (∑ j, (c j * qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M) ^ k) • v j)) := by
  let E := degenerateEmbedLinear (I := I) M k
  let R := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
    (phaseReflectionWord M k))).comp E
  let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
    (phaseDetectionWord M k))ᴴ).comp ((2 : ℂ) • E)
  change R (∑ j, c j • v j) + E (∑ j, c j • v j) =
    L (∑ j, (c j * qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M) ^ k) • v j)
  rw [map_sum, map_sum, map_sum]
  simp only [map_smul, ← Finset.sum_add_distrib, ← smul_add, mul_smul]
  apply Finset.sum_congr rfl
  intro j _
  have hj : R (v j) + E (v j) =
      L (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M) ^ k • v j) := by
    change phaseReflectionState W M k (v j) + phaseReflectionEmbed M k (v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))ᴴ
        ((2 : ℂ) • E (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M) ^ k • v j))
    rw [E.map_smul]
    exact phase_reflection_eigenstate_residual M k hM W (v j) (φ j) hW (he j)
  rw [hj, map_smul]

/-- For orthonormal eigenvectors, the squared phase reflection residual is `4 * ∑ j, ‖c j‖^2 *
‖qpeKernel M (φ j) 0‖^(2*k)`. -/
theorem conversion_phase_packet_error_sq
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, ApplyGate W (v j) = Complex.exp (2 * Real.pi * Complex.I * φ j) • v j)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0) :
    ‖toEuclidean_fromVec (phaseReflectionState W M k (∑ j, c j • v j) +
      phaseReflectionEmbed M k (∑ j, c j • v j))‖ ^ 2 =
      4 * ∑ j, ‖c j‖ ^ 2 * ‖qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)‖ ^ (2*k) := by
  rw [conversion_phase_packet_residual M k hM W hW v c φ he]
  have hD := (phaseDetectionWord_resources (I := I) M k (by omega)).1.evaluate_unitary
    (parallelOracle_unitary (controlOracle_unitary hW))
  rw [norm_applyGate_of_mem_unitaryGroup (conversion_adjoint_unitary hD)]
  change ‖(2 : ℂ) • toEuclidean_fromVec (phaseReflectionEmbed M k
    (∑ j, (c j * qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M) ^ k) • v j))‖ ^ 2 = _
  rw [norm_smul, phaseReflectionEmbed_norm M k (by omega), mul_pow,
    degenerate_packet_norm_sq v _ hv]
  norm_num only [Complex.norm_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]

/-- For positive clock size, every phase estimation kernel value has norm at most one. -/
private theorem conversion_kernel_norm_le_one (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M) :
    ‖qpeKernel M φ z‖ ≤ 1 := by
  have hphase := (offgrid_phase_kernel_formula M φ (⟨0,hM⟩ : Fin M) hM).2.2
  have hn : (∑ y : Fin M, ‖qpeKernel M φ y‖ ^ 2) = 1 :=
    normalized_applyGate (conversion_adjoint_unitary (qftMatrix_unitary hM)) hphase
  have hz : ‖qpeKernel M φ z‖ ^ 2 ≤ 1 := by
    rw [← hn]
    exact Finset.single_le_sum (fun y _ => sq_nonneg ‖qpeKernel M φ y‖) (Finset.mem_univ z)
  nlinarith [norm_nonneg (qpeKernel M φ z)]

/-- For an orthonormal eigenvector packet with phase distance at least `η` outside a chosen low
set, the squared reflection residual is bounded by four times the low coefficient mass plus
four times `(1/(2*M*η))^(2*k)` times the total coefficient mass. -/
theorem conversion_phase_low_high_bound
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, ApplyGate W (v j) = Complex.exp (2 * Real.pi * Complex.I * φ j) • v j)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0)
    (low : Finset J) (η : ℝ) (hη : 0 < η)
    (hHigh : ∀ j, j ∉ low → η ≤ phaseDistance (φ j) 0) :
    ‖toEuclidean_fromVec (phaseReflectionState W M k (∑ j, c j • v j) +
      phaseReflectionEmbed M k (∑ j, c j • v j))‖ ^ 2 ≤
      4 * ((∑ j ∈ low, ‖c j‖ ^ 2) +
        (1 / (2 * (M : ℝ) * η)) ^ (2*k) * (∑ j, ‖c j‖ ^ 2)) := by
  rw [conversion_phase_packet_error_sq M k hM W hW v c φ he hv]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsum : (∑ j, ‖c j‖ ^ 2 * ‖qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)‖ ^ (2*k)) ≤
      ∑ j, ((if j ∈ low then ‖c j‖ ^ 2 else 0) +
        (1 / (2 * (M : ℝ) * η)) ^ (2*k) * ‖c j‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ low
    · rw [if_pos hj]
      have hk := pow_le_pow_left₀ (norm_nonneg (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)))
        (conversion_kernel_norm_le_one M (by omega) (φ j) _) (2*k)
      have hm := mul_le_mul_of_nonneg_left hk (sq_nonneg ‖c j‖)
      simp only [one_pow, mul_one] at hm
      exact hm.trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hj, zero_add]
      have hk := pow_le_pow_left₀ (norm_nonneg (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)))
        (phase_detection_zero_label_gap_bound M (by omega) (φ j) η hη (hHigh j hj)) (2*k)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hk (sq_nonneg ‖c j‖)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum] using hsum

/-- For positive `W`, replacing `W` by `max 1 W` leaves its natural ceiling unchanged. -/
theorem conversion_budget_inflation_ceil (W : ℝ) (hW : 0 < W) :
    Nat.ceil (max 1 W) = Nat.ceil W := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply max_le
    · exact_mod_cast (Nat.one_le_ceil_iff.mpr hW)
    · exact Nat.le_ceil W
  · exact Nat.ceil_mono (le_max_right 1 W)

/-- The phase clock size `Nat.ceil (6400 * max 1 W / ε^2)`. -/
def conversionPhaseSize (W ε : ℝ) : ℕ := Nat.ceil (6400 * max 1 W / ε^2)
/-- The phase repetition count `Nat.ceil (Real.log (16/ε) / Real.log 2)`. -/
def conversionPhaseRepeats (ε : ℝ) : ℕ := Nat.ceil (Real.log (16 / ε) / Real.log 2)

/-- For positive `W` and `ε`, the phase clock size is at most `6400 * Nat.ceil W * Nat.ceil
(1/ε^2)`. -/
theorem conversionPhaseSize_bound (W ε : ℝ) (hW : 0 < W) (hε : 0 < ε) :
    conversionPhaseSize W ε ≤ 6400 * Nat.ceil W * Nat.ceil (1 / ε^2) := by
  have hA : max 1 W ≤ (Nat.ceil W : ℝ) := by
    rw [← conversion_budget_inflation_ceil W hW]
    exact Nat.le_ceil _
  have hB : 1 / ε^2 ≤ (Nat.ceil (1 / ε^2) : ℝ) := Nat.le_ceil _
  apply Nat.ceil_le.mpr
  push_cast
  calc
    6400 * max 1 W / ε^2 = 6400 * max 1 W * (1 / ε^2) := by ring
    _ ≤ 6400 * (Nat.ceil W : ℝ) * (Nat.ceil (1 / ε^2) : ℝ) := by
      gcongr

/-- For `0 < ε ≤ 1/2`, the phase repetition count is at most `6 * (Nat.ceil (Real.log (2/ε)) +
1)`. -/
theorem conversionPhaseRepeats_bound (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1/2) :
    conversionPhaseRepeats ε ≤ 6 * (Nat.ceil (Real.log (2 / ε)) + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2lower : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hL : 0 ≤ Real.log (2 / ε) := Real.log_nonneg (by
    apply (one_le_div hε).mpr
    linarith)
  have hlog : Real.log (16 / ε) = 3 * Real.log 2 + Real.log (2 / ε) := by
    rw [show 16 / ε = (2 : ℝ)^3 * (2 / ε) by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hC : Real.log (2 / ε) ≤ (Nat.ceil (Real.log (2 / ε)) : ℝ) := Nat.le_ceil _
  have hprod : 0 ≤ (Nat.ceil (Real.log (2 / ε)) : ℝ) * (Real.log 2 - 1/2) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  apply Nat.ceil_le.mpr
  push_cast
  apply (div_le_iff₀ hl2).mpr
  rw [hlog]
  nlinarith

/-- For positive `W` and `0 < ε ≤ 1/2`, bounds the expanded query expression by `1000000 *
Nat.ceil W * conversionPrecisionPrice ε` and the gate expression by `3 + 10000000 * Nat.ceil
W * conversionPrecisionPrice ε`. -/
theorem conversion_phase_expanded_cost_bounds (W ε : ℝ) (hW : 0 < W)
    (hε : 0 < ε) (hεmax : ε ≤ 1/2) :
    4 * conversionPhaseRepeats ε * (conversionPhaseSize W ε - 1) ≤
        1000000 * Nat.ceil W * conversionPrecisionPrice ε ∧
    16 * conversionPhaseRepeats ε * (conversionPhaseSize W ε - 1) +
        4 * conversionPhaseRepeats ε + 3 ≤
        3 + 10000000 * Nat.ceil W * conversionPrecisionPrice ε := by
  have hM := conversionPhaseSize_bound W ε hW hε
  have hk := conversionPhaseRepeats_bound ε hε hεmax
  have hsub : conversionPhaseSize W ε - 1 ≤ conversionPhaseSize W ε := Nat.sub_le _ _
  have hCB : 1 ≤ Nat.ceil (1 / ε^2) := Nat.one_le_ceil_iff.mpr (by positivity)
  have hCW : 1 ≤ Nat.ceil W := Nat.one_le_ceil_iff.mpr hW
  have hprod : 1 ≤ Nat.ceil W * Nat.ceil (1 / ε^2) := by nlinarith
  unfold conversionPrecisionPrice
  constructor <;> nlinarith

/-- For a vector annihilated by `Λ`, twice the sum of the first `M` walk powers applied to its
`P` component telescopes to the vector minus its `M`th walk iterate. -/
theorem conversion_walk_power_sum
    {I : Type} [Fintype I] [DecidableEq I] (P Λ : Matrix I I ℂ)
    (ψ : QState I) (hΛ : ApplyGate Λ ψ = 0) (M : ℕ) :
    (2 : ℂ) • (∑ t ∈ Finset.range M,
      ApplyGate ((ReflectionAbout P * ReflectionAbout Λ)^t) (ApplyGate P ψ)) =
      ψ - ApplyGate ((ReflectionAbout P * ReflectionAbout Λ)^M) ψ := by
  let U := ReflectionAbout P * ReflectionAbout Λ
  have hUψ : ApplyGate U ψ = ψ - (2 : ℂ) • ApplyGate P ψ :=
    conversion_walk_forbidden_identity P Λ ψ hΛ
  have hstep (t : ℕ) : (2 : ℂ) • ApplyGate (U^t) (ApplyGate P ψ) =
      ApplyGate (U^t) ψ - ApplyGate (U^(t+1)) ψ := by
    have h := congrArg (ApplyGate (U^t)) hUψ
    rw [← applyGate_mul, ← pow_succ] at h
    simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul] at h ⊢
    rw [h]
    module
  change (2 : ℂ) • (∑ t ∈ Finset.range M, ApplyGate (U^t) (ApplyGate P ψ)) = ψ - ApplyGate (U^M) ψ
  induction M with
  | zero => simp [applyGate_one]
  | succ M ih =>
    rw [Finset.sum_range_succ, smul_add, ih, hstep]
    abel

/-- For orthogonal projectors `P` and `Λ` and a vector annihilated by `Λ`, the sum of the first
`M` walk iterates of its `P` component has norm at most the original vector's norm. -/
theorem conversion_walk_power_sum_norm
    {I : Type} [Fintype I] [DecidableEq I] (P Λ : Matrix I I ℂ)
    (hP : IsOrthogonalProjector P) (hΛ : IsOrthogonalProjector Λ)
    (ψ : QState I) (hψ : ApplyGate Λ ψ = 0) (M : ℕ) :
    ‖toEuclidean_fromVec (∑ t ∈ Finset.range M,
      ApplyGate ((ReflectionAbout P * ReflectionAbout Λ)^t) (ApplyGate P ψ))‖ ≤
      ‖toEuclidean_fromVec ψ‖ := by
  let U := ReflectionAbout P * ReflectionAbout Λ
  have hU : U ∈ Matrix.unitaryGroup I ℂ := (Matrix.unitaryGroup I ℂ).mul_mem
    (reflectionAbout_unitary hP) (reflectionAbout_unitary hΛ)
  have hsum := conversion_walk_power_sum P Λ ψ hψ M
  have hn := congrArg (fun v : QState I => ‖toEuclidean_fromVec v‖) hsum
  change ‖(2 : ℂ) • toEuclidean_fromVec (∑ t ∈ Finset.range M, ApplyGate (U^t) (ApplyGate P ψ))‖ =
    ‖toEuclidean_fromVec ψ - toEuclidean_fromVec (ApplyGate (U^M) ψ)‖ at hn
  rw [norm_smul, show ‖(2 : ℂ)‖ = 2 by norm_num] at hn
  have hb := norm_sub_le (toEuclidean_fromVec ψ) (toEuclidean_fromVec (ApplyGate (U^M) ψ))
  rw [norm_applyGate_of_mem_unitaryGroup ((Matrix.unitaryGroup I ℂ).pow_mem hU M)] at hb
  nlinarith

/-- For positive clock size, the zero-output phase estimation amplitude is the average of the
first `M` powers of the unitary applied to the input state. -/
theorem conversion_qpe_zero_branch
    {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (U : Matrix I I ℂ) (ψ : QState I) (i : I) :
    qpeOutput M U ψ (⟨0,hM⟩,i) =
      (M : ℂ)⁻¹ * ∑ t : Fin M, ApplyGate (U^t.val) ψ i := by
  have hp (t : Fin M) (i : I) :
      (ControlledPowers U M *ᵥ
        TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ) (t,i) =
      (Real.sqrt (M : ℝ) : ℂ)⁻¹ * ApplyGate (U^t.val) ψ i := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ControlledPowers,
      Matrix.of_apply, TensorState]
    rw [Finset.sum_eq_single t]
    · simp only [if_true, ApplyGate, Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro s _ hs
      simp [show t ≠ s from fun h => hs h.symm]
    · intro h
      exact absurd (Finset.mem_univ t) h
  simp only [qpeOutput, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, qftMatrix_apply]
  simp
  conv_lhs =>
    arg 2
    intro t
    arg 2
    rw [← Fintype.sum_prod_type (fun p : Fin M × I =>
      ControlledPowers U M (t,i) p * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * ψ p.2))]
  change (∑ t : Fin M, (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
    (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ) (t,i)) =
    (M : ℂ)⁻¹ * ∑ t : Fin M, ApplyGate (U^t.val) ψ i
  simp only [hp, ← mul_assoc, inv_sqrt_mul_inv_sqrt hM, ← Finset.mul_sum]

/-- For orthogonal projectors and a vector annihilated by `Λ`, the zero branch of phase
estimation on its `P` component has norm at most the vector's norm divided by `M`. -/
theorem conversion_qpe_forbidden_zero_branch_bound
    {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (P Λ : Matrix I I ℂ) (hP : IsOrthogonalProjector P) (hΛ : IsOrthogonalProjector Λ)
    (ψ : QState I) (hψ : ApplyGate Λ ψ = 0) :
    ‖toEuclidean_fromVec (fun i => qpeOutput M (ReflectionAbout P * ReflectionAbout Λ)
      (ApplyGate P ψ) (⟨0,hM⟩,i))‖ ≤ ‖toEuclidean_fromVec ψ‖ / (M : ℝ) := by
  let U := ReflectionAbout P * ReflectionAbout Λ
  have hv : (fun i => qpeOutput M U (ApplyGate P ψ) (⟨0,hM⟩,i)) =
      (M : ℂ)⁻¹ • (∑ t ∈ Finset.range M, ApplyGate (U^t) (ApplyGate P ψ)) := by
    funext i
    rw [conversion_qpe_zero_branch M hM U]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Fin.sum_univ_eq_sum_range (fun t => ApplyGate (U^t) (ApplyGate P ψ) i) M]
  change ‖toEuclidean_fromVec (fun i => qpeOutput M U (ApplyGate P ψ) (⟨0,hM⟩,i))‖ ≤ _
  rw [hv]
  change ‖(M : ℂ)⁻¹ • toEuclidean_fromVec (∑ t ∈ Finset.range M,
    ApplyGate (U^t) (ApplyGate P ψ))‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hb := mul_le_mul_of_nonneg_left
    (conversion_walk_power_sum_norm P Λ hP hΛ ψ hψ M) (inv_nonneg.mpr (Nat.cast_nonneg M : (0 : ℝ) ≤ M))
  simpa only [div_eq_mul_inv, mul_comm] using hb

/-- For a unitary and positive clock size, the phase reflection residual equals the inverse
detection circuit applied to twice the detection state collapsed onto the all-zero clock
event. -/
theorem conversion_phase_actual_residual
    {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 0 < M) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    phaseReflectionState U M k ψ + phaseReflectionEmbed M k ψ =
      ApplyGate (evaluate (parallelOracle (controlOracle U)) (phaseDetectionWord M k))ᴴ
        ((2 : ℂ) • Collapse (degenerateDetectionState U M k ψ) (phaseZeroEvent M k)) := by
  let D := evaluate (parallelOracle (controlOracle U)) (phaseDetectionWord (I := I) M k)
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hU))
  have hcancel : ApplyGate Dᴴ (ApplyGate D (phaseReflectionEmbed M k ψ)) =
      phaseReflectionEmbed M k ψ := by
    rw [← applyGate_mul, show Dᴴ * D = 1 by
      simpa only [Matrix.star_eq_conjTranspose] using hD.1, applyGate_one]
  have hstate : phaseReflectionState U M k ψ =
      ApplyGate Dᴴ (ApplyGate (phaseZeroReflection M k)
        (ApplyGate D (phaseReflectionEmbed M k ψ))) := by
    simp only [phaseReflectionState, phaseReflectionWord, evaluate_append,
      evaluate_adjointCircuit, evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul, D]
  rw [hstate, phaseZeroReflection, applyGate_reflectionAbout]
  change ApplyGate Dᴴ ((2 : ℂ) • Collapse (ApplyGate D (phaseReflectionEmbed M k ψ))
      (phaseZeroEvent M k) - ApplyGate D (phaseReflectionEmbed M k ψ)) +
      phaseReflectionEmbed M k ψ = _
  simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul] at hcancel ⊢
  rw [hcancel]
  simp only [degenerateDetectionState, D, ApplyGate]
  module

/-- For a unitary and positive clock size, the phase reflection residual norm equals twice the
norm of the detection state collapsed onto the all-zero clock event. -/
theorem conversion_phase_actual_error_norm
    {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 0 < M) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (phaseReflectionState U M k ψ + phaseReflectionEmbed M k ψ)‖ =
      2 * ‖toEuclidean_fromVec
        (Collapse (degenerateDetectionState U M k ψ) (phaseZeroEvent M k))‖ := by
  rw [conversion_phase_actual_residual M k hM U hU ψ]
  have hD := (phaseDetectionWord_resources (I := I) M k hM).1.evaluate_unitary
    (parallelOracle_unitary (controlOracle_unitary hU))
  rw [norm_applyGate_of_mem_unitaryGroup (conversion_adjoint_unitary hD)]
  change ‖(2 : ℂ) • toEuclidean_fromVec _‖ = _
  rw [norm_smul]
  norm_num only [Complex.norm_ofNat]
  rfl

/-- The inner product of tensor product states factors into the product of the component inner
products. -/
private theorem conversion_tensor_inner {I J : Type} [Fintype I] [Fintype J]
    (a b : QState I) (c d : QState J) :
    Qatlib.Foundations.PureStateMath.Inner (TensorState a c) (TensorState b d) = Qatlib.Foundations.PureStateMath.Inner a b * Qatlib.Foundations.PureStateMath.Inner c d := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, TensorState, dotProduct, Fintype.sum_prod_type,
    Pi.star_apply, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For positive clock size, the phase reflection embedding preserves inner products. -/
theorem phaseReflectionEmbed_inner {I : Type} [Fintype I] [DecidableEq I]
    {M : ℕ} (hM : 0 < M) (k : ℕ) (a b : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (phaseReflectionEmbed M k a) (phaseReflectionEmbed M k b) = Qatlib.Foundations.PureStateMath.Inner a b := by
  rw [phaseReflectionEmbed_tensor M k hM a, phaseReflectionEmbed_tensor M k hM b,
    conversion_tensor_inner, inner_ket_ket, if_pos rfl, one_mul,
    conversion_tensor_inner, inner_ket_ket, if_pos rfl, one_mul]

/-- The phase reflection state construction commutes with complex scalar multiplication. -/
theorem phaseReflectionState_smul {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (M k : ℕ) (c : ℂ) (x : QState I) :
    phaseReflectionState W M k (c • x) = c • phaseReflectionState W M k x := by
  simp only [phaseReflectionState, phaseReflectionEmbed_smul, ApplyGate,
    Matrix.mulVec_smul]

/-- The phase reflection state construction preserves subtraction. -/
theorem phaseReflectionState_sub {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (M k : ℕ) (x y : QState I) :
    phaseReflectionState W M k (x - y) =
      phaseReflectionState W M k x - phaseReflectionState W M k y := by
  simp only [phaseReflectionState, phaseReflectionEmbed_sub, ApplyGate,
    Matrix.mulVec_sub]

/-- For a unitary matrix and clock size at least two, the phase reflection state has the same
Euclidean norm as its input. -/
theorem phaseReflectionState_norm {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ) (M k : ℕ) (hM : 2 ≤ M)
    (hMk : 0 < M) (x : QState I) :
    ‖toEuclidean_fromVec (phaseReflectionState W M k x)‖ = ‖toEuclidean_fromVec x‖ := by
  have hD : (evaluate (parallelOracle (controlOracle W)) (phaseReflectionWord M k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phase_reflection_actual_queries_and_macros M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have h := norm_applyGate_of_mem_unitaryGroup hD (phaseReflectionEmbed M k x)
  rwa [phaseReflectionEmbed_norm M k hMk x] at h

/-- One repetition of the detection state is the relabeled tensor product of the empty clock's
zero state and the flagged phase estimation output. -/
theorem conversion_detection_single {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (ψ : QState I) :
    degenerateDetectionState U M 1 ψ =
      relabelState (phaseHeadSplit I M 0).symm
        (TensorState (Ket (phaseZeroIndex M 0 hM))
          (phaseFlagEmbed M (qpeOutput M U ψ))) := by
  have hsub0 : Subsingleton (Fin 0 → Fin M) := inferInstance
  have hsub1 : Subsingleton (Fin 1) := inferInstance
  have hEmbed : phaseReflectionEmbed M 1 ψ =
      relabelState (phaseHeadSplit I M 0).symm
        (TensorState (Ket (phaseZeroIndex M 0 hM))
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) ψ))) := by
    funext p
    rw [relabelState_apply, Equiv.symm_symm]
    change (if p.2.1 = false ∧ ∀ j, (p.1 j).val = 0 then ψ p.2.2 else 0) =
      (Ket (phaseZeroIndex M 0 hM)) (fun j : Fin 0 => p.1 j.succ) *
        ((Ket (⟨0, hM⟩ : Fin M)) (p.1 (0 : Fin 1)) * ((Ket false) p.2.1 * ψ p.2.2))
    rw [show (Ket (phaseZeroIndex M 0 hM)) (fun j : Fin 0 => p.1 j.succ) = 1 from
      if_pos (hsub0.elim _ _), one_mul]
    have hz : (∀ j, (p.1 j).val = 0) ↔ p.1 (0 : Fin 1) = (⟨0, hM⟩ : Fin M) := by
      constructor
      · intro h; exact Fin.ext (h 0)
      · intro h j
        rw [show p.1 j = p.1 (0 : Fin 1) from congrArg p.1 (hsub1.elim j 0), h]
    cases hb : p.2.1 <;> simp [Ket, hz]
  have hEval : evaluate (parallelOracle (controlOracle U)) (phaseDetectionWord (I := I) M 1) =
      phaseHeadGate M 0 (evaluate (parallelOracle (J := Fin M) (controlOracle U))
        (phaseCompileCircuit (countedPhaseCircuit M))) := by
    rw [phaseDetectionWord_evaluate_succ U M 0]
    have h0 : phaseDetectionWord (I := I) M 0 = [] := rfl
    rw [h0]
    simp only [evaluate]
    rw [phaseTailGate, tensorGate_one,
        Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one, Matrix.one_mul]
  rw [degenerateDetectionState, hEval, phaseHeadGate, hEmbed, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, phaseCompileCircuit_evaluate]
  have hOracle : parallelOracle (J := Fin M) (controlOracle U) =
      TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle U) :=
    parallelOracle_eq_kronecker _
  rw [hOracle]
  have hqpe := (counted_offgrid_qpe_clean_flag (I := I) M hM U ψ).1
  rw [hqpe]
  rfl

/-- The amplitude of a single detection repetition is the flagged phase estimation amplitude at
its sole clock value and payload. -/
theorem conversion_detection_single_apply {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (ψ : QState I)
    (p : PhaseReflectionSpace I M 1) :
    degenerateDetectionState U M 1 ψ p =
      phaseFlagEmbed M (qpeOutput M U ψ) (p.1 (0 : Fin 1), p.2) := by
  have hsub0 : Subsingleton (Fin 0 → Fin M) := inferInstance
  rw [conversion_detection_single U M hM ψ, relabelState_apply, Equiv.symm_symm]
  change (Ket (phaseZeroIndex M 0 hM)) (fun j : Fin 0 => p.1 j.succ) *
    phaseFlagEmbed M (qpeOutput M U ψ) (p.1 (0 : Fin 1), p.2) = _
  rw [show (Ket (phaseZeroIndex M 0 hM)) (fun j : Fin 0 => p.1 j.succ) = 1 from
    if_pos (hsub0.elim _ _), one_mul]

/-- The single-repetition degenerate zero branch equals the zero-output branch of phase
estimation. -/
theorem conversion_zero_branch_single {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (ψ : QState I) (i : I) :
    degenerateZeroBranch U M 1 hM ψ i = qpeOutput M U ψ ((⟨0, hM⟩ : Fin M), i) := by
  rw [degenerateZeroBranch, conversion_detection_single_apply U M hM ψ]
  rfl

/-- Collapsing a single detection repetition onto the zero clock event gives the phase embedding
of its degenerate zero branch. -/
theorem conversion_collapse_single {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (ψ : QState I) :
    Collapse (degenerateDetectionState U M 1 ψ) (phaseZeroEvent M 1) =
      phaseReflectionEmbed M 1 (degenerateZeroBranch U M 1 hM ψ) := by
  funext p
  rw [collapse_apply, conversion_detection_single_apply U M hM ψ]
  by_cases hx : ∀ j, (p.1 j).val = 0
  · have hp0 : p.1 (0 : Fin 1) = (⟨0, hM⟩ : Fin M) := Fin.ext (hx 0)
    simp only [phaseZeroEvent, Finset.mem_filter, Finset.mem_univ,
      true_and, hx, phaseFlagEmbed, phaseReflectionEmbed, hp0]
    rw [conversion_zero_branch_single U M hM ψ]
    cases p.2.1 <;> simp
  · have hp0 : (p.1 (0 : Fin 1)).val ≠ 0 := by
      intro h
      apply hx
      intro j
      simpa only [Subsingleton.elim j (0 : Fin 1)] using h
    simp [phaseZeroEvent, hx, phaseReflectionEmbed, hp0]

/-- For a unitary and positive clock size, the single-pass reflection residual norm is twice the
norm of the degenerate zero branch. -/
theorem conversion_reflection_error_single {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (M : ℕ) (hM : 0 < M)
    (ψ : QState I) :
    ‖toEuclidean_fromVec (phaseReflectionState U M 1 ψ + phaseReflectionEmbed M 1 ψ)‖ =
      2 * ‖toEuclidean_fromVec (degenerateZeroBranch U M 1 hM ψ)‖ := by
  rw [conversion_phase_actual_error_norm M 1 hM U hU ψ,
    conversion_collapse_single U M hM ψ, phaseReflectionEmbed_norm M 1 hM]

/-- If `Λ` annihilates `w`, `P` sends `w` to `t`, and `‖w‖ ≤ C`, then a single phase pass for
the orthogonal-projector walk has sign-reversal error on `t` at most `2*C/M`. -/
theorem conversion_onepass_forbidden_root_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (P Λ : Matrix I I ℂ) (hP : IsOrthogonalProjector P)
    (hΛ : IsOrthogonalProjector Λ) (t w : QState I)
    (hwΛ : ApplyGate Λ w = 0) (hPw : ApplyGate P w = t) (C : ℝ)
    (hC : ‖toEuclidean_fromVec w‖ ≤ C) :
    ‖toEuclidean_fromVec (phaseReflectionState (ReflectionAbout P * ReflectionAbout Λ)
        M 1 t + phaseReflectionEmbed M 1 t)‖ ≤ 2 * C / (M : ℝ) := by
  have hU : (ReflectionAbout P * ReflectionAbout Λ) ∈ Matrix.unitaryGroup I ℂ :=
    (Matrix.unitaryGroup I ℂ).mul_mem (reflectionAbout_unitary hP) (reflectionAbout_unitary hΛ)
  rw [conversion_reflection_error_single _ hU M hM t]
  have hfun : degenerateZeroBranch (ReflectionAbout P * ReflectionAbout Λ) M 1 hM t =
      fun i => qpeOutput M (ReflectionAbout P * ReflectionAbout Λ) t ((⟨0, hM⟩ : Fin M), i) :=
    funext (conversion_zero_branch_single _ M hM t)
  rw [hfun]
  have hb := conversion_qpe_forbidden_zero_branch_bound M hM P Λ hP hΛ w hwΛ
  rw [hPw] at hb
  calc
    2 * ‖toEuclidean_fromVec (fun i => qpeOutput M
        (ReflectionAbout P * ReflectionAbout Λ) t (⟨0, hM⟩, i))‖ ≤
        2 * (‖toEuclidean_fromVec w‖ / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 2 * (C / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (by positivity)) (by positivity)
    _ = 2 * C / (M : ℝ) := by ring

/-- For a unitary and positive clock size, phase reflection acts exactly as the clean embedding
on a fixed vector. -/
theorem conversion_onepass_fixed_exact {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 0 < M) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hfix : ApplyGate U ψ = ψ) :
    phaseReflectionState U M k ψ = phaseReflectionEmbed M k ψ := by
  let D := evaluate (parallelOracle (controlOracle U)) (phaseDetectionWord (I := I) M k)
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hU))
  have heigen : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ)) • ψ := by
    rw [hfix]; simp
  have hzero : phaseDistance 0 0 = 0 := by norm_num [phaseDistance]
  have hz := qpeKernel_zero_distance M hM 0 hzero
  have hpkt : phaseKernelPacket M k 0 ψ = phaseReflectionEmbed M k ψ := by
    funext ⟨x, b, i⟩
    cases b with
    | true => simp [phaseKernelPacket, phaseReflectionEmbed]
    | false =>
      by_cases hx : ∀ j, (x j).val = 0
      · have he : x = phaseZeroIndex M k hM := by
          funext j; exact Fin.ext (hx j)
        subst x
        simp [phaseKernelPacket, phaseReflectionEmbed, hz, phaseZeroIndex, Ket]
      · obtain ⟨j, hj⟩ := not_forall.mp hx
        have hne : x j ≠ (⟨0, hM⟩ : Fin M) := fun he => hj (congrArg Fin.val he)
        have hprod : (∏ j : Fin k, qpeKernel M 0 (x j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz]; simp [Ket, hne])
        simp [phaseKernelPacket, phaseReflectionEmbed, hx, hprod]
  have he : ApplyGate D (phaseReflectionEmbed M k ψ) = phaseReflectionEmbed M k ψ :=
    (phaseDetectionWord_eigenstate M k hM U ψ 0 heigen).trans hpkt
  have hp : ApplyGate (Projector (phaseZeroEvent M k)) (phaseReflectionEmbed M k ψ) =
      phaseReflectionEmbed M k ψ := by
    change Collapse (phaseReflectionEmbed M k ψ) (phaseZeroEvent M k) = _
    funext ⟨x, b, i⟩
    by_cases hx : ∀ j, (x j).val = 0 <;>
      simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed, hx]
  have hc : ApplyGate Dᴴ (phaseReflectionEmbed M k ψ) = phaseReflectionEmbed M k ψ := by
    calc
      _ = ApplyGate Dᴴ (ApplyGate D (phaseReflectionEmbed M k ψ)) := congrArg (ApplyGate Dᴴ) he.symm
      _ = _ := by rw [← applyGate_mul, show Dᴴ * D = 1 by
          simpa only [Matrix.star_eq_conjTranspose] using hD.1, applyGate_one]
  simp only [phaseReflectionState, phaseReflectionWord, evaluate_append,
    evaluate_adjointCircuit, evaluate, instructionMatrix, Matrix.mul_one, applyGate_mul]
  change ApplyGate Dᴴ (ApplyGate (phaseZeroReflection M k)
    (ApplyGate D (phaseReflectionEmbed M k ψ))) = _
  rw [he, phaseZeroReflection, applyGate_reflectionAbout_of_fixed hp, hc]

/-- For a unitary and clock size at least two, a state within distance `δ` of a fixed vector has
phase reflection error from its clean embedding at most `2*δ`. -/
theorem conversion_onepass_fixed_root_error {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 2 ≤ M) (hMk : 0 < M) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (fw t : QState I)
    (hfix : ApplyGate U fw = fw) (δ : ℝ)
    (hdist : ‖toEuclidean_fromVec (fw - t)‖ ≤ δ) :
    ‖toEuclidean_fromVec (phaseReflectionState U M k t -
        phaseReflectionEmbed M k t)‖ ≤ 2 * δ := by
  have hexact := conversion_onepass_fixed_exact M k hMk U hU fw hfix
  have hsplit : phaseReflectionState U M k t - phaseReflectionEmbed M k t =
      phaseReflectionState U M k (t - fw) +
        phaseReflectionEmbed M k (fw - t) := by
    rw [phaseReflectionState_sub, phaseReflectionEmbed_sub, hexact]
    abel
  rw [hsplit]
  have h1 : ‖toEuclidean_fromVec (phaseReflectionState U M k (t - fw))‖ =
      ‖toEuclidean_fromVec (t - fw)‖ :=
    phaseReflectionState_norm U hU M k hM hMk (t - fw)
  have h2 : ‖toEuclidean_fromVec (phaseReflectionEmbed M k (fw - t))‖ =
      ‖toEuclidean_fromVec (fw - t)‖ := phaseReflectionEmbed_norm M k hMk _
  change ‖toEuclidean_fromVec (phaseReflectionState U M k (t - fw)) +
    toEuclidean_fromVec (phaseReflectionEmbed M k (fw - t))‖ ≤ 2 * δ
  calc
    _ ≤ ‖toEuclidean_fromVec (phaseReflectionState U M k (t - fw))‖ +
        ‖toEuclidean_fromVec (phaseReflectionEmbed M k (fw - t))‖ := norm_add_le _ _
    _ = 2 * ‖toEuclidean_fromVec (fw - t)‖ := by
      rw [h1, h2]
      have hc : toEuclidean_fromVec (t - fw) = -toEuclidean_fromVec (fw - t) := by
        simp [toEuclidean_fromVec, neg_sub]
      rw [hc, norm_neg]
      ring
    _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hdist (by positivity)

/-- Bounds the source-to-target root conversion error by `a+b` when the plus-root preservation
error is at most `a` and the minus-root sign-reversal error is at most `b`. -/
theorem conversion_onepass_balanced_error {H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (U : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ)
    (M : ℕ) (ρ σ : QState H) (a b : ℝ)
    (hplus : ‖toEuclidean_fromVec (phaseReflectionState U M 1 (conversionPlusRoot ρ σ) -
      phaseReflectionEmbed M 1 (conversionPlusRoot ρ σ))‖ ≤ a)
    (hminus : ‖toEuclidean_fromVec (phaseReflectionState U M 1 (conversionMinusRoot ρ σ) +
      phaseReflectionEmbed M 1 (conversionMinusRoot ρ σ))‖ ≤ b) :
    ‖toEuclidean_fromVec (phaseReflectionState U M 1 (conversionSourceRoot ρ) -
      phaseReflectionEmbed M 1 (conversionTargetRoot σ))‖ ≤ a + b := by
  have he : phaseReflectionState U M 1 (conversionSourceRoot ρ) -
      phaseReflectionEmbed M 1 (conversionTargetRoot σ) =
      (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) •
        ((phaseReflectionState U M 1 (conversionPlusRoot ρ σ) -
          phaseReflectionEmbed M 1 (conversionPlusRoot ρ σ)) +
         (phaseReflectionState U M 1 (conversionMinusRoot ρ σ) +
          phaseReflectionEmbed M 1 (conversionMinusRoot ρ σ))) := by
    rw [← conversion_source_root_split ρ σ, ← conversion_target_root_split ρ σ,
      phaseReflectionState_smul, phaseReflectionState_add,
      phaseReflectionEmbed_smul, phaseReflectionEmbed_sub, ← smul_sub]
    congr 1
    abel
  have hc : ‖(((Real.sqrt 2 : ℝ)⁻¹ : ℂ))‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))
  rw [he]
  let ep := phaseReflectionState U M 1 (conversionPlusRoot ρ σ) -
    phaseReflectionEmbed M 1 (conversionPlusRoot ρ σ)
  let em := phaseReflectionState U M 1 (conversionMinusRoot ρ σ) +
    phaseReflectionEmbed M 1 (conversionMinusRoot ρ σ)
  have hl : toEuclidean_fromVec ((((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) • (ep + em)) =
      (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) • (toEuclidean_fromVec ep + toEuclidean_fromVec em) := by
    simp [toEuclidean_fromVec]
  rw [hl, norm_smul]
  calc
    _ ≤ 1 * ‖toEuclidean_fromVec ep + toEuclidean_fromVec em‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ a + b := by
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add hplus hminus)

/-- For normalized states and a filtered Gram factorization with witness budgets at most `B ≥
1`, a clock of size at least `100*B/η^2` yields a common orthogonal projector and
single-pass root conversion error at most `2*η` when `0 < η ≤ 1`. -/
theorem conversion_onepass_witness_error {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u v : Fin n → X → Q → ℂ) (B η : ℝ) (hB : 1 ≤ B) (hη : 0 < η) (hη1 : η ≤ 1)
    (M : ℕ) (hM : 2 ≤ M) (hsize : 100 * B / η ^ 2 ≤ (M : ℝ))
    (hnorm : ∀ x, Normalized (ρ x) ∧ Normalized (σ x))
    (hu : ∀ x, (∑ j, ∑ q, ‖u j x q‖ ^ 2) ≤ B)
    (hv : ∀ x, (∑ j, ∑ q, ‖v j x q‖ ^ 2) ≤ B)
    (hEq : ∀ y x, (gramStateMatrix ρ - gramStateMatrix σ) y x =
      ∑ j, gramFilterDelta input j y x * (star (u j y) ⬝ᵥ v j x)) :
    ∃ Λ : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ,
      IsOrthogonalProjector Λ ∧ ∀ x,
      let U :=
          ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ
      ‖toEuclidean_fromVec (phaseReflectionState U M 1 (conversionSourceRoot (ρ x)) -
        phaseReflectionEmbed M 1 (conversionTargetRoot (σ x)))‖ ≤ 2 * η := by
  let α := η / (2 * Real.sqrt B)
  have hBp : 0 < B := by linarith
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨Λ, hΛ, hForbidden, hFixed⟩ := conversion_witness_public_projection input ρ σ u v α hEq
  refine ⟨Λ, hΛ, ?_⟩
  intro x
  let P := conversionLogicalProjector (H := H) (Q := Q) input x
  let U := ReflectionAbout P * ReflectionAbout Λ
  have hP : IsOrthogonalProjector P := conversionLogicalProjector_orthogonal input x
  have hU : U ∈ Matrix.unitaryGroup _ ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem (reflectionAbout_unitary hP) (reflectionAbout_unitary hΛ)
  have hf : ApplyGate U (conversionFixedWitness input ρ σ v α x) =
      conversionFixedWitness input ρ σ v α x := by
    change ApplyGate (ReflectionAbout P * ReflectionAbout Λ) _ = _
    rw [applyGate_mul, applyGate_reflectionAbout_of_fixed (hFixed x)]
    exact applyGate_reflectionAbout_of_fixed
        (conversionLogicalProjector_fixedWitness input ρ σ v α x)
  have hplus := conversion_onepass_fixed_root_error M 1 hM (by omega) U hU
    (conversionFixedWitness input ρ σ v α x) (conversionPlusRoot (ρ x) (σ x)) hf (η / 2)
    (conversion_fixed_gap_bound input ρ σ v B η hBp hη.le x (hv x))
  have hwΛ : ApplyGate Λ (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) = 0 := by
    simp only [ApplyGate, Matrix.mulVec_smul] at hForbidden ⊢
    rw [hForbidden x, smul_zero]
  have hminus := conversion_onepass_forbidden_root_error M (by omega) P Λ hP hΛ
    (conversionMinusRoot (ρ x) (σ x))
    (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) hwΛ
    (conversion_forbidden_scaled_projector input ρ σ u α hα x) (2 * B / η)
    (conversion_forbidden_size_bound input ρ σ u B η hB hη hη1 x (hnorm x).1 (hnorm x).2 (hu x))
  have hsmall : 2 * (2 * B / η) / (M : ℝ) ≤ η / 25 := by
    have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    apply (div_le_iff₀ hMp).mpr
    have ht := (div_le_iff₀ (sq_pos_of_pos hη)).mp hsize
    rw [show 2 * (2 * B / η) = 4 * B / η by ring]
    apply (div_le_iff₀ hη).mpr
    nlinarith
  have hb := conversion_onepass_balanced_error U M (ρ x) (σ x) (2 * (η / 2)) (η / 25)
    hplus (hminus.trans hsmall)
  (try dsimp only)
  exact hb.trans (by linarith)

/-- For `0 < ε ≤ 1/2`, the selected phase clock size is at least two and at least `100 * max 1 W
/ (ε/8)^2`. -/
theorem conversionPhaseSize_scale (W ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1/2) :
    2 ≤ conversionPhaseSize W ε ∧
      100 * max 1 W / (ε / 8) ^ 2 ≤ (conversionPhaseSize W ε : ℝ) := by
  have hb : 1 ≤ max 1 W := le_max_left _ _
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have he2max : ε ^ 2 ≤ 1/4 := by nlinarith
  have ht : 2 ≤ 6400 * max 1 W / ε ^ 2 := by
    apply (le_div_iff₀ he2).mpr
    nlinarith
  refine ⟨?_, ?_⟩
  · exact_mod_cast ht.trans (Nat.le_ceil _)
  · rw [show 100 * max 1 W / (ε / 8) ^ 2 = 6400 * max 1 W / ε ^ 2 by ring]
    exact Nat.le_ceil _

/-- For positive `W` and `ε`, bounds the one-pass query expression by `1000000 * Nat.ceil W *
conversionPrecisionPrice ε` and the gate expression by `3 + 10000000 * Nat.ceil W *
conversionPrecisionPrice ε`. -/
theorem conversion_onepass_cost_bounds (W ε : ℝ) (hW : 0 < W) (hε : 0 < ε) :
    4 * (conversionPhaseSize W ε - 1) ≤ 1000000 * Nat.ceil W * conversionPrecisionPrice ε ∧
    8 * (conversionPhaseSize W ε - 1) + 7 ≤
      3 + 10000000 * Nat.ceil W * conversionPrecisionPrice ε := by
  have hM := conversionPhaseSize_bound W ε hW hε
  have hsub := Nat.sub_le (conversionPhaseSize W ε) 1
  have hCW : 1 ≤ Nat.ceil W := Nat.one_le_ceil_iff.mpr hW
  have hCE : 1 ≤ Nat.ceil (1 / ε^2) := Nat.one_le_ceil_iff.mpr (by positivity)
  have hprice : Nat.ceil W * Nat.ceil (1 / ε^2) ≤ Nat.ceil W * conversionPrecisionPrice ε := by
    unfold conversionPrecisionPrice
    nlinarith
  have hpos : 1 ≤ Nat.ceil W * Nat.ceil (1 / ε^2) := by nlinarith
  constructor <;> nlinarith

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
