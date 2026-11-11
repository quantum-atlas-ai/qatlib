/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveLaw.MixedSelectivePerturbation
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers

/-!
# Selected-output stability for fair-bit qDRIFT

A stabilized channel error bound controls both the output operator and its
mass after selecting a set of instrument outcomes. If the ideal selected mass
`p` exceeds the error `δ`, the normalized selected states differ in trace norm
by at most `2 * δ / p`. Applying this to finite fair-bit qDRIFT also records
the executed circuit's gate, query, random-bit, and sampling-work bounds.

The simulator originates in [Campbell2019]; channel distinguishability and
postselection background are treated in
[Watrous, *The Theory of Quantum Information*][Watrous2018]. The finite sampler
and selected-output guarantees here are properties of the local construction.
-/
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.HspRecovery.SieveLaw

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Stabilized channel error controls selected masses and, when `δ < p`,
normalized selected outputs by `2 * δ / p`. For the channel-norm framework,
see [Watrous, completely bounded trace norms][Watrous2018]. -/
theorem selected_channel_stabilized_reference_error :
    ∀ (O : Type) [Fintype O] (D E F r : ℕ) (T U : QuantumChannel D E)
    (J : Instrument O E F) (S : Finset O) (δ : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    0 ≤ δ → X.PosSemidef → (Matrix.trace X).re = 1 →
    (∀ Y : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft (T.map-U.map) Y) ≤ δ*Matrix.traceNorm Y) →
    let σ := tensorLeft (selectiveMap J S) (tensorLeft T.map X)
    let τ := tensorLeft (selectiveMap J S) (tensorLeft U.map X)
    Matrix.traceNorm (σ-τ) ≤ δ ∧
    |(Matrix.trace σ).re-(Matrix.trace τ).re| ≤ δ ∧
    (δ < (Matrix.trace τ).re →
      0 < (Matrix.trace σ).re ∧
      Matrix.traceNorm (normalizedPositiveBranch σ-normalizedPositiveBranch τ) ≤
        2*δ/(Matrix.trace τ).re) := by
  intro O _ D E F r T U J S δ X hδ hX htrX hcert
  obtain ⟨hA, -, hsel⟩ := selective_instrument_cp_tni_reference_contraction O E F J S
  have hXT : (tensorLeft T.map X).PosSemidef := tensorLeft_posSemidef T.completelyPositive hX
  have hXU : (tensorLeft U.map X).PosSemidef := tensorLeft_posSemidef U.completelyPositive hX
  have hmap : tensorLeft T.map X - tensorLeft U.map X = tensorLeft (T.map - U.map) X :=
    (tensorLeft_map_sub T.map U.map X).symm
  have hnormX : Matrix.traceNorm X = 1 := by
    rw [posSemidef_traceNorm_eq_re hX, htrX]
  have hbound : Matrix.traceNorm (tensorLeft T.map X - tensorLeft U.map X) ≤ δ := by
    rw [hmap]
    have h1 := diamond_uniform_bound_of_input_bound (T.map - U.map) δ hcert r X
    rw [hnormX] at h1
    simpa using h1
  have hcontr : Matrix.traceNorm
      (tensorLeft (selectiveMap J S) (tensorLeft T.map X)
        - tensorLeft (selectiveMap J S) (tensorLeft U.map X)) ≤ δ := by
    rw [← tensorLeft_sub]
    exact (hsel r _ (hXT.isHermitian.sub hXU.isHermitian)).trans hbound
  have hG2 := positive_selected_output_mass_and_normalization_stability
    (Fin F × Fin r) (tensorLeft (selectiveMap J S) (tensorLeft T.map X))
    (tensorLeft (selectiveMap J S) (tensorLeft U.map X)) δ
    (tensorLeft_posSemidef hA hXT) (tensorLeft_posSemidef hA hXU) hδ hcontr
  exact ⟨hcontr, hG2.1, hG2.2.2⟩

/-- For a normalized positive input and the prescribed fair-bit qDRIFT budgets, an ideal
selected mass `p` above `δ = (1/2)^s` gives actual selected mass at least `p - δ` and
normalized-output trace-norm error at most `2 * δ / p`. Every sampled circuit has zero
oracle queries, `n` gates, and the stated fair-bit and comparison bounds. See
[Campbell2019]. -/
theorem fair_qdrift_actual_selected_output_and_ledgers :
    ∀ (O : Type) [Fintype O] (L D E T s r : ℕ) (w : Fin L → ℕ) (j₀ : Fin L)
    (K : Fin L → Operator D) (t : ℝ) (J : Instrument O D E) (S : Finset O)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    X.PosSemidef → (Matrix.trace X).re = 1 → 0 < weightTotal w → |t| ≤ T →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    let n := fairQdriftSteps (weightTotal w) T s
    let R := fairQdriftFuel n s
    let V := TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r)
    let σ := tensorLeft (selectiveMap J S) (fairQdriftReferenceOutput w j₀ n R K t r X)
    let τ := tensorLeft (selectiveMap J S) (V*X*Vᴴ)
    let p := (Matrix.trace τ).re
    let δ := (1/2:ℝ)^s
    (δ < p →
      p-δ ≤ (Matrix.trace σ).re ∧
      Matrix.traceNorm (normalizedPositiveBranch σ-normalizedPositiveBranch τ) ≤ 2*δ/p) ∧
    (∀ ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)),
      QueryCount (fairQdriftCircuit w j₀ n R K t ω) = 0 ∧
      GateCount (fairQdriftCircuit w j₀ n R K t ω) = n ∧
      (∑ k, (fairQdriftPick w j₀ R (ω k)).2.1) ≤ n*Nat.clog 2 (weightTotal w)*R ∧
      (∑ k, (fairQdriftPick w j₀ R (ω k)).2.2) ≤ n*L*R) := by
  intro O _ L D E T s r w j₀ K t J S X hX htrX hW ht hK
  obtain ⟨hA, -, hsel⟩ := selective_instrument_cp_tni_reference_contraction O D E J S
  have hnormX : Matrix.traceNorm X = 1 := by
    rw [posSemidef_traceNorm_eq_re hX, htrX]
  have hUunit : ∀ j : Fin L, HamiltonianEvolution (K j)
      (t*(weightTotal w : ℝ)/((fairQdriftSteps (weightTotal w) T s : ℝ)))
      ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    fun j => hamiltonianEvolution_unitary (hK j).1 _
  have hYσ : (fairQdriftReferenceOutput w j₀ (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X).PosSemidef := by
    rw [fair_bit_qdrift_actual_fresh_channel_bridge L D (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) r w j₀ K t X hW]
    exact (finite_reference_mixture_iteration (fairQdriftLaw w j₀
        (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s))
      (fun j => HamiltonianEvolution (K j)
        (t*(weightTotal w : ℝ)/((fairQdriftSteps (weightTotal w) T s : ℝ))))
      hUunit _ _ X).2.2.1 hX
  have hYτ : (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
      (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ).PosSemidef :=
    hX.mul_mul_conjTranspose_same _
  have hQ := fairQdrift_computed_budget_trace L D T s r w j₀ K t X hW ht hK
  have hbound : Matrix.traceNorm (fairQdriftReferenceOutput w j₀
      (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X -
      TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
      (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ)
      ≤ (1/2:ℝ)^s := by
    have h1 := hQ
    rw [hnormX] at h1
    have hdelta : (1/2:ℝ)^s = ((2:ℝ)⁻¹)^s := by rw [one_div]
    rw [hdelta]
    simpa using h1
  have hcontr : Matrix.traceNorm
      (tensorLeft (selectiveMap J S) (fairQdriftReferenceOutput w j₀
        (fairQdriftSteps (weightTotal w) T s)
        (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X) -
      tensorLeft (selectiveMap J S) (TensorGate
        (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ))
      ≤ (1/2:ℝ)^s := by
    rw [← tensorLeft_sub]
    exact (hsel r _ (hYσ.isHermitian.sub hYτ.isHermitian)).trans hbound
  have hG2 := positive_selected_output_mass_and_normalization_stability (Fin E × Fin r)
    (tensorLeft (selectiveMap J S) (fairQdriftReferenceOutput w j₀
      (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X))
    (tensorLeft (selectiveMap J S) (TensorGate
      (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
      (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ))
    ((1/2:ℝ)^s) (tensorLeft_posSemidef hA hYσ) (tensorLeft_posSemidef hA hYτ)
    (by positivity) hcontr
  refine ⟨?_, ?_⟩
  · intro hp
    have hlow : ((Matrix.trace (tensorLeft (selectiveMap J S) (TensorGate
        (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ))).re)
        - (1/2:ℝ)^s
        ≤ ((Matrix.trace (tensorLeft (selectiveMap J S) (fairQdriftReferenceOutput w j₀
        (fairQdriftSteps (weightTotal w) T s)
        (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t r X))).re) := by
      have h2 := (abs_le.mp hG2.1).1
      linarith
    exact ⟨hlow, (hG2.2.2 hp).2⟩
  · intro ω
    have hc := fair_bit_qdrift_actual_quantum_and_classical_path_counts L D
      (fairQdriftSteps (weightTotal w) T s)
      (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) w j₀ K t ω hW
      (fun j => (hK j).1)
    exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

end Qatlib.Concepts.RandCompile.ChannelBudget
