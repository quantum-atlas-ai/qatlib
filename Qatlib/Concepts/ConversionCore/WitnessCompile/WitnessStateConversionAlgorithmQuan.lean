/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessStateConversionAlgorithmStat
import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessConversionPhysicalProgram
import Qatlib.Concepts.ConversionCore.WitnessCompile.ResidualEntry

/-!
# Counted state conversion from filtered witnesses

`witnessStateConversionAlgorithm` proves the explicit circuit-existence specification from a
filtered Gram certificate. Its query and gate bounds depend on the ceiling of the witness budget
and `conversionPrecisionPrice`, and its output guarantee is Euclidean state-vector error.

`witnessStateConversionZeroCorner` supplies exact conversion with zero queries when the budget
or input length vanishes. The witness method comes from [LeeEtAl2011].

## Main statements

* `witnessStateConversionZeroCorner`: handles the zero-budget and zero-input cases.
* `witnessStateConversionAlgorithm`: proves the full counted conversion specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option synthInstance.maxSize 512
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators

/-- A filtered Gram certificate with zero budget or zero input length yields an exact clean
conversion circuit with zero queries and the stated gate and error bounds. -/
theorem witnessStateConversionZeroCorner
    (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n : ℕ) (input : X → Fin n → Bool) (ρ σ : X → QState H) (W ε : ℝ)
    (hCert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (gramFilterDelta input) W) (hε : 0 ≤ ε) (hZero : W = 0 ∨ n = 0) :
    ∃ (r : ℕ) (hr : 0 < r)
      (C : Circuit ((Fin (n+1) × Bool) × ((Bool × H) × Fin r))),
    IsUnitaryCircuit C ∧
    QueryCount C ≤ 1000000 * Nat.ceil W * conversionPrecisionPrice ε ∧
    GateCount C ≤ 3 + 10000000 * Nat.ceil W * conversionPrecisionPrice ε ∧
    ((W = 0 ∨ n = 0) → QueryCount C = 0) ∧
    ∀ x : X,
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := (Bool × H) × Fin r) (conversionPaddedInput input x)) C
        (conversionCleanEmbed n r hr false (ρ x)) - conversionCleanEmbed n r hr true (σ x))‖ ≤ ε ∧
    ((W = 0 ∨ n = 0) →
      Run (workspaceBitOracle (W := (Bool × H) × Fin r) (conversionPaddedInput input x)) C
        (conversionCleanEmbed n r hr false (ρ x)) = conversionCleanEmbed n r hr true (σ x)) := by
  obtain ⟨C, hC, hQ, hG, hOut⟩ := conversion_zero_corner_word X H n input ρ σ W hCert hZero
  refine ⟨1, by omega, C, hC, ?_, ?_, fun _ => hQ, ?_⟩
  · rw [hQ]
    exact Nat.zero_le _
  · rw [hG]
    omega
  · intro x
    refine ⟨?_, fun _ => hOut x⟩
    rw [hOut x, sub_self]
    simpa [toEuclidean_fromVec] using! hε

/-- Proves the clean-state conversion specification from a filtered Gram witness, with explicit
query and gate bounds and exact zero-query behavior in the degenerate cases. This realizes
the witness conversion principle of [Lee et al., Theorem 4.1][LeeEtAl2011]. -/
theorem witnessStateConversionAlgorithm : WitnessStateConversionAlgorithm := by
  intro X H _ _ _ _ _ n input ρ σ W ε hnorm hW hcert hε hεmax
  by_cases hz : W = 0 ∨ n = 0
  · exact witnessStateConversionZeroCorner X H n input ρ σ W ε hcert hε.le hz
  have hWpos : 0 < W := by
    have hne : W ≠ 0 := fun h => hz (Or.inl h)
    exact lt_of_le_of_ne hW (Ne.symm hne)
  let B := max 1 W
  let η := ε / 8
  let M := conversionPhaseSize W ε
  have hB : 1 ≤ B := le_max_left _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hscale := conversionPhaseSize_scale W ε hε hεmax
  have hM : 2 ≤ M := hscale.1
  obtain ⟨Q,hQ,u,v,hu,hv,hEq⟩ := gramFilteredCert_mono hcert (le_max_right 1 W)
  letI := hQ
  letI : DecidableEq Q := Classical.decEq Q
  have hu' : ∀ x, (∑ j, ∑ q, ‖u j x q‖ ^ 2) ≤ B := by
    simpa only [Complex.normSq_eq_norm_sq] using! hu
  have hv' : ∀ x, (∑ j, ∑ q, ‖v j x q‖ ^ 2) ≤ B := by
    simpa only [Complex.normSq_eq_norm_sq] using! hv
  obtain ⟨Λ,hΛ,hlogic⟩ := conversion_onepass_witness_error input ρ σ u v B η hB hη hη1
    M hM hscale.2 hnorm hu' hv' hEq
  obtain ⟨C,hC,hQC,hGC,hout⟩ := conversion_physical_phase_word input M hM Λ hΛ
  let G := (H ⊕ H) ⊕ (Fin n × Bool × Q)
  let S := ((Fin 1 → Fin M) × Bool) × G
  let r := Fintype.card S
  let h0 : H := Classical.choice inferInstance
  letI : Nonempty G := ⟨Sum.inl (Sum.inl h0)⟩
  letI : Nonempty (Fin 1 → Fin M) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hr : 0 < r := Fintype.card_pos
  let e := conversionPhaseFrameEquiv G M 1
  let addr := conversionFrameAddress (H := H) (Q := Q) n
  let F (ψ : QState (PhaseReflectionSpace G M 1)) :=
    conversionWorkspaceEmbed n h0 (Qatlib.Concepts.ConversionCore.WitnessCompile.reflectionsFrame addr (relabelState e ψ))
  let start (x : X) := F (phaseReflectionEmbed M 1 (conversionSourceRoot (Q := Q) (n := n) (ρ x)))
  let target (x : X) := F (phaseReflectionEmbed M 1 (conversionTargetRoot (Q := Q) (n := n) (σ x)))
  have hFinner (ψ φ) : Inner (F ψ) (F φ) = Inner ψ φ := by
    dsimp only [F]
    rw [conversion_workspace_inner, conversion_frame_inner, inner_relabelState]
  have hFsub (ψ φ) : F ψ - F φ = F (ψ - φ) := by
    funext p
    simp only [F, conversionWorkspaceEmbed, relabelState, TensorState,
      Qatlib.Concepts.ConversionCore.WitnessCompile.reflectionsFrame, Function.comp_apply, Pi.sub_apply]
    split_ifs <;> simp [sub_mul]
  have hFnorm (ψ) : ‖toEuclidean_fromVec (F ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
    conversion_inner_norm_transport _ _ (hFinner ψ ψ)
  have hstart (x y) : Inner (start x) (start y) = Inner (ρ x) (ρ y) := by
    dsimp only [start]
    rw [hFinner, phaseReflectionEmbed_inner (M := M) (by omega) 1, conversion_source_root_inner]
  have htarget (x y) : Inner (target x) (target y) = Inner (σ x) (σ y) := by
    dsimp only [target]
    rw [hFinner, phaseReflectionEmbed_inner (M := M) (by omega) 1, conversion_target_root_inner]
  let C' := conversionWorkspaceCircuit (H := H) n C
  have hlift := conversion_workspace_resources (H := H) n C hC
  have herror (x) : ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := (Bool × H) × Fin r) (conversionPaddedInput input x)) C' (start x) -
        target x)‖ ≤ ε := by
    dsimp only [C', start, target, F]
    rw [conversion_workspace_run, hout]
    change ‖toEuclidean_fromVec
      (F (phaseReflectionState
        (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ)
        M 1 (conversionSourceRoot (ρ x))) -
        F (phaseReflectionEmbed M 1 (conversionTargetRoot (σ x))))‖ ≤ ε
    rw [hFsub, hFnorm]
    exact (hlogic x).trans (by dsimp [η]; linarith)
  obtain ⟨D,hD,hQD,hGD,hfinal⟩ := conversion_clean_transport_word n r hr input ρ σ start target
    hstart htarget C' hlift.1 ε herror
  have hcost := conversion_onepass_cost_bounds W ε hWpos hε
  refine ⟨r,hr,D,hD,?_,?_,fun h => (hz h).elim,?_⟩
  · rw [hQD, hlift.2.1, hQC]
    exact hcost.1
  · rw [hGD, hlift.2.2, hGC]
    convert! hcost.2 using 1
  · intro x
    exact ⟨hfinal x,fun h => (hz h).elim⟩

end Qatlib.Concepts.ConversionCore.WitnessCompile
