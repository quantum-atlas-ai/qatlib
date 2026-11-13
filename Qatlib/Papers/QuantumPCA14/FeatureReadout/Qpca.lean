/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumPCA14.FeatureReadout.QpcaDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution

/-!
# Quantum PCA readout endpoint results

This module proves that `clusterAssignment` attains the largest supplied score. It also
assembles the endpoint specifications for shared loading, spectral and low rank exponentiation
results, and finite copy discrimination and score based assignment. See
[LloydMohseniRebentrost2014].

## Main statements

* `clusterAssignment_maximizes`: The score of the selected cluster equals the maximal observable
  score.
* `clause16_endpoint`: The endpoint specification `clause16EndpointSpec` for shared loading
  holds.
* `clause17_endpoint`: The endpoint specification `clause17EndpointSpec`, combining shared
  spectral results, restricted low rank exponentiation, and Gram state identities, holds.
* `clause19_endpoint`: The endpoint specification `clause19EndpointSpec`, collecting finite copy
  discrimination, resource and error formulas, score maximization, and copy budget properties,
  holds.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.CopyEvolution.SelfTomography

set_option autoImplicit false

namespace Qatlib.Papers.QuantumPCA14.FeatureReadout

open Matrix Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

/-- The score of the selected cluster equals the maximal observable score. -/
theorem clusterAssignment_maximizes {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) :
    score x (clusterAssignment score x) = maximalObservableScore score x := by
  have hm : clusterAssignment score x ∈ maximalScoreIndices score x :=
    Finset.min'_mem _ _
  simp only [maximalScoreIndices, Finset.mem_filter] at hm
  exact hm.2

/-- The endpoint specification `clause16EndpointSpec` for shared loading holds. -/
theorem clause16_endpoint : clause16EndpointSpec := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.walkGoal_endpoint

/-- The endpoint specification `clause17EndpointSpec`, combining shared spectral results,
restricted low rank exponentiation, and Gram state identities, holds. -/
theorem clause17_endpoint : clause17EndpointSpec := by
  refine ⟨?_, ?_, ?_⟩
  · exact Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.clause16_endpoint
  · exact lowRankExponentiationRestricted
  · intro r d ψ hψ w hw hsumw
    exact gramFirstRegisterDensity r d ψ hψ w hw hsumw

/-- The endpoint specification `clause19EndpointSpec`, collecting finite copy discrimination,
resource and error formulas, score maximization, and copy budget properties, holds. -/
theorem clause19_endpoint : clause19EndpointSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteCopyHelstromDiscrimination
  · exact trainingSetFiniteDiscrimination
  · intro M n hM
    have h1 := twoSpeciesQPEResources_same_path 1 M n hM
    rw [h1, copyQPEProgramResources_eq]
    have h2 := (counted_offgrid_qpe_clean_flag M hM (1 : Operator 1)
      (0 : QState (Fin 1))).2.1
    rw [h2]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · intro M n γ
    rfl
  · intro d M n ρ hM hρ
    have h := timedTwoSpecies_sign_masses_sum d M n ρ ρ ρ hM hρ hρ hρ
    refine ⟨?_, ?_⟩
    · rw [h]
    · rw [h]
      norm_num
  · intro m S _ _ _ score x
    exact clusterAssignment_maximizes score x
  · intro t ε R R' hε hR hRR'
    unfold Qatlib.Concepts.CopyEvolution.SelfTomography.normDependentCopyBudget
    have hceil : Nat.ceil (8 * t ^ 2 * R / ε) ≤ Nat.ceil (8 * t ^ 2 * R' / ε) := by
      apply Nat.ceil_mono
      apply (div_le_iff₀ hε).2
      have heq : (8 * t ^ 2 * R' / ε) * ε = 8 * t ^ 2 * R' := by field_simp
      rw [heq]
      have h1 : t ^ 2 * R ≤ t ^ 2 * R' := mul_le_mul_of_nonneg_left hRR' (sq_nonneg t)
      have h2 : 8 * (t ^ 2 * R) ≤ 8 * (t ^ 2 * R') :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      simpa [mul_assoc] using! h2
    apply (Nat.max_le).2
    constructor
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans hceil (Nat.le_max_right _ _)
  · intro t ε R hε hR
    unfold Qatlib.Concepts.CopyEvolution.SelfTomography.normDependentCopyBudget
    exact Nat.le_max_left _ _

end Qatlib.Papers.QuantumPCA14.FeatureReadout
