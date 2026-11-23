/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.RandCompiler19.ControlledDrift
public import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore

@[expose] public section

/-!
# Controlled qDRIFT at the precision-driven rotation count

Appendix D of [Campbell2019] observes that the controlled simulation of
`exp (i * (|1⟩⟨1| ⊗ H) * t)` uses the same decomposition of `H` as the uncontrolled
simulation. Consequently, for a fixed time and target accuracy `ε`, the number of component
exponentials is exactly the uncontrolled qDRIFT budget `N = qdriftSteps λ t (2 * ε)`; only
the hardware realization of each controlled rotation changes.

The locked library proves the controlled finite-diamond error at a fixed step count and the
resource ledger of a controlled path. This module composes those results at the precision
driven `N`, and states the equality of the controlled and uncontrolled gate counts for every
sampled path. The count holds at any component evolution time, in particular at
`t * λ / N`, the time used by both mixture-power maps.

## Main statements

* `controlled_qdrift_precision_rotation_budget`: at `N = qdriftSteps λ t (2 * ε)`, both the
  controlled and the uncontrolled qDRIFT channels are within `ε` in finite diamond distance,
  and every controlled and uncontrolled path has exactly `N` component exponentials.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Papers.RandCompiler19.ControlledDrift

namespace Qatlib.Papers.RandCompiler19.ControlledDrift

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators

/-- The precision-driven qDRIFT step count is always positive. -/
private theorem qdriftSteps_pos (lam t ε : ℝ) : 0 < qdriftSteps lam t ε := by
  unfold qdriftSteps
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- For a Hermitian contraction decomposition, the precision-driven qDRIFT budget uses the
same number of component exponentials in the controlled and uncontrolled simulations. At that
budget both channels are within `ε` in finite diamond distance, and every sampled controlled
or uncontrolled path has exactly `N` component exponentials. -/
theorem controlled_qdrift_precision_rotation_budget :
    ∀ (L D : ℕ) (_ : 1 ≤ L) (_ : 0 < D)
      (d : FinDist (Fin L)) (K : Fin L → Operator D)
      (lam t ε : ℝ) (_ : 0 ≤ lam) (_ : 0 < ε)
      (_ : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1),
      ∃ N : ℕ,
        0 < N ∧
        N = qdriftSteps lam t (2 * ε) ∧
        (N : ℝ) ≤ 2 * lam ^ 2 * t ^ 2 / ε + 1 ∧
        finiteDiamondDistance
          (exactQdriftMap d (fun j => controlledCopyHamiltonian D (K j)) lam t N)
          (conjBranch (copyControlledEvolution (qdriftHamiltonian d K lam) t)) ≤
            ENNReal.ofReal ε ∧
        finiteDiamondDistance (exactQdriftMap d K lam t N)
          (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤
            ENNReal.ofReal ε ∧
        ∀ (ω : Fin N → Fin L) (s : ℝ),
          GateCount (mixturePathCircuit
            (fun j => HamiltonianEvolution (controlledCopyHamiltonian D (K j)) s) ω) = N ∧
          GateCount (mixturePathCircuit (fun j => HamiltonianEvolution (K j) s) ω) = N := by
  intro L D hL hD d K lam t ε hlam hε hK
  let N := qdriftSteps lam t (2 * ε)
  have hbudget := (exact_qdrift_actual_finite_diamond_budget L D d K lam t N
    hlam (qdriftSteps_pos _ _ _) hK).2 ε hε
  refine ⟨N, hbudget.1, rfl, hbudget.2.1, ?_, hbudget.2.2, ?_⟩
  · have hcontrolled := (exact_qdrift_actual_finite_diamond_budget L (2 * D) d
      (fun j => controlledCopyHamiltonian D (K j)) lam t N hlam
      (qdriftSteps_pos _ _ _)
      (fun j => source_controlled_components D (K j) (hK j).1 (hK j).2)).2 ε hε
    rw [source_controlled_mean, ← copyControlledEvolution_hamiltonian] at hcontrolled
    exact hcontrolled.2.2
  · intro ω s
    have hcontrolled := source_controlled_path_cost L D N K ω s (fun _ => 0) hK
    have huncontrolled := qdrift_actual_fresh_path_and_component_cost L D N K ω s (fun _ => 0)
    exact ⟨hcontrolled.2.2.1, huncontrolled.2.2.2.1⟩

end Qatlib.Papers.RandCompiler19.ControlledDrift
