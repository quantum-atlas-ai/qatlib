/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionDefs

/-!
# Specification of counted witness state conversion

`WitnessStateConversionAlgorithm` specifies a unitary bit-query circuit converting normalized
input states to target states from a filtered Gram certificate. The specification requires error
at most ε, explicit query and gate bounds, and exact zero-query behavior when the budget or
input length vanishes.

This is a concrete resource-accounted formulation of the witness approach in [LeeEtAl2011].

## Main statements

* `WitnessStateConversionAlgorithm`: states clean-state conversion and its resource bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical

/-- Specifies clean-state conversion from a filtered Gram certificate with Euclidean error at
most `ε`, query bound `1000000 * Nat.ceil W * conversionPrecisionPrice ε`, and the stated
gate bound. It also requires exact conversion with zero queries when `W = 0` or `n = 0`. -/
def WitnessStateConversionAlgorithm : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n : ℕ) (input : X → Fin n → Bool) (ρ σ : X → QState H) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ W →
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ) (gramFilterDelta input) W →
    0 < ε → ε ≤ 1/2 →
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
        (conversionCleanEmbed n r hr false (ρ x)) = conversionCleanEmbed n r hr true (σ x))

end Qatlib.Concepts.ConversionCore.WitnessCompile
