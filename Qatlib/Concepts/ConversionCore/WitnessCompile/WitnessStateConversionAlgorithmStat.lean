/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionDefs
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
