/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit

/-!
# Statement of ordered search circuit realization

This module defines `TiPolynomialActualAlgorithm`, which states that normalized polynomial data
satisfying the root matching equations realizes an explicit unitary ordered search circuit. It
includes preparation from a basis state, resource counts, translation symmetry, and readout
probabilities equal to the squared norm of the final constant coefficient. The construction
belongs to the invariant ordered search framework of [FarhiEtAl1999].

## Main statements

* `TiPolynomialActualAlgorithm`: packages circuit realization and readout guarantees from
  polynomial data.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

/-- The proposition that normalized polynomial data with the prescribed initial vector and root
matching realizes unitary query and prepared circuits with explicit resource counts and
correct-output probability `Complex.normSq (p k 0)`. -/
def TiPolynomialActualAlgorithm : Prop :=
  ∀ (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ),
    p 0 = tiDirichletVec n →
    (∀ t ∈ Finset.Icc 0 k, ∑ i, Complex.normSq (p t i) = 1) →
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z^n = (-1 : ℂ)^t →
      ‖tiPolyEval (p t) z‖ = ‖tiPolyEval (p (t-1)) z‖) →
    IsUnitaryCircuit (tiPolynomialQueryWord n k p) ∧
    IsUnitaryCircuit (tiPolynomialPreparedWord n k p) ∧
    QueryCount (tiPolynomialQueryWord n k p) = k ∧
    GateCount (tiPolynomialQueryWord n k p) = k ∧
    QueryCount (tiPolynomialPreparedWord n k p) = k ∧
    GateCount (tiPolynomialPreparedWord n k p) = k+1 ∧
    (∀ U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ,
      Step.gate U ∈ tiPolynomialQueryWord n k p → tiTranslation n * U = U * tiTranslation n) ∧
    Normalized (Uniform (Fin (2*n))) ∧ Normalized (Ket (0 : Fin (2*n))) ∧
    (∀ y z : Fin n, Inner (tiPolynomialReadoutVector n k y) (tiPolynomialReadoutVector n k z) =
      if y=z then 1 else 0) ∧
    ∀ j : Fin (2*n),
      PhaseOracle (ospBit n j) ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ ∧
      Run (PhaseOracle (ospBit n j)) (tiPolynomialQueryWord n k p) (Uniform (Fin (2*n))) =
        ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n k (p k)) ∧
      Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0) =
        Run (PhaseOracle (ospBit n j)) (tiPolynomialQueryWord n k p) (Uniform (Fin (2*n))) ∧
      Normalized (Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0)) ∧
      (∑ y : Fin n, Complex.normSq (Inner (tiPolynomialReadoutVector n k y)
        (Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0)))) = 1 ∧
      Complex.normSq (Inner (tiPolynomialReadoutVector n k (ospFun n j))
        (Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0))) =
          Complex.normSq (p k 0) ∧
      MeasureProb (Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0))
        (tiFoldedEvent n (ospFun n j)) = Complex.normSq (p k 0)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
