/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

def TiInvariantProgramCharacterization : Prop :=
  ∀ (n k : ℕ) [NeZero n] (ε : ℝ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ),
    (∀ t ∈ Finset.Icc 1 k, U t ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ ∧
      tiTranslation n * U t = U t * tiTranslation n) →
    (∀ j : Fin (2*n), 1-ε ≤ Complex.normSq (Inner (tiPolynomialReadoutVector n k (ospFun n j))
      (Run (PhaseOracle (ospBit n j)) (tiInvariantQueryWord n k U) (Uniform (Fin (2*n)))))) →
    IsUnitaryCircuit (tiInvariantQueryWord n k U) ∧
    QueryCount (tiInvariantQueryWord n k U) = k ∧ GateCount (tiInvariantQueryWord n k U) = k ∧
    (∃ p : ℕ → Fin n → ℂ,
      p 0 = tiDirichletVec n ∧
      (∀ t ∈ Finset.Icc 0 k, ∑ i, Complex.normSq (p t i) = 1) ∧
      (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z^n = (-1 : ℂ)^t →
        ‖tiPolyEval (p t) z‖ = ‖tiPolyEval (p (t-1)) z‖) ∧
      1-ε ≤ Complex.normSq (p k 0) ∧
      ∀ t ∈ Finset.Icc 0 k, ∀ j : Fin (2*n),
        Run (PhaseOracle (ospBit n j)) (tiInvariantQueryWord n t U) (Uniform (Fin (2*n))) =
          ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n t (p t))) ∧
    tiPolyConditions n k ε ∧ tiSDPFeasible n k ε

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
