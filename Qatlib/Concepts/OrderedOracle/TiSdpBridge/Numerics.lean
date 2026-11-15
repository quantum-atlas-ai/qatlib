/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.NumericsDefs
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.CertifiedApproximation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Qatlib
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false

/-- The approximation polynomial `cheb` agrees with `chebT`. -/
theorem approximation_is_frozen (n : ℕ) : cheb n = Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebT n :=
  cheb_eq_frozen n

/-- The degree of the degree-`n` approximation polynomial is `n`. -/
theorem approximation_degree (n : ℕ) : (cheb n).natDegree = n :=
  cheb_degree n

/-- The approximation polynomial evaluates to one at the right endpoint. -/
theorem approximation_right_endpoint (n : ℕ) : (cheb n).eval 1 = 1 :=
  cheb_endpoint_right n

/-- The approximation polynomial evaluates at negative one to the corresponding power of
negative one. -/
theorem approximation_left_endpoint (n : ℕ) : (cheb n).eval (-1) = (-1 : ℝ) ^ n :=
  cheb_endpoint_left n

/-- The numerical bit cost is the product of the degree and node budgets. -/
theorem numerical_bit_cost (b : NumericalBudget) :
    numericalBitCost b = b.degree * b.nodes := rfl

/-- The numerical coefficient count is one more than the degree budget. -/
theorem numerical_coefficient_count (b : NumericalBudget) :
    numericalCoefficientCount b = b.degree + 1 := rfl

/-- Collects the Chebyshev identification, degree and endpoint formulas, and numerical budget
accounting identities. -/
theorem clause28_endpoint :
    (∀ (n : ℕ), cheb n = Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebT n) ∧
    (∀ (n : ℕ), (cheb n).natDegree = n) ∧
    (∀ (n : ℕ), (cheb n).eval 1 = 1) ∧
    (∀ (n : ℕ), (cheb n).eval (-1) = (-1 : ℝ) ^ n) ∧
    (∀ (b : NumericalBudget), numericalBitCost b = b.degree * b.nodes) ∧
    (∀ (b : NumericalBudget), numericalCoefficientCount b = b.degree + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact approximation_is_frozen n
  · intro n
    exact approximation_degree n
  · intro n
    exact approximation_right_endpoint n
  · intro n
    exact approximation_left_endpoint n
  · intro b
    exact numerical_bit_cost b
  · intro b
    exact numerical_coefficient_count b

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
