/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

/-!
# Born readout error from oracle perturbations

This module turns the circuit hybrid norm bound into an error bound for the Born probability of
any finite measurement event. `measureProb_run_sub_le_queryCount` controls the probability
change by twice the query count times the unitary oracle perturbation norm.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `measureProb_run_sub_le_queryCount`: bounds event-probability error directly.
* `measureProb_run_sub_le_queryCount_of_le`: uses a supplied upper bound on the oracle error.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For a normalized input and a unitary circuit, replacing a unitary oracle changes any
finite-event Born probability by at most `2 * QueryCount C * ‖O - P‖`. -/
theorem measureProb_run_sub_le_queryCount
    (O P : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (E : Finset I)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (hP : P ∈ Matrix.unitaryGroup I ℂ)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    |MeasureProb (Run O C ψ) E - MeasureProb (Run P C ψ) E| ≤
      2 * (QueryCount C : ℝ) * ‖O - P‖ := by
  have hhybrid := norm_run_sub_run_le_queryCount O P C ψ hO hP hC
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one] at hhybrid
  calc
    |MeasureProb (Run O C ψ) E - MeasureProb (Run P C ψ) E| ≤
        2 * ‖toEuclidean_fromVec (Run O C ψ - Run P C ψ)‖ :=
      measureProb_sub_le_two_mul_l2 _ _ E (hC.normalized_run hO hψ)
        (hC.normalized_run hP hψ)
    _ ≤ 2 * ((QueryCount C : ℝ) * ‖O - P‖) :=
      mul_le_mul_of_nonneg_left hhybrid (by norm_num)
    _ = 2 * (QueryCount C : ℝ) * ‖O - P‖ := by ring

/-- If two unitary oracles differ in operator norm by at most `δ`, their finite-event Born
probabilities differ by at most `2 * QueryCount C * δ` for a unitary circuit on a normalized
input. -/
theorem measureProb_run_sub_le_queryCount_of_le
    (O P : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (E : Finset I) (δ : ℝ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (hP : P ∈ Matrix.unitaryGroup I ℂ)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (hδ : ‖O - P‖ ≤ δ) :
    |MeasureProb (Run O C ψ) E - MeasureProb (Run P C ψ) E| ≤
      2 * (QueryCount C : ℝ) * δ :=
  (measureProb_run_sub_le_queryCount O P C ψ E hO hP hC hψ).trans
    (mul_le_mul_of_nonneg_left hδ (by positivity))

end Qatlib.Concepts.LchsSimulation.StaticLchs
