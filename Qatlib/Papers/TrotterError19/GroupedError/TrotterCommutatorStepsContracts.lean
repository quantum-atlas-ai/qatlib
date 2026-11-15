/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Papers.TrotterError19.GroupedError

open Matrix
open scoped Matrix.Norms.L2Operator

def TrotterCommutatorScalingSteps : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p : ℕ), 1 ≤ p →
    (∀ X ∈ xs, Xᴴ = -X) → Hᴴ = -H →
    (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t ε : ℝ, 0 < ε →
    let r := max 1 (Nat.ceil
      ((pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * ε)) ^ ((1 : ℝ) / p)))
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten
    0 < r ∧
    ‖w.prod - NormedSpace.exp (t • H)‖ ≤ ε ∧
    w.length = r * xs.length

end Qatlib.Papers.TrotterError19.GroupedError
