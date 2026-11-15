/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetFramework

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Papers.CheatSheet15.BornBaseline

open Qatlib

set_option synthInstance.maxSize 100000 in
def CheatSheetQuantumUpperBound : Prop :=
  ∀ (c M κ : ℕ) (_hc : 0 < c) (hκ : 0 < κ)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (Wg Wφ : Type) [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]
    (Cg : Circuit ((Fin M × Bool) × Wg)) (ψg : QState ((Fin M × Bool) × Wg))
    (Eg : Finset ((Fin M × Bool) × Wg))
    (Cφ : Circuit (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (ψφ : QState (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (Eφ : Finset (((Fin M ⊕ Fin κ) × Bool) × Wφ)),
    IsCertifying M κ hκ dom g φ →
    IsUnitaryCircuit Cg → Normalized ψg →
    IsUnitaryCircuit Cφ → Normalized ψφ →
    (∀ x : Fin M → Bool, dom x →
      1 - 1 / (6 * (c : ℝ)) ≤ MeasureProb (Run (workspaceBitOracle x) Cg ψg)
        (if g x then Eg else Egᶜ)) →
    (∀ (x : Fin M → Bool) (y : Fin κ → Bool),
      1 - 1 / (6 * (c : ℝ)) ≤ MeasureProb (Run (workspaceBitOracle (Sum.elim x y)) Cφ ψφ)
        (if φ x y then Eφ else Eφᶜ)) →
    ∃ (C : Circuit ((CheatSheetIndex c M κ × Bool) ×
          ((Fin c → ((Fin M × Bool) × Wg)) ×
            (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)))
      (ψ₀ : QState ((CheatSheetIndex c M κ × Bool) ×
          ((Fin c → ((Fin M × Bool) × Wg)) ×
            (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)))
      (E : Finset ((CheatSheetIndex c M κ × Bool) ×
          ((Fin c → ((Fin M × Bool) × Wg)) ×
            (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool))),
      IsUnitaryCircuit C ∧ Normalized ψ₀ ∧
      QueryCount C ≤ c * (QueryCount Cg + QueryCount Cφ) ∧
      ∀ z : CheatSheetIndex c M κ → Bool,
        2 / 3 ≤ MeasureProb (Run (workspaceBitOracle z) C ψ₀)
          (if cheatSheetFun (c := c) g φ z then E else Eᶜ)

end Qatlib.Papers.CheatSheet15.BornBaseline
