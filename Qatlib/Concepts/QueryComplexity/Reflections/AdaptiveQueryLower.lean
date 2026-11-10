/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCompilation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
open scoped Matrix.Norms.L2Operator

variable {d n q : ℕ} [NeZero q] {W : Type} [Fintype W]

omit [NeZero q] [Fintype W] in

theorem native_budget (P : TniCircuit d) :
    instrumentCircuitQueryBudget (toInstrument P) = tniBudget P := by
  induction P with
  | halt b => rfl
  | step action P ih =>
      cases action <;> simp only [toInstrument, instrumentCircuitQueryBudget, tniBudget, ih]
  | instrument s K hK next ih =>
      simp only [toInstrument, instrumentCircuitQueryBudget, tniBudget]
      congr 1
      funext a
      exact Fin.cases rfl (fun i => ih i) a

theorem frontier1 {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : TniCircuit d) (hP : tniWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ tniEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (tniBudget P : ℝ) * maxFilterNorm input Gamma := by
  have hs (x : X) : 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x))
      (toInstrument P) rho (fun b rec => decide (decode b (restoreTniRecord P rec) = f x)) := by
    exact (toInstrument_event (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))).symm ▸ hsuccess x
  have h := phase_instrument_mixed_query_lower_bound e input f Gamma (toInstrument P)
    (toInstrument_wellFormed P hP) (fun b rec => decode b (restoreTniRecord P rec)) rho hrho eps he0 he1 hG hz hs
  simpa only [native_budget] using! h
end Qatlib.Concepts.QueryComplexity.Reflections
