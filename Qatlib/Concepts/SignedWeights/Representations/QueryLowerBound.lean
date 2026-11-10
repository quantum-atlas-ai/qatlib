/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.QueryLowerBound

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

theorem theorem2_general
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ ∧
    ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) / 2) *
      advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞) := by
  have h := stageA_general_adversary_clause16_full_endpoint_v2 q n X W Y input f Γ C psi out eps
    hΓ hz hrun
  exact ⟨h.1, h.2.1⟩

theorem theorem2_boolean
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) (hc : Fintype.card Y = 2) :
    (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ ∧
    ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps))) / 2) *
      advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞) :=
  (stageA_general_adversary_clause16_full_endpoint_v2 q n X W Y input f Γ C psi out eps
    hΓ hz hrun).2.2 hc

end

end Qatlib.Concepts.SignedWeights.Representations.QueryLowerBound
