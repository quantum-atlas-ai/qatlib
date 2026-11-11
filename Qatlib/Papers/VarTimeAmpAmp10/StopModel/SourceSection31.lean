/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari

set_option backward.isDefEq.respectTransparency false

/-!
# Source §3.1 — the variable-time stopping model

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  §3.1 is printed on p.5–6.

Source §3.1 fixes the semantics of an algorithm that may stop at different
times.  The algorithm has stopping times `t_i` and stops after `t_i` with
probability `p_i`; its evolution is a sequence of unitary stages, and the
stopped part of the state must stay stopped.  Concretely the source requires:

1. once a branch has stopped, later stages do not touch it (the reached
   stopped subspace is invariant, i.e. collapse onto it commutes with every
   later stage);
2. the stopped probability mass is nondecreasing across stages, with
   nonnegative per-stage stopping increments;
3. every prefix of the stage sequence is unitary.

The frozen library proves exactly this as
`QuantumAlgorithm.Papers.VarTimeAmpAmp10.StopModel.variableTimeModelWellFormed_answer`
(the `VariableTimeModelWellFormed` Prop) for an arbitrary legal stage list with
an arbitrary legal history of reached stopping coordinates.  The paper-layer
theorem below states the three clauses in source form (invariance, monotone
mass with nonnegative increment, prefix unitarity) for explicit stages and
history and derives them from that frozen result.  Reused FQN:
`QuantumAlgorithm.Papers.VarTimeAmpAmp10.StopModel.variableTimeModelWellFormed_answer`.
-/

open Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- Fixed arXiv:1010.4458v2, §3.1 (printed p.5–6).

For any `C`-valued stage list `stages` together with a history
`history : ℕ → Finset C` of reached stopping coordinates that is *legal*
(`GrowingVtLegal stages history`), the source's three stopping-model clauses
hold:

1. every stage preserves the reached stopped subspace (collapse invariance);
2. the reached stopped mass is nondecreasing and each per-stage stopping
   increment is nonnegative;
3. every prefix run matrix `vtRunMatrix stages k` is unitary. -/
theorem source_section31
    (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hs : GrowingVtLegal stages history) :
    (∀ k, (h : k < stages.length) → ∀ ψ : QState (VtSpace C),
        Collapse (ApplyGate stages[k] ψ) (reachedStoppedSet history k)
          = Collapse ψ (reachedStoppedSet history k)) ∧
    (∀ ψ k, k < stages.length →
        reachedStoppedMass stages history ψ k ≤ reachedStoppedMass stages history ψ (k + 1) ∧
          0 ≤ reachedPstop stages history ψ k) ∧
    (∀ k, vtRunMatrix stages k ∈ Matrix.unitaryGroup (VtSpace C) ℂ) :=
  variableTimeModelWellFormed_answer C stages history hs

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
