/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 2 — signed-adversary lower bound on bounded-error query complexity

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 2, §3 (printed pages 5 and 11):

`Q_ε(f) ≥ (1 - 2√(ε(1-ε)) - 2ε)/2 · ADV±(f)` for a general output alphabet, and
`Q_ε(f) ≥ (1 - 2√(ε(1-ε)))/2 · ADV±(f)` when `f` has Boolean output (`|Σ_O| = 2`).

The paper-layer theorem uses
`Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause16_full_endpoint_v2`
of type `g16Prop`, whose first and third conjuncts are exactly the two printed
inequalities (per-run spectral form and optimized `ADV±` form).  That theorem
includes the printed `-2ε` term and the Boolean improvement, the complex
Hermitian witness with same-output zero blocks, and the actual finite
workspace/unitary-circuit Born-event model.  The bridge does not weaken any
hypothesis: the paper's `ADV±(f)` is `advPmValue`, and the paper's
bounded-error algorithm is `IsBoundedErrorRun`.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.QueryLowerBound

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- **Theorem 2, general output alphabet (printed form).**
For a finite input set `X`, a `q`-ary query alphabet (`q ≥ 1`), a finite
workspace `W`, an output alphabet `Y`, a bounded-error run `C` with error
`ε` on `f : X → Y`, and a Hermitian adversary matrix `Γ` vanishing on
same-output pairs, the printed spectral inequality holds, and the optimized
value obeys `Q_ε(f) ≥ (1 - 2√(ε(1-ε)) - 2ε)/2 · ADV±(f)`.

This is quant-ph/0611054v2 Theorem 2 (p. 5); the optimized inequality is the
paper's `Q_ε(f) ≥ … · ADV±(f)` with `ADV± = advPmValue` and `Q_ε ≤ QueryCount C`
for every bounded-error run. -/
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

/-- **Theorem 2, Boolean output (printed improvement).**
When the output alphabet has two elements (`|Σ_O| = 2`, encoded as
`Fintype.card Y = 2`), the error parameter `ε` enters only through
`1 - 2√(ε(1-ε))` (the printed Boolean form, without the additional `-2ε`),
both for the per-run spectral inequality and for the optimized value
inequality `Q_ε(f) ≥ (1 - 2√(ε(1-ε)))/2 · ADV±(f)`.

This is quant-ph/0611054v2 Theorem 2 (p. 5), second display. -/
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

end Qatlib.Papers.NegWeights06.MainResults.QueryLowerBound
