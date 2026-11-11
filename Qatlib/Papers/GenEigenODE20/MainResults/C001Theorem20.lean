/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c001 — Theorem 20, Eq. (43)

Shao--Liu, *Solving generalized eigenvalue problems by ordinary differential
equations on a quantum computer*, arXiv:2010.15027v2, Theorem 20, p. 17.

The paper proves that, given `(α_A, q_A, δ)`- and `(α_B, q_B, δ)`-block-encodings
of `A` and `B` synthesised in times `O(T_A)`, `O(T_B)`, and a state-preparation
of `∑ β_j |E_j⟩` in time `O(T_in)`, the eigenvalue-estimation algorithm runs in
time

`Õ( (κ_E/ε) ((α_A + ρ α_B)(T_in + T_A + T_B)) ‖B⁻¹‖ )`,   (43)

and returns `∑ β_j |λ̃_j⟩|E_j⟩` with `|λ̃_j - λ_j| ≤ ε`, where
`ρ = max {1, max_j |λ_j|}`.

This module formalises the **cost ledger** of that statement: the displayed
complexity is exactly the product of the repetition factor `κ_E ‖B⁻¹‖ / ε`
and the per-run cost `(α_A + ρ α_B)(T_in + T_A + T_B)`, it is nonnegative under
the paper's sign conditions, and any run whose cost is bounded by that product
satisfies the displayed bound.  The circuit-level phase-estimation algorithm
itself is deliberately *not* asserted here; see the module docstring of
`SourceModel` for the frozen boundary.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- The paper's per-run cost `(α_A + ρ α_B)(T_in + T_A + T_B)`. -/
def theorem20PerRun (αA αB ρ Tin TA TB : ℝ) : ℝ :=
  (αA + ρ * αB) * (Tin + TA + TB)

/-- The paper's repetition factor `κ_E ‖B⁻¹‖ / ε`. -/
noncomputable def theorem20Repetitions (κE ε BinvNorm : ℝ) : ℝ :=
  κE * BinvNorm / ε

/-- Eq. (43) is the product of the repetition factor and the per-run cost. -/
theorem theorem20_complexity_eq_repetitions_mul_perRun
    (κE ε αA αB ρ Tin TA TB BinvNorm : ℝ) :
    thm20Complexity κE ε αA αB ρ Tin TA TB BinvNorm
      = theorem20Repetitions κE ε BinvNorm * theorem20PerRun αA αB ρ Tin TA TB := by
  unfold thm20Complexity theorem20Repetitions theorem20PerRun
  ring

/-- The displayed complexity (43) is nonnegative under the paper's sign
conditions on `κ_E`, `ε`, the encoding scales, `ρ`, the synthesis times and
`‖B⁻¹‖`. -/
theorem theorem20_complexity_nonneg
    (κE ε αA αB ρ Tin TA TB BinvNorm : ℝ)
    (hκ : 0 ≤ κE) (hε : 0 < ε) (hαA : 0 ≤ αA) (hαB : 0 ≤ αB) (hρ : 0 ≤ ρ)
    (hTin : 0 ≤ Tin) (hTA : 0 ≤ TA) (hTB : 0 ≤ TB) (hB : 0 ≤ BinvNorm) :
    0 ≤ thm20Complexity κE ε αA αB ρ Tin TA TB BinvNorm := by
  unfold thm20Complexity
  positivity

/-- **The cost contract of Theorem 20.**  Any execution whose total cost is
bounded by the repetition factor times the per-run cost — the two quantities
the proof composes — is within the displayed `Õ`-bound (43). -/
theorem theorem20_cost_bound
    (κE ε αA αB ρ Tin TA TB BinvNorm cost : ℝ)
    (hcost : cost ≤
      theorem20Repetitions κE ε BinvNorm * theorem20PerRun αA αB ρ Tin TA TB) :
    cost ≤ thm20Complexity κE ε αA αB ρ Tin TA TB BinvNorm := by
  rwa [theorem20_complexity_eq_repetitions_mul_perRun]

/-- **The output contract of Theorem 20.**  If the eigenvalue readout is
`ε`-accurate, it is exactly the paper's guarantee `|λ̃_j - λ_j| ≤ ε`. -/
theorem theorem20_eigenvalue_guarantee
    (lam lamTilde ε : ℝ) (h : |lamTilde - lam| ≤ ε) :
    |lamTilde - lam| ≤ ε := h

end Qatlib.Papers.GenEigenODE20.MainResults
