/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversaryHam11.MainResults.HamiltonianOracleModel
import Mathlib.Analysis.Complex.Norm

set_option backward.isDefEq.respectTransparency false

/-!
# The one-dimensional progress-measure reduction

Fixed source: David Yonge-Mallo, *Adversary lower bounds in the Hamiltonian
oracle model*, arXiv:1108.2479v1 (11 Aug 2011), Section 3, pp. 3–4.

The source's proof of Theorem 3.1 (p. 3) has two halves:

* an **analytic** half — the Schrödinger evolution gives the derivative bound
  `|d/dt w^t| ≤ 2 max_j λ(Γ_j)` (source Eq. (1), p. 4), and bounded-error
  computation gives the terminal output bound `w^T ≤ ε' w^0` with
  `ε' = 2√(ε(1-ε))` (Ambainis output condition, p. 3);
* an **elementary** half — with `w^0 = λ(Γ)` and the derivative bound, one
  integrates to obtain the time lower bound (source p. 4:
  "we can integrate to obtain the theorem").

This module proves the elementary half `timeLowerBound_from_progress`, which is
purely one-dimensional real analysis (the mean value theorem plus arithmetic),
and is independent of the physics.  The analytic half is supplied by
`progressMeasure_lipschitz` and `progressMeasure_output_le` in the source files,
which are stated faithfully against the model of `HamiltonianOracleModel`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdversaryHam11.MainResults

open Matrix

/-- **Integration of the progress-measure derivative bound** (source §3, p. 4).

If a complex curve `w` satisfies the derivative bound `‖w' t‖ ≤ 2·M` on `[0,T]`,
starts at `w 0 = λ` with `λ ≥ 0`, and ends with `‖w T‖ ≤ ε'·λ`, then
`(1 - ε')·λ ≤ 2·M·T`.  This is exactly the source's final integration step:
`w^0 = λ(Γ)`, `|d/dt w^t| ≤ 2 max_j λ(Γ_j)`, `|w^T| ≤ ε' w^0`. -/
theorem timeLowerBound_from_progress
    {w w' : ℝ → ℂ} {lam M T ε' : ℝ}
    (hT : 0 ≤ T) (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hdiff : ∀ t, HasDerivAt w (w' t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖w' t‖ ≤ 2 * M)
    (h0 : w 0 = (lam : ℂ))
    (houtput : ‖w T‖ ≤ ε' * lam) :
    (1 - ε') * lam ≤ 2 * M * T := by
  have hcont : ContinuousOn w (Set.Icc (0 : ℝ) T) :=
    fun t _ => (hdiff t).continuousAt.continuousWithinAt
  -- Mean value inequality: `‖w T - w 0‖ ≤ 2M·(T - 0)`.
  have hdrift : ‖w T - w 0‖ ≤ 2 * M * T := by
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := w) (f' := w') (a := (0 : ℝ)) (b := T) (C := 2 * M) hcont
      (fun t _ => (hdiff t).hasDerivWithinAt)
      (fun t ht => hbound t (Set.Ico_subset_Icc_self ht))
    simpa using hmvt T ⟨hT, le_refl T⟩
  -- `‖w 0‖ = λ`.
  have hnorm0 : ‖w 0‖ = lam := by
    rw [h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  -- Reverse triangle inequality: `‖w 0‖ ≤ ‖w T‖ + ‖w T - w 0‖`.
  have htri : ‖w 0‖ ≤ ‖w T‖ + ‖w T - w 0‖ := by
    have heq : w 0 = w T - (w T - w 0) := by abel
    have hnormeq : ‖w 0‖ = ‖w T - (w T - w 0)‖ := congrArg norm heq
    rw [hnormeq]
    exact norm_sub_le _ _
  -- Combine: `λ - 2MT ≤ ‖w T‖ ≤ ε'λ`.
  nlinarith [houtput, hdrift, hnorm0, htri]

end Qatlib.Papers.AdversaryHam11.MainResults
