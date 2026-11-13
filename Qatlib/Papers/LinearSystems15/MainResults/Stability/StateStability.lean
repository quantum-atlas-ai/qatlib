/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# LinearSystems15 — stability of normalized states

Paper-layer statements for Childs–Kothari–Somma (arXiv:1511.02306), §2.2.

* `proposition9_state_perturbation` — source **Proposition 9** (p. 8): a
  Hermitian `C` with `‖C⁻¹‖ ≤ 1` and an approximation `D` with
  `‖C - D‖ ≤ ε < 1/2` give normalized states within `4ε`.  Proved here in the
  generality of real normed spaces; Hermiticity is not needed (the constant
  `2ε` of `normalize_error_of_gap` is sharper than `4ε`).
* `corollary10_state_accuracy` — source **Corollary 10** (p. 9): the analytic
  accuracy core of the LCU state-preparation corollary.  The algorithm/cost
  layer (expected `O(α/‖f(A)b‖)` uses of `P_B, U, V`, constant success
  probability) is outside the scope of this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Qatlib.Papers.LinearSystems15.MainResults.Stability


open Qatlib.Concepts.BlockEncoding.Postselection
/-! ## Proposition 9 — normalized-state stability -/

/-- **Source Proposition 9** (arXiv:1511.02306, §2.2, p. 8).
Let `C, D` be bounded operators on a real normed space with a left inverse
`Cinv` of `C` satisfying `‖Cinv‖ ≤ 1` (the paper's `‖C⁻¹‖ ≤ 1`, i.e. the
smallest singular value is at least `1`) and `‖D - C‖ ≤ ε` with `ε < 1/2`.
Then for any unit `ψ`, the normalized states `Dψ/‖Dψ‖` and `Cψ/‖Cψ‖` are at
distance at most `4ε`.

The source additionally assumes `C` Hermitian; the argument only uses the
inverse bound, so this statement is strictly more general.  Uses
`normalize_error_of_gap` (full FQN
`Qatlib.Papers.QSingValue19.QsVtStability.normalize_error_of_gap`),
which yields the sharper `2ε/‖Cψ‖ ≤ 2ε`. -/
theorem proposition9_state_perturbation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C D Cinv : E →L[ℝ] E) (ε : ℝ)
    (hCinv : ∀ x, Cinv (C x) = x) (hCinv_norm : ‖Cinv‖ ≤ 1)
    (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hCD : ‖D - C‖ ≤ ε) (ψ : E) (hψ : ‖ψ‖ = 1) :
    D ψ ≠ 0 ∧
      ‖NormedSpace.normalize (D ψ) - NormedSpace.normalize (C ψ)‖ ≤ 4 * ε := by
  -- `‖Cψ‖ ≥ ‖ψ‖ = 1`, hence the normalization gap `ε < ‖Cψ‖`.
  have hCψ_ge : 1 ≤ ‖C ψ‖ := by
    have h1 : ‖ψ‖ = ‖Cinv (C ψ)‖ := by rw [hCinv]
    calc 1 = ‖ψ‖ := hψ.symm
      _ = ‖Cinv (C ψ)‖ := h1
      _ ≤ ‖Cinv‖ * ‖C ψ‖ := ContinuousLinearMap.le_opNorm Cinv (C ψ)
      _ ≤ 1 * ‖C ψ‖ :=
          mul_le_mul_of_nonneg_right hCinv_norm (norm_nonneg _)
      _ = ‖C ψ‖ := one_mul _
  have hgap : ε < ‖C ψ‖ := by linarith
  -- `(D - C)ψ` is `ε`-close.
  have hclose : ‖D ψ - C ψ‖ ≤ ε := by
    have hsub : D ψ - C ψ = (D - C) ψ := rfl
    rw [hsub]
    calc ‖(D - C) ψ‖ ≤ ‖D - C‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm (D - C) ψ
      _ = ‖D - C‖ * 1 := by rw [hψ]
      _ ≤ ε := by rw [mul_one]; exact hCD
  obtain ⟨hy, hdist⟩ := normalize_error_of_gap hclose hgap
  refine ⟨hy, hdist.trans ?_⟩
  -- `2ε/‖Cψ‖ ≤ 2ε ≤ 4ε`.
  have hdiv : 2 * ε / ‖C ψ‖ ≤ 2 * ε :=
    div_le_self (by linarith) hCψ_ge
  linarith

/-! ## Corollary 10 — accuracy of the LCU-prepared state -/

/-- **Source Corollary 10** (arXiv:1511.02306, §2.2, p. 9), analytic core.
Let `M = Σ_i α_i T_i(A)` be `ε`-close to `f(A)` on the state `|b>` (i.e.
`‖(M - f(A)) b‖ ≤ ε`, the consequence of `f` being `ε`-close to the LCU
expansion on the spectral domain `D`) and let `|f(x)| ≥ 1` on `D` give
`1 ≤ ‖f(A) b‖` for a unit `b`.  Then the normalized LCU output `M|b>/‖M|b‖`
is `4ε`-close to `f(A)|b>/‖f(A)|b‖`.

This is the accuracy half of Corollary 10, obtained from Proposition 9 with
`C = f(A)`, `D = M` (or directly from `normalize_error_of_gap`).  The
algorithmic half — constant success probability, `O(α/‖f(A)b‖)` expected and
`O(α)` worst-case uses of `P_B, U, V` — is outside the scope of this file. It
is the LCU plus amplitude-amplification cost layer described in the docstrings
of `lemma7_nonunitary_lcu_corner`. -/
theorem corollary10_state_accuracy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M fA : E →L[ℝ] E) (ε : ℝ) (b : E) (_ : ‖b‖ = 1)
    (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hclose : ‖(M - fA) b‖ ≤ ε) (hgap1 : 1 ≤ ‖fA b‖) :
    M b ≠ 0 ∧
      ‖NormedSpace.normalize (M b) - NormedSpace.normalize (fA b)‖ ≤ 4 * ε := by
  have hgap : ε < ‖fA b‖ := by linarith
  have hcl : ‖M b - fA b‖ ≤ ε := by
    have hsub : M b - fA b = (M - fA) b := rfl
    rw [hsub]; exact hclose
  obtain ⟨hy, hdist⟩ := normalize_error_of_gap hcl hgap
  refine ⟨hy, hdist.trans ?_⟩
  have hdiv : 2 * ε / ‖fA b‖ ≤ 2 * ε :=
    div_le_self (by linarith) hgap1
  linarith

end Qatlib.Papers.LinearSystems15.MainResults.Stability
