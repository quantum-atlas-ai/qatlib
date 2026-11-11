/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.GibbsNorm
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 16 (source restatement)

Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*, fixed
arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Lemma 16 is printed on p. 19, Eq. (85), and proved on pp. 19–20.

Source statement: for Hermitian `H, H′`,

`‖ e^H/tr(e^H) − e^{H′}/tr(e^{H′}) ‖₁ ≤ 2 (e^{‖H−H′‖} − 1)`  (Eq. (85)).

The matrix `e^H / tr(e^H)` is rendered as `(tr e^H)⁻¹ • e^H` (scalar inverse
times the matrix), which is the source expression.  The bound is the Frozen
answer theorem
`QuantumAlgorithm.Foundations.MatrixExpTrace.GibbsNorm.normalized_gibbs_branch_traceNorm_le`,
which proves the same statement for arbitrary nonempty finite bases and arbitrary
Hermitian `H, K` with **no commutativity assumption**; the normalised branch is
unfolded here to the paper's inverse-partition form.

The companion Frozen theorem `sdp_gibbs_perturbation_noncommuting` states the
bound directly on `Operator D`; it is restated below as the paper-layer
`Operator`-form consumer.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma16Gibbs

open Matrix

/-- Lemma 16, Eq. (85) (p. 19): `‖e^H/tr(e^H) − e^K/tr(e^K)‖₁ ≤ 2(e^{‖H−K‖} − 1)`
for Hermitian `H, K` on any nonempty finite-dimensional complex space. -/
theorem lemma16_gibbsTraceNorm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H K : Matrix I I ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
       ((Matrix.trace (NormedSpace.exp K)).re : ℂ)⁻¹ • NormedSpace.exp K) ≤
      2 * (Real.exp ‖H - K‖ - 1) := by
  have hHpos : 0 < (Matrix.trace (NormedSpace.exp H)).re :=
    Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos H hH
  have hKpos : 0 < (Matrix.trace (NormedSpace.exp K)).re :=
    Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos K hK
  have h := (Qatlib.Concepts.MatrixExpTrace.GibbsNorm.normalized_gibbs_branch_traceNorm_le
    H K hH (fun _ => hK)).2.2.2.2
  simpa only [Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch,
    if_pos hHpos, if_pos hKpos] using h

/-- Lemma 16 on the `Operator D` register used by the source algorithm (companion
Frozen theorem `sdp_gibbs_perturbation_noncommuting`). -/
theorem lemma16_operatorForm (D : ℕ)
    (H K : Qatlib.Foundations.PureStateMath.Operator D)
    (hD : 0 < D) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
       ((Matrix.trace (NormedSpace.exp K)).re : ℂ)⁻¹ • NormedSpace.exp K) ≤
      2 * (Real.exp ‖H - K‖ - 1) :=
  Qatlib.Concepts.MatrixExpTrace.GibbsNorm.sdp_gibbs_perturbation_noncommuting
    D H K hD hH hK

end Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma16Gibbs
