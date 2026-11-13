/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.GibbsNorm

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 16 — Gibbs-state trace-distance perturbation (Brandão–Svore 2016)

Fixed source: arXiv:1609.05537v5, printed Lemma 16 / Eq. (85), page 19.

The source proves that for Hermitian matrices `H, H'`
`‖e^H/tr e^H − e^{H'}/tr e^{H'}‖₁ ≤ 2(e^{‖H−H'‖} − 1)`, which is exactly the
established noncommuting Gibbs bound reused below (`sdp_gibbs_perturbation_noncommuting`,
an `equivalent`-coverage theorem in `Foundations.MatrixExpTrace.GibbsNorm`).

This file only *bridges* the source notation onto that theorem: the paper's
`e^H/tr(e^H)` is the inverse-partition normalized state
`((tr e^H).re : ℂ)⁻¹ • e^H` (the trace of `e^H` is real because `H` is
Hermitian), and the paper's trace distance is `Matrix.traceNorm`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixExpTrace.GibbsNorm
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- **Source Lemma 16 (Eq. (85), printed p. 19).**

For Hermitian matrices `H, H'` of any dimension `D > 0`, the trace distance
between the Gibbs states `e^H / tr(e^H)` and `e^{H'} / tr(e^{H'})` is at most
`2 * (exp ‖H − H'‖ − 1)`.  No commutativity or closeness hypothesis is
required.

The theorem used here is:
`Qatlib.Foundations.MatrixExpTrace.GibbsNorm.sdp_gibbs_perturbation_noncommuting`. -/
theorem lemma16_gibbsTraceDistance (D : ℕ) (H H' : Operator D) (hD : 0 < D)
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
       ((Matrix.trace (NormedSpace.exp H')).re : ℂ)⁻¹ • NormedSpace.exp H') ≤
      2 * (Real.exp ‖H - H'‖ - 1) :=
  sdp_gibbs_perturbation_noncommuting D H H' hD hH hH'

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
