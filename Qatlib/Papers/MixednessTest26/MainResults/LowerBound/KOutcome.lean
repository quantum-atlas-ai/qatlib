/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Adaptive `k`-outcome lower bound (Corollary 1.4)

Paper: arXiv:2608.18839v3, Corollary 1.4 (page 3 of the PDF):

> The total number of copies needed for Adaptive `k`-outcome mixedness testing
> is `n = Ω( √(4^N) / (ε² min{k, 2^N}) )`.

The corollary is derived from Theorem 1.3 together with [LiuAcharya2024a, Lemma 2.3] and
`‖L_M‖_op ≤ 1`.  The PDF extraction of the displayed formula is ambiguous about
the exponent of `4^N` and the placement of `min{k,2^N}`; the quoted statement
follows the literal
`√(4^N)/(ε²·min{k,2^N})` form of the claim.

The measurement model is `MeasurementModel N` restricted to `k`-outcome POVMs
(`MeasurementModel.k = k`), and protocols are `AdaptiveFamilyProtocol` with
`Fin k` outcomes.

## Mathematical background and scope

* Fixed source: arXiv:2608.18839v3, Corollary 1.4 and §5.1.
* Proof outline: Theorem 1.3 + `‖L_M‖_op ≤ 1` (spectral norm of a
  measurement information channel) and [LiuAcharya2024a, Lemma 2.3], which bounds
  `‖L_M‖_HS = √(‖L_M‖_op ‖L_M‖₁)` by `√(min{k,2^N})` for `k`-outcome POVMs.
  This yields the displayed `Ω(√(4^N)/(ε² min{k,2^N}))` after simplification.
* Scope note: this module imports the measurement model and describes the
  corollary. The Hilbert–Schmidt norm bound for `k`-outcome MICs
  [LiuAcharya2024a, Lemma 2.3], the eigenvalue computation of Theorem 5.7, and
  the lower-bound proof are outside the scope of this file.
* Related definitions: `MeasurementModel.micLop/micL1/micScale`,
  `SourceModel.micOperatorNorm`, and `SourceModel.micTraceNorm`. Theorem 1.3 is
  described in `LowerBound/Framework.lean`.
* The trace-norm bound, obtained by summing over the `k` outcomes and using
  trace-product inequalities, gives `micScale ≤ √min{k,2^N}`. Square-root
  monotonicity then supplies the comparison in Theorem 1.3.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
