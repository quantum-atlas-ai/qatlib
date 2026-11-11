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

The corollary is derived from Theorem 1.3 together with [LA24a, Lemma 2.3] and
`‖L_M‖_op ≤ 1`.  The PDF extraction of the displayed formula is ambiguous about
the exponent of `4^N` and the placement of `min{k,2^N}` (the metadata records
this OCR ambiguity); the statement below follows the literal
`√(4^N)/(ε²·min{k,2^N})` form of the claim.

The measurement model is `MeasurementModel N` restricted to `k`-outcome POVMs
(`MeasurementModel.k = k`), and protocols are `AdaptiveFamilyProtocol` with
`Fin k` outcomes.

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Corollary 1.4 and §5.1.
* Key proof route: Theorem 1.3 + `‖L_M‖_op ≤ 1` (spectral norm of a
  measurement information channel) and [LA24a, Lemma 2.3], which bounds
  `‖L_M‖_HS = √(‖L_M‖_op ‖L_M‖₁)` by `√(min{k,2^N})` for `k`-outcome POVMs.
  This yields the displayed `Ω(√(4^N)/(ε² min{k,2^N}))` after simplification.
* Lean gap: [LA24a, Lemma 2.3] (the Hilbert–Schmidt norm bound for `k`-outcome
  MICs) is not available in Frozen/Dev; it would have to be proved from the
  eigenvalue computation of Theorem 5.7, which is also missing.  The statement
  records the faithful lower-bound shape conditional on that input.
* Reusable dependencies: `MeasurementModel.micLop/micL1/micScale`,
  `SourceModel.micOperatorNorm`, `SourceModel.micTraceNorm`, and the
  (removed scaffold) `LowerBound/Framework.lean` Theorem 1.3.
* Suggested tactics: instantiate `adaptive_mic_lower_bound`, prove
  `micScale ≤ √min{k,2^N}` from the trace-norm bound
  (`Finset.sum` over the `k` outcomes and `Matrix.trace_mul` inequalities), then
  `nlinarith` with `Real.sqrt` monotonicity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
