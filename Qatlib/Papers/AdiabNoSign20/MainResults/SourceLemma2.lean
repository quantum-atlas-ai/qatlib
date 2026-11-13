/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
/-!
# Transport of Classical Query Lower Bounds Across Oracle Models (Lemma 2)

This module formalizes Lemma 2 (Section 2.2, pp. 8--9) of Hastings showing that
establishing the classical superpolynomial query lower bound for `AdNSP` in the
modified query model implies the corresponding lower bound in the original query
model.

## Main statements

* `lemma2`: Lemma 2, `NoAlgorithmBeatsInModel QueryModelKind.modified -> NoAlgorithmBeatsInModel QueryModelKind.original`.

## References

* [Hastings, 2021][Hastings2021AdiabNoSign], Section 2.2, Lemma 2, pp. 8--9.
-/

namespace Qatlib.Papers.AdiabNoSign20.MainResults.SourceLemma2

open Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel

set_option autoImplicit false

/-- **Lemma 2** (§2.2, p. 8-9).  If no algorithm beats `exp(-cN)` in the
modified query model, then no algorithm beats `exp(-cN)` in the original query
model. -/
theorem lemma2 (h : NoAlgorithmBeatsInModel QueryModelKind.modified) :
    NoAlgorithmBeatsInModel QueryModelKind.original := by
  rcases h with ⟨params, c, K, hc, hK, hmod⟩
  refine ⟨params, c, K, hc, hK, ?_⟩
  intro N hN ι R _ _ _ _ alg _ hq hsol
  exact hmod N hN ι R { alg with model := QueryModelKind.modified } rfl hq hsol

end Qatlib.Papers.AdiabNoSign20.MainResults.SourceLemma2
