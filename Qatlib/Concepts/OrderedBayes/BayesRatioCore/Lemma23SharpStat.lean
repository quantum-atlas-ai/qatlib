/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

/-!
# Quadratic information gain specification

This module defines `Lemma2_3Sharp` as `Lemma2_3SharpContract` in the ordered search setting of
[BenOrHassidim2007]. The proposition bounds the expected posterior information gain below by
`queryInfo p` minus 4ε²(1 - 2p)² for a cut whose prefix mass is within ε below one half, subject
to the stated parameter bounds.

## Main definitions

* `Lemma2_3Sharp`: the information-gain proposition with an explicit quadratic error term.

## References

* [Ben-Or and Hassidim, Lemma 2.3][BenOrHassidim2007]
-/

set_option autoImplicit false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition `Lemma2_3SharpContract`, giving an expected-information lower bound of
`queryInfo p` - 4ε²(1 - 2p)² under the specified prior, cut, and parameter assumptions. -/
def Lemma2_3Sharp : Prop := Lemma2_3SharpContract

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
