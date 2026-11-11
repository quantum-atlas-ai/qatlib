/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SubgraphDet26.MainResults.GraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# Certificate search: the second-moment lemma and Theorems 1.5 / 3.1 and Corollary 3.2

Paper: Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for Subgraph Detection*,
fixed arXiv:2609.40263v1.

This file carries the definitions of the certificate-search engine of §2.3 and §3
at paper fidelity: the crossing family `F(j, S)` of Eq. (10), the second-moment
quantity `W` of Lemma 2.2, the certificate count `Z(x)` and the product measure
`µ_p` probability functional.  The statements of Lemma 2.2, Theorem 3.1 (Eq. (12)),
Corollary 3.2 (Eq. (13)) and Theorem 1.5 were removed: their proofs need the
finite-probability second-moment calculation over `∏ Bernoulli(p)` and the
conditioning machinery of Lemmas 3.5–3.8, which are not available; the statements
are preserved in the branch history at `161317a85`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.SubgraphDet26.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix

/-! ## Certificate families and the product measure `µ_p` -/


end Qatlib.Papers.SubgraphDet26.MainResults
