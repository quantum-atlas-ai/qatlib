/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma53DetCertificateBlockStat
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityCertificateTree

/-!
# Deterministic query trees from certificates

This module proves `lemma53DeterministicCertificateBlock` using the certificate tree
construction. Every total Boolean function has a correct deterministic query tree of maximum
depth at most its one certificate complexity times its block sensitivity, realizing Lemma 5.3 of
[BealsEtAl2001].

## Main statements

* `lemma53DeterministicCertificateBlock`: construct a tree using at most C¹(f)bs(f) queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

/-- Every total Boolean function has a deterministic query tree computing it with maximum query
count at most its one certificate complexity times its block sensitivity. See [Beals et al.,
Lemma 5.3][BealsEtAl2001]. -/
theorem lemma53DeterministicCertificateBlock : Lemma53DeterministicCertificateBlock := by
  intro N f
  exact certificateTree_exists f

end Qatlib.Concepts.QueryComplexity.DecisionTrees
