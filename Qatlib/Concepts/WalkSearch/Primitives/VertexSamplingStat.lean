/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts

/-!
# Vertex-sampling contract

`VertexSampling` names the proposition `lemma3Sampling`, which specifies a failure-count bound
for the prescribed with-replacement vertex sample. This is the sampling interface used by the
graph subset-search reductions [ChildsEisenberg2003].

## Main statements

* `VertexSampling`: the with-replacement sampling proposition.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The proposition `lemma3Sampling`, exposed as the vertex-sampling contract. -/
def VertexSampling : Prop := lemma3Sampling

end Qatlib.Concepts.WalkSearch.Primitives
