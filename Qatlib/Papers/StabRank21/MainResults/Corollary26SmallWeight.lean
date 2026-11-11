/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.CubeCombinatorics

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 2.6 of Peleg–Shpilka–Volk (arXiv:2106.03214v2, p.7, §2)

Let `U ⊆ F_2^n` be an affine subspace with `dim U = n − k > 0`.  Then there is
`u ∈ U` with Hamming weight `|u| ≤ k`.

The pinned Frozen release already proves exactly this statement as
`StabilizerRank.ExactRank.exists_small_weight_mem_affine`
(file `.../ExactRank/CubeCombinatorics/CubeCombinatorics.lean`): its hypothesis
is `Module.finrank (ZMod 2) ↥U.direction = n − k` together with `0 < n − k`.
The Frozen proof minimises the weight on `U` and uses
`finrank (supportedSubmodule u) + finrank U.direction ≤ n`
(from disjointness of the support direction and `U.direction`).  This file is
the paper-layer bridge and does not weaken the statement.
-/

set_option autoImplicit false

namespace Qatlib.Papers.StabRank21.MainResults.Corollary26SmallWeight

open Qatlib.Concepts.PauliClifford.ExactRank

/-- **Corollary 2.6** (arXiv:2106.03214v2, p.7).  An affine subspace
`U ⊆ F_2^n` whose direction has dimension `n − k > 0` contains a vector of
Hamming weight at most `k`.

Reuses Frozen
`StabilizerRank.ExactRank.exists_small_weight_mem_affine`
(definitionally the same statement); complete proof, no `sorry`. -/
theorem corollary_2_6_exists_small_weight
    {n k : ℕ} (U : AffineSubspace (ZMod 2) (BooleanVec n))
    (hdim : Module.finrank (ZMod 2) ↥(U.direction) = n - k) (hk : 0 < n - k) :
    ∃ u ∈ U, cubeWeight u ≤ k :=
  exists_small_weight_mem_affine U hdim hk

end Qatlib.Papers.StabRank21.MainResults.Corollary26SmallWeight
