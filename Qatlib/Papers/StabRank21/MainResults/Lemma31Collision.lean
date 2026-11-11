/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.ExactRankCollision

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.1 of Peleg–Shpilka–Volk (arXiv:2106.03214v2, p.7, §3)

Let `F : F_2^n → ℂ` be a function of stabilizer rank `r` with `r ≤ n/100`.
Then there are `y, z ∈ F_2^n` with `|y| ≠ |z|` and `F(y) = F(z)`.

The pinned Frozen release proves this as
`StabilizerRank.ExactRank.exact_rank_collision`
(file `.../ExactRank/ExactRankCollision/ExactRankCollision.lean`), with the
hypotheses `1 ≤ n`, `100 * r ≤ n` and `stabilizerRank F ≤ r`.  The extra
`1 ≤ n` only rules out the degenerate empty cube (where no two different
Hamming layers exist); it is not a strengthening of the mathematical content.
The Frozen proof follows the paper: extract a minimal stabilizer decomposition,
find an affine region on which every linear/quadratic/support datum is
constant, use Corollary 2.6 to translate by a small-weight vector, and obtain
a collision between different Hamming layers.
-/

set_option autoImplicit false

namespace Qatlib.Papers.StabRank21.MainResults.Lemma31Collision

open Qatlib.Concepts.PauliClifford.ExactRank

/-- **Lemma 3.1** (arXiv:2106.03214v2, p.7).  If `F : F_2^n → ℂ` has exact
stabilizer rank at most `r` and `100 r ≤ n`, then `F` takes equal values at two
points of different Hamming weight.

Reuses Frozen
`StabilizerRank.ExactRank.exact_rank_collision`;
complete proof, no `sorry`. -/
theorem lemma_3_1_rank_collision {n r : ℕ} (F : BooleanVec n → ℂ) (hn : 1 ≤ n)
    (hrn : 100 * r ≤ n) (hF : stabilizerRank F ≤ r) :
    ∃ y z : BooleanVec n, cubeWeight y ≠ cubeWeight z ∧ F y = F z :=
  exact_rank_collision F hn hrn hF

end Qatlib.Papers.StabRank21.MainResults.Lemma31Collision
