/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Lemma 3.2.1 (arXiv:2408.07764v2, p.25)

The following hold for the triorthogonal matrix `G` of Definition 3.0.1:

1. the `k` rows of `G₁` are linearly independent over `𝔽_q`; and
2. `G₀ ∩ G₁ = {0}`.

The paper proves this by pairing a linear relation among the first `k` rows with
`σ_i g_i^b` and summing over `i`, extracting `c_b τ_b` using Eq (119); since
`τ ≠ 0`, every coefficient vanishes. The same pairing annihilates the `G₀` rows.

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalRowsDirect`,
restated in the paper's notation.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Lemma321

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Lemma 3.2.1 (p.25, Eqs (143)–(145)): for every
triorthogonal datum the `G₁` rows are linearly independent and `𝒢₀ ∩ 𝒢₁ = 0`.
Reuses `MagicDistill.Triorthogonal.triorthogonalRowsDirect`. -/
theorem source_lemma_3_2_1 :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
      (∀ c : Fin k → F1024,
          ∑ a, c a • D.G (Fin.castLE D.hk a) = 0 → ∀ a, c a = 0)
        ∧ triG1 D ⊓ triG0 D = ⊥ :=
  triorthogonalRowsDirect

end Qatlib.Papers.MagicDistill24.MainResults.Lemma321
