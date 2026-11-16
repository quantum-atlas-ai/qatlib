/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCssZDistanceCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 3.2.1 (arXiv:2408.07764v2, p.26, Eq (148))

Our quantum code satisfies `d_X ≥ d_Z`, so in particular `d_Z` equals the
distance of the code. The paper argues this via Claim 3.2.2 and the map `m_σ`
(Definition 3.2.1): every `Z`-logical operator gives a `X`-logical operator of
no larger weight. Both distances are `ℕ∞`-valued (`⊤` when the respective set of
logical operators is empty).

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalCssZDistance`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim321

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Claim 3.2.1 (p.26, Eq (148)): `d_Z ≤ d_X`, hence
the distance of the code is the `Z`-distance relevant to magic state distillation.
Reuses `MagicDistill.Triorthogonal.triorthogonalCssZDistance`. -/
theorem source_claim_3_2_1 :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
      triDistanceZ D ≤ triDistanceX D :=
  triorthogonalCssZDistance

end Qatlib.Papers.MagicDistill24.MainResults.Claim321
