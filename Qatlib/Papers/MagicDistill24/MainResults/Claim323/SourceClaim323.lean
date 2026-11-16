/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalLogicalPaulisCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 3.2.3 (arXiv:2408.07764v2, p.27, Eqs (159)–(163))

For `a = 1, …, k`, the encoded operators acting on the `a`-th logical qudit may
be chosen as `X̄_a^β = X^(β g^a)` and `Z̄_a^γ = Z^(γ ĝ^a)`, where `g^a` is the
`a`-th row of `G` and `ĝ_i^a = τ_a⁻¹ σ_i g_i^a` (Eq (161)). These commute with
all stabilisers and satisfy the logical commutation relation
`X̄_a^β Z̄_b^γ = (-1)^(tr(βγ) δ_ab) Z̄_b^γ X̄_a^β`.

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalLogicalPaulis`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim323

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Claim 3.2.3 (p.27, Eqs (159)–(163)): the encoded
`X̄_a^β`, `Z̄_a^γ` commute with all stabilisers and realise the single-qudit
commutation phase on the logical qudits.
Reuses `MagicDistill.Triorthogonal.triorthogonalLogicalPaulis`. -/
theorem source_claim_3_2_3 :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k) (a b : Fin k) (β γ : F1024),
      (∀ w ∈ triDual (triG D),
        quditXVec (β • D.G (Fin.castLE D.hk a)) * quditZVec w
          = quditZVec w * quditXVec (β • D.G (Fin.castLE D.hk a)))
      ∧ (∀ v ∈ triG0 D,
        quditZVec (γ • triGhat D a) * quditXVec v
          = quditXVec v * quditZVec (γ • triGhat D a))
      ∧ (quditXVec (β • D.G (Fin.castLE D.hk a)) * quditZVec (γ • triGhat D b)
          = qPhase (f1024Trace (β * γ) * if a = b then 1 else 0)
              • (quditZVec (γ • triGhat D b)
                  * quditXVec (β • D.G (Fin.castLE D.hk a)))) :=
  triorthogonalLogicalPaulis

end Qatlib.Papers.MagicDistill24.MainResults.Claim323
