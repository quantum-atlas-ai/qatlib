/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.Claim322DualDecompositionCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 3.2.2 (arXiv:2408.07764v2, pp.26–27, Eqs (153)–(158))

`𝒢₀^⊥ = m_σ(𝒢₁) + 𝒢^⊥`, where `m_σ` is componentwise multiplication by the
certified nonzero scalars `σ_i`; moreover the sum is direct
(`m_σ(𝒢₁) ∩ 𝒢^⊥ = {0}`). This is the generalisation of point 4 of Lemma 1 of
[13] and completes the distance argument of Claim 3.2.1.

This is the frozen result
`MagicDistill.Triorthogonal.claim322DualDecomposition`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim322

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Claim 3.2.2 (pp.26–27, Eqs (153)–(158)):
`𝒢₀^⊥ = m_σ(𝒢₁) ⊔ 𝒢^⊥` and the intersection `m_σ(𝒢₁) ∩ 𝒢^⊥` is trivial.
Reuses `MagicDistill.Triorthogonal.claim322DualDecomposition`. -/
theorem source_claim_3_2_2 :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
      triDual (triG0 D)
        = Submodule.map (mulSigmaLin D.σ) (triG1 D) ⊔ triDual (triG D)
        ∧ Submodule.map (mulSigmaLin D.σ) (triG1 D) ⊓ triDual (triG D) = ⊥ :=
  claim322DualDecomposition

end Qatlib.Papers.MagicDistill24.MainResults.Claim322
