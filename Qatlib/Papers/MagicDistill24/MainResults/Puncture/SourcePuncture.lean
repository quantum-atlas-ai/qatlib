/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalFromSevenfoldCodeCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: triorthogonality after puncturing (arXiv:2408.07764v2, pp.41–43, Eqs (245)–(260))

If the classical code `C = rowspace(G̃)`, with `G̃ = [[I_k, G₁], [0, G₀]]` in
standard form, is sevenfold-orthogonal (Eq (245)) and weighted-pair-orthogonal
`∑_i w_i⁵ y₁(i) y₂(i) = 0` (Eq (246)) for everywhere-nonzero weights `w`, then
the punctured matrix `G = [[G₁], [G₀]]` is triorthogonal with
`σ_i = w_{k+i}⁵` and `τ_a = w_a⁵` (Eqs (259)–(260)). The paper uses this to
conclude that `G` is a triorthogonal matrix in the sense of Definition 5.0.1.

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalFromSevenfoldCode`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Puncture

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Section 5.2 (pp.41–43, Eqs (259)–(260)):
puncturing a standard-form generator whose rowspace is sevenfold- and
weighted-pair-orthogonal yields a triorthogonal matrix.
Reuses `MagicDistill.Triorthogonal.triorthogonalFromSevenfoldCode`. -/
theorem source_puncture_triorthogonal :
    ∀ (k m' n : ℕ) (G₁ : Matrix (Fin k) (Fin n) F1024) (G₀ : Matrix (Fin m') (Fin n) F1024)
      (w : Fin k ⊕ Fin n → F1024) (_hw : ∀ j, w j ≠ 0),
      (∀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : Fin k ⊕ Fin n → F1024,
        y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
        y₃ ∈ triRowSpace (triStdGen G₁ G₀) → y₄ ∈ triRowSpace (triStdGen G₁ G₀) →
        y₅ ∈ triRowSpace (triStdGen G₁ G₀) → y₆ ∈ triRowSpace (triStdGen G₁ G₀) →
        y₇ ∈ triRowSpace (triStdGen G₁ G₀) →
          ∑ i, y₁ i * y₂ i * y₃ i * y₄ i * y₅ i * y₆ i * y₇ i = 0) →
      (∀ y₁ y₂ : Fin k ⊕ Fin n → F1024,
        y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
          ∑ i, (w i) ^ 5 * y₁ i * y₂ i = 0) →
      TriTripleOrth (triPuncture G₁ G₀) k
        ∧ TriPairOrth (triPuncture G₁ G₀) k
            (fun i => (w (Sum.inr i)) ^ 5) (fun a => (w (Sum.inl a)) ^ 5) :=
  triorthogonalFromSevenfoldCode

end Qatlib.Papers.MagicDistill24.MainResults.Puncture
