/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalTransversalGateCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Lemma 3.2.2 (arXiv:2408.07764v2, pp.27–28, Eqs (164)–(175))

With `q = 2^s`, `s` a positive integer, and a triorthogonal matrix `G` as in
Definition 3.0.1, consider the CSS code `CSS(X, 𝒢₀; Z, 𝒢^⊥)` and `U = U_1^{(7)}`
from Eq (120). Then `U^{⊗ n}` and the encoded gate `U^{⊗ k}` act in the same way
on code states, i.e. the quantum code supports `U` transversally: `U^{⊗ n}`
multiplies each codeword `|ū⟩` by exactly the phase
`exp[iπ tr(∑_a u_a⁷)]` of the encoded gate.

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalTransversalGate`
(stated at the fixed field `q = 2^10`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Lemma322

open Matrix
open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Lemma 3.2.2 (pp.27–28, Eq (175)): the transversal
gate `(U_1^{(7)})^{⊗ n}` fixes every codeword `|ū⟩` up to the scalar phase
`exp[iπ tr(∑_a u_a⁷)]` of the encoded gate `U^{⊗ k}`.
Reuses `MagicDistill.Triorthogonal.triorthogonalTransversalGate`. -/
theorem source_lemma_3_2_2 :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k) (u : Fin k → F1024),
      tensorDiagGate u1SeventhPhase *ᵥ triCodeword D u
        = Complex.exp (Complex.I * Real.pi * ((f1024Trace (∑ a, u a ^ 7)).val : ℝ))
            • triCodeword D u :=
  triorthogonalTransversalGate

end Qatlib.Papers.MagicDistill24.MainResults.Lemma322
