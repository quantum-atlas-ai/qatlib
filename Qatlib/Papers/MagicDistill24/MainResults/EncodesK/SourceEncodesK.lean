/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCssEncodesKCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: encoded qudit count (arXiv:2408.07764v2, pp.25–26)

The quantum code `CSS(X, 𝒢₀; Z, 𝒢^⊥)` built from a triorthogonal matrix encodes
exactly `k` logical qudits of dimension `q = 2^10`; equivalently its stabiliser
`+1` common eigenspace (the code space) has complex dimension `q^k`. The paper
derives this from `dim 𝒢^⊥ = n − dim 𝒢 = n − (dim 𝒢₀ + k)` using both points of
Lemma 3.2.1 (Eqs (58)–(60), (146)–(147)).

This is the frozen result
`MagicDistill.Triorthogonal.triorthogonalCssEncodesK`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.EncodesK

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Section 3.2 (pp.25–26, Eqs (58)–(60), (146)–(147)):
the code space of the triorthogonal CSS code has complex dimension `q^k`, so the
code encodes exactly `k` qudits of dimension `2^10`.
Reuses `MagicDistill.Triorthogonal.triorthogonalCssEncodesK`. -/
theorem source_encodes_k :
    ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
      Module.finrank ℂ (triCodespace D) = (Fintype.card F1024) ^ k :=
  triorthogonalCssEncodesK

end Qatlib.Papers.MagicDistill24.MainResults.EncodesK
