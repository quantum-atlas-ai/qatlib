/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.5 — a Boolean Macaulay solution lifts to a Macaulay solution

Fixed paper: arXiv:2111.00405, Lemma 5.5 on p.13.

Statement (verbatim): *Let `M₁y⃗₁ = b⃗₁` be the Macaulay linear system of a polynomial system
`F = F₁ ∪ F₂` and let `M₂y⃗₂ = b⃗₂` be the corresponding Boolean Macaulay linear system, where
the Macaulay matrix is `M̂ = [M₁ − b⃗₁]` and the Boolean Macaulay matrix is `B̂ = [M₂ − b⃗₂]`.
Then a solution `ŷ₂` of the Boolean Macaulay linear system `M₂y⃗₂ = b⃗₂` corresponds to a
solution `ŷ₁` of the Macaulay linear system `M₁y⃗₁ = b⃗₁`.*

The reduction of Lemma 5.3 turns `M̂` into `[0 B̂; I₂ B₂] = [0 M₂ −b⃗₂; I₂ B₂′ 0]`, so the
paper sets `ẑ₁ := −B₂′ŷ₂` and observes that `[ẑ₁; ŷ₂]` solves `[0 M₂; I₂ B₂′][z⃗₁; y⃗₂] =
[b⃗₂; 0]`.  That lifting step is proved below.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma55

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- **Lemma 5.5** (arXiv:2111.00405, p.13): given a solution `y₂` of the Boolean Macaulay
system `M₂y₂ = b₂`, the vector `[−B₂′y₂; y₂]` solves the reduced Macaulay system
`[0 M₂; I₂ B₂′][z₁; y₂] = [b₂; 0]`. -/
theorem lemma55_lift_solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M2 B2' : Matrix κ κ ℂ) (b2 y2 : κ → ℂ)
    (hy2 : M2 *ᵥ y2 = b2) :
    Matrix.fromBlocks (0 : Matrix κ κ ℂ) M2 (1 : Matrix κ κ ℂ) B2' *ᵥ
        (Sum.elim (-(B2' *ᵥ y2)) y2) = Sum.elim b2 (0 : κ → ℂ) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [hy2, Matrix.zero_mulVec, Matrix.one_mulVec]

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma55
