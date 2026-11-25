/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TopoData14.MainResults.SourceDiracOperator

@[expose] public section

/-!
# The zero eigenvalue on the embedded simplex register

The Dirac matrix in Eq. (6) has the boundary operator in its upper
off-diagonal block. A state from the second summand is therefore in
its zero eigenspace exactly when its boundary vanishes.
-/

set_option autoImplicit false

open Matrix
open Qatlib.Papers.TopoData14.MainResults

namespace Qatlib.Papers.TopoData14.MainResults

/-- Membership in the Dirac kernel for a vector supported on the
second summand is equivalent to membership in the boundary kernel. -/
theorem dirac_block_kernel_right {α β : Type*} [Fintype α] [Fintype β]
    (p : Matrix α β ℂ) (y : β → ℂ) :
    diracBlock p *ᵥ Sum.elim 0 y = 0 ↔ p *ᵥ y = 0 := by
  have hleft : Sum.elim (0 : α → ℂ) y ∘ Sum.inl = 0 := rfl
  have hright : Sum.elim (0 : α → ℂ) y ∘ Sum.inr = y := rfl
  simp only [diracBlock, Matrix.fromBlocks_mulVec, hleft, hright,
    zero_mulVec, mulVec_zero, zero_add, add_zero]
  constructor
  · intro h
    funext x
    exact congrFun h (Sum.inl x)
  · intro h
    funext x
    cases x with
    | inl x => exact congrFun h x
    | inr x => rfl

end Qatlib.Papers.TopoData14.MainResults
