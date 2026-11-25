/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.CodeWeight

@[expose] public section

/-!
# Equal fibres of the row-dot-product map

Theorem 1 of [ShepherdBremner2009] averages over the column code `C_s`, while the Lean form
`Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.bias_eq_codeWeight` averages uniformly
over `F₂ⁿ`. The two averages agree because the row-dot-product map `a ↦ (i ↦ dot (p i) a)` is
linear: every nonempty fibre is a coset of its kernel, so all nonempty fibres have the same
cardinality. This module supplies the linearity of `rowDots` and that equal-fibre statement; the
resulting pushforward identity for the uniform average is not formalized here.

## Main statements

* `rowDots_add`: the row-dot-product map is additive.
* `fibre_card_eq_of_mem_image`: any nonempty fibre has the cardinality of the kernel.
* `fibre_card_eq_zero_of_not_mem_image`: a value outside the image has the empty fibre.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009], Theorem 1 and Appendix, Eq. (29),
  [arXiv:0809.0847](https://arxiv.org/abs/0809.0847)
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults

open Qatlib.Papers.Instantaneous08.MainResults.XProgram
open Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

attribute [local instance] Classical.propDecidable

/-- The row-dot-product map attached to the rows `p`: the codeword whose `i`th entry is the dot
product of `a` with the `i`th row. -/
def rowDots {n k : ℕ} (p : Fin k → F2Vec n) (a : F2Vec n) : Fin k → ZMod 2 :=
  fun i => dot (p i) a

/-- The row-dot-product map is additive in its vector argument. -/
theorem rowDots_add {n k : ℕ} (p : Fin k → F2Vec n) (a b : F2Vec n) :
    rowDots p (a + b) = rowDots p a + rowDots p b := by
  funext i
  simp only [rowDots, Pi.add_apply]
  change (p i) ⬝ᵥ (a + b) = (p i) ⬝ᵥ a + (p i) ⬝ᵥ b
  rw [dotProduct_add]

/-- The row-dot-product map sends zero to zero. -/
@[simp] theorem rowDots_zero {n k : ℕ} (p : Fin k → F2Vec n) : rowDots p (0 : F2Vec n) = 0 := by
  funext i
  change (p i) ⬝ᵥ (0 : F2Vec n) = 0
  rw [dotProduct_zero]

/-- Every nonempty fibre of the row-dot-product map has the cardinality of the kernel at zero,
because it is a translate of the kernel. -/
theorem fibre_card_eq_of_mem_image {n k : ℕ} (p : Fin k → F2Vec n) {c : Fin k → ZMod 2}
    (hc : ∃ a : F2Vec n, rowDots p a = c) :
    (Finset.univ.filter (fun a : F2Vec n => rowDots p a = c)).card =
      (Finset.univ.filter (fun a : F2Vec n => rowDots p a = 0)).card := by
  classical
  obtain ⟨a₀, rfl⟩ := hc
  refine Finset.card_bij (fun a _ => a + a₀) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [rowDots_add, ha]
    exact add_self_eq_zero_vec _
  · intro a1 _ a2 _ h
    exact add_right_cancel h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    refine ⟨b + a₀, ?_, ?_⟩
    · rw [rowDots_add, hb, zero_add]
    · rw [add_assoc, add_self_eq_zero_vec, add_zero]

/-- A value outside the image of the row-dot-product map has the empty fibre. -/
theorem fibre_card_eq_zero_of_not_mem_image {n k : ℕ} (p : Fin k → F2Vec n)
    {c : Fin k → ZMod 2} (hc : ¬ ∃ a : F2Vec n, rowDots p a = c) :
    (Finset.univ.filter (fun a : F2Vec n => rowDots p a = c)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a - ha
  exact hc ⟨a, ha⟩

end Qatlib.Papers.Instantaneous08.MainResults
