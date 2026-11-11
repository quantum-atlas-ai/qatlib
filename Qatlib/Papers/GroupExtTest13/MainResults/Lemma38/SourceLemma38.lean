/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroupExtTest13.MainResults.Cohomology.CohomologyDefs

set_option backward.isDefEq.respectTransparency false

/-!
# `Lemma38` — the explicit form of a factorised coboundary (claim `c009`)

Fixed source version: arXiv:1305.1327v1 (6 May 2013), Lemma 3.8, page 11
(text line 257 of `assets/1305.1327.txt`):

> Lemma 3.8. If `h ∈ B_F²(G,A)`, then there exist `α_1,…,α_m ∈ A` such that
> `h(x,y) = ∏_{i=1}^m α_i^{δ_i}`, where `δ_i = 1` if `x_i + y_i ≥ d_i` and `0`
> otherwise and `α_i = a_i^{d_i}` for some `a_i`.

The model is additive (`Cohomology/CohomologyDefs`): `G = ∏_i ℤ/d_i`,
`A` an additive commutative group.  The paper's `α_i^{δ_i}` becomes
`δ_i • α_i` and `α_i = a_i^{d_i}` becomes `α_i = (d_i : ℤ) • a_i`.

The proof is the paper's computation on page 11:
`∂v(x,y) = ∑_i (x_i + y_i - (x_i+y_i)) • a_i`, and the bracket is `d_i`
exactly when the standard representatives carry (`x_i + y_i ≥ d_i`).
This is discharged by `zmod_val_add_carry_z`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroupExtTest13.MainResults

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {A : Type*} [AddCommGroup A]

/-- **Lemma 3.8, pointwise core.**  For a factorised function `v = FForm d a`,
the coboundary of `v` at `(x,y)` is the sum of the carried multiples
`δ_i • ((d_i) • a_i)`. -/
theorem FForm_coboundary (d : ι → ℕ) [∀ i, NeZero (d i)] (a : ι → A)
    (x y : CyclicProduct d) :
    coboundary (FForm d a) x y
      = ∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • ((d i : ℤ) • a i) := by
  simp only [coboundary, FForm, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hZ : ((x i).val : ℤ) + (y i).val - (((x i) + (y i)).val : ℤ)
      = (d i : ℤ) * (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) := by
    linarith [zmod_val_add_carry_z (d i) (x i) (y i)]
  rw [← add_smul, ← sub_smul, hZ, mul_comm (d i : ℤ), mul_smul]

/-- **Lemma 3.8** (arXiv:1305.1327v1, Lemma 3.8, page 11).
If `h` is a coboundary of a factorised function `F(G,A)`, say `h = ∂(FForm d a)`,
then `h(x,y) = ∑_i δ_i • ((d_i) • a_i)` for all `x, y`, with
`δ_i = 1` iff `x_i + y_i ≥ d_i`.  Writing `α_i := (d_i) • a_i` this is the
paper's `h(x,y) = ∏ α_i^{δ_i}` with `α_i = a_i^{d_i}`. -/
theorem lemma38 (d : ι → ℕ) [∀ i, NeZero (d i)] {h : CyclicProduct d → CyclicProduct d → A}
    (hh : h ∈ BF2 (A := A) d) :
    ∃ a : ι → A, ∀ x y : CyclicProduct d,
      h x y
        = ∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • ((d i : ℤ) • a i) := by
  rcases hh with ⟨a, rfl⟩
  exact ⟨a, fun x y => FForm_coboundary d a x y⟩

end Qatlib.Papers.GroupExtTest13.MainResults
