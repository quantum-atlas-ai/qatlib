/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 10 (Low-degree matching)

Fixed source: arXiv:2610.01839v2, Lemma 10 and Eq. (70), p. 15.  The terms of
the finite-label expansion (69) whose insertion degree satisfies `d(z) ≤ Q`
sum exactly to the truncated path expansion
`A_Q = ∑_{|Γ| ≤ Q} d_Γ W_Γ`.

The combinatorial content is the bijection between low-degree labels `z` and
paths `Γ` of length at most `Q`; the formal statement isolates that bijection
as an equivalence `e` and proves the resulting sum identity.  This is the
"label ↔ path" matching used by the error analysis of Lemma 11.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open scoped BigOperators

/-- **Lemma 10 (Low-degree matching).** Fixed arXiv:2610.01839v2, Lemma 10,
Eq. (70), p. 15.  Let `deg` be the insertion degree of the finite-label
expansion, `d` the length of a path, `coeff` the label coefficient and `dΓ`
the path weight.  If the low-degree labels and the paths with `d(Γ) ≤ Q` are
matched by a bijection `e` preserving coefficients
(`coeff z = dΓ (e z)`), then the sum of all low-degree label terms equals the
truncated path expansion. -/
theorem source_lemma10_lowDegreeMatching
    {ι Γ : Type*} [Fintype ι] [Fintype Γ]
    (deg : ι → ℕ) (d : Γ → ℕ) (coeff : ι → ℂ) (dΓ : Γ → ℂ) (Q : ℕ)
    (e : {z : ι // deg z ≤ Q} ≃ {g : Γ // d g ≤ Q})
    (hcoeff : ∀ z : {z : ι // deg z ≤ Q}, coeff z.1 = dΓ (e z).1) :
    (∑ z : {z : ι // deg z ≤ Q}, coeff z.1) =
      (∑ g : {g : Γ // d g ≤ Q}, dΓ g.1) := by
  refine Fintype.sum_equiv e (fun z : {z : ι // deg z ≤ Q} => coeff z.1)
    (fun g : {g : Γ // d g ≤ Q} => dΓ g.1) ?_
  intro z
  exact hcoeff z

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
