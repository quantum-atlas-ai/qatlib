/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.GroupAction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.1: the isogeny problem is an injective hidden shift problem

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Lemma 5.1 (§5, p. 9).

The source reduces isogeny construction to the abelian hidden shift problem as
follows.  For horizontally isogenous curves `E₀`, `E₁` with endomorphism ring
`O_Δ` the class group `Cl(O_Δ)` acts on the set of `j`-invariants, the action is
free and transitive (the source cites [39, Thm. 4.5]), and one puts

`f_c [b] = [b] * j(E_c)`.

Writing `[s]` for the class with `[s] * j(E₀) = j(E₁)`, Lemma 5.1 asserts

* `f₁ [b] = f₀ ([b] [s])`, and
* `f₀` is injective.

Both facts are properties of the group action alone; the module therefore states
them for an abstract group `G` acting on a type `X`, with `x₀` the base point and
`hfree` the freeness of the action at `x₀` (the only part of "free and
transitive" needed for injectivity).  Transitivity and the elliptic-curve
dictionary (`j`-invariants, `Ell_{q,n}(O_Δ)`, `Cl(O_Δ)`) are *not* formalized
here; see the PR notes for the remaining gap.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

variable {G X : Type*} [Group G] [MulAction G X]

/-- The readout function `f_c([b]) = [b] * j(E_c)` of the source, written for an
arbitrary group action: `isogenyReadout x b = b • x`. -/
def isogenyReadout (x : X) (b : G) : X := b • x

/-- **Lemma 5.1, shift identity.** If `x₁ = s • x₀` (the source's
`[s] * j(E₀) = j(E₁)`), then `f₁([b]) = f₀([b][s])` for every class `[b]`. -/
theorem lemma5_1_shift (x₀ x₁ : X) (s : G) (hs : x₁ = s • x₀) (b : G) :
    isogenyReadout x₁ b = isogenyReadout x₀ (b * s) := by
  simp only [isogenyReadout, hs, mul_smul]

/-- **Lemma 5.1, injectivity.** If the action is free at `x₀`, i.e. only the
identity class fixes `x₀`, then `f₀` is injective.  This is exactly the source's
argument: `[b] * j(E₀) = [b'] * j(E₀)` forces `[b']⁻¹[b] = 1`. -/
theorem lemma5_1_injective (x₀ : X) (hfree : ∀ g : G, g • x₀ = x₀ → g = 1) :
    Function.Injective (fun b : G => isogenyReadout x₀ b) := by
  intro a b hab
  simp only [isogenyReadout] at hab
  have hfix : (a⁻¹ * b) • x₀ = x₀ := by
    rw [mul_smul, ← hab, inv_smul_smul]
  have hone : a⁻¹ * b = 1 := hfree _ hfix
  exact inv_mul_eq_one.mp hone

/-- **Lemma 5.1 packaged.** The pair `(f₀, f₁)` hides the shift `s`: the
injectivity of `f₀` and the identity `f₁ = f₀(· s)` hold simultaneously. -/
theorem lemma5_1 (x₀ x₁ : X) (s : G) (hs : x₁ = s • x₀)
    (hfree : ∀ g : G, g • x₀ = x₀ → g = 1) :
    Function.Injective (fun b : G => isogenyReadout x₀ b) ∧
      ∀ b : G, isogenyReadout x₁ b = isogenyReadout x₀ (b * s) :=
  ⟨lemma5_1_injective x₀ hfree, fun b => lemma5_1_shift x₀ x₁ s hs b⟩

end Qatlib.Papers.EllipticIsog10.MainResults
