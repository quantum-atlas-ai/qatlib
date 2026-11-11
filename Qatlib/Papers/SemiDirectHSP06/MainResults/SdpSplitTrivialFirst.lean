/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct

/-!
# Splitting a factor fixed pointwise by a semidirect-product action

Given an action `φ` on `N1 × N2` that fixes the first embedded factor and preserves the second
embedded factor, `sdp_sndAction` constructs the induced action on `N2`.
`sdp_split_trivial_first` rearranges coordinates to split `N1` off as a direct factor. See
[ChiKimLee2006] for the mathematical setting.

## Main statements

* `sdp_sndAction`: constructs the induced action on the second factor.
* `sdp_split_trivial_first`: identifies the original semidirect product with `N1` times the
  induced semidirect product.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {N1 N2 P : Type*} [Group N1] [Group N2] [Group P]
variable {φ : P →* MulAut (N1 × N2)}

/-- If the action fixes the first factor pointwise and preserves the second factor, its first
output coordinate equals its first input coordinate. -/
lemma sdp_phi_fst (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1)
    (g : P) (a : N1) (b : N2) : (φ g (a, b)).1 = a := by
  have h : (a, b) = (a, 1) * (1, b) := by ext <;> simp
  rw [h, map_mul]
  simp [h1, h2]

/-- If the action fixes the first factor pointwise, its second output coordinate depends only on
the second input coordinate. -/
lemma sdp_phi_snd (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (g : P) (a : N1) (b : N2) : (φ g (a, b)).2 = (φ g (1, b)).2 := by
  have h : (a, b) = (1, b) * (a, 1) := by ext <;> simp
  rw [h, map_mul]
  simp [h1]

/-- The endomorphism of `N2` obtained by embedding into the second factor, applying `φ g`, and
projecting to `N2`. -/
def sdp_sndHom (φ : P →* MulAut (N1 × N2)) (g : P) : N2 →* N2 where
  toFun b := (φ g (1, b)).2
  map_one' := by
    change ((φ g) (1, 1)).2 = 1
    rw [show ((1 : N1), (1 : N2)) = (1 : N1 × N2) from rfl, map_one]
    rfl
  map_mul' b c := by
    change (φ g (1, b * c)).2 = (φ g (1, b)).2 * (φ g (1, c)).2
    have hp : (φ g) (1, b) * (φ g) (1, c) = (φ g) (1, b * c) := by
      rw [← map_mul]
      congr 1
      ext <;> simp
    exact (congrArg Prod.snd hp).symm

/-- The induced second-coordinate homomorphism is injective under the pointwise-fixing and
second-factor-preservation hypotheses. -/
lemma sdp_sndHom_injective (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1)
    (g : P) : Function.Injective (sdp_sndHom φ g) := by
  intro b c hbc
  have h1' : φ g (1, b) = φ g (1, c) := by
    ext
    · rw [h2, h2]
    · exact hbc
  have h2' := (φ g).injective h1'
  simpa using congrArg Prod.snd h2'

/-- The induced second-coordinate homomorphism is surjective under the pointwise-fixing and
second-factor-preservation hypotheses. -/
lemma sdp_sndHom_surjective (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1)
    (g : P) : Function.Surjective (sdp_sndHom φ g) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := (φ g).surjective (1, y)
  have ha : a = 1 := by
    have hh := sdp_phi_fst h1 h2 g a b
    rw [hab] at hh
    exact hh.symm
  subst ha
  refine ⟨b, ?_⟩
  change (φ g (1, b)).2 = y
  exact congrArg Prod.snd hab

/-- The induced second-factor automorphism under the pointwise-fixing and factor-preservation
hypotheses. -/
def sdp_sndAut (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1) (g : P) :
    MulAut N2 :=
  MulEquiv.ofBijective (sdp_sndHom φ g)
    ⟨sdp_sndHom_injective h1 h2 g, sdp_sndHom_surjective h1 h2 g⟩

/-- The induced second-factor automorphisms respect multiplication of acting-group elements. -/
lemma sdp_sndAut_map_mul (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1)
    (g1 g2 : P) :
    sdp_sndAut h1 h2 (g1 * g2) = sdp_sndAut h1 h2 g1 * sdp_sndAut h1 h2 g2 := by
  ext b
  change (φ (g1 * g2) (1, b)).2 = (φ g1 (1, (φ g2 (1, b)).2)).2
  rw [map_mul]
  have hb : (φ g2 (1, b)).1 = 1 := h2 g2 b
  have h : φ g2 (1, b) = (1, (φ g2 (1, b)).2) := by ext <;> simp [hb]
  have key : (φ g1) ((φ g2) (1, b)) = (φ g1) (1, (φ g2 (1, b)).2) := by rw [h]
  simpa using congrArg Prod.snd key

/-- The action on `N2` induced by an action on `N1 × N2` fixing the first factor pointwise and
preserving the second factor. -/
def sdp_sndAction (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1) :
    P →* MulAut N2 where
  toFun g := sdp_sndAut h1 h2 g
  map_one' := by
    ext b
    change (φ 1 (1, b)).2 = b
    simp
  map_mul' := sdp_sndAut_map_mul h1 h2

/-- An action fixing the first factor pointwise and preserving the second factor yields an
isomorphism from `(N1 × N2) ⋊ P` to `N1 × (N2 ⋊ P)` with the induced second-factor action. -/
theorem sdp_split_trivial_first (h1 : ∀ (g : P) (a : N1), φ g (a, 1) = (a, 1))
    (h2 : ∀ (g : P) (b : N2), (φ g (1, b)).1 = 1) :
    Nonempty
      ((N1 × N2) ⋊[φ] P ≃* (N1 × (N2 ⋊[sdp_sndAction h1 h2] P))) := by
  let e : ((N1 × N2) ⋊[φ] P) ≃ (N1 × (N2 ⋊[sdp_sndAction h1 h2] P)) :=
    { toFun := fun x => (x.1.1, (⟨x.1.2, x.2⟩ : N2 ⋊[sdp_sndAction h1 h2] P))
      invFun := fun y => (⟨(y.1, y.2.1), y.2.2⟩ : (N1 × N2) ⋊[φ] P)
      left_inv := by intro x; ext <;> rfl
      right_inv := by intro y; ext <;> rfl }
  refine ⟨MulEquiv.mk e ?_⟩
  intro x y
  dsimp [e]
  ext
  · simp only [SemidirectProduct.mul_def, SemidirectProduct.mul_left, Prod.fst_mul,
      sdp_phi_fst h1 h2]
  · simp only [SemidirectProduct.mul_def, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, Prod.fst_mul, Prod.snd_mul, sdp_phi_snd h1]
    rfl
  · rfl

end Qatlib.Papers.SemiDirectHSP06.MainResults
