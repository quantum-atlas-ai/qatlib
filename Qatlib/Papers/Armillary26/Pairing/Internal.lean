/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.Pairing.Ordered
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

@[expose] public section

/-!
# Internal channel permutations and cyclic station shifts

An internal action translates each station by a channel-dependent amount and
then permutes the channel.  Explicit composition and inverse formulas fix the
semidirect-product convention.  Relative-action equality is equivalent to a
channel equality together with the pointwise modular shift equation; through
`Qatlib.Concepts.CodeCert.PermBlocks.pairCancel`, these conditions imply
equality of the corresponding block products. These are purely algebraic
statements about internal equivalences.
-/

namespace Qatlib.Papers.Armillary26.Pairing

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix
open Qatlib.Concepts.CodeCert.PermBlocks

/-- The internal action `(i,j) ↦ (i + ell j, sigma j)`. -/
def intAct {p q : ℕ} (ell : Fin q → ZMod p) (sigma : Equiv.Perm (Fin q)) :
    Equiv.Perm (ZMod p × Fin q) where
  toFun x := (x.1 + ell x.2, sigma x.2)
  invFun x := (x.1 - ell (sigma.symm x.2), sigma.symm x.2)
  left_inv x := by
    rcases x with ⟨i, j⟩
    simp
  right_inv x := by
    rcases x with ⟨i, j⟩
    simp

/-- Applying an internal action gives its channel-dependent translation. -/
theorem intAct_apply {p q : ℕ} (ell : Fin q → ZMod p) (sigma : Equiv.Perm (Fin q))
    (i : ZMod p) (j : Fin q) : intAct ell sigma (i, j) = (i + ell j, sigma j) := rfl

/-- The inverse internal action subtracts the translated channel's shift. -/
theorem intAct_symm {p q : ℕ} (ell : Fin q → ZMod p) (sigma : Equiv.Perm (Fin q))
    (i : ZMod p) (j : Fin q) :
    (intAct ell sigma).symm (i, j) = (i - ell (sigma.symm j), sigma.symm j) := rfl

/-- Composition adds the second shift to the first shift at the second channel. -/
theorem intAct_mul {p q : ℕ} (ell ell' : Fin q → ZMod p)
    (sigma sigma' : Equiv.Perm (Fin q)) :
    intAct ell sigma * intAct ell' sigma' =
      intAct (fun j => ell' j + ell (sigma' j)) (sigma * sigma') := by
  apply Equiv.ext
  rintro ⟨i, j⟩
  simp [intAct, Equiv.Perm.mul_apply, add_assoc]

/-- Inversion negates shifts after applying the inverse channel permutation. -/
theorem intAct_inv {p q : ℕ} (ell : Fin q → ZMod p) (sigma : Equiv.Perm (Fin q)) :
    (intAct ell sigma)⁻¹ = intAct (fun j => -ell (sigma.symm j)) sigma⁻¹ := by
  apply Equiv.ext
  rintro ⟨i, j⟩
  simp [intAct, sub_eq_add_neg]

/-- The relative action from a base equivalence to a primed equivalence. -/
def relAct {ι : Type*} (e e' : Equiv.Perm ι) : Equiv.Perm ι := e' * e⁻¹

/-- A relative internal action applies inverse, then primed, shift and channel maps. -/
theorem relApply {p q : ℕ} (ell ell' : Fin q → ZMod p)
    (sigma sigma' : Equiv.Perm (Fin q)) (i : ZMod p) (j : Fin q) :
    relAct (intAct ell sigma) (intAct ell' sigma') (i, j) =
      (i - ell (sigma.symm j) + ell' (sigma.symm j), (sigma' * sigma⁻¹) j) := by
  simp [relAct, intAct, Equiv.Perm.mul_apply, sub_eq_add_neg, add_assoc]

/-- Equality of relative actions is equivalent to the relative equality in
`Qatlib.Concepts.CodeCert.PermBlocks.pairCancel`. -/
theorem rel_pair {ι : Type*} (x x' z z' : Equiv.Perm ι) :
    relAct x x' = relAct z z' ↔ z⁻¹ * x = (z')⁻¹ * x' := by
  constructor
  · intro h
    have hi := congrArg Inv.inv h
    simp only [relAct, mul_inv_rev, inv_inv] at hi
    calc
      z⁻¹ * x = z⁻¹ * (x * (x')⁻¹) * x' := by group
      _ = z⁻¹ * (z * (z')⁻¹) * x' := by rw [hi]
      _ = (z')⁻¹ * x' := by group
  · intro h
    have hx : x * (x')⁻¹ = z * (z')⁻¹ := by
      calc
        x * (x')⁻¹ = (z * (z⁻¹ * x)) * (x')⁻¹ := by group
        _ = (z * ((z')⁻¹ * x')) * (x')⁻¹ := by rw [h]
        _ = z * (z')⁻¹ := by group
    have hi := congrArg Inv.inv hx
    simpa only [relAct, mul_inv_rev, inv_inv] using hi

/-- Block-product equality is equivalent to equality of cross relative actions. -/
theorem K_iff_rel {K ι : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x x' z z' : Equiv.Perm ι) :
    (permMat x * (permMat z)ᵀ : Matrix ι ι K) = permMat x' * (permMat z')ᵀ ↔
      relAct x x' = relAct z z' :=
  (pairCancel x x' z z').trans (rel_pair x x' z z').symm

/-- Relative internal equality separates into channel and pointwise shift equations. -/
theorem rel_iff {p q : ℕ} (ellx ellx' ellz ellz' : Fin q → ZMod p)
    (sx sx' sz sz' : Equiv.Perm (Fin q)) :
    relAct (intAct ellx sx) (intAct ellx' sx') =
        relAct (intAct ellz sz) (intAct ellz' sz') ↔
      (sx' * sx⁻¹ = sz' * sz⁻¹) ∧
      ∀ j, ellx j - ellx' j - ellz ((sz⁻¹ * sx) j) + ellz' ((sz⁻¹ * sx) j) = 0 := by
  constructor
  · intro h
    constructor
    · apply Equiv.ext
      intro j
      have hj := congrArg (fun e : Equiv.Perm (ZMod p × Fin q) => (e (0, j)).2) h
      simpa only [relApply] using hj
    · intro j
      have hj := congrArg (fun e : Equiv.Perm (ZMod p × Fin q) => (e (0, sx j)).1) h
      simp only [relApply, Equiv.symm_apply_apply, Equiv.Perm.mul_apply] at hj
      change 0 - ellx j + ellx' j =
        0 - ellz (sz.symm (sx j)) + ellz' (sz.symm (sx j)) at hj
      calc
        ellx j - ellx' j - ellz ((sz⁻¹ * sx) j) + ellz' ((sz⁻¹ * sx) j) =
            (0 - ellz ((sz⁻¹ * sx) j) + ellz' ((sz⁻¹ * sx) j)) -
              (0 - ellx j + ellx' j) := by abel
        _ = 0 := sub_eq_zero.mpr hj.symm
  · rintro ⟨hc, hs⟩
    apply Equiv.ext
    rintro ⟨i, j⟩
    rw [relApply, relApply]
    apply Prod.ext
    · have hj := hs (sx.symm j)
      simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] at hj
      change ellx (sx.symm j) - ellx' (sx.symm j) -
        ellz (sz.symm j) + ellz' (sz.symm j) = 0 at hj
      have heq : -ellx (sx.symm j) + ellx' (sx.symm j) =
          -ellz (sz.symm j) + ellz' (sz.symm j) := by
        apply sub_eq_zero.mp
        calc
          (-ellx (sx.symm j) + ellx' (sx.symm j)) -
              (-ellz (sz.symm j) + ellz' (sz.symm j)) =
            -(ellx (sx.symm j) - ellx' (sx.symm j) -
              ellz (sz.symm j) + ellz' (sz.symm j)) := by abel
          _ = 0 := by simp [hj]
      change i - ellx (sx.symm j) + ellx' (sx.symm j) =
        i - ellz (sz.symm j) + ellz' (sz.symm j)
      calc
        i - ellx (sx.symm j) + ellx' (sx.symm j) =
            i + (-ellx (sx.symm j) + ellx' (sx.symm j)) := by abel
        _ = i + (-ellz (sz.symm j) + ellz' (sz.symm j)) := by rw [heq]
        _ = i - ellz (sz.symm j) + ellz' (sz.symm j) := by abel
    · exact congrArg (fun e : Equiv.Perm (Fin q) => e j) hc

/-- Channel and pointwise shift conditions imply the block-product pairing equality. -/
theorem K_of_shift {K : Type*} [Field K] {p q : ℕ} [NeZero p]
    (ellx ellx' ellz ellz' : Fin q → ZMod p)
    (sx sx' sz sz' : Equiv.Perm (Fin q))
    (hc : sx' * sx⁻¹ = sz' * sz⁻¹)
    (hs : ∀ j, ellx j - ellx' j - ellz ((sz⁻¹ * sx) j) + ellz' ((sz⁻¹ * sx) j) = 0) :
    (permMat (intAct ellx sx) * (permMat (intAct ellz sz))ᵀ :
        Matrix (ZMod p × Fin q) (ZMod p × Fin q) K) =
      permMat (intAct ellx' sx') * (permMat (intAct ellz' sz'))ᵀ := by
  apply (K_iff_rel (intAct ellx sx) (intAct ellx' sx')
    (intAct ellz sz) (intAct ellz' sz')).mpr
  exact (rel_iff ellx ellx' ellz ellz' sx sx' sz sz').mpr ⟨hc, hs⟩

end Qatlib.Papers.Armillary26.Pairing
