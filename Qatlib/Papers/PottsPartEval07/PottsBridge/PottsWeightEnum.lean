/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.PottsBridge

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (q : ℕ) [NeZero q] (ends : E → V × V)

def coboundary : (V → ZMod q) →+ (E → ZMod q) where
  toFun σ := fun e => σ (ends e).1 - σ (ends e).2
  map_zero' := by
    ext e
    simp
  map_add' := by
    intro σ τ
    ext e
    simp only [Pi.add_apply]
    abel

@[simp] lemma coboundary_apply (σ : V → ZMod q) (e : E) :
    coboundary q ends σ e = σ (ends e).1 - σ (ends e).2 := rfl

def hammingWeight (w : E → ZMod q) : ℕ :=
  (Finset.univ.filter fun e => w e ≠ 0).card

def monochromatic (σ : V → ZMod q) : Finset E :=
  Finset.univ.filter fun e => σ (ends e).1 = σ (ends e).2

theorem weight_add_monochromatic (σ : V → ZMod q) :
    hammingWeight q (coboundary q ends σ) + (monochromatic q ends σ).card = Fintype.card E := by
  have hfil : (Finset.univ.filter fun e => ¬ σ (ends e).1 = σ (ends e).2)
      = (Finset.univ.filter fun e => coboundary q ends σ e ≠ 0) := by
    apply Finset.filter_congr
    intro e _
    rw [coboundary_apply]
    exact sub_ne_zero.symm
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset E)) (p := fun e => σ (ends e).1 = σ (ends e).2)
  rw [Finset.card_univ] at h
  rw [hfil] at h
  unfold hammingWeight monochromatic
  omega

noncomputable def kernelSize : ℕ :=
  (Finset.univ.filter fun σ : V → ZMod q => coboundary q ends σ = 0).card

noncomputable def codeWeightEnum (y : ℝ) : ℝ :=
  ∑ w ∈ Finset.univ.image (coboundary q ends), y ^ hammingWeight q w

theorem fiber_card_eq_kernelSize (w : E → ZMod q)
    (hw : w ∈ Finset.univ.image (coboundary q ends)) :
    (Finset.univ.filter fun σ : V → ZMod q => coboundary q ends σ = w).card
      = kernelSize q ends := by
  obtain ⟨σ₀, _hmem, rfl⟩ := Finset.mem_image.mp hw
  have hx : coboundary q ends σ₀ ∈ Set.range (coboundary q ends) := ⟨σ₀, rfl⟩
  have hy : (0 : E → ZMod q) ∈ Set.range (coboundary q ends) :=
    ⟨0, map_zero (coboundary q ends)⟩
  have h := AddMonoidHom.card_fiber_eq_of_mem_range (coboundary q ends) hx hy
  simpa [kernelSize] using h

theorem sum_coboundary_eq (y : ℝ) :
    (∑ σ : V → ZMod q, y ^ hammingWeight q (coboundary q ends σ))
      = (kernelSize q ends : ℝ)
        * ∑ w ∈ Finset.univ.image (coboundary q ends), y ^ hammingWeight q w := by
  have hmap : ∀ σ ∈ (Finset.univ : Finset (V → ZMod q)),
      coboundary q ends σ ∈ Finset.univ.image (coboundary q ends) :=
    fun σ _ => Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  have key := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ)
    (t := Finset.univ.image (coboundary q ends)) (g := coboundary q ends)
    (f := fun w => y ^ hammingWeight q w) hmap
  rw [← key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro w hw
  rw [Finset.sum_const, fiber_card_eq_kernelSize q ends w hw, nsmul_eq_mul]

noncomputable def pottsZ (y : ℝ) : ℝ :=
  ∑ σ : V → ZMod q, (y ^ (monochromatic q ends σ).card)⁻¹

theorem potts_weight_enumerator (y : ℝ) (hy : y ≠ 0) :
    y ^ Fintype.card E * pottsZ q ends y
      = (kernelSize q ends : ℝ) * codeWeightEnum q ends y := by
  have hterm : ∀ σ : V → ZMod q,
      y ^ Fintype.card E * (y ^ (monochromatic q ends σ).card)⁻¹
        = y ^ hammingWeight q (coboundary q ends σ) := by
    intro σ
    have hsum := weight_add_monochromatic q ends σ
    have hle : (monochromatic q ends σ).card ≤ Fintype.card E := by omega
    rw [← pow_sub₀ y hy hle]
    congr 1
    omega
  unfold pottsZ codeWeightEnum
  rw [show y ^ Fintype.card E * (∑ σ : V → ZMod q, (y ^ (monochromatic q ends σ).card)⁻¹)
      = ∑ σ : V → ZMod q, y ^ hammingWeight q (coboundary q ends σ) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => hterm σ)]
  exact sum_coboundary_eq q ends y

end Qatlib.Papers.PottsPartEval07.PottsBridge
