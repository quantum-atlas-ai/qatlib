/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Group.Submodule

/-!
# Precision for partial unitary operators

`PartialOp` consists of input and output subspaces joined by a linear isometric equivalence.
`PartialOp.Represents` expresses domain and codomain inclusion together with a relative error
bound on the original domain; the module proves additive composition error, preservation of the
bound under inversion, and zero-error self-representation. The development follows [Kitaev1995].

## Main statements

* `partialComp_error`: adds precision errors for compatible compositions.
* `partialInv_error`: transfers the error bound to inverse maps on the original codomain.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

/-- A partial unitary operator specified by domain and codomain subspaces and a linear isometric
equivalence between them. -/
structure PartialOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where

  dom : Submodule ℂ E

  cod : Submodule ℂ E

  iso : dom ≃ₗᵢ[ℂ] cod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace PartialOp

/-- The precision relation requiring inclusion of the original domain and codomain and an error
at most `δ * ‖ξ‖` on the original domain. -/
structure Represents (U U' : PartialOp E) (δ : ℝ) : Prop where

  dom_le : U.dom ≤ U'.dom

  cod_le : U.cod ≤ U'.cod

  error : ∀ ξ : U.dom,
    ‖(U.iso ξ : E) - (U'.iso ⟨ξ, dom_le ξ.2⟩ : E)‖ ≤ δ * ‖(ξ : E)‖

/-- For two compatible pairs of partial operators satisfying precision bounds `δ₁` and `δ₂`, the
composed outputs differ by at most `(δ₁ + δ₂) * ‖ξ‖` on the original input domain. This
implements the partial-operator extension of [Kitaev, 1995, Lemma 3][Kitaev1995]. -/
theorem partialComp_error (U₁ U₁' U₂ U₂' : PartialOp E) (δ₁ δ₂ : ℝ)
    (h₁ : Represents U₁ U₁' δ₁) (h₂ : Represents U₂ U₂' δ₂)
    (hc : U₁.cod ≤ U₂.dom) (hc' : U₁'.cod ≤ U₂'.dom) :
    ∀ ξ : U₁.dom,
      ‖(U₂.iso ⟨(U₁.iso ξ : U₁.cod), hc (U₁.iso ξ).2⟩ : E) -
        (U₂'.iso ⟨(U₁'.iso ⟨ξ, h₁.dom_le ξ.2⟩ : U₁'.cod),
          hc' (U₁'.iso ⟨ξ, h₁.dom_le ξ.2⟩).2⟩ : E)‖ ≤
          (δ₁ + δ₂) * ‖(ξ : E)‖ := by
  intro ξ

  let a : U₂.dom := ⟨(U₁.iso ξ : U₁.cod), hc (U₁.iso ξ).2⟩
  let b : U₂'.dom :=
    ⟨(U₁'.iso ⟨ξ, h₁.dom_le ξ.2⟩ : U₁'.cod), hc' (U₁'.iso ⟨ξ, h₁.dom_le ξ.2⟩).2⟩
  let c : U₂'.cod := U₂'.iso ⟨(a : E), h₂.dom_le a.2⟩

  have hstep1 : ‖(U₂.iso a : E) - (c : E)‖ ≤ δ₂ * ‖(a : E)‖ := by
    have hh := h₂.error a
    simpa [c] using hh

  have hstep2 : ‖(c : E) - (U₂'.iso b : E)‖ ≤ δ₁ * ‖(ξ : E)‖ := by
    have hiso : ‖(c : E) - (U₂'.iso b : E)‖
        = ‖(⟨(a : E), h₂.dom_le a.2⟩ : U₂'.dom) - b‖ := by
      have hmap : U₂'.iso ((⟨(a : E), h₂.dom_le a.2⟩ : U₂'.dom) - b)
          = U₂'.iso ⟨(a : E), h₂.dom_le a.2⟩ - U₂'.iso b := map_sub U₂'.iso _ _
      have hn := U₂'.iso.norm_map ((⟨(a : E), h₂.dom_le a.2⟩ : U₂'.dom) - b)
      rw [hmap] at hn
      simpa [c] using hn
    rw [hiso]
    have hsub : ‖(⟨(a : E), h₂.dom_le a.2⟩ : U₂'.dom) - b‖ = ‖(a : E) - (b : E)‖ := by
      simp
    rw [hsub]
    have hb : (b : E) = (U₁'.iso ⟨ξ, h₁.dom_le ξ.2⟩ : E) := rfl
    have ha : (a : E) = (U₁.iso ξ : E) := rfl
    rw [ha, hb]
    exact h₁.error ξ

  have hanorm : ‖(a : E)‖ = ‖(ξ : E)‖ := U₁.iso.norm_map ξ
  calc ‖(U₂.iso a : E) - (U₂'.iso b : E)‖
      = ‖((U₂.iso a : E) - (c : E)) + ((c : E) - (U₂'.iso b : E))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖(U₂.iso a : E) - (c : E)‖ + ‖(c : E) - (U₂'.iso b : E)‖ := norm_add_le _ _
    _ ≤ δ₂ * ‖(a : E)‖ + δ₁ * ‖(ξ : E)‖ := add_le_add hstep1 hstep2
    _ = (δ₁ + δ₂) * ‖(ξ : E)‖ := by rw [hanorm]; ring

/-- If one partial operator represents another with error `δ`, their inverse outputs on the
original codomain differ by at most `δ * ‖η‖`, as used in [Kitaev1995]. -/
theorem partialInv_error (U U' : PartialOp E) (δ : ℝ) (h : Represents U U' δ)
    (η : U.cod) :
    ‖((U'.iso.symm ⟨(η : E), h.cod_le η.2⟩ : U'.dom) : E) -
        ((U.iso.symm η : U.dom) : E)‖ ≤ δ * ‖(η : E)‖ := by
  let ξ : U.dom := U.iso.symm η
  let ξ' : U'.dom := U'.iso.symm ⟨(η : E), h.cod_le η.2⟩
  have hξ : (U.iso ξ : E) = (η : E) := by
    have hh := U.iso.apply_symm_apply η
    simpa [ξ] using congrArg (fun z : U.cod => (z : E)) hh
  have hξ' : (U'.iso ξ' : E) = (η : E) := by
    have hh := U'.iso.apply_symm_apply ⟨(η : E), h.cod_le η.2⟩
    simpa [ξ'] using congrArg (fun z : U'.cod => (z : E)) hh
  have hiso : ‖(ξ' : E) - (ξ : E)‖
      = ‖(U'.iso ξ' : E) - (U'.iso ⟨ξ, h.dom_le ξ.2⟩ : E)‖ := by
    have hmap : U'.iso (ξ' - ⟨ξ, h.dom_le ξ.2⟩)
        = U'.iso ξ' - U'.iso ⟨ξ, h.dom_le ξ.2⟩ := map_sub U'.iso _ _
    have hn := U'.iso.norm_map (ξ' - ⟨ξ, h.dom_le ξ.2⟩)
    rw [hmap] at hn
    simpa using hn.symm
  have hξnorm : ‖(ξ : E)‖ = ‖(η : E)‖ := by
    have hh := U.iso.norm_map ξ
    rw [show U.iso ξ = η from U.iso.apply_symm_apply η] at hh
    simpa using hh.symm
  calc ‖(ξ' : E) - (ξ : E)‖
      = ‖(U'.iso ξ' : E) - (U'.iso ⟨ξ, h.dom_le ξ.2⟩ : E)‖ := hiso
    _ = ‖(U.iso ξ : E) - (U'.iso ⟨ξ, h.dom_le ξ.2⟩ : E)‖ := by rw [hξ', ← hξ]
    _ ≤ δ * ‖(ξ : E)‖ := h.error ξ
    _ = δ * ‖(η : E)‖ := by rw [hξnorm]

/-- Every partial unitary operator represents itself with zero error, as used in [Kitaev1995]. -/
theorem represents_zero (U : PartialOp E) : Represents U U 0 := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  intro ξ
  simp

end PartialOp

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
