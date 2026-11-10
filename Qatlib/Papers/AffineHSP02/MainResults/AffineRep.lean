/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AffineHSP02.MainResults.AffineGroup
import Qatlib.Papers.AffineHSP02.HarmonicCore.GaussSums

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AffineHSP02.MainResults

open HarmonicCore (qroot)

def delta (p : ℕ) [DecidableEq (ZMod p)] (j : ZMod p) : ZMod p → ℂ :=
  fun k => if k = j then 1 else 0

noncomputable def affineRepLM (p : ℕ) [NeZero p] (g : Aff p) :
    (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun f j := (ZMod.stdAddChar (g.b * j) : ℂ) * f ((g.a : ZMod p) * j)
  map_add' := by
    intro f h
    ext j
    simp only [Pi.add_apply, mul_add]
  map_smul' := by
    intro c f
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem affineRepLM_apply (p : ℕ) [NeZero p] (g : Aff p) (f : ZMod p → ℂ)
    (j : ZMod p) :
    affineRepLM p g f j = (ZMod.stdAddChar (g.b * j) : ℂ) * f ((g.a : ZMod p) * j) :=
  rfl

noncomputable def affineRep (p : ℕ) [NeZero p] :
    Aff p →* ((ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) where
  toFun := affineRepLM p
  map_one' := by
    apply LinearMap.ext
    intro f
    funext j
    simp [affineRepLM]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro f
    change affineRepLM p (g * h) f = (affineRepLM p g).comp (affineRepLM p h) f
    rw [LinearMap.comp_apply]
    funext j
    rw [affineRepLM_apply, affineRepLM_apply, affineRepLM_apply]

    rw [Aff.mul_b, Aff.mul_a]
    have hchar : (ZMod.stdAddChar (((g.b + (g.a : ZMod p) * h.b) * j)) : ℂ)
        = (ZMod.stdAddChar (g.b * j) : ℂ) *
          (ZMod.stdAddChar (h.b * ((g.a : ZMod p) * j)) : ℂ) := by
      rw [add_mul, AddChar.map_add_eq_mul]
      push_cast
      congr 2 <;> ring
    rw [hchar]
    have harg : (((g.a * h.a : (ZMod p)ˣ)) : ZMod p) * j
        = (h.a : ZMod p) * ((g.a : ZMod p) * j) := by
      rw [Units.val_mul]
      ring
    rw [harg]
    ring

theorem affineRep_apply (p : ℕ) [NeZero p] (g : Aff p) (f : ZMod p → ℂ) (j : ZMod p) :
    affineRep p g f j = (ZMod.stdAddChar (g.b * j) : ℂ) * f ((g.a : ZMod p) * j) :=
  rfl

theorem affineRep_matrix_entry (p : ℕ) [NeZero p] [DecidableEq (ZMod p)] (g : Aff p)
    (j k : ZMod p) :
    affineRep p g (delta p k) j =
      if k = (g.a : ZMod p) * j then (ZMod.stdAddChar (g.b * j) : ℂ) else 0 := by
  rw [affineRep_apply]
  unfold delta
  by_cases h : k = (g.a : ZMod p) * j
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), mul_zero]

theorem affineRep_trans_apply (p : ℕ) [NeZero p] (b : ZMod p) (f : ZMod p → ℂ)
    (j : ZMod p) :
    affineRep p (Aff.trans b) f j = (ZMod.stdAddChar (b * j) : ℂ) * f j := by
  rw [affineRep_apply]
  simp

theorem affineRep_mult_apply (p : ℕ) [NeZero p] (a : (ZMod p)ˣ) (f : ZMod p → ℂ)
    (j : ZMod p) :
    affineRep p (Aff.mult a) f j = f ((a : ZMod p) * j) := by
  rw [affineRep_apply]
  simp

theorem affineRep_mult_delta (p : ℕ) [NeZero p] [DecidableEq (ZMod p)]
    (a : (ZMod p)ˣ) (k : ZMod p) :
    affineRep p (Aff.mult a) (delta p k) =
      delta p (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k) := by
  ext j
  rw [affineRep_mult_apply]
  unfold delta
  by_cases h : (a : ZMod p) * j = k
  · have h' : j = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k := by
      calc j = (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p)) * j := by simp
        _ = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((a : ZMod p) * j) := by ring
        _ = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k := by rw [h]
    rw [if_pos h, if_pos h']
  · have h' : j ≠ ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k := by
      intro heq
      apply h
      calc (a : ZMod p) * j
          = (a : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * k) := by rw [heq]
        _ = k := by simp
    rw [if_neg h, if_neg h']

end Qatlib.Papers.AffineHSP02.MainResults
