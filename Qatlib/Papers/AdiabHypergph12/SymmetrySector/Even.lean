/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

noncomputable section

open scoped BigOperators

variable {ι : Type*}

def permOp (σ : ι ≃ ι) (v : ι → ℝ) : ι → ℝ := fun i => v (σ i)

@[simp] theorem permOp_apply (σ : ι ≃ ι) (v : ι → ℝ) (i : ι) :
    permOp σ v i = v (σ i) := rfl

def permLin (σ : ι ≃ ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := permOp σ
  map_add' v w := by funext i; simp [permOp]
  map_smul' c v := by funext i; simp [permOp]

@[simp] theorem permLin_apply (σ : ι ≃ ι) (v : ι → ℝ) :
    permLin σ v = permOp σ v := rfl

theorem permOp_involutive (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (v : ι → ℝ) :
    permOp σ (permOp σ v) = v := by
  funext i
  simp [permOp, hσ]

def IsEven (σ : ι ≃ ι) (v : ι → ℝ) : Prop := permLin σ v = v

def evenSubspace (σ : ι ≃ ι) : Submodule ℝ (ι → ℝ) where
  carrier := {v | IsEven σ v}
  zero_mem' := map_zero (permLin σ)
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq, IsEven] at hv hw ⊢
    rw [map_add, hv, hw]
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, IsEven] at hv ⊢
    rw [map_smul, hv]

theorem mem_evenSubspace {σ : ι ≃ ι} {v : ι → ℝ} (hv : IsEven σ v) :
    v ∈ evenSubspace σ := hv

def uniformVec (c : ℝ) : ι → ℝ := fun _ => c

theorem uniformVec_isEven (σ : ι ≃ ι) (c : ℝ) : IsEven σ (uniformVec c) := by
  unfold IsEven permLin
  funext i
  simp [permOp, uniformVec]

theorem uniformVec_mem_evenSubspace (σ : ι ≃ ι) (c : ℝ) :
    uniformVec c ∈ evenSubspace σ :=
  mem_evenSubspace (uniformVec_isEven σ c)

theorem maps_even (σ : ι ≃ ι) (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hcomm : ∀ v, T (permLin σ v) = permLin σ (T v))
    {v : ι → ℝ} (hv : IsEven σ v) : IsEven σ (T v) := by
  simp only [IsEven] at hv ⊢
  rw [← hcomm v, hv]

theorem maps_even_pow (σ : ι ≃ ι) (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hcomm : ∀ v, T (permLin σ v) = permLin σ (T v)) (n : ℕ) :
    ∀ {v : ι → ℝ}, IsEven σ v → IsEven σ ((T ^ n) v) := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
      intro v hv
      simpa [pow_succ] using ih (maps_even σ T hcomm hv)

def bitFlip (N : ℕ) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun z := fun i => !z i
  invFun := fun z => fun i => !z i
  left_inv := by intro z; funext i; exact Bool.not_not (z i)
  right_inv := by intro z; funext i; exact Bool.not_not (z i)

theorem bitFlip_bitFlip (N : ℕ) (z : Fin N → Bool) :
    bitFlip N (bitFlip N z) = z := by
  funext i
  exact Bool.not_not (z i)

theorem uniformVec_bitFlip_even (N : ℕ) (c : ℝ) :
    IsEven (bitFlip N) (uniformVec (ι := Fin N → Bool) c) :=
  uniformVec_isEven (bitFlip N) c

end

end Qatlib.Papers.AdiabHypergph12.SymmetrySector
