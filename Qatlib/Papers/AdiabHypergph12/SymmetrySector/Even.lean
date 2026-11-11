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

/-!
# Even permutation symmetry sectors

Defines the coordinate permutation operator `permLin`, its fixed subspace `evenSubspace`, and
the global bit-flip equivalence. Constant vectors belong to this sector, and linear maps
commuting with the permutation preserve it under every natural power. See [FarhiEtAl2012].

## Main statements

* `evenSubspace`: The real subspace fixed by a coordinate permutation.
* `maps_even_pow`: Powers of a commuting linear map preserve even vectors.
* `uniformVec_bitFlip_even`: A constant vector is invariant under global bit flip.

## References

* [Farhi et al., 2012][FarhiEtAl2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

noncomputable section

open scoped BigOperators

variable {ι : Type*}

/-- Precomposition of a real coordinate vector by the equivalence `σ`. -/
def permOp (σ : ι ≃ ι) (v : ι → ℝ) : ι → ℝ := fun i => v (σ i)

/-- Evaluating the permutation operator at `i` gives `v (σ i)`. -/
@[simp] theorem permOp_apply (σ : ι ≃ ι) (v : ι → ℝ) (i : ι) :
    permOp σ v i = v (σ i) := rfl

/-- The linear map on real coordinate vectors induced by precomposition with `σ`. -/
def permLin (σ : ι ≃ ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := permOp σ
  map_add' v w := by funext i; simp [permOp]
  map_smul' c v := by funext i; simp [permOp]

/-- The permutation linear map acts by `permOp`. -/
@[simp] theorem permLin_apply (σ : ι ≃ ι) (v : ι → ℝ) :
    permLin σ v = permOp σ v := rfl

/-- An involutive coordinate permutation induces an involutive operator on vectors. -/
theorem permOp_involutive (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (v : ι → ℝ) :
    permOp σ (permOp σ v) = v := by
  funext i
  simp [permOp, hσ]

/-- The condition that a vector is fixed by `permLin σ`. -/
def IsEven (σ : ι ≃ ι) (v : ι → ℝ) : Prop := permLin σ v = v

/-- The real subspace of vectors fixed by the coordinate permutation `σ`. -/
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

/-- An even vector belongs to the fixed subspace `evenSubspace σ`. -/
theorem mem_evenSubspace {σ : ι ≃ ι} {v : ι → ℝ} (hv : IsEven σ v) :
    v ∈ evenSubspace σ := hv

/-- The constant real vector with value `c`. -/
def uniformVec (c : ℝ) : ι → ℝ := fun _ => c

/-- Every constant vector is fixed by every coordinate permutation. -/
theorem uniformVec_isEven (σ : ι ≃ ι) (c : ℝ) : IsEven σ (uniformVec c) := by
  unfold IsEven permLin
  funext i
  simp [permOp, uniformVec]

/-- Every constant vector belongs to the even subspace for any coordinate permutation
[FarhiEtAl2012]. -/
theorem uniformVec_mem_evenSubspace (σ : ι ≃ ι) (c : ℝ) :
    uniformVec c ∈ evenSubspace σ :=
  mem_evenSubspace (uniformVec_isEven σ c)

/-- A linear map commuting with `permLin σ` sends even vectors to even vectors [FarhiEtAl2012]. -/
theorem maps_even (σ : ι ≃ ι) (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hcomm : ∀ v, T (permLin σ v) = permLin σ (T v))
    {v : ι → ℝ} (hv : IsEven σ v) : IsEven σ (T v) := by
  simp only [IsEven] at hv ⊢
  rw [← hcomm v, hv]

/-- Every natural power of a linear map commuting with `permLin σ` preserves even vectors
[FarhiEtAl2012]. -/
theorem maps_even_pow (σ : ι ≃ ι) (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hcomm : ∀ v, T (permLin σ v) = permLin σ (T v)) (n : ℕ) :
    ∀ {v : ι → ℝ}, IsEven σ v → IsEven σ ((T ^ n) v) := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
      intro v hv
      simpa [pow_succ] using ih (maps_even σ T hcomm hv)

/-- The equivalence on Boolean strings that negates every bit. -/
def bitFlip (N : ℕ) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun z := fun i => !z i
  invFun := fun z => fun i => !z i
  left_inv := by intro z; funext i; exact Bool.not_not (z i)
  right_inv := by intro z; funext i; exact Bool.not_not (z i)

/-- Applying global bit flip twice returns the original Boolean string. -/
theorem bitFlip_bitFlip (N : ℕ) (z : Fin N → Bool) :
    bitFlip N (bitFlip N z) = z := by
  funext i
  exact Bool.not_not (z i)

/-- The constant vector on Boolean strings is invariant under global bit flip [FarhiEtAl2012]. -/
theorem uniformVec_bitFlip_even (N : ℕ) (c : ℝ) :
    IsEven (bitFlip N) (uniformVec (ι := Fin N → Bool) c) :=
  uniformVec_isEven (bitFlip N) c

end

end Qatlib.Papers.AdiabHypergph12.SymmetrySector
