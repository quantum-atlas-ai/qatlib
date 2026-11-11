/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.BlockUnitary
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonPhaseAux
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Residual estimates for the Johnson walk

`jwIdealWalk` replaces the first Johnson-walk half-step by the diagonal `jwSignCorrection`. The
module computes block residual energies and bounds the Euclidean distance between the actual and
ideal walks.

The estimates combine with orthogonality to a vector concentrated at coordinate zero to localize
eigenvalues near the ideal block phases and bound their distances from 1 and −1. See
[Ambainis2007ElementDistinctness] for the mathematical background.

## Main statements

* `jwWalk_ideal_residual_norm`: norm bound for the walk perturbation.
* `jwWalk_eigenvalue_localization_of_start_weight`: localization using a start-vector weight
  bound.
* `jwIdealBlock_amplification_bounds`: bounds for amplified ideal phases.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- The complex number `1 - 2 * ε + 2 * I * sqrt (ε - ε²)` associated with an ideal Johnson-walk
block. -/
noncomputable def jwIdealBlockPhase (ε : ℝ) : ℂ :=
  (1-2*ε : ℝ) + Complex.I * (2*Real.sqrt (ε-ε*ε) : ℝ)

/-- The diagonal matrix assigning sign −1 to coordinates whose Boolean `jwPsiCoord` component is
true and sign 1 to the remaining coordinates. -/
noncomputable def jwSignCorrection (k : ℕ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ :=
  Matrix.diagonal fun i => if (jwPsiCoord k i).2 then -1 else 1

/-- The ideal Johnson walk obtained by composing `jwSignCorrection` with the second half-step
`jwStep2`. -/
noncomputable def jwIdealWalk (k r : ℕ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ :=
  jwStep2 k r * jwSignCorrection k

/-- Decomposes a sum over `Fin (2 * k + 1)` into the `k` coordinate pairs and the final
coordinate. -/
theorem jwSumPairs {A : Type*} [AddCommMonoid A] (k : ℕ)
    (f : Fin (2*k+1) → A) :
    (∑ i, f i) =
      (∑ j : Fin k, (f (jwPairIndex k false j) + f (jwPairIndex k true j))) +
        f (Fin.last (2*k)) := by
  let g : ℕ → Bool → A := fun j b =>
    f ⟨(2*j + if b then 1 else 0) % (2*k+1), Nat.mod_lt _ (by omega)⟩
  have hg : ∀ i : Fin (2*k+1), g (jwPsiCoord k i).1 (jwPsiCoord k i).2 = f i := by
    intro i
    dsimp [g]
    congr 1
    apply Fin.ext
    dsimp [jwPsiCoord]
    have hi : (2*(i.val/2) + if i.val % 2 == 1 then 1 else 0) = i.val := by
      split_ifs <;> simp_all <;> omega
    simpa only [Fin.val_mk] using!
      (congrArg (fun n : ℕ => n % (2*k+1)) hi).trans (Nat.mod_eq_of_lt i.isLt)
  have h := jwTypeSum k g
  simp only [hg] at h
  refine h.trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    congr 1 <;> congr 1 <;> apply Fin.ext <;>
      dsimp [jwPairIndex] <;> rw [Nat.mod_eq_of_lt] <;> omega
  · dsimp [g]
    congr 1
    apply Fin.ext
    simp only [Fin.val_last]
    exact Nat.mod_eq_of_lt (by omega)

/-- Applying `jwSignCorrection` multiplies each coordinate by the sign determined by its Boolean
type. -/
theorem jwSignCorrection_action (k : ℕ) (v : Fin (2*k+1) → ℂ)
    (i : Fin (2*k+1)) :
    (jwSignCorrection k *ᵥ v) i = (if (jwPsiCoord k i).2 then -1 else 1)*v i := by
  classical
  simp [jwSignCorrection, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- On a coordinate indexed by `jwPairIndex k a j`, the sign correction multiplies by −1 when
`a` is true and by 1 otherwise. -/
theorem jwSignCorrection_pair_action (k : ℕ) (v : Fin (2*k+1) → ℂ)
    (a : Bool) (j : Fin k) :
    (jwSignCorrection k *ᵥ v) (jwPairIndex k a j) =
      (if a then -1 else 1)*v (jwPairIndex k a j) := by
  rw [jwSignCorrection_action]
  cases a <;> simp [jwPairIndex,jwPsiCoord,Nat.add_mod]

/-- The sign correction fixes the final coordinate of every vector. -/
theorem jwSignCorrection_last_action (k : ℕ) (v : Fin (2*k+1) → ℂ) :
    (jwSignCorrection k *ᵥ v) (Fin.last (2*k)) = v (Fin.last (2*k)) := by
  simp [jwSignCorrection_action,jwPsiCoord]

/-- For `0 ≤ e ≤ 1`, the squared residual energy between `jwD2 e` and the diagonal sign matrix
is `4 * e` times the input energy. -/
theorem jwD2_sign_residual_energy (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (x y : ℂ) :
    Complex.normSq ((jwD2 e false false - 1)*x + jwD2 e false true*y) +
      Complex.normSq (jwD2 e true false*x + (jwD2 e true true + 1)*y) =
      4*e*(Complex.normSq x + Complex.normSq y) := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ e-e*e)
  norm_num [jwD2, Complex.normSq_apply]
  linear_combination 4*(x.re^2+x.im^2+y.re^2+y.im^2)*hs

/-- For `0 ≤ e ≤ 1`, the ideal rotation block minus the identity has squared residual energy `4
* e` times the input energy. -/
theorem jwD2_rotation_energy_sub_one (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (x y : ℂ) :
    Complex.normSq ((jwD2 e false false - 1)*x - jwD2 e false true*y) +
      Complex.normSq (jwD2 e true false*x - (jwD2 e true true + 1)*y) =
      4*e*(Complex.normSq x + Complex.normSq y) := by
  simpa using! jwD2_sign_residual_energy e he he1 x (-y)

/-- For `0 ≤ e ≤ 1`, the ideal rotation block plus the identity has squared residual energy `4 *
(1 - e)` times the input energy. -/
theorem jwD2_rotation_energy_add_one (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (x y : ℂ) :
    Complex.normSq ((jwD2 e false false + 1)*x - jwD2 e false true*y) +
      Complex.normSq (jwD2 e true false*x + (1 - jwD2 e true true)*y) =
      4*(1-e)*(Complex.normSq x + Complex.normSq y) := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ e-e*e)
  norm_num [jwD2, Complex.normSq_apply]
  linear_combination 4*(x.re^2+x.im^2+y.re^2+y.im^2)*hs

/-- Expresses the squared residual between the first half-step and the sign correction as a sum
of pair energies weighted by `4 * (k - j) / (N - r)`, when `r < N` and `k ≤ N - r`. -/
theorem jwStep1_sign_residual_energy (k N r : ℕ) (hNr : r < N)
    (hkr : k ≤ N-r) (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwStep1 k N r *ᵥ v) i -
      (jwSignCorrection k *ᵥ v) i)) =
    ∑ j : Fin k, 4*((k-j.val : ℝ)/(N-r)) *
      (Complex.normSq (v (jwPairIndex k false j)) +
        Complex.normSq (v (jwPairIndex k true j))) := by
  have hNrR : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  rw [jwSumPairs]
  rw [jwStep1_last_action, jwSignCorrection_last_action]
  simp only [sub_self, map_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have he : 0 ≤ (k-j.val : ℝ)/(N-r) :=
    div_nonneg (by
      have h : (j.val : ℝ) < k := by exact_mod_cast j.isLt
      linarith) (le_of_lt hNrR)
  have he1 : (k-j.val : ℝ)/(N-r) ≤ 1 := by
    apply (div_le_one hNrR).mpr
    have hkR : (k : ℝ) ≤ N-r := by
      have h : (k : ℝ) ≤ ((N-r : ℕ) : ℝ) := by exact_mod_cast hkr
      rw [Nat.cast_sub (by omega : r ≤ N)] at h
      exact h
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  rw [jwStep1_pair_action, jwStep1_pair_action,
    jwSignCorrection_pair_action, jwSignCorrection_pair_action]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  convert jwD2_sign_residual_energy ((k-j.val : ℝ)/(N-r)) he he1
    (v (jwPairIndex k false j)) (v (jwPairIndex k true j)) using 1
  congr 1 <;> ring_nf

/-- When `r < N` and `k ≤ N - r`, the squared residual between the first half-step and the sign
correction is at most `4 * k / (N - r)` times the input energy. -/
theorem jwStep1_sign_residual_bound (k N r : ℕ) (hNr : r < N)
    (hkr : k ≤ N-r) (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwStep1 k N r *ᵥ v) i -
      (jwSignCorrection k *ᵥ v) i)) ≤
    (4*k/(N-r) : ℝ) * ∑ i, Complex.normSq (v i) := by
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  rw [jwStep1_sign_residual_energy k N r hNr hkr]
  have hcoef : ∀ j : Fin k, 4*((k-j.val : ℝ)/(N-r)) ≤ 4*k/(N-r) := by
    intro j
    have h : ((k-j.val : ℝ)/(N-r)) ≤ (k : ℝ)/(N-r) :=
      div_le_div_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg j.val)) (le_of_lt hD)
    calc
      _ ≤ 4*((k : ℝ)/(N-r)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∑ j : Fin k, (4*k/(N-r) : ℝ)*
        (Complex.normSq (v (jwPairIndex k false j)) +
          Complex.normSq (v (jwPairIndex k true j))) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcoef j)
        (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    _ = (4*k/(N-r) : ℝ) * ∑ j : Fin k,
        (Complex.normSq (v (jwPairIndex k false j)) +
          Complex.normSq (v (jwPairIndex k true j))) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [jwSumPairs]
      exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- The second half-step preserves the sum of squared coordinate norms when `k ≤ r + 1`. -/
theorem jwStep2_energy (k r : ℕ) (hkr : k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwStep2 k r *ᵥ v) i)) =
      ∑ i, Complex.normSq (v i) := by
  have hdot : ∀ w : Fin (2*k+1) → ℂ,
      star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct,Pi.star_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  have hu := jwStep2_unitary k r hkr
  rw [Matrix.star_eq_conjTranspose] at hu
  have h : star (jwStep2 k r *ᵥ v) ⬝ᵥ (jwStep2 k r *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,hu,
      Matrix.vecMul_one]
  rw [hdot,hdot] at h
  exact Complex.ofReal_injective h

/-- Under the stated size conditions, the squared residual between the actual and ideal Johnson
walks is at most `4 * k / (N - r)` times the input energy. -/
theorem jwWalk_ideal_residual_bound (k N r : ℕ) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : k ≤ r+1) (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwWalk k N r *ᵥ v) i -
      (jwIdealWalk k r *ᵥ v) i)) ≤
    (4*k/(N-r) : ℝ) * ∑ i, Complex.normSq (v i) := by
  have hvec : jwWalk k N r *ᵥ v - jwIdealWalk k r *ᵥ v =
      jwStep2 k r *ᵥ (jwStep1 k N r *ᵥ v - jwSignCorrection k *ᵥ v) := by
    simp only [jwWalk,jwIdealWalk,Matrix.mulVec_mulVec,Matrix.mulVec_sub]
  change (∑ i, Complex.normSq ((jwWalk k N r *ᵥ v - jwIdealWalk k r *ᵥ v) i)) ≤ _
  rw [hvec,jwStep2_energy k r hkr]
  exact jwStep1_sign_residual_bound k N r hNr hkN v

/-- The sign correction acts on reversed pair coordinates by the sign determined by the Boolean
pair label. -/
theorem jwSignCorrection_rev_pair_action (k : ℕ) (v : Fin (2*k+1) → ℂ)
    (a : Bool) (j : Fin k) :
    (jwSignCorrection k *ᵥ v) (jwPairIndex k a j).rev =
      (if a then -1 else 1)*v (jwPairIndex k a j).rev := by
  rw [jwSignCorrection_action]
  have ha : (jwPsiCoord k (jwPairIndex k a j).rev).2 = a := by
    cases a <;> simp [jwPsiCoord,jwPairIndex,Fin.val_rev] <;> omega
  rw [ha]

/-- Expresses the ideal walk on each reversed pair as the corresponding `jwD2` block with the
second input coordinate negated. -/
theorem jwIdealWalk_pair_action (k r : ℕ) (v : Fin (2*k+1) → ℂ)
    (a : Bool) (j : Fin k) :
    (jwIdealWalk k r *ᵥ v) (jwPairIndex k a j).rev =
      jwD2 ((k-j.val : ℝ)/(r+1)) a false*v (jwPairIndex k false j).rev -
        jwD2 ((k-j.val : ℝ)/(r+1)) a true*v (jwPairIndex k true j).rev := by
  rw [jwIdealWalk,← Matrix.mulVec_mulVec,jwStep2_pair_action,
    jwSignCorrection_rev_pair_action,jwSignCorrection_rev_pair_action]
  simp [sub_eq_add_neg]

/-- The ideal Johnson walk fixes coordinate zero of every vector. -/
theorem jwIdealWalk_zero_action (k r : ℕ) (v : Fin (2*k+1) → ℂ) :
    (jwIdealWalk k r *ᵥ v) 0 = v 0 := by
  rw [jwIdealWalk,← Matrix.mulVec_mulVec,jwStep2_zero_action]
  simp [jwSignCorrection_action,jwPsiCoord]

/-- Decomposes a sum over `Fin (2 * k + 1)` into reversed coordinate pairs and coordinate zero. -/
theorem jwSumRevPairs {A : Type*} [AddCommMonoid A] (k : ℕ)
    (f : Fin (2*k+1) → A) :
    (∑ i, f i) =
      (∑ j : Fin k, (f (jwPairIndex k false j).rev + f (jwPairIndex k true j).rev)) +
        f 0 := by
  rw [← Equiv.sum_comp (Fin.revPerm (n := 2*k+1)) f,jwSumPairs]
  simp [Fin.revPerm]

/-- When `k ≤ r + 1`, the squared residual of the ideal walk from the identity is the sum of
reversed pair energies weighted by `4 * (k - j) / (r + 1)`. -/
theorem jwIdealWalk_energy_sub_one (k r : ℕ) (hkr : k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwIdealWalk k r *ᵥ v) i-v i)) =
      ∑ j : Fin k, 4*((k-j.val : ℝ)/(r+1)) *
        (Complex.normSq (v (jwPairIndex k false j).rev) +
          Complex.normSq (v (jwPairIndex k true j).rev)) := by
  rw [jwSumRevPairs,jwIdealWalk_zero_action]
  simp only [sub_self,map_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have he : 0 ≤ (k-j.val : ℝ)/(r+1) := by
    have h : (j.val : ℝ) < k := by exact_mod_cast j.isLt
    exact div_nonneg (by linarith) (by positivity)
  have he1 : (k-j.val : ℝ)/(r+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have h : (k : ℝ) ≤ r+1 := by exact_mod_cast hkr
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  rw [jwIdealWalk_pair_action,jwIdealWalk_pair_action]
  convert jwD2_rotation_energy_sub_one ((k-j.val : ℝ)/(r+1)) he he1
    (v (jwPairIndex k false j).rev) (v (jwPairIndex k true j).rev) using 1
  congr 1 <;> ring_nf

/-- When `k ≤ r + 1`, the squared norm of the ideal walk plus the input is the sum of reversed
pair energies weighted by `4 * (1 - (k - j) / (r + 1))`, together with four times the energy
at coordinate zero. -/
theorem jwIdealWalk_energy_add_one (k r : ℕ) (hkr : k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    (∑ i, Complex.normSq ((jwIdealWalk k r *ᵥ v) i+v i)) =
      (∑ j : Fin k, 4*(1-(k-j.val : ℝ)/(r+1)) *
        (Complex.normSq (v (jwPairIndex k false j).rev) +
          Complex.normSq (v (jwPairIndex k true j).rev))) + 4*Complex.normSq (v 0) := by
  rw [jwSumRevPairs,jwIdealWalk_zero_action]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    have he : 0 ≤ (k-j.val : ℝ)/(r+1) := by
      have h : (j.val : ℝ) < k := by exact_mod_cast j.isLt
      exact div_nonneg (by linarith) (by positivity)
    have he1 : (k-j.val : ℝ)/(r+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have h : (k : ℝ) ≤ r+1 := by exact_mod_cast hkr
      linarith [Nat.cast_nonneg (α := ℝ) j.val]
    rw [jwIdealWalk_pair_action,jwIdealWalk_pair_action]
    convert jwD2_rotation_energy_add_one ((k-j.val : ℝ)/(r+1)) he he1
      (v (jwPairIndex k false j).rev) (v (jwPairIndex k true j).rev) using 1
    congr 1 <;> ring_nf
  · simp [Complex.normSq_apply]
    ring

/-- When `2 * k ≤ r + 1`, the squared norm of the ideal walk plus the input is at least twice
the input energy. -/
theorem jwIdealWalk_energy_add_one_lower (k r : ℕ) (hkr : 2*k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    2*(∑ i, Complex.normSq (v i)) ≤
      ∑ i, Complex.normSq ((jwIdealWalk k r *ᵥ v) i+v i) := by
  rw [jwIdealWalk_energy_add_one k r (by omega),jwSumRevPairs,mul_add,
    Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    have h : (2 : ℝ)*k ≤ r+1 := by exact_mod_cast hkr
    have he : (k-j.val : ℝ)/(r+1) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) j.val]
    apply mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  · nlinarith [Complex.normSq_nonneg (v 0)]

/-- The Euclidean norm of a finite complex coordinate vector, defined through `EuclideanSpace`. -/
noncomputable def jwL2Norm {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖

/-- The square of `jwL2Norm` equals the sum of the squared norms of the coordinates. -/
theorem jwL2Norm_sq {n : ℕ} (v : Fin n → ℂ) :
    jwL2Norm v^2 = ∑ i, Complex.normSq (v i) := by
  simp [jwL2Norm,EuclideanSpace.norm_sq_eq,Complex.normSq_eq_norm_sq]

/-- A nonzero vector has strictly positive `jwL2Norm`. -/
theorem jwL2Norm_pos {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) : 0 < jwL2Norm v := by
  apply norm_pos_iff.mpr
  intro h
  apply hv
  exact congrArg WithLp.ofLp h

/-- The Euclidean norm `jwL2Norm` is nonnegative. -/
theorem jwL2Norm_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ jwL2Norm v := norm_nonneg _

/-- Scaling a vector by a complex scalar multiplies `jwL2Norm` by the scalar's norm. -/
theorem jwL2Norm_smul {n : ℕ} (c : ℂ) (v : Fin n → ℂ) :
    jwL2Norm (c • v) = ‖c‖*jwL2Norm v := by
  exact norm_smul c (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))

/-- The norm `jwL2Norm` satisfies the triangle inequality. -/
theorem jwL2Norm_add_le {n : ℕ} (v w : Fin n → ℂ) :
    jwL2Norm (v+w) ≤ jwL2Norm v+jwL2Norm w := by
  exact norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 w)

/-- Under the stated size conditions, the norm of the actual-minus-ideal walk residual is at
most `2 * sqrt (k / (N - r))` times the input norm. -/
theorem jwWalk_ideal_residual_norm (k N r : ℕ) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : k ≤ r+1) (v : Fin (2*k+1) → ℂ) :
    jwL2Norm (jwWalk k N r *ᵥ v - jwIdealWalk k r *ᵥ v) ≤
      2*Real.sqrt ((k : ℝ)/(N-r))*jwL2Norm v := by
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg k) (le_of_lt hD))
  have h := jwWalk_ideal_residual_bound k N r hNr hkN hkr v
  rw [← jwL2Norm_sq,← jwL2Norm_sq] at h
  have hr : 0 ≤ 2*Real.sqrt ((k : ℝ)/(N-r))*jwL2Norm v := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (jwL2Norm_nonneg v)
  apply (sq_le_sq₀ (jwL2Norm_nonneg _) hr).mp
  calc
    _ ≤ (4*k/(N-r) : ℝ)*jwL2Norm v^2 := h
    _ = _ := by
      rw [mul_pow,mul_pow,hs]
      ring

/-- Under the stated size conditions, an eigenvalue with a nonzero eigenvector has distance at
least `sqrt 2 - 2 * sqrt (k / (N - r))` from −1. -/
theorem jwWalk_eigenvalue_gap_neg_one_sharp (k N r : ℕ) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : 2*k ≤ r+1) (μ : ℂ) (v : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v) (hv : v ≠ 0) :
    Real.sqrt 2-2*Real.sqrt ((k : ℝ)/(N-r)) ≤ ‖μ+1‖ := by
  have hlower := jwIdealWalk_energy_add_one_lower k r hkr v
  rw [← jwL2Norm_sq,← jwL2Norm_sq] at hlower
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hlo : Real.sqrt 2*jwL2Norm v ≤ jwL2Norm (jwIdealWalk k r *ᵥ v+v) := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg 2) (jwL2Norm_nonneg v))
      (jwL2Norm_nonneg _)).mp
    rw [mul_pow,hs]
    exact hlower
  have hdecomp : jwIdealWalk k r *ᵥ v+v =
      -(jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v) + (μ+1) • v := by
    rw [heigen]
    module
  have htri := jwL2Norm_add_le (-(jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)) ((μ+1) • v)
  rw [← hdecomp,jwL2Norm_smul] at htri
  have hneg : jwL2Norm (-(jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)) =
      jwL2Norm (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v) := by simp [jwL2Norm,norm_sub_rev]
  rw [hneg] at htri
  have hres := jwWalk_ideal_residual_norm k N r hNr hkN (by omega) v
  have hvp := jwL2Norm_pos v hv
  have h : (Real.sqrt 2-2*Real.sqrt ((k : ℝ)/(N-r)))*jwL2Norm v ≤
      ‖μ+1‖*jwL2Norm v := by nlinarith
  exact (mul_le_mul_iff_left₀ hvp).mp h

/-- For `k ≥ 1` and `r < N`, bounds the sharp perturbation error `2 * sqrt (k / (N - r))` by the
stated larger spectral error. -/
theorem jwSpectral_error_dominates_sharp (k N r : ℕ) (hk : 1 ≤ k) (hNr : r < N) :
    2*Real.sqrt ((k : ℝ)/(N-r)) ≤
      (2 : ℝ)^(((k : ℝ)+2)/2)*2*Real.sqrt 2*Real.sqrt ((k : ℝ)^3/(N-r)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  have hpow := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ ((k : ℝ)+2)/2)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := one_le_pow₀ hkR
  have hk3 : (k : ℝ) ≤ (k : ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  calc
    _ ≤ 2*Real.sqrt ((k : ℝ)^3/(N-r)) := by
      gcongr
    _ = 1*2*1*Real.sqrt ((k : ℝ)^3/(N-r)) := by ring
    _ ≤ _ := by gcongr

/-- Bounds the distance of a Johnson-walk eigenvalue from −1 by `sqrt 2` minus the stated
spectral error, under the given size conditions. -/
theorem jwWalk_eigenvalue_gap_neg_one (k N r : ℕ) (hk : 1 ≤ k) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : 2*k ≤ r+1) (μ : ℂ) (v : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v) (hv : v ≠ 0) :
    Real.sqrt 2 -
      (2 : ℝ)^(((k : ℝ)+2)/2)*2*Real.sqrt 2*Real.sqrt ((k : ℝ)^3/(N-r)) ≤ ‖μ+1‖ := by
  have hsharp := jwWalk_eigenvalue_gap_neg_one_sharp k N r hNr hkN hkr μ v heigen hv
  have herr := jwSpectral_error_dominates_sharp k N r hk hNr
  linarith

/-- The vector obtained by replacing coordinate zero by zero and retaining all other
coordinates. -/
def jwEraseZero {n : ℕ} (v : Fin (n+1) → ℂ) : Fin (n+1) → ℂ :=
  fun i => if i = 0 then 0 else v i

/-- The squared norm of a vector splits into the squared norm after erasing coordinate zero and
the energy of that coordinate. -/
theorem jwEraseZero_energy {n : ℕ} (v : Fin (n+1) → ℂ) :
    jwL2Norm (jwEraseZero v)^2 + Complex.normSq (v 0) = jwL2Norm v^2 := by
  rw [jwL2Norm_sq,jwL2Norm_sq]
  have h : (∑ i : Fin (n+1), (Complex.normSq (jwEraseZero v i) +
      if i=0 then Complex.normSq (v 0) else 0)) = ∑ i, Complex.normSq (v i) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=0 <;> simp [jwEraseZero,hi]
  simpa [Finset.sum_add_distrib] using h

/-- The Hermitian inner product splits into the inner product after erasing coordinate zero and
the contribution at coordinate zero. -/
theorem jwEraseZero_inner {n : ℕ} (v s : Fin (n+1) → ℂ) :
    (star (jwEraseZero v) ⬝ᵥ jwEraseZero s) + star (v 0)*s 0 = star v ⬝ᵥ s := by
  have h : (∑ i : Fin (n+1), (star (jwEraseZero v i)*jwEraseZero s i +
      if i=0 then star (v 0)*s 0 else 0)) = ∑ i, star (v i)*s i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=0 <;> simp [jwEraseZero,hi]
  simpa [Finset.sum_add_distrib,dotProduct] using h

/-- The absolute value of the Hermitian inner product is bounded by the product of the Euclidean
norms. -/
theorem jwL2Inner_cauchy {n : ℕ} (v s : Fin n → ℂ) :
    ‖star v ⬝ᵥ s‖ ≤ jwL2Norm v*jwL2Norm s := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))
    (WithLp.toLp 2 s)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm] at h
  exact h

/-- For orthogonal vectors `v` and `s`, bounds the energy of `v` weighted by `s 0` using the
energy remaining after erasing `v 0`. -/
theorem jwEraseZero_orthogonal_energy {n : ℕ} (v s : Fin (n+1) → ℂ)
    (horth : star v ⬝ᵥ s = 0) :
    Complex.normSq (s 0)*jwL2Norm v^2 ≤
      jwL2Norm s^2*jwL2Norm (jwEraseZero v)^2 := by
  have hinner := jwEraseZero_inner v s
  rw [horth] at hinner
  have hval : star (jwEraseZero v) ⬝ᵥ jwEraseZero s = -(star (v 0)*s 0) := by
    linear_combination hinner
  have hc := jwL2Inner_cauchy (jwEraseZero v) (jwEraseZero s)
  rw [hval,norm_neg,norm_mul,norm_star] at hc
  have hcs :=
      (sq_le_sq₀ (by positivity) (mul_nonneg (jwL2Norm_nonneg _) (jwL2Norm_nonneg _))).mpr hc
  rw [mul_pow,mul_pow,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq] at hcs
  have hv := jwEraseZero_energy v
  have hs := jwEraseZero_energy s
  nlinarith

/-- If `v` is orthogonal to `s` and at least half the energy of `s` lies at its nonzero
coordinate zero, then `jwL2Norm v` is at most `sqrt 2` times the norm of `jwEraseZero v`. -/
theorem jwEraseZero_orthogonal_norm_ratio {n : ℕ} (v s : Fin (n+1) → ℂ)
    (horth : star v ⬝ᵥ s = 0)
    (hweight : jwL2Norm s^2 ≤ 2*Complex.normSq (s 0))
    (hs0 : s 0 ≠ 0) : jwL2Norm v ≤ Real.sqrt 2*jwL2Norm (jwEraseZero v) := by
  have h := jwEraseZero_orthogonal_energy v s horth
  have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg (jwL2Norm (jwEraseZero v)))
  have hp : 0 < Complex.normSq (s 0) := Complex.normSq_pos.mpr hs0
  have hsquare : jwL2Norm v^2 ≤ 2*jwL2Norm (jwEraseZero v)^2 := by nlinarith
  apply (sq_le_sq₀ (jwL2Norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 2) (jwL2Norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hsquare

/-- Erasing coordinate zero cannot increase the Euclidean norm. -/
theorem jwEraseZero_norm_le {n : ℕ} (v : Fin (n+1) → ℂ) :
    jwL2Norm (jwEraseZero v) ≤ jwL2Norm v := by
  apply (sq_le_sq₀ (jwL2Norm_nonneg _) (jwL2Norm_nonneg _)).mp
  have h := jwEraseZero_energy v
  linarith [Complex.normSq_nonneg (v 0)]

/-- A reversed pair index is distinct from coordinate zero. -/
theorem jwPairIndex_rev_ne_zero (k : ℕ) (a : Bool) (j : Fin k) :
    (jwPairIndex k a j).rev ≠ 0 := by
  intro h
  have hh := congrArg Fin.val h
  cases a <;> simp [jwPairIndex,Fin.val_rev] at hh <;> omega

/-- When `k ≤ r + 1`, the squared residual of the ideal walk from the identity is at least `4 /
(r + 1)` times the energy away from coordinate zero. -/
theorem jwIdealWalk_energy_sub_one_lower (k r : ℕ) (hkr : k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    (4/(r+1) : ℝ)*jwL2Norm (jwEraseZero v)^2 ≤
      jwL2Norm (jwIdealWalk k r *ᵥ v-v)^2 := by
  have hrest : jwL2Norm (jwEraseZero v)^2 =
      ∑ j : Fin k, (Complex.normSq (v (jwPairIndex k false j).rev) +
        Complex.normSq (v (jwPairIndex k true j).rev)) := by
    have h := jwEraseZero_energy v
    rw [jwL2Norm_sq v,jwSumRevPairs] at h
    linarith
  rw [hrest,jwL2Norm_sq]
  simp only [Pi.sub_apply]
  rw [jwIdealWalk_energy_sub_one k r hkr,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  have hj : (j.val : ℝ)+1 ≤ k := by exact_mod_cast j.isLt
  have hdiv : (1 : ℝ)/(r+1) ≤ (k-j.val : ℝ)/(r+1) := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  calc
    _ = 4*((1 : ℝ)/(r+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by norm_num)

/-- When `k ≤ r + 1`, the ideal-walk residual norm is at least `2 / sqrt (r + 1)` times the norm
after erasing coordinate zero. -/
theorem jwIdealWalk_norm_sub_one_lower (k r : ℕ) (hkr : k ≤ r+1)
    (v : Fin (2*k+1) → ℂ) :
    (2/Real.sqrt (r+1 : ℝ))*jwL2Norm (jwEraseZero v) ≤
      jwL2Norm (jwIdealWalk k r *ᵥ v-v) := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (jwL2Norm_nonneg _)) (jwL2Norm_nonneg _)).mp
  rw [mul_pow,div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r+1)]
  simpa only [show (2 : ℝ)^2=4 by norm_num] using
    jwIdealWalk_energy_sub_one_lower k r hkr v

/-- For a nonzero eigenvector orthogonal to `s`, whose nonzero coordinate zero carries at least
half its energy, the eigenvalue's distance from 1 is at least `2 / sqrt (r + 1) - 2 * sqrt 2
* sqrt (k / (N - r))` under the stated size conditions. -/
theorem jwWalk_eigenvalue_gap_one_of_start_weight (k N r : ℕ) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : k ≤ r+1) (μ : ℂ) (v s : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v) (hv : v ≠ 0)
    (horth : star v ⬝ᵥ s = 0)
    (hweight : jwL2Norm s^2 ≤ 2*Complex.normSq (s 0)) (hs0 : s 0 ≠ 0) :
    2/Real.sqrt (r+1 : ℝ)-2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) ≤ ‖μ-1‖ := by
  have hratio := jwEraseZero_orthogonal_norm_ratio v s horth hweight hs0
  have hlow := jwIdealWalk_norm_sub_one_lower k r hkr v
  have hres := jwWalk_ideal_residual_norm k N r hNr hkN hkr v
  have hvp := jwL2Norm_pos v hv
  have hvQp : 0 < jwL2Norm (jwEraseZero v) := by
    nlinarith [jwL2Norm_nonneg (jwEraseZero v),Real.sqrt_nonneg 2]
  have hdecomp : jwIdealWalk k r *ᵥ v-v =
      -(jwEraseZero (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)) + (μ-1) • jwEraseZero v := by
    funext i
    by_cases hi : i=0
    · subst i
      simp [jwIdealWalk_zero_action,jwEraseZero]
    · rw [heigen]
      simp only [Pi.sub_apply,Pi.neg_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,jwEraseZero,if_neg hi]
      ring
  have htri := jwL2Norm_add_le (-(jwEraseZero (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)))
    ((μ-1) • jwEraseZero v)
  rw [← hdecomp,jwL2Norm_smul] at htri
  have hneg : jwL2Norm (-(jwEraseZero (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v))) =
      jwL2Norm (jwEraseZero (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)) := by
    simp only [jwL2Norm,WithLp.toLp_neg,norm_neg]
  rw [hneg] at htri
  have hcontract := jwEraseZero_norm_le (jwWalk k N r *ᵥ v-jwIdealWalk k r *ᵥ v)
  have hr : 0 ≤ 2*Real.sqrt ((k : ℝ)/(N-r)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hratio hr
  have h : (2/Real.sqrt (r+1 : ℝ)-2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)))*
      jwL2Norm (jwEraseZero v) ≤ ‖μ-1‖*jwL2Norm (jwEraseZero v) := by nlinarith
  exact (mul_le_mul_iff_left₀ hvQp).mp h

/-- For `k ≥ 1` and `r < N`, the stated spectral error dominates the projected perturbation
error `2 * sqrt 2 * sqrt (k / (N - r))`. -/
theorem jwSpectral_error_dominates_projected (k N r : ℕ) (hk : 1 ≤ k) (hNr : r < N) :
    2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r)) ≤
      (2 : ℝ)^(((k : ℝ)+2)/2)*2*Real.sqrt 2*Real.sqrt ((k : ℝ)^3/(N-r)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  have hpow := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ ((k : ℝ)+2)/2)
  have hk2 : (1 : ℝ) ≤ (k : ℝ)^2 := one_le_pow₀ hkR
  have hk3 : (k : ℝ) ≤ (k : ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  calc
    _ ≤ 2*Real.sqrt 2*Real.sqrt ((k : ℝ)^3/(N-r)) := by gcongr
    _ = 1*2*Real.sqrt 2*Real.sqrt ((k : ℝ)^3/(N-r)) := by ring
    _ ≤ _ := by gcongr

/-- Decomposes the squared residual of an ideal block at `μ` into contributions from
`jwIdealBlockPhase e` and its complex conjugate. -/
theorem jwIdealBlock_residual_energy (e : ℝ) (μ x y : ℂ) :
    Complex.normSq ((jwD2 e false false-μ)*x-jwD2 e false true*y) +
      Complex.normSq (jwD2 e true false*x-(jwD2 e true true+μ)*y) =
    (Complex.normSq (jwIdealBlockPhase e-μ)*Complex.normSq (x+Complex.I*y) +
      Complex.normSq (star (jwIdealBlockPhase e)-μ)*Complex.normSq (x-Complex.I*y))/2 := by
  norm_num [jwD2,jwIdealBlockPhase,Complex.normSq_apply,Complex.star_def]
  ring

/-- The squared norms of `x + I * y` and `x - I * y` sum to twice the total energy of `x` and
`y`. -/
theorem jwIdealBlock_coefficient_energy (x y : ℂ) :
    Complex.normSq (x+Complex.I*y) + Complex.normSq (x-Complex.I*y) =
      2*(Complex.normSq x+Complex.normSq y) := by
  simp [Complex.normSq_apply]
  ring

/-- A common lower bound on the squared distances from `μ` to both ideal block phases gives the
same lower bound on the residual energy relative to the input energy. -/
theorem jwIdealBlock_residual_lower (e a : ℝ) (μ x y : ℂ)
    (hp : a ≤ Complex.normSq (jwIdealBlockPhase e-μ))
    (hm : a ≤ Complex.normSq (star (jwIdealBlockPhase e)-μ)) :
    a*(Complex.normSq x+Complex.normSq y) ≤
      Complex.normSq ((jwD2 e false false-μ)*x-jwD2 e false true*y) +
        Complex.normSq (jwD2 e true false*x-(jwD2 e true true+μ)*y) := by
  rw [jwIdealBlock_residual_energy]
  have h1 := mul_le_mul_of_nonneg_right hp (Complex.normSq_nonneg (x+Complex.I*y))
  have h2 := mul_le_mul_of_nonneg_right hm (Complex.normSq_nonneg (x-Complex.I*y))
  have hc := jwIdealBlock_coefficient_energy x y
  have h3 := congrArg (fun z : ℝ => a*z) hc
  nlinarith

/-- Strict lower bounds on both squared phase distances yield a strict residual-energy bound
when the input pair has positive energy. -/
theorem jwIdealBlock_residual_strict_lower (e a : ℝ) (μ x y : ℂ)
    (hp : a < Complex.normSq (jwIdealBlockPhase e-μ))
    (hm : a < Complex.normSq (star (jwIdealBlockPhase e)-μ))
    (hxy : 0 < Complex.normSq x+Complex.normSq y) :
    a*(Complex.normSq x+Complex.normSq y) <
      Complex.normSq ((jwD2 e false false-μ)*x-jwD2 e false true*y) +
        Complex.normSq (jwD2 e true false*x-(jwD2 e true true+μ)*y) := by
  rw [jwIdealBlock_residual_energy]
  have hc := jwIdealBlock_coefficient_energy x y
  have h3 := congrArg (fun z : ℝ => a*z) hc
  by_cases hx : 0 < Complex.normSq (x+Complex.I*y)
  · have h1 := mul_lt_mul_of_pos_right hp hx
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt hm) (Complex.normSq_nonneg (x-Complex.I*y))
    nlinarith
  · have hy : 0 < Complex.normSq (x-Complex.I*y) := by nlinarith [Complex.normSq_nonneg (x+Complex.I*y)]
    have h1 := mul_le_mul_of_nonneg_right (le_of_lt hp) (Complex.normSq_nonneg (x+Complex.I*y))
    have h2 := mul_lt_mul_of_pos_right hm hy
    nlinarith

/-- Under the stated size and start-vector weight conditions, an eigenvalue with a nonzero
eigenvector orthogonal to the start vector lies within squared distance `8 * k / (N - r)` of
an ideal block phase or its conjugate. -/
theorem jwWalk_eigenvalue_localization_of_start_weight (k N r : ℕ) (hNr : r < N)
    (hkN : k ≤ N-r) (hkr : k ≤ r+1) (μ : ℂ) (v s : Fin (2*k+1) → ℂ)
    (heigen : jwWalk k N r *ᵥ v = μ • v) (hv : v ≠ 0)
    (horth : star v ⬝ᵥ s = 0)
    (hweight : jwL2Norm s^2 ≤ 2*Complex.normSq (s 0)) (hs0 : s 0 ≠ 0) :
    ∃ j : Fin k,
      Complex.normSq (jwIdealBlockPhase ((k-j.val : ℝ)/(r+1))-μ) ≤ 8*k/(N-r) ∨
      Complex.normSq (star (jwIdealBlockPhase ((k-j.val : ℝ)/(r+1)))-μ) ≤ 8*k/(N-r) := by
  let E : Fin k → ℝ := fun j => Complex.normSq (v (jwPairIndex k false j).rev) +
    Complex.normSq (v (jwPairIndex k true j).rev)
  let R : Fin k → ℝ := fun j =>
    Complex.normSq ((jwD2 ((k-j.val : ℝ)/(r+1)) false false-μ)*v (jwPairIndex k false j).rev-
      jwD2 ((k-j.val : ℝ)/(r+1)) false true*v (jwPairIndex k true j).rev) +
    Complex.normSq (jwD2 ((k-j.val : ℝ)/(r+1)) true false*v (jwPairIndex k false j).rev-
      (jwD2 ((k-j.val : ℝ)/(r+1)) true true+μ)*v (jwPairIndex k true j).rev)
  have hrest : jwL2Norm (jwEraseZero v)^2 = ∑ j, E j := by
    have h := jwEraseZero_energy v
    rw [jwL2Norm_sq v,jwSumRevPairs] at h
    dsimp [E]
    linarith
  have hratio := jwEraseZero_orthogonal_norm_ratio v s horth hweight hs0
  have hvp := jwL2Norm_pos v hv
  have hQp : 0 < jwL2Norm (jwEraseZero v) := by
    nlinarith [jwL2Norm_nonneg (jwEraseZero v),Real.sqrt_nonneg 2]
  have hratioSq : jwL2Norm v^2 ≤ 2*jwL2Norm (jwEraseZero v)^2 := by
    have h := (sq_le_sq₀ (jwL2Norm_nonneg v)
      (mul_nonneg (Real.sqrt_nonneg 2) (jwL2Norm_nonneg _))).mpr hratio
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have hres := jwWalk_ideal_residual_bound k N r hNr hkN hkr v
  have hpoint : ∀ i, Complex.normSq ((jwIdealWalk k r *ᵥ v) i-μ*v i) =
      Complex.normSq ((jwWalk k N r *ᵥ v) i-(jwIdealWalk k r *ᵥ v) i) := by
    intro i
    rw [heigen]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [← neg_sub (μ*v i)]
    exact Complex.normSq_neg _
  have hsumR : (∑ j, R j) ≤ ∑ i, Complex.normSq ((jwIdealWalk k r *ᵥ v) i-μ*v i) := by
    rw [jwSumRevPairs]
    have hpairs : (∑ j, R j) = ∑ j : Fin k,
        (Complex.normSq ((jwIdealWalk k r *ᵥ v) (jwPairIndex k false j).rev-μ*v (jwPairIndex k false j).rev) +
          Complex.normSq ((jwIdealWalk k r *ᵥ v) (jwPairIndex k true j).rev-μ*v (jwPairIndex k true j).rev)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [jwIdealWalk_pair_action,jwIdealWalk_pair_action]
      dsimp [R]
      congr 1 <;> congr 1 <;> ring
    rw [hpairs]
    exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
  simp only [hpoint] at hsumR
  have hD : (0 : ℝ) < N-r := by
    have h : (r : ℝ) < N := by exact_mod_cast hNr
    linarith
  have hbound : (∑ j, R j) ≤ (8*k/(N-r) : ℝ)*(∑ j, E j) := by
    rw [← hrest]
    have hmul := mul_le_mul_of_nonneg_left hratioSq (by positivity : (0 : ℝ) ≤ 4*k/(N-r))
    rw [jwL2Norm_sq v] at hmul
    calc
      _ ≤ _ := hsumR.trans hres
      _ ≤ _ := hmul
      _ = _ := by ring
  by_contra hloc
  push Not at hloc
  have hle : ∀ j, (8*k/(N-r) : ℝ)*E j ≤ R j := by
    intro j
    exact jwIdealBlock_residual_lower _ _ μ _ _ (le_of_lt (hloc j).1) (le_of_lt (hloc j).2)
  have hpositive : 0 < ∑ j, E j := by rw [← hrest]; exact sq_pos_of_pos hQp
  obtain ⟨j,hj,hE⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ =>
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))).mp hpositive
  have hlt : (8*k/(N-r) : ℝ)*E j < R j :=
    jwIdealBlock_residual_strict_lower _ _ μ _ _ (hloc j).1 (hloc j).2 hE
  have hsum := Finset.sum_lt_sum (fun j _ => hle j) ⟨j,hj,hlt⟩
  rw [← Finset.mul_sum] at hsum
  linarith

/-- For `1 ≤ k` and `2 * k ≤ r + 1`, bounds the ideal phase multiplied by `jwT2 k r` between `π
/ (3 * sqrt k)` and 3, and bounds `jwT2 k r` by `4 * sqrt (r + 1) / (3 * sqrt k)`. -/
theorem jwIdealBlock_amplification_bounds (k r : ℕ) (hk : 1 ≤ k) (hr : 2*k ≤ r+1)
    (j : Fin k) :
    Real.pi/(3*Real.sqrt (k : ℝ)) ≤
      (jwT2 k r : ℝ)*(2*Real.arcsin (Real.sqrt ((k-j.val : ℝ)/(r+1)))) ∧
    (jwT2 k r : ℝ)*(2*Real.arcsin (Real.sqrt ((k-j.val : ℝ)/(r+1)))) ≤ 3 ∧
    (jwT2 k r : ℝ) ≤ (4/3 : ℝ)*Real.sqrt (r+1 : ℝ)/Real.sqrt (k : ℝ) := by
  let K : ℝ := Real.sqrt (k : ℝ)
  let R : ℝ := Real.sqrt (r+1 : ℝ)
  let e : ℝ := (k-j.val : ℝ)/(r+1)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 0 < K := Real.sqrt_pos.mpr (by linarith)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hKsq : K^2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
  have hRsq : R^2 = r+1 := Real.sq_sqrt (by positivity)
  have hrR : (2 : ℝ)*k ≤ r+1 := by exact_mod_cast hr
  have hj : (j.val : ℝ)+1 ≤ k := by exact_mod_cast j.isLt
  have he : 0 ≤ e := div_nonneg (by linarith) (by positivity)
  have hehalf : e ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  have hs := Real.sq_sqrt he
  have hlower : 1/R ≤ Real.sqrt e := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [div_pow,one_pow,hRsq,hs]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hupper : Real.sqrt e ≤ K/R := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [div_pow,hKsq,hRsq,hs]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg j.val)) (by positivity)
  have harc := jw_arcsin_sqrt_bounds e he hehalf
  have hRK : (7/5 : ℝ)*K ≤ R := by
    apply (sq_le_sq₀ (by positivity) (le_of_lt hR)).mp
    nlinarith [sq_nonneg K]
  have hone : (1 : ℝ) ≤ (5/7)*R/K := by
    apply (le_div_iff₀ hK).mpr
    linarith
  have hceilLo : Real.pi*R/(6*K) ≤ (jwT2 k r : ℝ) := by
    exact Nat.le_ceil _
  have hceilHi : (jwT2 k r : ℝ) ≤ Real.pi*R/(6*K)+1 := by
    exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have ht : (jwT2 k r : ℝ) ≤ (5/4)*R/K := by
    have hbase : Real.pi*R/(6*K)+(5/7)*R/K = (Real.pi/6+5/7)*R/K := by ring
    calc
      _ ≤ Real.pi*R/(6*K)+1 := hceilHi
      _ ≤ Real.pi*R/(6*K)+(5/7)*R/K := by linarith
      _ = _ := hbase
      _ ≤ (5/4)*R/K := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hK)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hR)
        linarith [Real.pi_lt_d2]
  have hθlo : 2/R ≤ 2*Real.arcsin (Real.sqrt e) := by
    calc
      _ = 2*(1/R) := by ring
      _ ≤ 2*Real.sqrt e := mul_le_mul_of_nonneg_left hlower (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left harc.1 (by norm_num)
  have hθhi : 2*Real.arcsin (Real.sqrt e) ≤ (12/5)*K/R := by
    calc
      _ ≤ 2*((6/5)*Real.sqrt e) := mul_le_mul_of_nonneg_left harc.2 (by norm_num)
      _ = (12/5)*Real.sqrt e := by ring
      _ ≤ (12/5)*(K/R) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = _ := by ring
  refine ⟨?_,?_,?_⟩
  · calc
      _ = (Real.pi*R/(6*K))*(2/R) := by field_simp; ring
      _ ≤ (jwT2 k r : ℝ)*(2*Real.arcsin (Real.sqrt e)) := by
        exact mul_le_mul hceilLo hθlo (by positivity) (by positivity)
  · calc
      _ ≤ ((5/4)*R/K)*((12/5)*K/R) :=
        mul_le_mul ht hθhi (by linarith [harc.1]) (by positivity)
      _ = 3 := by field_simp; ring
  · calc
      _ ≤ (5/4)*R/K := ht
      _ ≤ (4/3)*R/K :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (5/4 : ℝ) ≤ 4/3) (le_of_lt hR))
          (le_of_lt hK)

/-- The stated population bound makes the perturbation error multiplied by `jwT2 k r` at most `1
/ (6 * π * sqrt k)`. -/
theorem jwT2_perturbation_bound (k N r : ℕ) (hk : 1 ≤ k) (hr : 2*k ≤ r+1)
    (hsize : (512*Real.pi^2*k*(r+1) : ℝ) ≤ N-r) :
    (jwT2 k r : ℝ)*(2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r))) ≤
      1/(6*Real.pi*Real.sqrt (k : ℝ)) := by
  let K : ℝ := Real.sqrt (k : ℝ)
  let R : ℝ := Real.sqrt (r+1 : ℝ)
  let δ : ℝ := 2*Real.sqrt 2*Real.sqrt ((k : ℝ)/(N-r))
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 0 < K := Real.sqrt_pos.mpr (by linarith)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRsq : R^2 = r+1 := Real.sq_sqrt (by positivity)
  have hD : (0 : ℝ) < N-r := by
    have hp : (0 : ℝ) < 512*Real.pi^2*k*(r+1) := by positivity
    linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδsq : δ^2 = 8*k/(N-r) := by
    dsimp [δ]
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg k) (le_of_lt hD)),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hfrac : (512*Real.pi^2*k*(r+1) : ℝ)/(N-r) ≤ 1 := (div_le_one hD).mpr hsize
  have hsq : (8*Real.pi*R*δ)^2 ≤ (1 : ℝ)^2 := by
    rw [mul_pow,mul_pow,mul_pow,hRsq,hδsq]
    convert hfrac using 1 <;> ring
  have hsmall : 8*Real.pi*R*δ ≤ 1 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mp hsq
  have ht := (jwIdealBlock_amplification_bounds k r hk hr ⟨0,by omega⟩).2.2
  have hscaled : ((4/3 : ℝ)*R/K)*δ ≤ 1/(6*Real.pi*K) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 6*Real.pi*K)).mpr
    have hid : (((4/3 : ℝ)*R/K)*δ)*(6*Real.pi*K) = 8*Real.pi*R*δ := by
      field_simp
      ring
    rw [hid]
    exact hsmall
  exact (mul_le_mul_of_nonneg_right ht hδ).trans hscaled

end Qatlib.Concepts.WalkFind.WalkSpectrum
