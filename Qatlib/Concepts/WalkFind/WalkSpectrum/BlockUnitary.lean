/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Block decompositions of the Johnson diffusion steps

This module proves unitarity of the two-dimensional diffusion block and expresses each reduced
Johnson diffusion step as such blocks together with one fixed coordinate. The resulting size
conditions ensure identity Gram matrices for the two steps in the collision-search walk
[Ambainis2007ElementDistinctness].

Pairwise action formulas and fixed-vector criteria expose the same decomposition directly on
state vectors.

## Main statements

* `jwD2_unitary`: unitarity of a diffusion block for parameters in `[0,1]`.
* `jwStep1_unitary` and `jwStep2_unitary`: conditional unitarity of the reduced steps.
* `jwStep1_fixed_of_pairs` and `jwStep2_fixed_of_pairs`: pairwise fixed-vector criteria.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- For `0 ≤ ε ≤ 1`, the two-dimensional diffusion matrix has identity Gram matrix. -/
theorem jwD2_unitary (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    star (Matrix.of (jwD2 ε)) * Matrix.of (jwD2 ε) = (1 : Matrix Bool Bool ℂ) := by
  have hs : (Real.sqrt (ε - ε * ε) : ℂ) ^ 2 = (ε - ε * ε : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by nlinarith)
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Matrix.star_apply, jwD2, map_ofNat]
  all_goals push_cast at hs ⊢
  all_goals ring_nf at hs ⊢
  all_goals linear_combination 4 * hs

/-- The disjoint union of `k` Boolean coordinate pairs and one singleton coordinate. -/
private abbrev BlockIndex (k : ℕ) := (Bool × Fin k) ⊕ Fin 1

/-- Enumerate the Boolean coordinate pairs consecutively, followed by the final coordinate
`2*k`. -/
private def blockLabel (k : ℕ) : BlockIndex k → Fin (2 * k + 1)
  | .inl (b, j) => ⟨2 * j.val + if b then 1 else 0, by cases b <;> dsimp <;> omega⟩
  | .inr _ => ⟨2 * k, by omega⟩

/-- The enumeration of paired blocks and the final coordinate is bijective. -/
private theorem blockLabel_bijective (k : ℕ) : Function.Bijective (blockLabel k) := by
  constructor
  · intro x y h
    have hv := congrArg Fin.val h
    cases x with
    | inl x =>
      rcases x with ⟨b, j⟩
      cases y with
      | inl y =>
        rcases y with ⟨c, l⟩
        have hj := j.isLt
        have hl := l.isLt
        cases b <;> cases c <;> simp [blockLabel] at hv ⊢
        all_goals omega
      | inr y =>
        have hj := j.isLt
        cases b <;> simp [blockLabel] at hv <;> omega
    | inr x =>
      cases y with
      | inl y =>
        rcases y with ⟨b, j⟩
        have hj := j.isLt
        cases b <;> simp [blockLabel] at hv <;> omega
      | inr y => congr 1; exact Subsingleton.elim _ _
  · intro i
    by_cases h : i.val < 2 * k
    · let j : Fin k := ⟨i.val / 2, by omega⟩
      refine ⟨.inl (i.val % 2 == 1, j), ?_⟩
      apply Fin.ext
      simp only [blockLabel, j, beq_iff_eq]
      split_ifs <;> omega
    · refine ⟨.inr 0, ?_⟩
      apply Fin.ext
      simp only [blockLabel]
      omega

/-- The equivalence between the paired block index and `Fin (2*k+1)` induced by `blockLabel`. -/
private noncomputable def blockEquiv (k : ℕ) : BlockIndex k ≃ Fin (2 * k + 1) :=
  Equiv.ofBijective (blockLabel k) (blockLabel_bijective k)

/-- The block diagonal matrix of the `k` diffusion blocks, extended by the identity on the final
coordinate. -/
private noncomputable def blocks (k : ℕ) (ε : Fin k → ℝ) : Matrix (BlockIndex k) (BlockIndex k) ℂ :=
  Matrix.fromBlocks (Matrix.blockDiagonal fun j => Matrix.of (jwD2 (ε j))) 0 0 1

/-- If each diffusion parameter lies in `[0,1]`, the block matrix has identity Gram matrix. -/
private theorem blocks_unitary (k : ℕ) (ε : Fin k → ℝ)
    (hε : ∀ j, 0 ≤ ε j ∧ ε j ≤ 1) : star (blocks k ε) * blocks k ε = 1 := by
  have h : star (Matrix.blockDiagonal fun j => Matrix.of (jwD2 (ε j))) *
      Matrix.blockDiagonal (fun j => Matrix.of (jwD2 (ε j))) = 1 := by
    change (Matrix.blockDiagonal fun j => Matrix.of (jwD2 (ε j)))ᴴ * _ = _
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [← Matrix.star_eq_conjTranspose, jwD2_unitary _ (hε _).1 (hε _).2]
    exact Matrix.blockDiagonal_one
  change (blocks k ε)ᴴ * blocks k ε = 1
  simp only [blocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  change Matrix.fromBlocks (star _ * _) 0 0 1 = _
  rw [h]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

/-- Identity Gram matrix for a matrix reindexed by an equivalence implies identity Gram matrix
for the original matrix. -/
private theorem unitary_of_submatrix {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A : Matrix m m ℂ)
    (h : star (A.submatrix e e) * A.submatrix e e = 1) : star A * A = 1 := by
  have hs : (star A * A).submatrix e e = (1 : Matrix m m ℂ).submatrix e e := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ e, Matrix.submatrix_one_equiv]
    exact h
  ext i j
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  exact congrFun (congrFun hs i') j'

/-- Reindexing the first diffusion step by `blockEquiv` gives diffusion blocks with parameters
`(k-j)/(N-r)`. -/
private theorem step1_blocks (k N r : ℕ) :
    (jwStep1 k N r).submatrix (blockEquiv k) (blockEquiv k) =
      blocks k (fun j => (k - j.val : ℝ) / (N - r)) := by
  ext i j
  change jwStep1 k N r (blockLabel k i) (blockLabel k j) = _
  cases i with
  | inl i =>
    rcases i with ⟨a, i⟩
    cases j with
    | inl j =>
      rcases j with ⟨b, j⟩
      cases a <;> cases b <;>
        simp [jwStep1, blockLabel, jwPsiCoord, jwPhiCoord, blocks,
          Matrix.blockDiagonal_apply, Nat.add_div, Nat.add_mod, jwD2, Fin.ext_iff]
      all_goals split_ifs with h
      all_goals simp_all
    | inr j =>
      have hi := i.isLt
      cases a <;>
        simp [jwStep1, blockLabel, jwPsiCoord, jwPhiCoord, blocks, jwD2]
      all_goals omega
  | inr i =>
    cases j with
    | inl j =>
      rcases j with ⟨b, j⟩
      have hj := j.isLt
      cases b <;>
        simp [jwStep1, blockLabel, jwPsiCoord, jwPhiCoord, blocks, jwD2]
      all_goals omega
    | inr j => simp [jwStep1, blockLabel, jwPsiCoord, jwPhiCoord, blocks, jwD2, Nat.add_div, Subsingleton.elim i j]

/-- Reindexing the second diffusion step by the reversed block equivalence gives diffusion
blocks with parameters `(k-j)/(r+1)`. -/
private theorem step2_blocks (k r : ℕ) :
    (jwStep2 k r).submatrix ((blockEquiv k).trans Fin.revPerm)
        ((blockEquiv k).trans Fin.revPerm) =
      blocks k (fun j => (k - j.val : ℝ) / (r + 1)) := by
  have coords (a : Bool) (j : Fin k) :
      jwPhiCoord k (blockLabel k (.inl (a,j))).rev = (k - j.val, a) ∧
      jwPsiCoord k (blockLabel k (.inl (a,j))).rev =
        (k - j.val - if a then 1 else 0, a) := by
    have hj := j.isLt
    cases a <;> simp only [jwPsiCoord, jwPhiCoord, blockLabel, Fin.val_rev]
    all_goals constructor <;> apply Prod.ext
    all_goals simp
    all_goals omega
  have zero : (blockLabel k (.inr (0 : Fin 1))).rev = 0 := by
    apply Fin.ext
    simp [blockLabel, Fin.val_rev]
  ext i j
  change jwStep2 k r (blockLabel k i).rev (blockLabel k j).rev = _
  cases i with
  | inl i =>
    rcases i with ⟨a, i⟩
    cases j with
    | inl j =>
      rcases j with ⟨b, j⟩
      have hi := i.isLt
      have hj := j.isLt
      have hci : k - i.val - 1 + 1 = k - i.val := by omega
      have hcast : ((k - j.val : ℕ) : ℝ) = k - j.val := by
        rw [Nat.cast_sub (by omega)]
      cases a <;> cases b <;>
        simp [jwStep2, (coords _ _).1, (coords _ _).2, blocks,
          Matrix.blockDiagonal_apply, jwD2, hci, Fin.ext_iff]
      all_goals split_ifs with h
      all_goals simp_all
      all_goals omega
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hi := i.isLt
      cases a <;> simp [jwStep2, zero, (coords _ _).2,
        blocks, jwD2]
      all_goals simp [jwPhiCoord]
      all_goals omega
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j with
    | inl j =>
      rcases j with ⟨b, j⟩
      have hj := j.isLt
      cases b <;> simp [jwStep2, zero, (coords _ _).1,
        blocks, jwD2]
      all_goals simp [jwPsiCoord]
      all_goals omega
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [jwStep2, zero, jwPsiCoord, jwPhiCoord, blocks, jwD2]

/-- If `k ≤ N-r`, the first reduced Johnson diffusion step has identity Gram matrix. -/
theorem jwStep1_unitary (k N r : ℕ) (hkr : k ≤ N - r) :
    star (jwStep1 k N r) * jwStep1 k N r = 1 := by
  apply unitary_of_submatrix (blockEquiv k)
  rw [step1_blocks]
  apply blocks_unitary
  intro j
  have hj : (j.val : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt j.isLt
  have hk : (k : ℝ) ≤ N - r := by
    have hjn := j.isLt
    have hc : (k : ℝ) + r ≤ N := by exact_mod_cast (by omega : k + r ≤ N)
    linarith
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · have hjn := j.isLt
    have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    exact (div_le_one (by linarith)).mpr (by linarith)

/-- If `k ≤ r+1`, the second reduced Johnson diffusion step has identity Gram matrix. -/
theorem jwStep2_unitary (k r : ℕ) (hkr : k ≤ r + 1) :
    star (jwStep2 k r) * jwStep2 k r = 1 := by
  apply unitary_of_submatrix ((blockEquiv k).trans Fin.revPerm)
  rw [step2_blocks]
  apply blocks_unitary
  intro j
  have hj : (j.val : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt j.isLt
  have hk : (k : ℝ) ≤ r + 1 := by exact_mod_cast hkr
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · exact (div_le_one (by positivity)).mpr (by linarith)

/-- A sum over reduced coordinates splits into `k` Boolean coordinate pairs and the final type
`(k, false)`. -/
theorem jwTypeSum {A : Type*} [AddCommMonoid A] (k : ℕ) (f : ℕ → Bool → A) :
    (∑ i : Fin (2 * k + 1), f (jwPsiCoord k i).1 (jwPsiCoord k i).2) =
      (∑ j : Fin k, (f j.val false + f j.val true)) + f k false := by
  rw [← (blockEquiv k).sum_comp (fun i => f (jwPsiCoord k i).1 (jwPsiCoord k i).2)]
  simp [blockEquiv, blockLabel, jwPsiCoord, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Nat.add_div, Nat.add_mod, Finset.sum_add_distrib, add_comm]

/-- The reduced coordinate at position `2*j` or `2*j+1`, selected by the Boolean parameter. -/
def jwPairIndex (k : ℕ) (a : Bool) (j : Fin k) : Fin (2*k+1) :=
  ⟨2*j.val + if a then 1 else 0, by cases a <;> dsimp <;> omega⟩

/-- On each coordinate pair, the first diffusion step acts by the block `jwD2 ((k-j)/(N-r))`. -/
theorem jwStep1_pair_action (k N r : ℕ) (v : Fin (2*k+1) → ℂ)
    (a : Bool) (j : Fin k) :
    (jwStep1 k N r *ᵥ v) (jwPairIndex k a j) =
      jwD2 ((k - j.val : ℝ) / (N-r)) a false * v (jwPairIndex k false j) +
      jwD2 ((k - j.val : ℝ) / (N-r)) a true * v (jwPairIndex k true j) := by
  rw [Matrix.mulVec, dotProduct, ← (blockEquiv k).sum_comp]
  change (∑ x, (jwStep1 k N r).submatrix (blockEquiv k) (blockEquiv k)
    (.inl (a,j)) x * v (blockLabel k x)) = _
  rw [step1_blocks]
  simp [blocks, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  exact add_comm _ _

/-- The first diffusion step preserves the final coordinate of every vector. -/
theorem jwStep1_last_action (k N r : ℕ) (v : Fin (2*k+1) → ℂ) :
    (jwStep1 k N r *ᵥ v) (Fin.last (2*k)) = v (Fin.last (2*k)) := by
  change (jwStep1 k N r *ᵥ v) (blockLabel k (.inr 0)) = _
  rw [Matrix.mulVec, dotProduct, ← (blockEquiv k).sum_comp]
  change (∑ x, (jwStep1 k N r).submatrix (blockEquiv k) (blockEquiv k)
    (.inr 0) x * v (blockLabel k x)) = _
  rw [step1_blocks]
  simp [blocks, Fintype.sum_sum_type, blockLabel]
  rfl

/-- On each reversed coordinate pair, the second diffusion step acts by the block `jwD2
((k-j)/(r+1))`. -/
theorem jwStep2_pair_action (k r : ℕ) (v : Fin (2*k+1) → ℂ)
    (a : Bool) (j : Fin k) :
    (jwStep2 k r *ᵥ v) (jwPairIndex k a j).rev =
      jwD2 ((k - j.val : ℝ) / (r+1)) a false * v (jwPairIndex k false j).rev +
      jwD2 ((k - j.val : ℝ) / (r+1)) a true * v (jwPairIndex k true j).rev := by
  rw [Matrix.mulVec, dotProduct, ← ((blockEquiv k).trans Fin.revPerm).sum_comp]
  change (∑ x, (jwStep2 k r).submatrix ((blockEquiv k).trans Fin.revPerm)
    ((blockEquiv k).trans Fin.revPerm) (.inl (a,j)) x * v (blockLabel k x).rev) = _
  rw [step2_blocks]
  simp [blocks, Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  exact add_comm _ _

/-- The second diffusion step preserves coordinate zero of every vector. -/
theorem jwStep2_zero_action (k r : ℕ) (v : Fin (2*k+1) → ℂ) :
    (jwStep2 k r *ᵥ v) 0 = v 0 := by
  have hz : (blockLabel k (.inr (0 : Fin 1))).rev = 0 := by
    apply Fin.ext
    simp [blockLabel, Fin.val_rev]
  rw [← hz, Matrix.mulVec, dotProduct,
    ← ((blockEquiv k).trans Fin.revPerm).sum_comp]
  change (∑ x, (jwStep2 k r).submatrix ((blockEquiv k).trans Fin.revPerm)
    ((blockEquiv k).trans Fin.revPerm) (.inr 0) x * v (blockLabel k x).rev) = _
  rw [step2_blocks]
  simp [blocks, Fintype.sum_sum_type, hz]

/-- A vector fixed by every first-step diffusion block is fixed by the whole first diffusion
step. -/
theorem jwStep1_fixed_of_pairs (k N r : ℕ) (v : Fin (2*k+1) → ℂ)
    (h : ∀ (j : Fin k) (a : Bool),
      jwD2 ((k - j.val : ℝ) / (N-r)) a false * v (jwPairIndex k false j) +
      jwD2 ((k - j.val : ℝ) / (N-r)) a true * v (jwPairIndex k true j) =
      v (jwPairIndex k a j)) : jwStep1 k N r *ᵥ v = v := by
  funext i
  obtain ⟨x,rfl⟩ := (blockEquiv k).surjective i
  cases x with
  | inl x =>
    rcases x with ⟨a,j⟩
    exact (jwStep1_pair_action k N r v a j).trans (h j a)
  | inr x =>
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    exact jwStep1_last_action k N r v

/-- A vector fixed by every reversed second-step diffusion block is fixed by the whole second
diffusion step. -/
theorem jwStep2_fixed_of_pairs (k r : ℕ) (v : Fin (2*k+1) → ℂ)
    (h : ∀ (j : Fin k) (a : Bool),
      jwD2 ((k - j.val : ℝ) / (r+1)) a false * v (jwPairIndex k false j).rev +
      jwD2 ((k - j.val : ℝ) / (r+1)) a true * v (jwPairIndex k true j).rev =
      v (jwPairIndex k a j).rev) : jwStep2 k r *ᵥ v = v := by
  funext i
  obtain ⟨x,rfl⟩ := ((blockEquiv k).trans Fin.revPerm).surjective i
  cases x with
  | inl x =>
    rcases x with ⟨a,j⟩
    exact (jwStep2_pair_action k r v a j).trans (h j a)
  | inr x =>
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have hz : (blockLabel k (.inr (0 : Fin 1))).rev = 0 := by
      apply Fin.ext
      simp [blockLabel, Fin.val_rev]
    change (jwStep2 k r *ᵥ v) (blockLabel k (.inr 0)).rev = v (blockLabel k (.inr 0)).rev
    rw [hz]
    exact jwStep2_zero_action k r v

end Qatlib.Concepts.WalkFind.WalkSpectrum
