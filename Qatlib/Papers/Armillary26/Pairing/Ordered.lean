/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.RoutingModel.Routing
public import Qatlib.Papers.Armillary26.Pairing.Elimination
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# Ordered block algebra and involutive pair cancellation

A step matrix retains the block at the column actually visited at that step.
Rows may be retained checks equipped with their own map into the cyclic group;
they need not range over every group. Summing the steps recovers the full
permutation-block matrix. The ordered cross-time sum selects, at each block
column, the two modular times at which the X and Z rows visit that column.
Fixed-point-free involutions give separate static and ordered cancellation.
-/

namespace Qatlib.Papers.Armillary26.Pairing

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators Matrix
open Qatlib.Concepts.CodeCert.PermBlocks
open Qatlib.Papers.Armillary26.RoutingModel

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The step matrix at `t` occupies column `b` exactly when `b - g a = t`. -/
def steps {M : ℕ} {α ι : Type*} [DecidableEq ι]
    (g : α → Fin M) (E : α → Fin M → Equiv.Perm ι) (t : Fin M) :
    Matrix (α × ι) (Fin M × ι) (ZMod 2) :=
  fun ap bq => if bq.1 - g ap.1 = t then permMat (E ap.1 bq.1) ap.2 bq.2 else 0

/-- Modular finite-index addition agrees with the additive visit law. -/
theorem visit_fin {M : ℕ} (a t : Fin M) :
    visitAt M (t : ℕ) a = a + t := by
  apply Fin.ext
  rfl

/-- The step-matrix occupancy condition is the actual visit law `b = g a + t`. -/
theorem steps_visit {M : ℕ} [NeZero M] {α ι : Type*} [DecidableEq ι]
    (g : α → Fin M) (E : α → Fin M → Equiv.Perm ι) (t : Fin M) (a : α) (b : Fin M)
    (p q : ι) : steps g E t (a, p) (b, q) =
      if b = visitAt M (t : ℕ) (g a) then permMat (E a b) p q else 0 := by
  simp [steps, visit_fin, sub_eq_iff_eq_add, add_comm]

/-- The block product associated with one retained X/Z row pair and one block column. -/
def pairK {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (x : α) (z : β) (b : Fin M) : Matrix ι ι (ZMod 2) :=
  permMat (E x b) * (permMat (Z z b))ᵀ

/-- The binary indicator that the X visit to `b` precedes the Z visit. -/
def chi {M : ℕ} (x z b : Fin M) : ZMod 2 :=
  if (b - x).val < (b - z).val then 1 else 0

/-- The ordered contribution of one block column. -/
def ordK {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (x : α) (z : β) (b : Fin M) : Matrix ι ι (ZMod 2) :=
  chi (gX x) (gZ z) b • pairK E Z x z b

/-- The sum of all step matrices is the assembled permutation-block matrix. -/
theorem steps_sum {M : ℕ} {α ι : Type*} [DecidableEq ι]
    (g : α → Fin M) (E : α → Fin M → Equiv.Perm ι) :
    (∑ t : Fin M, steps g E t) = (permBlocks E : Matrix (α × ι) (Fin M × ι) (ZMod 2)) := by
  classical
  ext ⟨x, p⟩ ⟨b, q⟩
  simp [Matrix.sum_apply, steps, permBlocks, permMat]

/-- Entrywise expansion of the static product into block-column products. -/
theorem block_mul_entry {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (x : α) (z : β) (p q : ι) :
    (((permBlocks E : Matrix (α × ι) (Fin M × ι) (ZMod 2)) *
        (permBlocks Z : Matrix (β × ι) (Fin M × ι) (ZMod 2))ᵀ)
        (x, p) (z, q)) = ∑ b : Fin M, pairK E Z x z b p q := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rfl

/-- A cross-time product is supported on columns visited by both rows. -/
theorem step_mul_entry {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (t u : Fin M) (x : α) (z : β) (p q : ι) :
    (steps gX E t * (steps gZ Z u)ᵀ) (x, p) (z, q) =
      ∑ b : Fin M, if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hx : b - gX x = t <;> by_cases hz : b - gZ z = u <;>
    simp [steps, hx, hz, pairK, Matrix.mul_apply]

/-- Selecting the two visit times gives the ordered indicator at each column. -/
theorem time_pick {M : ℕ} (x z b : Fin M) (v : ZMod 2) :
    (∑ t : Fin M, ∑ u : Fin M, if (t : ℕ) < (u : ℕ) then
      (if b - x = t ∧ b - z = u then v else 0) else 0) = chi x z b * v := by
  classical
  by_cases h : (b - x).val < (b - z).val
  · rw [Finset.sum_eq_single_of_mem (b - x) (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (b - z) (Finset.mem_univ _)]
      · simp [chi, h]
      · intro u _ hu
        simp [Ne.symm hu]
    · intro t _ ht
      simp [Ne.symm ht]
  · have hz : chi x z b = 0 := by simp [chi, h]
    rw [hz, zero_mul]
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro u _
    by_cases htu : (t : ℕ) < (u : ℕ)
    · by_cases hb : b - x = t ∧ b - z = u
      · have hlt : (b - x).val < (b - z).val := by
          simpa [hb.1, hb.2] using htu
        exact (h hlt).elim
      · simp [htu, hb]
    · simp [htu]

/-- The ordered-time entries are the sum of `chi`-weighted block products. -/
theorem ordC_steps {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (x : α) (z : β) (p q : ι) :
    ordC (steps gX E) (steps gZ Z) (x, p) (z, q) = ∑ b : Fin M, ordK gX gZ E Z x z b p q := by
  classical
  simp only [ordC, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  simp_rw [step_mul_entry]
  have hpush (t u : Fin M) :
      (if (t : ℕ) < (u : ℕ) then
        (∑ b : Fin M, if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0)
        else 0) =
      ∑ b : Fin M, if (t : ℕ) < (u : ℕ) then
        (if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hpush]
  calc
    (∑ t : Fin M, ∑ u : Fin M, ∑ b : Fin M,
        if (t : ℕ) < (u : ℕ) then
          (if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0) else 0) =
      ∑ t : Fin M, ∑ b : Fin M, ∑ u : Fin M,
        if (t : ℕ) < (u : ℕ) then
          (if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
    _ = ∑ b : Fin M, ∑ t : Fin M, ∑ u : Fin M,
        if (t : ℕ) < (u : ℕ) then
          (if b - gX x = t ∧ b - gZ z = u then pairK E Z x z b p q else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b : Fin M, ordK gX gZ E Z x z b p q := by
      apply Finset.sum_congr rfl
      intro b _
      simpa [ordK] using time_pick (gX x) (gZ z) b (pairK E Z x z b p q)

/-- A fixed-point-free involution cancels equal summands in characteristic two. -/
theorem sum_inv_zero {β R : Type*} [Fintype β] [Ring R] [CharP R 2]
    (f : β → R) (rho : β → β) (hinv : Function.Involutive rho)
    (hfix : ∀ b, rho b ≠ b) (hf : ∀ b, f (rho b) = f b) : ∑ b : β, f b = 0 := by
  classical
  apply Finset.sum_ninvolution (s := Finset.univ) rho
  · intro b
    rw [hf b]
    exact CharTwo.add_self_eq_zero _
  · intro b _
    exact hfix b
  · intro b
    exact Finset.mem_univ _
  · exact hinv

/-- Pairing data for every retained X/Z row pair, including `K` and `chi` invariance. -/
def Kchi {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (rho : α → β → Fin M → Fin M) : Prop :=
  (∀ x z, Function.Involutive (rho x z)) ∧
  (∀ x z b, rho x z b ≠ b) ∧
  (∀ x z b, pairK E Z x z (rho x z b) = pairK E Z x z b) ∧
  (∀ x z b, chi (gX x) (gZ z) (rho x z b) = chi (gX x) (gZ z) b)

/-- Row-dependent involutive pairing eliminates the full static block product. -/
theorem static_zero {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (rho : α → β → Fin M → Fin M) (h : Kchi gX gZ E Z rho) :
    (permBlocks E : Matrix (α × ι) (Fin M × ι) (ZMod 2)) *
      (permBlocks Z : Matrix (β × ι) (Fin M × ι) (ZMod 2))ᵀ = 0 := by
  classical
  ext ⟨x, p⟩ ⟨z, q⟩
  rw [block_mul_entry]
  apply sum_inv_zero (rho := rho x z)
  · exact h.1 x z
  · exact h.2.1 x z
  · intro b
    exact congrFun₂ (h.2.2.1 x z b) p q

/-- The same row-dependent pairing independently eliminates the ordered sum. -/
theorem ordered_zero {M : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (gX : α → Fin M) (gZ : β → Fin M)
    (E : α → Fin M → Equiv.Perm ι) (Z : β → Fin M → Equiv.Perm ι)
    (rho : α → β → Fin M → Fin M) (h : Kchi gX gZ E Z rho) :
    ordC (steps gX E) (steps gZ Z) = 0 := by
  classical
  ext ⟨x, p⟩ ⟨z, q⟩
  rw [ordC_steps]
  apply sum_inv_zero (rho := rho x z)
  · exact h.1 x z
  · exact h.2.1 x z
  · intro b
    simp [ordK, h.2.2.1 x z b, h.2.2.2 x z b]

end Qatlib.Papers.Armillary26.Pairing
