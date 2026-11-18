/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Rank bounds from equal block-row sums

The argument works over any field. A common sum in each block row produces
independent left relations, witnessed by an identity minor. Permutation blocks
are a consumer of this criterion, rather than an assumption of the rank theorem.
-/

namespace Qatlib.Concepts.CodeCert.PermBlocks

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

/-- Equal block-row sums give one independent relation for each noninitial block. -/
theorem rank_add_le {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (r : ℕ) (p₀ : ι) (H : Matrix (Fin (r + 1) × ι) κ K)
    (hbal : ∀ (a : Fin (r + 1)) (j : κ),
      ∑ p : ι, H (a, p) j = ∑ p : ι, H (0, p) j) :
    Matrix.rank H + r ≤ (r + 1) * Fintype.card ι := by
  classical
  let D : Matrix (Fin r) (Fin (r + 1) × ι) K := fun i ap =>
    (if ap.1 = i.succ then 1 else 0) - (if ap.1 = 0 then 1 else 0)
  have hminor : D.submatrix id (fun i : Fin r => (i.succ, p₀)) = 1 := by
    ext i j
    simp [D, Matrix.submatrix, Matrix.one_apply, eq_comm]
  have hD : r ≤ Matrix.rank D := by
    have h := Matrix.rank_submatrix_le D id (fun i : Fin r => (i.succ, p₀))
    simpa only [hminor, Matrix.rank_one, Fintype.card_fin] using h
  have hDH : D * H = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Fintype.sum_prod_type_right]
    simp_rw [D, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
    simp only [Fintype.sum_ite_eq']
    rw [hbal i.succ j]
    simp
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero hDH
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- The block-row bound can also be expressed with natural-number subtraction. -/
theorem rank_le {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (r : ℕ) (p₀ : ι) (H : Matrix (Fin (r + 1) × ι) κ K)
    (hbal : ∀ (a : Fin (r + 1)) (j : κ),
      ∑ p : ι, H (a, p) j = ∑ p : ι, H (0, p) j) :
    Matrix.rank H ≤ (r + 1) * Fintype.card ι - r := by
  have h := rank_add_le r p₀ H hbal
  omega

/-- Assemble permutation incidence matrices with initial row labels on the left. -/
def permBlocks {K α β ι : Type*} [Zero K] [One K] [DecidableEq ι]
    (σ : α → β → Equiv.Perm ι) : Matrix (α × ι) (β × ι) K :=
  fun ap bq => if σ ap.1 bq.1 ap.2 = bq.2 then 1 else 0

/-- Each column of each permutation block contains exactly one unit entry. -/
theorem block_col_sum {K α β ι : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    (σ : α → β → Equiv.Perm ι) (a : α) (b : β) (q : ι) :
    ∑ p : ι, permBlocks (K := K) σ (a, p) (b, q) = 1 := by
  unfold permBlocks
  calc
    (∑ p : ι, if σ a b p = q then (1 : K) else 0) =
        ∑ p : ι, if p = q then (1 : K) else 0 :=
      Fintype.sum_equiv (σ a b) _ _ (fun _ => rfl)
    _ = 1 := by simp

/-- Permutation-block check matrices satisfy the common block-row rank bound. -/
theorem perm_rank_add {K β ι : Type*} [Field K] [Fintype β] [Fintype ι]
    [DecidableEq ι] (r : ℕ) (p₀ : ι) (σ : Fin (r + 1) → β → Equiv.Perm ι) :
    Matrix.rank (permBlocks (K := K) σ) + r ≤ (r + 1) * Fintype.card ι := by
  apply rank_add_le r p₀
  intro a ⟨b, q⟩
  rw [block_col_sum, block_col_sum]

end Qatlib.Concepts.CodeCert.PermBlocks
