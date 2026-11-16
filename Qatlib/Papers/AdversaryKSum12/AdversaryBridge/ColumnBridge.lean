/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryKSum12.ArrayWitness.SourceModel

@[expose] public section


set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
namespace Qatlib.Papers.AdversaryKSum12.AdversaryBridge
open Qatlib.Papers.AdversaryKSum12.ArrayWitness

/-! ## Removing illegal columns as a right multiplication -/

/-- Zeroing the illegal columns of `Γ̃ ∘ Δ_i` is right multiplication by the
`0/1` diagonal of legal columns. -/
theorem removeIllegal_hadamard_eq_mul {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (α : ℕ → ℝ) (i : Fin n) :
    removeIllegal T (advGamma q n k T α) ⊙ deltaAt q n k i
      = (advGamma q n k T α ⊙ deltaAt q n k i) *
          diagonal (legalDiagonal T) := by
  ext r y
  simp only [Matrix.hadamard, removeIllegal, legalDiagonal, deltaAt, Matrix.mul_apply,
    Matrix.diagonal]
  rw [Finset.sum_eq_single y]
  · by_cases hy : IsIllegal T y <;> by_cases hd : r.2 i = y i <;> simp [hy, hd]
  · intro b _ hb; simp [hb]
  · intro hy; exact absurd (Finset.mem_univ y) hy

/-- The `0/1` legal-column diagonal has spectral norm at most one. -/
theorem norm_legalDiagonal_le_one {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q)) :
    ‖diagonal (legalDiagonal T)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun y => ?_
  rw [Real.norm_eq_abs]
  by_cases hy : IsIllegal T y <;> simp [legalDiagonal, hy]

/-- **Lemma 11 (p.7), first assertion.**  For the adversary matrix `Γ =
Γ̃` with the illegal columns removed, `‖Γ ∘ Δ_i‖ ≤ ‖Γ̃ ∘ Δ_i‖`.  Column
deletion is an isometry on the column space, so it can only decrease the
spectral norm. -/
theorem source_lemma11_delta_norm_le {q n k : ℕ}
    (T : ∀ S : Finset (Fin n), S.card = k → Finset (Fin k → Fin q))
    (α : ℕ → ℝ) (i : Fin n) :
    ‖removeIllegal T (advGamma q n k T α) ⊙ deltaAt q n k i‖
      ≤ ‖advGamma q n k T α ⊙ deltaAt q n k i‖ := by
  rw [removeIllegal_hadamard_eq_mul]
  calc
    ‖(advGamma q n k T α ⊙ deltaAt q n k i) * diagonal (legalDiagonal T)‖
        ≤ ‖advGamma q n k T α ⊙ deltaAt q n k i‖ * ‖diagonal (legalDiagonal T)‖ :=
          Matrix.l2_opNorm_mul _ _
    _ ≤ ‖advGamma q n k T α ⊙ deltaAt q n k i‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_legalDiagonal_le_one T) (norm_nonneg _)
    _ = ‖advGamma q n k T α ⊙ deltaAt q n k i‖ := mul_one _


end Qatlib.Papers.AdversaryKSum12.AdversaryBridge
