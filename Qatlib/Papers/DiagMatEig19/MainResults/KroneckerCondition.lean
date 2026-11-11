/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# Condition number of a Kronecker product (DiagMatEig19)

Source: *Computing eigenvalues of diagonalizable matrices in a quantum computer*,
fixed arXiv:1912.08015, Lemma 17 (§3, p.16).

The paper proves that if `σ_1 ≥ … ≥ σ_n > 0` are the singular values of a
nonsingular matrix `P`, then the singular values of `P ⊗ P̄` are `σ_i σ_j`
(both `P` and `P̄` have the same singular values), hence

`κ(P ⊗ P̄) = (max_{i,j} σ_i σ_j) / (min_{i,j} σ_i σ_j) = σ_1² / σ_n² = κ(P)²`.

The formal statement models the condition number exactly as the paper does:
`κ(P)` is the ratio of the largest to the smallest singular value and
`κ(P ⊗ P̄)` is the ratio of the largest to the smallest pairwise product
`σ_i σ_j`.  The extremal values of the pairwise-product family are computed
with `Finset.sup'/inf'`, so the open part of the paper's proof (the SVD
computation `svd(P ⊗ P̄) = {σ_i σ_j}`) is represented by the definition of the
pairwise-product condition number, and the remaining arithmetic is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagMatEig19.MainResults

open scoped BigOperators

/-- arXiv:1912.08015, Lemma 17, §3, p.16.  Let `σ : Fin n → ℝ` be the (positive)
singular values of a nonsingular matrix `P`, indexed so that
`max_i σ i` is the largest and `min_i σ i` the smallest singular value.  Since
the singular values of `P ⊗ P̄` are the pairwise products `σ i * σ j`, the
condition number of `P ⊗ P̄` — the ratio of the largest to the smallest of these
products — equals the square of the condition number of `P`. -/
theorem lemma17_kronecker_condition_number
    (n : ℕ) (hn : 0 < n) (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) :
    (Finset.univ.sup' ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
        (fun p : Fin n × Fin n => σ p.1 * σ p.2))
      / (Finset.univ.inf' ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
        (fun p : Fin n × Fin n => σ p.1 * σ p.2))
      = ((Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i : Fin n => σ i))
          / (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i : Fin n => σ i))) ^ 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n × Fin n) := inferInstance
  set a : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => σ i) with ha
  set b : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin n => σ i) with hb
  have haub : ∀ i, σ i ≤ a := by
    intro i
    rw [ha]
    exact Finset.le_sup' σ (Finset.mem_univ i)
  have hblb : ∀ i, b ≤ σ i := by
    intro i
    rw [hb]
    exact Finset.inf'_le σ (Finset.mem_univ i)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin n)))
    (H := Finset.univ_nonempty) σ
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin n)))
    (H := Finset.univ_nonempty) σ
  have ha_eq : a = σ i₀ := by rw [ha]; exact hi₀
  have hb_eq : b = σ j₀ := by rw [hb]; exact hj₀
  have hapos : 0 < a := by rw [ha_eq]; exact hσ i₀
  have hbpos : 0 < b := by rw [hb_eq]; exact hσ j₀
  have hsup_pair :
      Finset.univ.sup' Finset.univ_nonempty (fun p : Fin n × Fin n => σ p.1 * σ p.2)
        = a * a := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro p _
      exact mul_le_mul (haub p.1) (haub p.2) (le_of_lt (hσ p.2)) (le_of_lt hapos)
    · have hmem : (i₀, i₀) ∈ (Finset.univ : Finset (Fin n × Fin n)) := Finset.mem_univ _
      have hle := Finset.le_sup' (fun p : Fin n × Fin n => σ p.1 * σ p.2) hmem
      rw [ha_eq]
      exact hle
  have hinf_pair :
      Finset.univ.inf' Finset.univ_nonempty (fun p : Fin n × Fin n => σ p.1 * σ p.2)
        = b * b := by
    apply le_antisymm
    · have hmem : (j₀, j₀) ∈ (Finset.univ : Finset (Fin n × Fin n)) := Finset.mem_univ _
      have hle := Finset.inf'_le (fun p : Fin n × Fin n => σ p.1 * σ p.2) hmem
      rw [hb_eq]
      exact hle
    · apply Finset.le_inf'
      intro p _
      exact mul_le_mul (hblb p.1) (hblb p.2) (le_of_lt hbpos) (le_of_lt (hσ p.1))
  rw [hsup_pair, hinf_pair]
  field_simp [ne_of_gt hapos, ne_of_gt hbpos]

end Qatlib.Papers.DiagMatEig19.MainResults
