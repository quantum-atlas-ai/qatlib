/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Bayesian Deep Learning on a Quantum Computer (arXiv:1806.11463), Section III C.

This file fixes the operator-level source model behind Lemmas 1 and 2 and the
recursion of Theorem 1: the modified SWAP operators `S₁`, `S₂` acting on three
registers, the Hadamard product `⊙`, the diagonal outer product `⊘`, and the
exact partial-trace identities (paper Eqs. (10), (11) and their diagonal-outer
analogues) that are the mathematical core of the construction.

Paper version read: arXiv:1806.11463 (PDF pages 4-6).
-/
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.BayesDeepNet18.MainResults

/-! ## Elementwise operations on operators -/

/-- The Hadamard (entrywise) product `ρ₁ ⊙ ρ₂` of two `d`-dimensional operators,
as used in Lemma 1 of arXiv:1806.11463. -/
def hadamardProduct {d : ℕ} (ρ₁ ρ₂ : Operator d) : Operator d :=
  fun i j => ρ₁ i j * ρ₂ i j

/-- The outer product `ρ₁ ⊘ ρ₂` of the diagonal entries of `ρ₁` and `ρ₂`.  With
the index convention forced by the source operator `S₂` of arXiv:1806.11463,
its `(i,j)` entry is `(ρ₁)ⱼⱼ (ρ₂)ᵢᵢ`. -/
def diagOuterProduct {d : ℕ} (ρ₁ ρ₂ : Operator d) : Operator d :=
  fun i j => ρ₁ j j * ρ₂ i i

/-! ## The three-register model -/

/-- The three-register operator `ρ₁ ⊗ ρ₂ ⊗ σ`, indexed by `(ρ₁-index, ρ₂-index,
σ-index)`. -/
def tensor3 {d : ℕ} (ρ₁ ρ₂ σ : Operator d) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  fun i j => ρ₁ i.1.1 j.1.1 * ρ₂ i.1.2 j.1.2 * σ i.2 j.2

/-- Partial trace over the first two registers, keeping the third: `tr₁,₂` of
arXiv:1806.11463. -/
def ptrace12 {d : ℕ}
    (X : Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ) : Operator d :=
  fun c c' => ∑ a : Fin d, ∑ b : Fin d, X ((a, b), c) ((a, b), c')

/-- The modified SWAP operator `S₁ = Σ_{j,k} |j⟩⟨k| ⊗ |j⟩⟨k| ⊗ |k⟩⟨j|` of
arXiv:1806.11463 (Section III C, p.4). -/
def S1 (d : ℕ) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  fun i j => if i.1.1 = i.1.2 ∧ j.1.1 = j.1.2 ∧ i.2 = j.1.1 ∧ j.2 = i.1.1 then (1 : ℂ) else 0

/-- The modified SWAP operator `S₂ = Σ_{j,k} |j⟩⟨j| ⊗ |k⟩⟨k| ⊗ |k⟩⟨j|` of
arXiv:1806.11463 (Section III C, p.4). -/
def S2 (d : ℕ) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  fun i j => if i.1.1 = j.1.1 ∧ i.1.2 = j.1.2 ∧ i.2 = i.1.2 ∧ j.2 = i.1.1 then (1 : ℂ) else 0

/-! ## Exact partial-trace identities

These are paper Eqs. (10), (11) (Hadamard case) and the diagonal-outer analogues
stated on p.5.  They identify the first-order generator of the `S₁`/`S₂`
conjugation with the commutator against `ρ₁ ⊙ ρ₂` / `ρ₁ ⊘ ρ₂`. -/

/-- Paper Eq. (10): `tr₁,₂{S₁ (ρ₁ ⊗ ρ₂ ⊗ σ)} = (ρ₁ ⊙ ρ₂) σ`. -/
theorem S1_mul_tensor3_ptrace {d : ℕ} (ρ₁ ρ₂ σ : Operator d) :
    ptrace12 (S1 d * tensor3 ρ₁ ρ₂ σ) = hadamardProduct ρ₁ ρ₂ * σ := by
  ext c c'
  simp only [ptrace12, Matrix.mul_apply, S1, tensor3, hadamardProduct]
  have hinner : ∀ a : Fin d,
      (∑ b : Fin d, ∑ k : (Fin d × Fin d) × Fin d,
        (if a = b ∧ k.1.1 = k.1.2 ∧ c = k.1.1 ∧ k.2 = a then (1 : ℂ) else 0)
          * (ρ₁ k.1.1 a * ρ₂ k.1.2 b * σ k.2 c'))
      = ρ₁ c a * ρ₂ c a * σ a c' := by
    intro a
    rw [Finset.sum_eq_single a
      (by
        intro b _ hb
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg (by intro h; exact hb h.1.symm), zero_mul])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    rw [Finset.sum_eq_single ((c, c), a)
      (by
        intro k _ hk
        have hc : ¬ (a = a ∧ k.1.1 = k.1.2 ∧ c = k.1.1 ∧ k.2 = a) := by
          intro h
          apply hk
          have h1 : k.1.1 = c := h.2.2.1.symm
          have h2 : k.1.2 = c := h.2.1.symm.trans h.2.2.1.symm
          have h3 : k.2 = a := h.2.2.2
          ext <;> simp [h1, h2, h3]
        rw [if_neg hc, zero_mul])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    simp
  simp only [hinner]

/-- Paper Eq. (11): `tr₁,₂{(ρ₁ ⊗ ρ₂ ⊗ σ) S₁} = σ (ρ₁ ⊙ ρ₂)`. -/
theorem tensor3_mul_S1_ptrace {d : ℕ} (ρ₁ ρ₂ σ : Operator d) :
    ptrace12 (tensor3 ρ₁ ρ₂ σ * S1 d) = σ * hadamardProduct ρ₁ ρ₂ := by
  ext c c'
  simp only [ptrace12, Matrix.mul_apply, S1, tensor3, hadamardProduct]
  have hinner : ∀ a : Fin d,
      (∑ b : Fin d, ∑ k : (Fin d × Fin d) × Fin d,
        (ρ₁ a k.1.1 * ρ₂ b k.1.2 * σ c k.2)
          * (if a = b ∧ k.1.1 = k.1.2 ∧ k.2 = a ∧ c' = k.1.1 then (1 : ℂ) else 0))
      = ρ₁ a c' * ρ₂ a c' * σ c a := by
    intro a
    rw [Finset.sum_eq_single a
      (by
        intro b _ hb
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg (by intro h; exact hb h.1.symm), mul_zero])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    rw [Finset.sum_eq_single ((c', c'), a)
      (by
        intro k _ hk
        have hc : ¬ (a = a ∧ k.1.1 = k.1.2 ∧ k.2 = a ∧ c' = k.1.1) := by
          intro h
          apply hk
          have h1 : k.1.1 = c' := h.2.2.2.symm
          have h2 : k.1.2 = c' := h.2.1.symm.trans h.2.2.2.symm
          have h3 : k.2 = a := h.2.2.1
          ext <;> simp [h1, h2, h3]
        rw [if_neg hc, mul_zero])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    simp
  trans ∑ a : Fin d, (ρ₁ a c' * ρ₂ a c' * σ c a)
  · apply Finset.sum_congr rfl
    intro a _
    simpa only [and_comm, and_left_comm, and_assoc] using hinner a
  · apply Finset.sum_congr rfl
    intro m _
    ring

/-- Diagonal-outer analogue of Eq. (10):
`tr₁,₂{S₂ (ρ₁ ⊗ ρ₂ ⊗ σ)} = (ρ₁ ⊘ ρ₂) σ`. -/
theorem S2_mul_tensor3_ptrace {d : ℕ} (ρ₁ ρ₂ σ : Operator d) :
    ptrace12 (S2 d * tensor3 ρ₁ ρ₂ σ) = diagOuterProduct ρ₁ ρ₂ * σ := by
  ext c c'
  simp only [ptrace12, Matrix.mul_apply, S2, tensor3, diagOuterProduct]
  have hinner : ∀ a : Fin d,
      (∑ b : Fin d, ∑ k : (Fin d × Fin d) × Fin d,
        (if a = k.1.1 ∧ b = k.1.2 ∧ c = b ∧ k.2 = a then (1 : ℂ) else 0)
          * (ρ₁ k.1.1 a * ρ₂ k.1.2 b * σ k.2 c'))
      = ρ₁ a a * ρ₂ c c * σ a c' := by
    intro a
    rw [Finset.sum_eq_single c
      (by
        intro b _ hbc
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg (by intro h; exact hbc h.2.2.1.symm), zero_mul])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    rw [Finset.sum_eq_single ((a, c), a)
      (by
        intro k _ hk
        have hc : ¬ (a = k.1.1 ∧ c = k.1.2 ∧ c = c ∧ k.2 = a) := by
          intro h
          apply hk
          have h1 : k.1.1 = a := h.1.symm
          have h2 : k.1.2 = c := h.2.1.symm
          have h3 : k.2 = a := h.2.2.2
          ext <;> simp [h1, h2, h3]
        rw [if_neg hc, zero_mul])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    simp
  trans ∑ a : Fin d, (ρ₁ a a * ρ₂ c c * σ a c')
  · apply Finset.sum_congr rfl
    intro a _
    exact hinner a
  · rfl

/-- Diagonal-outer analogue of Eq. (11):
`tr₁,₂{(ρ₁ ⊗ ρ₂ ⊗ σ) S₂} = σ (ρ₁ ⊘ ρ₂)`. -/
theorem tensor3_mul_S2_ptrace {d : ℕ} (ρ₁ ρ₂ σ : Operator d) :
    ptrace12 (tensor3 ρ₁ ρ₂ σ * S2 d) = σ * diagOuterProduct ρ₁ ρ₂ := by
  ext c c'
  simp only [ptrace12, Matrix.mul_apply, S2, tensor3, diagOuterProduct]
  have hinner : ∀ a : Fin d,
      (∑ b : Fin d, ∑ k : (Fin d × Fin d) × Fin d,
        (ρ₁ a k.1.1 * ρ₂ b k.1.2 * σ c k.2)
          * (if k.1.1 = a ∧ k.1.2 = b ∧ k.2 = k.1.2 ∧ c' = k.1.1 then (1 : ℂ) else 0))
      = if c' = a then (∑ b : Fin d, ρ₁ a a * ρ₂ b b * σ c b) else 0 := by
    intro a
    by_cases hca : c' = a
    · rw [if_pos hca]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single ((a, b), b)
        (by
          intro k _ hk
          have hc : ¬ (k.1.1 = a ∧ k.1.2 = b ∧ k.2 = k.1.2 ∧ c' = k.1.1) := by
            intro h
            apply hk
            have h1 : k.1.1 = a := h.1
            have h2 : k.1.2 = b := h.2.1
            have h3 : k.2 = b := by rw [h.2.2.1, h2]
            ext <;> simp [h1, h2, h3]
          rw [if_neg hc, mul_zero])
        (by intro h; exact absurd (Finset.mem_univ _) h)]
      simp [hca]
    · rw [if_neg hca]
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by intro h; exact hca (h.2.2.2.trans h.1)), mul_zero]
  trans ∑ a : Fin d, (if c' = a then (∑ b : Fin d, ρ₁ a a * ρ₂ b b * σ c b) else 0)
  · apply Finset.sum_congr rfl
    intro a _
    exact hinner a
  · rw [Finset.sum_eq_single c'
      (by
        intro a _ hac
        rw [if_neg (by intro h; exact hac h.symm)])
      (by intro h; exact absurd (Finset.mem_univ _) h)]
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro m _
    ring

end Qatlib.Papers.BayesDeepNet18.MainResults
