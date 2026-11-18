/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.PermBlocks.Rank

@[expose] public section

/-!
# Permutation-block algebra: relative permutations and pair cancellation

Single-block permutation matrices compose and invert like their underlying
permutations, so the paper's pairing equivalence between block products
becomes equality of relative permutations. Assembled permutation blocks
have constant row and column weights.
-/

namespace Qatlib.Concepts.CodeCert.PermBlocks

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix

variable {K : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Field K] [DecidableEq K]

/-- The permutation matrix of a single block. -/
def permMat (σ : Equiv.Perm ι) : Matrix ι ι K :=
  Matrix.of fun p q => if σ p = q then 1 else 0

omit [Fintype ι] [DecidableEq K] in
/-- The identity permutation has the identity matrix. -/
theorem permMat_one : permMat (Equiv.refl ι) = (1 : Matrix ι ι K) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [permMat]
  · simp [permMat, hpq]

omit [Fintype ι] [DecidableEq K] in
/-- The transpose of a block permutation matrix is the inverse permutation. -/
theorem permMat_transpose (τ : Equiv.Perm ι) :
    (permMat τ : Matrix ι ι K)ᵀ = permMat τ⁻¹ := by
  ext p q
  by_cases hq : Equiv.symm τ p = q
  · have hτqp : τ q = p := by rw [← hq]; exact Equiv.apply_symm_apply τ p
    simp [permMat, hτqp, hq]
  · have hq' : ¬ (τ q = p) := by
      intro h
      apply hq
      rw [← h]
      exact Equiv.symm_apply_apply τ q
    simp [permMat, hq', hq]

omit [DecidableEq K] in
/-- Permutation matrices compose as their permutations do. -/
theorem permMat_mul (σ τ : Equiv.Perm ι) :
    permMat σ * permMat τ = (permMat (τ * σ) : Matrix ι ι K) := by
  ext p q
  have hone : ((permMat σ * permMat τ : Matrix ι ι K)) p q
      = (if τ (σ p) = q then (1 : K) else 0) := by
    rw [Matrix.mul_apply]
    have hdiag : ∀ r ∈ (Finset.univ : Finset ι), r ≠ σ p →
        ((permMat σ : Matrix ι ι K)) p r * permMat τ r q = 0 := by
      intro r _ hr
      by_cases hr2 : σ p = r
      · exact absurd hr2 (Ne.symm hr)
      · simp [permMat, hr2]
    rw [Finset.sum_eq_single_of_mem (σ p) (Finset.mem_univ _) hdiag]
    by_cases hq2 : τ (σ p) = q
    · simp [permMat, hq2]
    · simp [permMat, hq2]
  rw [hone, permMat, Matrix.of_apply, Equiv.Perm.mul_apply]

omit [Fintype ι] [DecidableEq K] in
/-- Distinct permutations give distinct block matrices. -/
theorem permMat_inj {σ τ : Equiv.Perm ι}
    (h : (permMat σ : Matrix ι ι K) = permMat τ) : σ = τ := by
  apply Equiv.ext
  intro p
  have hp := congrFun₂ h p (σ p)
  simp only [permMat, Matrix.of_apply] at hp
  by_cases hq : τ p = σ p
  · exact hq.symm
  · simp [hq] at hp

omit [DecidableEq K] in
/-- The paper's pairing equivalence: block products agree exactly when the
relative permutations agree. -/
theorem pairCancel (σx σx' σz σz' : Equiv.Perm ι) :
    (permMat σx * (permMat σz)ᵀ : Matrix ι ι K)
      = permMat σx' * (permMat σz')ᵀ
      ↔ σz⁻¹ * σx = (σz')⁻¹ * σx' := by
  rw [permMat_transpose, permMat_transpose, permMat_mul, permMat_mul]
  exact ⟨permMat_inj, fun h => by rw [h]⟩

/-- Row weight of a matrix counts its unit entries per row. -/
def matRowWt {α β : Type*} [Fintype β]
    (M : Matrix α β K) (a : α) : ℕ :=
  (Finset.univ.filter fun b => M a b = 1).card

/-- Column weight of a matrix counts its unit entries per column. -/
def matColWt {α β : Type*} [Fintype α]
    (M : Matrix α β K) (b : β) : ℕ :=
  (Finset.univ.filter fun a => M a b = 1).card

/-- Assembled permutation blocks have row weight equal to the column-block
count. -/
theorem permBlocks_rwt {α β : Type*}
    [Fintype β] [DecidableEq β] (σ : α → β → Equiv.Perm ι)
    (a : α) (p : ι) :
    matRowWt (permBlocks σ : Matrix (α × ι) (β × ι) K) (a, p) = Fintype.card β := by
  have hinj : Function.Injective (fun b : β => (b, σ a b p)) := by
    intro b1 b2 h
    exact congrArg Prod.fst h
  have himg : (Finset.univ.filter fun c : β × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) (a, p) c = 1)
      = Finset.univ.image (fun b : β => (b, σ a b p)) := by
    ext c
    constructor
    · intro h1
      simp only [Finset.mem_filter, Finset.mem_univ] at h1
      obtain ⟨_, h1⟩ := h1
      by_cases h2 : σ a c.1 p = c.2
      · refine Finset.mem_image.mpr ⟨c.1, Finset.mem_univ c.1, ?_⟩
        rw [h2, Prod.eta]
      · exfalso
        simp [permBlocks, h2] at h1
    · intro hmem
      obtain ⟨b, _, hbe⟩ := Finset.mem_image.mp hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hbe]
      simp [permBlocks]
  have hcard : (Finset.univ.filter fun c : β × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) (a, p) c = 1).card
      = Fintype.card β := by
    rw [himg, Finset.card_image_of_injective _ hinj]
    simp
  show (Finset.univ.filter fun c : β × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) (a, p) c = 1).card
    = Fintype.card β
  exact hcard

/-- Assembled permutation blocks have column weight equal to the row-block count. -/
theorem permBlocks_cwt {α β : Type*} [Fintype α] [DecidableEq α]
    (σ : α → β → Equiv.Perm ι) (b : β) (q : ι) :
    matColWt (permBlocks σ : Matrix (α × ι) (β × ι) K) (b, q) = Fintype.card α := by
  have hinj : Function.Injective (fun a : α => (a, (σ a b).symm q)) := by
    intro a1 a2 h
    exact congrArg Prod.fst h
  have himg : (Finset.univ.filter fun c : α × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) c (b, q) = 1)
      = Finset.univ.image (fun a : α => (a, (σ a b).symm q)) := by
    ext c
    constructor
    · intro h1
      simp only [Finset.mem_filter, Finset.mem_univ] at h1
      obtain ⟨_, h1⟩ := h1
      by_cases h2 : σ c.1 b c.2 = q
      · have hq : c.2 = (σ c.1 b).symm q := by
          rw [← h2]
          simp
        refine Finset.mem_image.mpr ⟨c.1, Finset.mem_univ c.1, ?_⟩
        exact Prod.ext rfl hq.symm
      · exfalso
        simp [permBlocks, h2] at h1
    · intro hmem
      obtain ⟨a, _, hbe⟩ := Finset.mem_image.mp hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hbe]
      simp [permBlocks]
  have hcard : (Finset.univ.filter fun c : α × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) c (b, q) = 1).card
      = Fintype.card α := by
    rw [himg, Finset.card_image_of_injective _ hinj]
    simp
  show (Finset.univ.filter fun c : α × ι =>
      (permBlocks σ : Matrix (α × ι) (β × ι) K) c (b, q) = 1).card
    = Fintype.card α
  exact hcard

end Qatlib.Concepts.CodeCert.PermBlocks
