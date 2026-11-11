/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs

/-!
# Isometric realization of equal complete branches

The predicate `IsUnitaryEmbedding` is the identity Gram condition for a rectangular complex
matrix. If a finite complete family of branch matrices is constant, the theorem constructs a
common isometric embedding by multiplying each branch by the square root of the branch count.
Its conjugation equals the sum of branch conjugations, formalizing the strong-determinism
implication in [DanosKashefi2006].

## Main statements

* `stronglyDeterministic_realizes_unitaryEmbedding`: A finite family of equal branch matrices
  whose Gram matrices sum to identity determines an isometric embedding equal to each branch
  scaled by the square root of the branch count. Conjugation by this embedding equals the sum of
  branch conjugations for every input matrix.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

variable {m n : ℕ}

/-- The predicate that a rectangular matrix has identity conjugate-transpose Gram matrix. -/
def IsUnitaryEmbedding (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  A.conjTranspose * A = 1

/-- A finite family of equal branch matrices whose Gram matrices sum to identity determines an
isometric embedding equal to each branch scaled by the square root of the branch count.
Conjugation by this embedding equals the sum of branch conjugations for every input matrix
[DanosKashefi2006]. -/
theorem stronglyDeterministic_realizes_unitaryEmbedding
    {S : Type*} [Fintype S]
    (A : S → Matrix (Fin m) (Fin n) ℂ)
    (hdet : ∀ s s' : S, A s = A s')
    (hcomplete : ∑ s : S, (A s).conjTranspose * (A s) = 1) :
    ∃ A' : Matrix (Fin m) (Fin n) ℂ,
      IsUnitaryEmbedding A' ∧
      (∀ s : S, A' = (Real.sqrt (Fintype.card S) : ℂ) • A s) ∧
      (∀ ρ : Matrix (Fin n) (Fin n) ℂ,
        ∑ s : S, A s * ρ * (A s).conjTranspose
          = A' * ρ * A'.conjTranspose) := by
  classical
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    set c : ℂ := (Real.sqrt (Fintype.card S) : ℂ) with hc_def
    set M : Matrix (Fin m) (Fin n) ℂ := A s₀ with hM_def

    have hcc : c * c = (Fintype.card S : ℂ) := by
      rw [hc_def, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card S))]
      simp
    have hstar : star c = c := by
      rw [hc_def, Complex.star_def, Complex.conj_ofReal]

    have hsum : ∑ s : S, (A s).conjTranspose * (A s)
        = (Fintype.card S : ℂ) • (M.conjTranspose * M) := by
      have h1 : ∑ s : S, (A s).conjTranspose * (A s)
          = ∑ _s : S, M.conjTranspose * M := by
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [hdet s s₀, hM_def]
      rw [h1, Finset.sum_const, Finset.card_univ]
      exact (Nat.cast_smul_eq_nsmul ℂ (Fintype.card S) (M.conjTranspose * M)).symm

    have hiso : IsUnitaryEmbedding (c • M) := by
      unfold IsUnitaryEmbedding
      calc ((c • M).conjTranspose * (c • M))
          = ((star c) • M.conjTranspose) * (c • M) := by
            rw [Matrix.conjTranspose_smul]
        _ = (star c * c) • (M.conjTranspose * M) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = (Fintype.card S : ℂ) • (M.conjTranspose * M) := by rw [hstar, hcc]
        _ = 1 := by rw [← hsum]; exact hcomplete

    have hT : ∀ ρ : Matrix (Fin n) (Fin n) ℂ,
        ∑ s : S, A s * ρ * (A s).conjTranspose
          = (c • M) * ρ * (c • M).conjTranspose := by
      intro ρ
      have h1 : ∑ s : S, A s * ρ * (A s).conjTranspose
          = ∑ _s : S, M * ρ * M.conjTranspose := by
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [hdet s s₀, hM_def]
      rw [h1, Finset.sum_const, Finset.card_univ]
      rw [show Fintype.card S • (M * ρ * M.conjTranspose)
            = (Fintype.card S : ℂ) • (M * ρ * M.conjTranspose) from
          (Nat.cast_smul_eq_nsmul ℂ (Fintype.card S) _).symm]
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hstar, hcc]
    refine ⟨c • M, hiso, ?_, hT⟩
    intro s
    rw [hM_def, hdet s s₀]
  · haveI : IsEmpty S := not_nonempty_iff.mp hS
    have hzero : (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have hempty : ∑ s : S, (A s).conjTranspose * (A s) = 0 := by
        rw [Finset.univ_eq_empty, Finset.sum_empty]
      rw [hempty] at hcomplete
      exact hcomplete
    refine ⟨0, ?_, ?_, ?_⟩
    · unfold IsUnitaryEmbedding
      rw [Matrix.conjTranspose_zero, Matrix.zero_mul]
      exact hzero
    · intro s
      exact (isEmptyElim s)
    · intro ρ
      simp [Finset.univ_eq_empty]

end Qatlib.Papers.OneWayDanos05.MainResults
