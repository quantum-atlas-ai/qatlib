/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.Vocabulary
import Mathlib.Data.Matrix.Basis

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — core twirl and permutation-operator lemmas (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This module collects the structural lemmas that the paper's Section 2 arguments
rely on:

* `permOp_eq_one_iff` and the row/column uniqueness of `permOp`: the permutation
  operator `W_π` of eq. (9) has exactly one non-zero entry per row and per column.
* `permOp_isUnitary`: `W_π` is a unitary operator, so the permutation operators
  form a unitary family (the paper's eq. (9) representation).
* `haarTwirl_of_central`: the Haar twirl `T_k` fixes every operator that commutes
  with all unitary conjugations (equation (23) of Proposition 2).
* `proposition2_haar`: Proposition 2 stated for the genuine Haar twirl.
* `proposition3_of_commutant_span`: Proposition 3's proof step — if the commutant
  of the unitary conjugation action is spanned by the `W_π`, then `T_k(X)` lies in
  that span and hence is a linear combination of permutation operators.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Classical

namespace Qatlib.Papers.Clifford3Des15.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ChannelTheory.TwirlChannel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι]

/-! ## The permutation operator `W_π` as a permutation matrix (eq. (9)) -/

/-- Entry form of the permutation operator `W_π`: the `(i,j)` entry is `1` exactly
when the register index `j` is the permutation `π` applied to the register index
`i` (under the enumeration `regEquiv`). -/
theorem permOp_apply (d k : ℕ) (π : Equiv.Perm (Fin k)) (i j : Fin (d ^ k)) :
    permOp d k π i j
      = if (regEquiv d k).symm j = (regEquiv d k).symm i ∘ π then (1 : ℂ) else 0 := rfl

/-- `W_π` has entry `1` at `(i,j)` exactly when the register index `j` equals the
`π`-image of the register index `i`. -/
theorem permOp_eq_one_iff (d k : ℕ) (π : Equiv.Perm (Fin k)) (i j : Fin (d ^ k)) :
    permOp d k π i j = 1 ↔ (regEquiv d k).symm j = (regEquiv d k).symm i ∘ π := by
  rw [permOp_apply]
  by_cases h : (regEquiv d k).symm j = (regEquiv d k).symm i ∘ π
  · simp [h]
  · simp [h]

/-- Every entry of `W_π` is `0` or `1`. -/
theorem permOp_entry_zero_or_one (d k : ℕ) (π : Equiv.Perm (Fin k)) (i j : Fin (d ^ k)) :
    permOp d k π i j = 0 ∨ permOp d k π i j = 1 := by
  rw [permOp_apply]
  split_ifs <;> simp

/-- Each row of `W_π` has exactly one entry equal to `1` (equation (9): `W_π` is a
permutation operator). -/
theorem permOp_row_unique (d k : ℕ) (π : Equiv.Perm (Fin k)) (i : Fin (d ^ k)) :
    ∃! j : Fin (d ^ k), permOp d k π i j = 1 := by
  refine ⟨(regEquiv d k) ((regEquiv d k).symm i ∘ ⇑π), ?_, ?_⟩
  · change permOp d k π i ((regEquiv d k) ((regEquiv d k).symm i ∘ ⇑π)) = 1
    rw [permOp_eq_one_iff]; simp
  · intro j hj
    rw [permOp_eq_one_iff] at hj
    rw [← hj]; simp

/-- Each column of `W_π` has exactly one entry equal to `1`. -/
theorem permOp_col_unique (d k : ℕ) (π : Equiv.Perm (Fin k)) (j : Fin (d ^ k)) :
    ∃! i : Fin (d ^ k), permOp d k π i j = 1 := by
  refine ⟨(regEquiv d k) ((regEquiv d k).symm j ∘ ⇑π.symm), ?_, ?_⟩
  · change permOp d k π ((regEquiv d k) ((regEquiv d k).symm j ∘ ⇑π.symm)) j = 1
    rw [permOp_eq_one_iff]
    funext x
    simp
  · intro i hi
    rw [permOp_eq_one_iff] at hi
    have hsymm : (regEquiv d k).symm i = (regEquiv d k).symm j ∘ ⇑π.symm := by
      funext x
      have h := congrFun hi (π.symm x)
      simpa [Function.comp_apply] using h.symm
    rw [← hsymm]; simp

/-- A `0/1` matrix with exactly one `1` per row and per column is unitary. -/
theorem isUnitaryMatrix_of_unique_support {D : ℕ} (M : Operator D)
    (hval : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrow : ∀ i, ∃! j, M i j = 1)
    (hcol : ∀ j, ∃! i, M i j = 1) :
    IsUnitaryMatrix M := by
  have hzero_of_ne : ∀ i j, M i j ≠ 1 → M i j = 0 := by
    intro i j h
    rcases hval i j with h0 | h1
    · exact h0
    · exact absurd h1 h
  constructor
  · ext i j
    -- `(M† * M) i j = Σ_k star(M k i) * M k j`; column `i` has a unique `1` at row `ci`.
    obtain ⟨ci, hci, huni⟩ := hcol i
    have hMki : ∀ k : Fin D, k ≠ ci → M k i = 0 := by
      intro k hk
      exact hzero_of_ne k i (fun h1 => hk (huni k h1))
    calc (M.conjTranspose * M) i j
        = ∑ k : Fin D, star (M k i) * M k j := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = star (M ci i) * M ci j := by
          refine Finset.sum_eq_single ci (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ ci) h)
          rw [hMki k hk, star_zero, zero_mul]
      _ = (1 : Operator D) i j := by
          rw [hci, star_one, one_mul]
          have hrowi : M ci j = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · subst hij; simp [hci]
            · have hne : M ci j ≠ 1 := fun h1 => hij ((hrow ci).unique hci h1)
              rw [hzero_of_ne ci j hne]; simp [hij]
          by_cases hij : i = j
          · subst hij; rw [hrowi]; simp
          · rw [hrowi]; simp [hij]
  · ext i j
    -- `(M * M†) i j = Σ_k M i k * star(M j k)`; row `i` has a unique `1` at column `ri`.
    obtain ⟨ri, hri, huni⟩ := hrow i
    have hMik : ∀ k : Fin D, k ≠ ri → M i k = 0 := by
      intro k hk
      exact hzero_of_ne i k (fun h1 => hk (huni k h1))
    calc (M * M.conjTranspose) i j
        = ∑ k : Fin D, M i k * star (M j k) := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = M i ri * star (M j ri) := by
          refine Finset.sum_eq_single ri (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ ri) h)
          rw [hMik k hk, zero_mul]
      _ = (1 : Operator D) i j := by
          rw [hri, one_mul]
          have hcolj : M j ri = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · subst hij; simp [hri]
            · have hne : M j ri ≠ 1 := fun h1 => hij ((hcol ri).unique hri h1)
              rw [hzero_of_ne j ri hne]; simp [hij]
          by_cases hij : i = j
          · subst hij; rw [hcolj]; simp
          · rw [hcolj]; simp [hij]

/-- The permutation operator `W_π` is unitary. -/
theorem permOp_isUnitary (d k : ℕ) (π : Equiv.Perm (Fin k)) :
    IsUnitaryMatrix (permOp d k π) :=
  isUnitaryMatrix_of_unique_support _
    (permOp_entry_zero_or_one d k π)
    (permOp_row_unique d k π)
    (permOp_col_unique d k π)

/-! ## Haar twirl fixes central operators (Proposition 2, eq. (23)) -/

/-- **Proposition 2 core** (eq. (23)): any operator `W` that is fixed by conjugation
with every unitary is fixed by the Haar twirl `T_k`. -/
theorem haarTwirl_of_central {D : ℕ} (H : HaarUnitaryMeasure D) (W : Operator D)
    (hW : ∀ A : Operator D, IsUnitaryMatrix A → A * W * A.conjTranspose = W) :
    HaarTwirl H W = W := by
  ext i j
  show MeasureTheory.integral H.μ
      (fun A : Operator D => (A * W * A.conjTranspose) i j) = W i j
  have hcongr : (fun A : Operator D => (A * W * A.conjTranspose) i j)
      =ᵐ[H.μ] fun _ : Operator D => W i j := by
    filter_upwards [haar_ae_unitary H] with A hA
    exact congrArg (fun M : Operator D => M i j) (hW A hA)
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const]
  change (H.μ).real Set.univ • W i j = W i j
  rw [haar_prob_real_univ H, one_smul]

/-- **Proposition 2** (claim `c006`; eq. (23)) for the genuine Haar twirl: if the
permutation operator `W` commutes with every unitary (the paper derives this for
`W_π` from `[W_π, V^{⊗k}] = 0`), then `T_k(W) = W`. -/
theorem proposition2_haar {D : ℕ} (H : HaarUnitaryMeasure D) (W : Operator D)
    (hcomm : ∀ A : Operator D, IsUnitaryMatrix A → A * W = W * A) :
    HaarTwirl H W = W := by
  refine haarTwirl_of_central H W ?_
  intro A hA
  rw [hcomm A hA, Matrix.mul_assoc, hA.2, Matrix.mul_one]

/-! ## Proposition 3's reduction to the commutant span -/

/-- **Proposition 3 core** (claim `c007`; eq. (24)): if the commutant of the unitary
conjugation action on `L(X^{⊗k})` is contained in the span of the permutation
operators `W_π = permOp d k π`, then `T_k(X)` is a complex linear combination of
those permutation operators — exactly the conclusion of Proposition 3.

The containment hypothesis is the paper's Theorem 1 (double commutant / Wedderburn)
applied to the tensor-power representation; `haarTwirl_unitary_conj_fixed` supplies
that `T_k(X)` lies in the commutant. -/
theorem proposition3_of_commutant_span {d k : ℕ} (H : HaarUnitaryMeasure (d ^ k))
    (X : Operator (d ^ k))
    (hspan : ∀ T : Operator (d ^ k),
      (∀ A : Operator (d ^ k), IsUnitaryMatrix A → A * T * A.conjTranspose = T) →
      T ∈ Submodule.span ℂ (Set.range (permOp d k))) :
    ∃ α : Equiv.Perm (Fin k) → ℂ,
      HaarTwirl H X = ∑ π : Equiv.Perm (Fin k), α π • permOp d k π := by
  have hmem : HaarTwirl H X ∈ Submodule.span ℂ (Set.range (permOp d k)) :=
    hspan _ (fun A hA => haarTwirl_unitary_conj_fixed H A X hA)
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  exact ⟨α, hα.symm⟩

end Qatlib.Papers.Clifford3Des15.MainResults
