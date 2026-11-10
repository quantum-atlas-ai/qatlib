/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsQuan
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem sourceRectCert_submatrix
    {R S R' S' : Type} {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (f : R' → R) (g : S' → S) (h : sourceRectCert n A Z w) :
    sourceRectCert n (A.submatrix f g) (fun j => (Z j).submatrix f g) w := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  exact ⟨m, fun r j => u (f r) j, fun s j => v (g s) j,
    fun r s => heq (f r) (g s), fun r => hu (f r), fun s => hv (g s)⟩

theorem sourceRectValue_submatrix_le
    {R S R' S' : Type} {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (f : R' → R) (g : S' → S) :
    sourceRectValue (A.submatrix f g) (fun j => (Z j).submatrix f g) ≤ sourceRectValue A Z :=
  sourceRectValue_le_of_cert_imp A Z _ _ (fun _ _ => sourceRectCert_submatrix f g)

theorem sourceRectValue_surjective_submatrix
    {R S R' S' : Type} {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (f : R' → R) (g : S' → S) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    sourceRectValue (A.submatrix f g) (fun j => (Z j).submatrix f g) = sourceRectValue A Z := by
  apply le_antisymm (sourceRectValue_submatrix_le A Z f g)
  choose f' hf' using hf
  choose g' hg' using hg
  apply sourceRectValue_le_of_cert_imp (A.submatrix f g) (fun j => (Z j).submatrix f g) A Z
  intro w _ h
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  refine ⟨m, fun r j => u (f' r) j, fun s j => v (g' s) j, ?_, ?_, ?_⟩
  · intro r s
    simpa only [Matrix.submatrix_apply, hf', hg'] using! heq (f' r) (g' s)
  · intro r; exact hu (f' r)
  · intro s; exact hv (g' s)

def sourceRectMask {R S : Type} (rows : Finset R) (cols : Finset S) (A : Matrix R S ℂ) : Matrix R S ℂ :=
  fun r s => if r ∈ rows ∧ s ∈ cols then A r s else 0

theorem sourceRectMask_norm_le
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (rows : Finset R) (cols : Finset S) (A : Matrix R S ℂ) : ‖sourceRectMask rows cols A‖ ≤ ‖A‖ := by
  let row : Matrix R R ℂ := Matrix.diagonal (fun r => if r ∈ rows then 1 else 0)
  let col : Matrix S S ℂ := Matrix.diagonal (fun s => if s ∈ cols then 1 else 0)
  have hrow : ‖row‖ ≤ 1 := by
    dsimp only [row]
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro r
    split_ifs <;> norm_num
  have hcol : ‖col‖ ≤ 1 := by
    dsimp only [col]
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro s
    split_ifs <;> norm_num
  have hmatrix : sourceRectMask rows cols A = row*A*col := by
    ext r s
    simp [sourceRectMask, row, col, Matrix.diagonal_mul, Matrix.mul_diagonal]
    split_ifs <;> simp_all
  rw [hmatrix]
  have hfirst : ‖row*A‖ ≤ ‖A‖ :=
    (Matrix.l2_opNorm_mul row A).trans (by nlinarith [norm_nonneg A])
  exact (Matrix.l2_opNorm_mul (row*A) col).trans
    ((mul_le_mul_of_nonneg_right hfirst (norm_nonneg col)).trans (by nlinarith [norm_nonneg A]))

theorem sourceFilterUnion_feasible_iff
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {m n : ℕ} (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (M : Matrix R S ℂ) :
    (∀ j, ‖sourceFilterUnion Y Z j ⊙ M‖ ≤ 1) ↔
      (∀ i, ‖Y i ⊙ M‖ ≤ 1) ∧ (∀ j, ‖Z j ⊙ M‖ ≤ 1) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [sourceFilterUnion, Equiv.symm_apply_apply, Sum.elim_inl] using!
        h (finSumFinEquiv (Sum.inl i))
    · intro j
      simpa only [sourceFilterUnion, Equiv.symm_apply_apply, Sum.elim_inr] using!
        h (finSumFinEquiv (Sum.inr j))
  · rintro ⟨hY,hZ⟩ j
    cases he : finSumFinEquiv.symm j with
    | inl i => simpa only [sourceFilterUnion, he, Sum.elim_inl] using! hY i
    | inr i => simpa only [sourceFilterUnion, he, Sum.elim_inr] using! hZ i

theorem sourceRectValue_le_of_dual_feasible_imp
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {m n : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (h : ∀ M : Matrix R S ℂ, (∀ j, ‖Y j ⊙ M‖ ≤ 1) → ∀ j, ‖Z j ⊙ M‖ ≤ 1) :
    sourceRectValue A Y ≤ sourceRectValue A Z := by
  rw [(rectangularSchurDuality R S m A Y).1, (rectangularSchurDuality R S n A Z).1]
  unfold sourceRectDual
  apply iSup_le
  intro M
  exact le_iSup_of_le ⟨M.val,h M.val M.property⟩ le_rfl

theorem sourceRectValue_filterUnion_le
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {m n : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue A (sourceFilterUnion Y Z) ≤ sourceRectValue A Z :=
  sourceRectValue_le_of_dual_feasible_imp A _ _ (fun M h => (sourceFilterUnion_feasible_iff Y Z M).mp h |>.2)

theorem sourceRectValue_filterUnion_eq_of_redundant
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {m n : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (h : ∀ M : Matrix R S ℂ, (∀ j, ‖Z j ⊙ M‖ ≤ 1) → ∀ i, ‖Y i ⊙ M‖ ≤ 1) :
    sourceRectValue A (sourceFilterUnion Y Z) = sourceRectValue A Z := by
  apply le_antisymm (sourceRectValue_filterUnion_le A Y Z)
  exact sourceRectValue_le_of_dual_feasible_imp A _ _
    (fun M hM => (sourceFilterUnion_feasible_iff Y Z M).mpr ⟨h M hM,hM⟩)

theorem sourceRectValue_filterUnion_eq_of_masks
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {m n : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (h : ∀ i, ∃ (j : Fin n) (rows : Finset R) (cols : Finset S),
      ∀ r s, Y i r s = if r ∈ rows ∧ s ∈ cols then Z j r s else 0) :
    sourceRectValue A (sourceFilterUnion Y Z) = sourceRectValue A Z := by
  apply sourceRectValue_filterUnion_eq_of_redundant
  intro M hM i
  obtain ⟨j, rows, cols, hj⟩ := h i
  have hmask : Y i ⊙ M = sourceRectMask rows cols (Z j ⊙ M) := by
    ext r s
    rw [Matrix.hadamard_apply, hj]
    simp only [sourceRectMask, Matrix.hadamard_apply]
    split_ifs <;> simp
  rw [hmask]
  exact (sourceRectMask_norm_le rows cols _).trans (hM j)

theorem sourceRectValue_convexFilter
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (p : Fin n → ℂ)
    (hp : (∑ j, ‖p j‖) ≤ 1) :
    sourceRectValue A (sourceFilterUnion Z (fun _ : Fin 1 => ∑ j, p j • Z j)) = sourceRectValue A Z := by
  apply le_antisymm
  · apply sourceRectValue_le_of_dual_feasible_imp
    intro M hM j
    exact (sourceFilterUnion_feasible_iff Z _ M).mp hM |>.1 j
  · apply sourceRectValue_le_of_dual_feasible_imp
    intro M hM
    apply (sourceFilterUnion_feasible_iff Z _ M).mpr
    refine ⟨hM, ?_⟩
    intro i
    have hsum : (∑ j, p j • Z j) ⊙ M = ∑ j, p j • (Z j ⊙ M) := by
      ext r s
      simp only [Matrix.hadamard_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [hsum]
    calc
      ‖∑ j, p j • (Z j ⊙ M)‖ ≤ ∑ j, ‖p j • (Z j ⊙ M)‖ := norm_sum_le _ _
      _ = ∑ j, ‖p j‖*‖Z j ⊙ M‖ := by simp only [norm_smul]
      _ ≤ ∑ j, ‖p j‖ := Finset.sum_le_sum fun j _ =>
        by simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hM j) (norm_nonneg (p j))
      _ ≤ 1 := hp

theorem sourceRowColumnDisjoint_hadamard {R S : Type} (A B M : Matrix R S ℂ)
    (h : sourceRowColumnDisjoint A B) : sourceRowColumnDisjoint (A ⊙ M) (B ⊙ M) := by
  constructor
  · intro r s t hrs
    simp only [Matrix.hadamard_apply] at hrs ⊢
    exact mul_eq_zero_of_left (h.1 r s t (fun he => hrs (by simp [he]))) _
  · intro s r t hrs
    simp only [Matrix.hadamard_apply] at hrs ⊢
    exact mul_eq_zero_of_left (h.2 s r t (fun he => hrs (by simp [he]))) _

theorem sourceRowColumnDisjoint_norm_add {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (A B : Matrix R S ℂ) (h : sourceRowColumnDisjoint A B) :
    ‖A+B‖ = max ‖A‖ ‖B‖ := by
  have hab : Aᴴ * B = 0 := by
    ext s t
    apply Finset.sum_eq_zero
    intro r _
    by_cases he : A r s = 0
    · simp [he]
    · simp [h.1 r s t he]
  have hab' : A * Bᴴ = 0 := by
    ext r t
    apply Finset.sum_eq_zero
    intro s _
    by_cases he : A r s = 0
    · simp [he]
    · simp [h.2 s r t he]
  have hba : Bᴴ * A = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using! congrArg Matrix.conjTranspose hab
  have hgram : (A+B)ᴴ*(A+B) = Aᴴ*A+Bᴴ*B := by
    simp [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hab, hba]
  have horth : (Aᴴ*A)*(Bᴴ*B) = 0 := by
    calc
      (Aᴴ*A)*(Bᴴ*B) = Aᴴ*(A*Bᴴ)*B := by simp only [Matrix.mul_assoc]
      _ = 0 := by simp [hab']
  letI : CompleteSpace (Matrix S S ℂ) := FiniteDimensional.complete ℂ (Matrix S S ℂ)
  letI : NonUnitalCStarAlgebra (Matrix S S ℂ) := { }
  have ha : IsSelfAdjoint (Aᴴ*A) := (Matrix.isHermitian_conjTranspose_mul_self A).isSelfAdjoint
  have hb : IsSelfAdjoint (Bᴴ*B) := (Matrix.isHermitian_conjTranspose_mul_self B).isSelfAdjoint
  have hg := IsSelfAdjoint.norm_add_eq_max (A := Matrix S S ℂ) ha hb horth
  have hn : ‖A+B‖*‖A+B‖ = max (‖A‖*‖A‖) (‖B‖*‖B‖) := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hgram]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self] using! hg
  rcases le_total ‖A‖ ‖B‖ with hh | hh
  · rw [max_eq_right hh]
    rw [max_eq_right (mul_self_le_mul_self (norm_nonneg A) hh)] at hn
    nlinarith [norm_nonneg (A+B), norm_nonneg B]
  · rw [max_eq_left hh]
    rw [max_eq_left (mul_self_le_mul_self (norm_nonneg B) hh)] at hn
    nlinarith [norm_nonneg (A+B), norm_nonneg A]

theorem sourceMergeTwo_feasible_iff {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (Z : Fin (n+2) → Matrix R S ℂ) (M : Matrix R S ℂ)
    (h : sourceRowColumnDisjoint (Z 0) (Z 1)) :
    (∀ j, ‖sourceMergeTwo Z j ⊙ M‖ ≤ 1) ↔ (∀ j, ‖Z j ⊙ M‖ ≤ 1) := by
  have hn : ‖(Z 0+Z 1) ⊙ M‖ = max ‖Z 0 ⊙ M‖ ‖Z 1 ⊙ M‖ := by
    rw [Matrix.add_hadamard]
    exact sourceRowColumnDisjoint_norm_add _ _ (sourceRowColumnDisjoint_hadamard _ _ _ h)
  constructor
  · intro hm j
    have h01 : max ‖Z 0 ⊙ M‖ ‖Z 1 ⊙ M‖ ≤ 1 := by
      rw [← hn]
      simpa only [sourceMergeTwo, Fin.val_zero, if_pos rfl] using! hm 0
    by_cases h0 : j.val = 0
    · have hj : j = 0 := Fin.ext h0
      simpa only [hj] using! (max_le_iff.mp h01).1
    by_cases h1 : j.val = 1
    · have hj : j = 1 := Fin.ext h1
      simpa only [hj] using! (max_le_iff.mp h01).2
    let k : Fin (n+1) := ⟨j.val-1, by omega⟩
    have hk : k.val ≠ 0 := by dsimp only [k]; omega
    have he : (⟨k.val+1, by omega⟩ : Fin (n+2)) = j := by
      apply Fin.ext
      dsimp only [k]
      omega
    simpa only [sourceMergeTwo, if_neg hk, he] using! hm k
  · intro hm j
    unfold sourceMergeTwo
    split_ifs with hj
    · rw [hn]
      exact max_le (hm 0) (hm 1)
    · exact hm _

theorem sourceRectValue_mergeTwo {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin (n+2) → Matrix R S ℂ)
    (h : sourceRowColumnDisjoint (Z 0) (Z 1)) :
    sourceRectValue A (sourceMergeTwo Z) = sourceRectValue A Z := by
  apply le_antisymm
  · exact sourceRectValue_le_of_dual_feasible_imp _ _ _
      (fun M hM => (sourceMergeTwo_feasible_iff Z M h).mp hM)
  · exact sourceRectValue_le_of_dual_feasible_imp _ _ _
      (fun M hM => (sourceMergeTwo_feasible_iff Z M h).mpr hM)

theorem filteredNormClosureLaws : FilteredNormClosureLaws := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R S R' S' _ _ _ _ _ _ _ _ n A Z f g hf hg
    exact sourceRectValue_surjective_submatrix A Z f g hf hg
  · intro R S _ _ _ _ n m A Y Z
    exact ⟨sourceRectValue_filterUnion_le A Y Z, sourceRectValue_filterUnion_eq_of_masks A Y Z⟩
  · intro R S _ _ _ _ n A Z p hp
    exact sourceRectValue_convexFilter A Z p hp
  · intro R S _ _ _ _ n A Z h
    exact sourceRectValue_mergeTwo A Z h

end Qatlib.Concepts.GramQueryCore.FilteredNorm
