/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan

/-!
# Basic laws of the rectangular filtered norm

This module proves the basic laws of `sourceRectValue`: definiteness, finiteness on supported
matrices, complex homogeneity, and the triangle inequality. Certificate constructions also
establish Hadamard product estimates and the effect of scaling the filters, following the
filtered γ₂ framework of [LeeEtAl2011].

## Main statements

* `sourceRectValue_zero_iff`: The rectangular filtered value vanishes exactly when its target
  matrix is zero.

* `sourceRectValue_finite_iff`: The rectangular filtered value is finite exactly when the
  filters support the target matrix.

* `sourceRectValue_smul`: Scaling the target by a complex scalar multiplies its rectangular
  filtered value by the norm of that scalar.

* `sourceRectValue_add_le`: The rectangular filtered value satisfies the triangle inequality in
  its target matrix.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- A rectangular filtered certificate with nonnegative budget `w` bounds the filtered value by
`ENNReal.ofReal w`. -/
theorem sourceRectValue_le_of_cert
    {R S : Type} {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (hw : 0 ≤ w) (h : sourceRectCert n A Z w) : sourceRectValue A Z ≤ ENNReal.ofReal w :=
  sInf_le ⟨w,hw,rfl,h⟩

/-- A transformation preserving every nonnegative certificate budget makes the target filtered
value no larger than the source value. -/
theorem sourceRectValue_le_of_cert_imp
    {R S R' S' : Type} {n m : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (B : Matrix R' S' ℂ) (Y : Fin m → Matrix R' S' ℂ)
    (h : ∀ w : ℝ, 0 ≤ w → sourceRectCert n A Z w → sourceRectCert m B Y w) :
    sourceRectValue B Y ≤ sourceRectValue A Z := by
  apply le_sInf
  rintro b ⟨w, hw, rfl, hc⟩
  exact sourceRectValue_le_of_cert hw (h w hw hc)

/-- Finite coordinate witnesses satisfying the filtered factorization identity and the row and
column budget bounds yield a rectangular filtered certificate. -/
theorem sourceRectCert_of_finiteWitness
    {R S Q : Type} [Fintype Q] {n : ℕ} {A : Matrix R S ℂ}
    {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (u : R → Fin n → Q → ℂ) (v : S → Fin n → Q → ℂ)
    (heq : ∀ r s, A r s = ∑ j, Z j r s * ∑ q, star (u r j q)*v s j q)
    (hu : ∀ r, ∑ j, ∑ q, Complex.normSq (u r j q) ≤ w)
    (hv : ∀ s, ∑ j, ∑ q, Complex.normSq (v s j q) ≤ w) : sourceRectCert n A Z w := by
  let e := (Fintype.equivFin Q).symm
  have hinner (r : R) (s : S) (j : Fin n) :
      (∑ k, star (u r j (e k))*v s j (e k)) = ∑ q, star (u r j q)*v s j q :=
    e.sum_comp (fun q => star (u r j q)*v s j q)
  have humass (r : R) (j : Fin n) :
      ‖toEuclidean_fromVec (fun k => u r j (e k))‖^2 = ∑ q, Complex.normSq (u r j q) := by
    rw [norm_toEuclidean_fromVec_sq]
    simpa only [Complex.normSq_eq_norm_sq] using! e.sum_comp (fun q => Complex.normSq (u r j q))
  have hvmass (s : S) (j : Fin n) :
      ‖toEuclidean_fromVec (fun k => v s j (e k))‖^2 = ∑ q, Complex.normSq (v s j q) := by
    rw [norm_toEuclidean_fromVec_sq]
    simpa only [Complex.normSq_eq_norm_sq] using! e.sum_comp (fun q => Complex.normSq (v s j q))
  refine ⟨Fintype.card Q, fun r j k => u r j (e k), fun s j k => v s j (e k), ?_, ?_, ?_⟩
  · intro r s; simpa only [hinner] using! heq r s
  · intro r; simpa only [humass] using! hu r
  · intro s; simpa only [hvmass] using! hv s

/-- The rectangular lift sends the zero matrix to zero. -/
theorem sourceRectLift_zero {R S : Type} : sourceRectLift (0 : Matrix R S ℂ) = 0 := by
  ext r s
  cases r <;> cases s <;> rfl

/-- The rectangular lift preserves matrix addition. -/
theorem sourceRectLift_add {R S : Type} (A B : Matrix R S ℂ) :
    sourceRectLift (A+B) = sourceRectLift A+sourceRectLift B := by
  ext r s
  cases r <;> cases s <;> simp [sourceRectLift]

/-- The rectangular filtered value of the zero matrix is zero. -/
theorem sourceRectValue_zero
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (Z : Fin n → Matrix R S ℂ) : sourceRectValue (0 : Matrix R S ℂ) Z = 0 := by
  rw [sourceRectValue_eq_lift, sourceRectLift_zero]
  exact filteredGamma2_zero_matrix _

/-- The rectangular filtered value vanishes exactly when its target matrix is zero. -/
theorem sourceRectValue_zero_iff
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue A Z = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have hc := (sourceRectValue_budget_boundary A Z 0 le_rfl).mp (by simp [hz])
    obtain ⟨m, u, v, heq, hu, _⟩ := hc
    have hu0 (r : R) (j : Fin n) (k : Fin m) : u r j k = 0 := by
      apply norm_eq_zero.mp
      have hj : ‖toEuclidean_fromVec (u r j)‖^2 ≤ 0 :=
        (Finset.single_le_sum (fun j' _ => sq_nonneg ‖toEuclidean_fromVec (u r j')‖)
          (Finset.mem_univ j)).trans (hu r)
      have hk : ‖u r j k‖^2 ≤ ‖toEuclidean_fromVec (u r j)‖^2 := by
        rw [norm_toEuclidean_fromVec_sq]
        exact Finset.single_le_sum (fun k' _ => sq_nonneg ‖u r j k'‖) (Finset.mem_univ k)
      nlinarith [norm_nonneg (u r j k)]
    ext r s
    rw [heq]
    simp [hu0]
  · rintro rfl
    exact sourceRectValue_zero Z

/-- The rectangular filtered value is finite exactly when the filters support the target matrix. -/
theorem sourceRectValue_finite_iff
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue A Z < ⊤ ↔ sourceSupports A Z := by
  constructor
  · intro hf r s hA
    have hs := gamma2_finite_support (sourceRectLift A) (fun j => sourceRectLift (Z j))
      (by rwa [← sourceRectValue_eq_lift])
    by_contra! hn
    apply hA
    simpa only [sourceRectLift] using! hs (.inl r) (.inr s) (by intro j; exact hn j)
  · intro hs
    rw [sourceRectValue_eq_lift]
    apply gamma2_support_finite
    intro r s hz
    cases r with
    | inl r =>
      cases s with
      | inl s => rfl
      | inr s =>
        by_contra hA
        obtain ⟨j, hj⟩ := hs r s hA
        exact hj (hz j)
    | inr r => cases s <;> rfl

/-- The rectangular filtered value is infinite exactly when the filters fail to support the
target matrix. -/
theorem sourceRectValue_top_iff
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue A Z = ⊤ ↔ ¬sourceSupports A Z := by
  rw [← sourceRectValue_finite_iff, not_lt, top_le_iff]

/-- The unfiltered value of a finite rectangular matrix is finite. -/
theorem sourceUnfiltered_finite
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (A : Matrix R S ℂ) : sourceUnfiltered A < ⊤ := by
  apply (sourceRectValue_finite_iff _ _).mpr
  intro r s _
  exact ⟨0, by norm_num⟩

/-- Scalar multiplication in the first factor commutes with the entrywise matrix product. -/
theorem sourceRect_smul_hadamard {R S : Type} (c : ℂ) (A M : Matrix R S ℂ) :
    (c • A) ⊙ M = c • (A ⊙ M) := by
  ext r s
  simp [Matrix.hadamard_apply, mul_assoc]

/-- Scaling the target by a complex scalar multiplies its rectangular filtered value by the norm
of that scalar. -/
theorem sourceRectValue_smul
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (c : ℂ) :
    sourceRectValue (c • A) Z = ENNReal.ofReal ‖c‖*sourceRectValue A Z := by
  rw [(rectangularSchurDuality R S n (c • A) Z).1, (rectangularSchurDuality R S n A Z).1]
  unfold sourceRectDual
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro M
  rw [sourceRect_smul_hadamard, norm_smul, ENNReal.ofReal_mul (norm_nonneg c)]

/-- A nonzero matrix has rectangular filtered value one when used as its own single filter. -/
theorem sourceRectValue_selfFilter
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (A : Matrix R S ℂ) (hA : A ≠ 0) : sourceRectValue A (fun _ : Fin 1 => A) = 1 := by
  apply le_antisymm
  · rw [← ENNReal.ofReal_one]
    apply (sourceRectValue_budget_boundary A (fun _ : Fin 1 => A) 1 (by norm_num)).mpr
    refine ⟨1, fun _ _ _ => 1, fun _ _ _ => 1, ?_, ?_, ?_⟩ <;> simp [norm_toEuclidean_fromVec_sq]
  · have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
    let M : Matrix R S ℂ := fun _ _ => ((‖A‖⁻¹ : ℝ) : ℂ)
    have hproduct : A ⊙ M = (((‖A‖⁻¹ : ℝ) : ℂ) • A) := by
      ext r s
      simp only [Matrix.hadamard_apply, M, Matrix.smul_apply, smul_eq_mul]
      ring
    have hnorm : ‖A ⊙ M‖ = 1 := by
      rw [hproduct, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
        inv_mul_cancel₀ hn.ne']
    have hM : ∀ j : Fin 1, ‖A ⊙ M‖ ≤ 1 := by intro _; rw [hnorm]
    rw [(rectangularSchurDuality R S 1 A (fun _ : Fin 1 => A)).1]
    unfold sourceRectDual
    apply le_iSup_of_le ⟨M,hM⟩
    rw [hnorm, ENNReal.ofReal_one]

/-- Scaling every filter by a nonzero complex scalar is equivalent to scaling the target by the
inverse scalar at the same certificate budget. -/
theorem sourceRectCert_smul_filters_iff
    {R S : Type} {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (c : ℂ) (hc : c ≠ 0) (w : ℝ) :
    sourceRectCert n A (fun j => c • Z j) w ↔ sourceRectCert n (c⁻¹ • A) Z w := by
  constructor
  · rintro ⟨m, u, v, heq, hu, hv⟩
    refine ⟨m, u, v, ?_, hu, hv⟩
    intro r s
    have h := congrArg (fun a : ℂ => c⁻¹*a) (heq r s)
    simpa [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc, hc] using! h
  · rintro ⟨m, u, v, heq, hu, hv⟩
    refine ⟨m, u, v, ?_, hu, hv⟩
    intro r s
    have h := congrArg (fun a : ℂ => c*a) (heq r s)
    simpa [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc, hc] using! h

/-- Scaling all filters by a nonzero complex scalar divides the rectangular filtered value by
the scalar norm. -/
theorem sourceRectValue_smul_filters
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (c : ℂ) (hc : c ≠ 0) :
    sourceRectValue A (fun j => c • Z j) =
      (ENNReal.ofReal ‖c‖)⁻¹*sourceRectValue A Z := by
  have hvalues : sourceRectValue A (fun j => c • Z j) = sourceRectValue (c⁻¹ • A) Z := by
    apply le_antisymm
    · exact sourceRectValue_le_of_cert_imp (c⁻¹ • A) Z A (fun j => c • Z j)
        (fun w _ => (sourceRectCert_smul_filters_iff A Z c hc w).mpr)
    · exact sourceRectValue_le_of_cert_imp A (fun j => c • Z j) (c⁻¹ • A) Z
        (fun w _ => (sourceRectCert_smul_filters_iff A Z c hc w).mp)
  rw [hvalues, sourceRectValue_smul, norm_inv, ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hc)]

/-- Two rectangular certificates with nonnegative budgets combine into a certificate for the sum
with the sum of the budgets. -/
theorem sourceRectCert_add
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} {A B : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w w' : ℝ}
    (hw : 0 ≤ w) (hw' : 0 ≤ w') (hA : sourceRectCert n A Z w) (hB : sourceRectCert n B Z w') :
    sourceRectCert n (A+B) Z (w+w') := by
  apply sourceRectCert_of_lift
  simpa only [sourceRectLift_add] using!
    gramFilteredCert_add (liftCert_of_sourceRectCert hw hA) (liftCert_of_sourceRectCert hw' hB)

/-- The rectangular filtered value satisfies the triangle inequality in its target matrix. -/
theorem sourceRectValue_add_le
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue (A+B) Z ≤ sourceRectValue A Z+sourceRectValue B Z := by
  by_cases hA : sourceRectValue A Z = ⊤
  · simp [hA]
  by_cases hB : sourceRectValue B Z = ⊤
  · simp [hB]
  let w := (sourceRectValue A Z).toReal
  let w' := (sourceRectValue B Z).toReal
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hw' : 0 ≤ w' := ENNReal.toReal_nonneg
  have heA : ENNReal.ofReal w = sourceRectValue A Z := ENNReal.ofReal_toReal hA
  have heB : ENNReal.ofReal w' = sourceRectValue B Z := ENNReal.ofReal_toReal hB
  have hcA := (sourceRectValue_budget_boundary A Z w hw).mp heA.ge
  have hcB := (sourceRectValue_budget_boundary B Z w' hw').mp heB.ge
  calc
    sourceRectValue (A+B) Z ≤ ENNReal.ofReal (w+w') :=
      sourceRectValue_le_of_cert (add_nonneg hw hw') (sourceRectCert_add hw hw' hcA hcB)
    _ = sourceRectValue A Z+sourceRectValue B Z := by rw [ENNReal.ofReal_add hw hw', heA, heB]

/-- Entrywise multiplying both the target and all filters by the same matrix preserves a
rectangular certificate. -/
theorem sourceRectCert_hadamard_filters
    {R S : Type} {n : ℕ} {A B : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (h : sourceRectCert n A Z w) : sourceRectCert n (A ⊙ B) (fun j => Z j ⊙ B) w := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  refine ⟨m, u, v, ?_, hu, hv⟩
  intro r s
  simp only [Matrix.hadamard_apply]
  rw [heq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entrywise multiplying the target and all filters by the same matrix cannot increase the
rectangular filtered value. -/
theorem sourceRectValue_hadamard_filters_le
    {R S : Type} {n : ℕ} (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue (A ⊙ B) (fun j => Z j ⊙ B) ≤ sourceRectValue A Z :=
  sourceRectValue_le_of_cert_imp A Z (A ⊙ B) (fun j => Z j ⊙ B)
    (fun _ _ => sourceRectCert_hadamard_filters)

/-- An unfiltered rectangular certificate lifts to a Gram filtered certificate with the same
nonnegative budget. -/
theorem sourceUnfiltered_liftCert
    {R S : Type} {B : Matrix R S ℂ} {w : ℝ} (hw : 0 ≤ w)
    (h : sourceRectCert 1 B (fun _ : Fin 1 => fun _ _ => 1) w) :
    gramFilteredCert (sourceRectLift B) (fun _ : Fin 1 => gramFilterAllOnes) w := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  let u' : Fin 1 → (R ⊕ S) → Fin m → ℂ := fun j z => Sum.elim (fun r => u r j) (fun _ => 0) z
  let v' : Fin 1 → (R ⊕ S) → Fin m → ℂ := fun j z => Sum.elim (fun _ => 0) (fun s => v s j) z
  refine ⟨Fin m, inferInstance, u', v', ?_, ?_, ?_⟩
  · intro z
    cases z with
    | inl r => simpa only [u', Sum.elim_inl, Complex.normSq_eq_norm_sq,
        ← norm_toEuclidean_fromVec_sq] using! hu r
    | inr s => simpa [u'] using! hw
  · intro z
    cases z with
    | inl r => simpa [v'] using! hw
    | inr s => simpa only [v', Sum.elim_inr, Complex.normSq_eq_norm_sq,
        ← norm_toEuclidean_fromVec_sq] using! hv s
  · intro r s
    cases r <;> cases s <;>
      simp only [sourceRectLift, gramFilterAllOnes, u', v', Sum.elim_inl, Sum.elim_inr,
        dotProduct, Pi.star_apply] <;> simp [heq]

/-- An unfiltered certificate for `B` removes the common entrywise factor `B` from the filters
at the cost of multiplying the nonnegative certificate budgets. -/
theorem sourceRectCert_hadamard_reverse
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} {A B : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w w' : ℝ}
    (hw : 0 ≤ w) (hw' : 0 ≤ w')
    (hA : sourceRectCert n A (fun j => Z j ⊙ B) w)
    (hB : sourceRectCert 1 B (fun _ : Fin 1 => fun _ _ => 1) w') :
    sourceRectCert n A Z (w*w') := by
  have hALift : gramFilteredCert (sourceRectLift A)
      (fun j r s => sourceRectLift (Z j) r s*sourceRectLift B r s) w := by
    simpa only [← sourceRectLift_hadamard, Matrix.hadamard_apply] using!
        liftCert_of_sourceRectCert hw hA
  exact sourceRectCert_of_lift
      (gramFilteredCert_hadamard_le hALift (sourceUnfiltered_liftCert hw' hB))

/-- The filtered value is bounded by the value with filters multiplied entrywise by `B` times
the unfiltered value of `B`, provided the former value is finite or `B` is nonzero. -/
theorem sourceRectValue_hadamard_reverse_le
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (hguard : sourceRectValue A (fun j => Z j ⊙ B) < ⊤ ∨ B ≠ 0) :
    sourceRectValue A Z ≤ sourceRectValue A (fun j => Z j ⊙ B)*sourceUnfiltered B := by
  by_cases hA : sourceRectValue A (fun j => Z j ⊙ B) = ⊤
  · have hB : B ≠ 0 := hguard.resolve_left (by rw [hA]; exact lt_irrefl _)
    have hBzero : sourceUnfiltered B ≠ 0 := by
      intro hz
      exact hB ((sourceRectValue_zero_iff B (fun _ : Fin 1 => fun _ _ => 1)).mp hz)
    rw [hA, ENNReal.top_mul hBzero]
    exact le_top
  · let w := (sourceRectValue A (fun j => Z j ⊙ B)).toReal
    let w' := (sourceUnfiltered B).toReal
    have hw : 0 ≤ w := ENNReal.toReal_nonneg
    have hw' : 0 ≤ w' := ENNReal.toReal_nonneg
    have heA : ENNReal.ofReal w = sourceRectValue A (fun j => Z j ⊙ B) := ENNReal.ofReal_toReal hA
    have heB : ENNReal.ofReal w' = sourceUnfiltered B :=
      ENNReal.ofReal_toReal (sourceUnfiltered_finite B).ne
    have hcA := (sourceRectValue_budget_boundary A (fun j => Z j ⊙ B) w hw).mp heA.ge
    have hcB := (sourceRectValue_budget_boundary B (fun _ : Fin 1 => fun _ _ => 1) w' hw').mp heB.ge
    calc
      sourceRectValue A Z ≤ ENNReal.ofReal (w*w') :=
        sourceRectValue_le_of_cert (mul_nonneg hw hw') (sourceRectCert_hadamard_reverse hw hw' hcA hcB)
      _ = _ := by rw [ENNReal.ofReal_mul hw, heA, heB]

/-- The rectangular filtered value of an entrywise product is bounded by the filtered value of
the first factor times the unfiltered value of the second. -/
theorem sourceRectValue_hadamard_le
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue (A ⊙ B) Z ≤ sourceRectValue A Z*sourceUnfiltered B := by
  by_cases hB : B = 0
  · subst B
    simp [sourceUnfiltered, sourceRectValue_zero]
  · exact (sourceRectValue_hadamard_reverse_le (A ⊙ B) B Z (Or.inr hB)).trans
      (mul_le_mul_left (sourceRectValue_hadamard_filters_le A B Z) (sourceUnfiltered B))

/-- The rectangular filtered value satisfies the bundled basic norm and Hadamard product laws
[LeeEtAl2011]. -/
theorem filteredNormBasicLaws : FilteredNormBasicLaws := by
  intro R S _ _ _ _ n A B Z
  exact ⟨sourceRectValue_selfFilter A, sourceRectValue_zero_iff A Z,
    sourceRectValue_top_iff A Z, sourceRectValue_smul A Z, sourceRectValue_smul_filters A Z,
    sourceRectValue_add_le A B Z, sourceRectValue_hadamard_le A B Z,
    sourceRectValue_hadamard_filters_le A B Z, sourceRectValue_hadamard_reverse_le A B Z⟩

end Qatlib.Concepts.GramQueryCore.FilteredNorm
