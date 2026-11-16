/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Qatlib.Papers.SteadyState20.MainResults.LiouvillianGap.LiouvillianGap

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Hermitian restriction of the Liouvillian block-gap claim

Fixed source: Ramusat--Savona, arXiv:2008.07133v2, Section 2, p.3,
Eq. (3) and its following paragraph. The PDF was read on pp.1--4;
SHA256: 73ac91d7516a221f62fcf4f879745924556c8a6f1d8cbd74b6ce2dc8b09fa263.

The block identities and all twelve original positive declarations are retained.
The source identifies squared block eigenvalues with squared eigenvalue moduli
of the Liouvillian. That identification, and consequently the unconditional
gap comparison, fails for general non-normal matrices. This premise repair
restricts the gap comparison to Hermitian matrices. Hermiticity is an explicit
additional assumption, not a claim that every physical Liouvillian satisfies it.

For a Hermitian matrix, block eigenvectors yield an eigenvector of the original
matrix with eigenvalue either `φ` or `-φ`; the elementary proof below does not
assume the desired gap comparison. The identity-matrix example verifies that
the repaired assumptions are satisfiable. The abstract matrix `[[2,3],[0,2]]` has gap
`2` but block eigenvalue `1`, verifying the necessity of a restriction.
These examples concern abstract matrices, not physical GKSL generators.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.LiouvillianGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restricted correction of the gap comparison following Eq. (3) on p.3 of
arXiv:2008.07133v2: a Hermitian matrix's eigenvalue gap lower-bounds each nonzero
block eigenvalue modulus. Hermiticity is additional to the source statement. -/
theorem liouvillian_gap_le_singularValue (L : Matrix ι ι ℂ) {g : ℝ}
    (hHerm : Lᴴ = L) (hgap : IsLiouvillianGap L g) {φ : ℂ}
    (hφ : HasEigenvector (blockOp L) φ) (hφ0 : φ ≠ 0) :
    g ≤ ‖φ‖ := by
  obtain ⟨v, hv, heig⟩ := hφ
  let a : ι → ℂ := fun i => v (Sum.inl i)
  let b : ι → ℂ := fun i => v (Sum.inr i)
  have hpair : vecPair a b = v := by
    funext i
    cases i <;> rfl
  have heig' : (blockOp L) *ᵥ vecPair a b = φ • vecPair a b := by
    simpa only [hpair] using heig
  obtain ⟨hLb, hLa⟩ := blockOp_eigen_relations L heig'
  rw [hHerm] at hLa
  apply liouvillian_gap_le_abs_of_normalSpectrum L hgap hφ0
  by_cases hab : a + b = 0
  · have hb : b ≠ 0 := (blockOp_eigen_sq_relation L hφ0
        (by simpa only [hpair] using hv) heig').1
    have ha : a = -b := eq_neg_of_add_eq_zero_left hab
    have hneg : -φ ≠ 0 := by
      intro h
      exact hφ0 (neg_eq_zero.mp h)
    have hEigNeg : HasEigenvector L (-φ) := by
      refine ⟨b, hb, ?_⟩
      simpa only [ha, smul_neg, neg_smul] using hLb
    refine ⟨(-φ : ℂ), hEigNeg, ?_, ?_⟩
    · exact hneg
    · simp
  · have hEig : HasEigenvector L φ := by
      refine ⟨a + b, hab, ?_⟩
      rw [Matrix.mulVec_add, hLa, hLb, smul_add, add_comm]
    exact ⟨φ, hEig, hφ0, rfl⟩


/-- The abstract identity matrix has gap one, and its block operator has eigenvalue one:
the premises of the restricted comparison hold on a concrete nonzero matrix. -/
theorem hermitian_gap_example :
    let L : Matrix Unit Unit ℂ := 1
    Lᴴ = L ∧ IsLiouvillianGap L 1 ∧ HasEigenvector (blockOp L) 1 := by
  dsimp
  refine ⟨by simp, ⟨?_, ?_⟩, ?_⟩
  · intro μ hμ hμ0
    obtain ⟨v, hv, heig⟩ := hμ
    have hv0 : v () ≠ 0 := by
      intro hz
      apply hv
      funext i
      cases i
      exact hz
    have he : μ = 1 := by
      have h := congrFun heig ()
      simp only [Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at h
      exact (mul_eq_right₀ hv0).mp h.symm
    simp [he]
  · refine ⟨1, ⟨fun _ => 1, ?_, ?_⟩, by norm_num, by norm_num⟩
    · intro h
      have := congrFun h ()
      norm_num at this
    · simp
  · refine ⟨vecPair (fun _ => 1) (fun _ => 1), ?_, ?_⟩
    · intro h
      have := congrFun h (Sum.inl ())
      norm_num [vecPair] at this
    · apply blockOp_eigen_of_relations <;> simp

/-- A concrete abstract non-normal matrix has eigenvalue gap two and a block eigenvalue
one, so the unconditional gap comparison would give the false inequality
`2 ≤ 1`. All hypotheses of the unrepaired comparison are exhibited. -/
theorem nonnormal_gap_example :
    let L : Matrix (Fin 2) (Fin 2) ℂ := !![2, 3; 0, 2]
    IsLiouvillianGap L 2 ∧ HasEigenvector (blockOp L) 1 ∧ ¬ (2 : ℝ) ≤ ‖(1 : ℂ)‖ := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ?_, by norm_num [Complex.norm_def]⟩
  · intro μ hμ hμ0
    obtain ⟨v, hv, heig⟩ := hμ
    have h0 := congrFun heig 0
    have h1 := congrFun heig 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have he : μ = 2 := by
      by_cases hv1 : v 1 = 0
      · have hv0 : v 0 ≠ 0 := by
          intro hz
          apply hv
          funext i
          fin_cases i <;> simp [hz, hv1]
        rw [hv1] at h0
        simp only [mul_zero, add_zero] at h0
        exact (mul_right_cancel₀ hv0 h0).symm
      · exact (h1.resolve_right hv1).symm
    norm_num [he]
  · refine ⟨2, ⟨![1, 0], ?_, ?_⟩, by norm_num, by norm_num⟩
    · intro h
      have := congrFun h 0
      norm_num at this
    · ext i
      fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨vecPair ![-1, 2] ![-2, 1], ?_, ?_⟩
    · intro h
      have := congrFun h (Sum.inl 0)
      norm_num [vecPair] at this
    · apply blockOp_eigen_of_relations
      · ext i
        fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · ext i
        fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Matrix.conjTranspose_apply, map_ofNat]

end Qatlib.Papers.SteadyState20.MainResults.LiouvillianGap
