/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.GeneralPOVM
import Mathlib.Tactic.LinearCombination

/-!
# Binary Projectors

Qubit Measure constructions for Copy Decision.
Defines `QubitMatrix`, `trinePureMatrix`, `binaryCenter`.
Proves `trinePureMatrix_hermitian`, `trinePureMatrix_explicit`, `binaryDisc_pos`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError
open Matrix
open scoped ComplexOrder

/-- Abbreviation for Qubit Matrix in the Qubit Measure construction. -/
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Definition of trine Pure Matrix in the Qubit Measure construction. -/
def trinePureMatrix (i : Fin 3) : QubitMatrix :=
  fun r c => trineState i r*star (trineState i c)

/-- The stated copy-decision construction satisfies `trinePureMatrix_hermitian` with the complete displayed premises. -/
lemma trinePureMatrix_hermitian (i : Fin 3) : (trinePureMatrix i).IsHermitian := by
  ext r c
  simp only [trinePureMatrix, Matrix.conjTranspose_apply, star_mul, star_star]

/-- The stated copy-decision construction satisfies `trinePureMatrix_explicit` with the complete displayed premises. -/
lemma trinePureMatrix_explicit (i : Fin 3) :
    trinePureMatrix i = if i=0 then !![1,0;0,0] else if i=1 then
      !![1/4,-(Real.sqrt 3:ℂ)/4;-(Real.sqrt 3:ℂ)/4,3/4] else
      !![1/4,(Real.sqrt 3:ℂ)/4;(Real.sqrt 3:ℂ)/4,3/4] := by
  have h3 : (Real.sqrt (3:ℝ) : ℂ)^2=3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    norm_num [trinePureMatrix, trineState, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring_nf
  all_goals norm_num [h3]

/-- Twice the actual weighted state difference with its scalar trace removed. -/
def binaryCenter (i j : Fin 3) (p q : ℝ) : QubitMatrix :=
  (2:ℂ) • ((p:ℂ) • trinePureMatrix i-(q:ℂ) • trinePureMatrix j)-((p-q:ℝ):ℂ) • 1

/-- Definition of binary Disc in the Qubit Measure construction. -/
def binaryDisc (p q : ℝ) : ℝ := Real.sqrt ((p+q)^2-p*q)

/-- The stated copy-decision construction satisfies `binaryDisc_pos` with the complete displayed premises. -/
lemma binaryDisc_pos {p q : ℝ} (hQ : 0 < p+q) :
    0 < binaryDisc p q := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg (p-q), sq_pos_of_pos hQ]

/-- The stated copy-decision construction satisfies `binaryDisc_sq` with the complete displayed premises. -/
lemma binaryDisc_sq (p q : ℝ) :
    (binaryDisc p q)^2=(p+q)^2-p*q := by
  apply Real.sq_sqrt
  nlinarith [sq_nonneg (p+q), sq_nonneg (p-q)]

/-- The stated copy-decision construction satisfies `binaryCenter_hermitian` with the complete displayed premises. -/
lemma binaryCenter_hermitian (i j : Fin 3) (p q : ℝ) : (binaryCenter i j p q).IsHermitian := by
  change (binaryCenter i j p q).conjTranspose= _
  simp [binaryCenter, Matrix.conjTranspose_smul, (trinePureMatrix_hermitian i).eq,
    (trinePureMatrix_hermitian j).eq]

/-- This uses the SAME explicit normalized trine input vectors. -/
lemma binaryCenter_square (i j : Fin 3) (hij : i≠j) (p q : ℝ) :
    binaryCenter i j p q*binaryCenter i j p q=(((p+q)^2-p*q:ℝ):ℂ) • (1:QubitMatrix) := by
  have h3 : (Real.sqrt (3:ℝ) : ℂ)^2=3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ext r c
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases r <;> fin_cases c <;>
    norm_num [binaryCenter, trinePureMatrix_explicit, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  all_goals ring_nf
  all_goals norm_num [h3]
  all_goals ring

/-- Definition of half Projection in the Qubit Measure construction. -/
def halfProjection (B : QubitMatrix) (d : ℝ) : QubitMatrix :=
  (1/2:ℂ) • (1+(d:ℂ)⁻¹ • B)

/-- The stated copy-decision construction satisfies `halfProjection_hermitian` with the complete displayed premises. -/
lemma halfProjection_hermitian (B : QubitMatrix) (hB : B.IsHermitian) (d : ℝ) :
    (halfProjection B d).IsHermitian := by
  change (halfProjection B d).conjTranspose= _
  simp [halfProjection, Matrix.conjTranspose_smul, hB.eq]

/-- The stated copy-decision construction satisfies `halfProjection_idempotent` with the complete displayed premises. -/
lemma halfProjection_idempotent (B : QubitMatrix) (d : ℝ) (hd : d≠0)
    (hB : B*B=(d:ℂ)^2 • (1:QubitMatrix)) :
    halfProjection B d*halfProjection B d=halfProjection B d := by
  have hdc : (d:ℂ)≠0 := by exact_mod_cast hd
  ext r c
  have hb := congrArg (fun A : QubitMatrix => A r c) hB
  fin_cases r <;> fin_cases c <;>
    norm_num [halfProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.one_apply] at hb ⊢
  all_goals field_simp [hdc]
  all_goals linear_combination hb

/-- Definition of binary Plus Matrix in the Qubit Measure construction. -/
def binaryPlusMatrix (i j : Fin 3) (p q : ℝ) : QubitMatrix :=
  halfProjection (binaryCenter i j p q) (binaryDisc p q)

/-- The stated copy-decision construction satisfies `binaryPlus_hermitian` with the complete displayed premises. -/
lemma binaryPlus_hermitian (i j : Fin 3) (p q : ℝ) :
    (binaryPlusMatrix i j p q).IsHermitian :=
  halfProjection_hermitian _ (binaryCenter_hermitian i j p q) _

/-- The stated copy-decision construction satisfies `binaryPlus_idempotent` with the complete displayed premises. -/
lemma binaryPlus_idempotent (i j : Fin 3) (hij : i≠j) {p q : ℝ}
    (hQ : 0 < p+q) :
    binaryPlusMatrix i j p q*binaryPlusMatrix i j p q=binaryPlusMatrix i j p q := by
  apply halfProjection_idempotent _ _ (ne_of_gt (binaryDisc_pos hQ))
  rw [binaryCenter_square i j hij]
  rw [← binaryDisc_sq p q]
  norm_cast

/-- Definition of binary Plus Effect in the Qubit Measure construction. -/
def binaryPlusEffect (i j : Fin 3) (p q : ℝ) : HermitianMat (Fin 2) ℂ :=
  ⟨binaryPlusMatrix i j p q, binaryPlus_hermitian i j p q⟩

/-- Actual complete binary POVM, with no p!=q or strictly positive-prior premise. -/
def binaryPOVM (i j : Fin 3) (hij : i≠j) (p q : ℝ)
    (hQ : 0 < p+q) : POVM (Fin 2) (Fin 2) where
  mats a := if a=0 then binaryPlusEffect i j p q else 1-binaryPlusEffect i j p q
  nonneg := by
    intro a
    have hP := binaryPlus_idempotent i j hij hQ
    have hH := (binaryPlus_hermitian i j p q).eq
    by_cases ha : a=0
    · simp only [ha, if_pos]
      apply HermitianMat.zero_le_iff.2
      change (binaryPlusMatrix i j p q).PosSemidef
      have h := Matrix.posSemidef_conjTranspose_mul_self (binaryPlusMatrix i j p q)
      rwa [hH, hP] at h
    · simp only [ha, if_false]
      apply HermitianMat.zero_le_iff.2
      change ((1:QubitMatrix)-binaryPlusMatrix i j p q).PosSemidef
      have hm : ((1:QubitMatrix)-binaryPlusMatrix i j p q)*
          (1-binaryPlusMatrix i j p q)=1-binaryPlusMatrix i j p q := by
        simp only [mul_sub, sub_mul, one_mul, mul_one, hP, sub_self, sub_zero]
      have h := Matrix.posSemidef_conjTranspose_mul_self ((1:QubitMatrix)-binaryPlusMatrix i j p q)
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, hm] at h
      exact h
  normalized := by simp [Fin.sum_univ_two]

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
