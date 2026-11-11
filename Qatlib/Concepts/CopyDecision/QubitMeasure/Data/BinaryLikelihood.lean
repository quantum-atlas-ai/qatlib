/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.BinaryProjectors

/-!
# Binary Likelihood

Qubit Measure constructions for Copy Decision.
Proves `trinePureMatrix_action`, `trinePureMatrix_quadratic`, `binaryPlus_quadratic_left`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError
open Matrix

/-- The stated copy-decision construction satisfies `trinePureMatrix_action` with the complete displayed premises. -/
lemma trinePureMatrix_action (i : Fin 3) (x : Qubit) :
    (trinePureMatrix i).toEuclideanLin x=(inner ℂ (trineState i) x) • trineState i := by
  ext r
  change (∑ c, trineState i r*star (trineState i c)*x c)=
    (∑ c, x c*star (trineState i c))*trineState i r
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The stated copy-decision construction satisfies `trinePureMatrix_quadratic` with the complete displayed premises. -/
lemma trinePureMatrix_quadratic (i j : Fin 3) :
    inner ℂ (trineState j) ((trinePureMatrix i).toEuclideanLin (trineState j))=
      if i=j then 1 else (1/4:ℂ) := by
  rw [trinePureMatrix_action, inner_smul_right]
  by_cases hij : i=j
  · subst j
    norm_num [trineState_gram, trineState_unit]
  · norm_num [trineState_gram, hij, Ne.symm hij]

/-- The stated copy-decision construction satisfies `binaryPlus_quadratic_left` with the complete displayed premises. -/
lemma binaryPlus_quadratic_left (i j : Fin 3) (hij : i≠j) (p q : ℝ)
    (hd : binaryDisc p q≠0) :
    inner ℂ (trineState i) ((binaryPlusMatrix i j p q).toEuclideanLin (trineState i))=
      (((p+q+binaryDisc p q-q/2)/(2*binaryDisc p q):ℝ):ℂ) := by
  have hdc : (binaryDisc p q:ℂ)≠0 := by exact_mod_cast hd
  simp only [binaryPlusMatrix, halfProjection, binaryCenter, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right, Matrix.toLpLin_one, LinearMap.id_apply,
    trinePureMatrix_quadratic, trineState_gram,
    if_neg (Ne.symm hij)]
  push_cast
  field_simp [hdc]
  ring

/-- The stated copy-decision construction satisfies `binaryPlus_quadratic_right` with the complete displayed premises. -/
lemma binaryPlus_quadratic_right (i j : Fin 3) (hij : i≠j) (p q : ℝ)
    (hd : binaryDisc p q≠0) :
    inner ℂ (trineState j) ((binaryPlusMatrix i j p q).toEuclideanLin (trineState j))=
      (((-(p+q)+binaryDisc p q+p/2)/(2*binaryDisc p q):ℝ):ℂ) := by
  have hdc : (binaryDisc p q:ℂ)≠0 := by exact_mod_cast hd
  simp only [binaryPlusMatrix, halfProjection, binaryCenter, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right, Matrix.toLpLin_one, LinearMap.id_apply,
    trinePureMatrix_quadratic, trineState_gram, if_neg hij]
  push_cast
  field_simp [hdc]
  ring

/-- Actual first-outcome Born likelihoods of the physically complete projector
measurement, for both possible remaining labels. -/
theorem binaryPOVM_born_plus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    qubitBorn ((binaryPOVM i j hij p q hQ).mats 0) (trineState i)=
      (p+q+binaryDisc p q-q/2)/(2*binaryDisc p q) ∧
    qubitBorn ((binaryPOVM i j hij p q hQ).mats 0) (trineState j)=
      (-(p+q)+binaryDisc p q+p/2)/(2*binaryDisc p q) := by
  constructor
  · exact congrArg Complex.re (binaryPlus_quadratic_left i j hij p q (ne_of_gt (binaryDisc_pos hQ)))
  · exact congrArg Complex.re (binaryPlus_quadratic_right i j hij p q (ne_of_gt (binaryDisc_pos hQ)))

/-- The stated copy-decision construction satisfies `binaryPOVM_born_minus` with the complete displayed premises. -/
lemma binaryPOVM_born_minus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (k : Fin 3) :
    qubitBorn ((binaryPOVM i j hij p q hQ).mats 1) (trineState k)=
      1-qubitBorn ((binaryPOVM i j hij p q hQ).mats 0) (trineState k) := by
  norm_num [binaryPOVM, qubitBorn, HermitianMat.mat_sub, inner_sub_right,
    trineState_gram, trineState_unit]

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
