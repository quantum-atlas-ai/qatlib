/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

def ancillaRotation (d : ℕ) (c s : ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d)) ((-s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d))
    ((s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d)) ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d))

def controlledReflection {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ := Matrix.fromBlocks 1 0 0 (F.sigma j)

def ancillaHadamard (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • Matrix.fromBlocks (1 : Qatlib.Foundations.PureStateMath.Operator d) 1 1 (-1)

def directCircuit {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  ancillaHadamard d * controlledReflection F j * ancillaRotation d c s

def directBranch {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) (b : Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  fun i k => directCircuit F c s j (if b then Sum.inr i else Sum.inl i) (Sum.inl k)

theorem directCircuit_blocks {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) :
    directCircuit F c s j = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      Matrix.fromBlocks
        ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) + (s : ℂ) • F.sigma j)
        ((-s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) + (c : ℂ) • F.sigma j)
        ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) - (s : ℂ) • F.sigma j)
        ((-s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) - (c : ℂ) • F.sigma j) := by
  simp only [directCircuit, ancillaHadamard, controlledReflection, ancillaRotation,
    Matrix.smul_mul, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Matrix.mul_smul, Matrix.neg_mul,
    smul_neg, sub_eq_add_neg]

theorem directBranch_eq {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) (b : Bool) :
    directBranch F c s j b = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) + ((if b then -s else s : ℝ) : ℂ) • F.sigma j) := by
  unfold directBranch
  rw [directCircuit_blocks]
  cases b <;> ext i k <;> simp [Matrix.fromBlocks, Matrix.smul_apply, sub_eq_add_neg]

theorem ancillaRotation_isometry (d : ℕ) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (ancillaRotation d c s).Isometry := by
  change (ancillaRotation d c s)ᴴ * ancillaRotation d c s = 1
  simp only [ancillaRotation, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, map_neg, Complex.conj_ofReal, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul]
  ext i k
  cases i with
  | inl i =>
    cases k with
    | inl k =>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      by_cases h : i = k
      · simp only [h, if_true, mul_one]
        exact_mod_cast (show c * c + s * s = 1 by nlinarith [hcs])
      · simp [h]
    | inr k =>
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, Sum.inl_ne_inr, if_false]
      ring
  | inr i =>
    cases k with
    | inl k =>
      simp only [Matrix.fromBlocks_apply₂₁, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, Sum.inr_ne_inl, if_false]
      ring
    | inr k =>
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      by_cases h : i = k
      · simp only [h, if_true, mul_one]
        have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
        calc
          _ = (c : ℂ) ^ 2 + (s : ℂ) ^ 2 := by ring
          _ = 1 := hc
      · simp [h]

theorem controlledReflection_isometry {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    (controlledReflection F j).Isometry := by
  change (controlledReflection F j)ᴴ * controlledReflection F j = 1
  have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
  simp [controlledReflection, Matrix.fromBlocks_conjTranspose, hj,
    Matrix.fromBlocks_multiply, F.square, Matrix.fromBlocks_one]

theorem ancillaHadamard_isometry (d : ℕ) : (ancillaHadamard d).Isometry := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
    exact_mod_cast (show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 by
      field_simp
      nlinarith [hsq])
  change (ancillaHadamard d)ᴴ * ancillaHadamard d = 1
  simp only [ancillaHadamard, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_neg,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, add_neg_cancel,
    ]
  ext i k
  cases i with
  | inl i =>
    cases k with
    | inl k =>
      simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.one_apply,
        smul_eq_mul, Sum.inl.injEq]
      by_cases h : i = k
      · subst k
        convert hc using 1 <;> norm_num
      · simp [h]
    | inr k => simp
  | inr i =>
    cases k with
    | inl k => simp
    | inr k =>
      simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply,
        smul_eq_mul, Sum.inr.injEq]
      by_cases h : i = k
      · subst k
        convert hc using 1 <;> norm_num
      · simp [h]

theorem directCircuit_isometry {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ)
    (j : Fin L) (hcs : c ^ 2 + s ^ 2 = 1) : (directCircuit F c s j).Isometry := by
  have hH : (ancillaHadamard d)ᴴ * ancillaHadamard d = 1 := ancillaHadamard_isometry d
  have hC : (controlledReflection F j)ᴴ * controlledReflection F j = 1 :=
    controlledReflection_isometry F j
  have hR : (ancillaRotation d c s)ᴴ * ancillaRotation d c s = 1 :=
      ancillaRotation_isometry d c s hcs
  change (directCircuit F c s j)ᴴ * directCircuit F c s j = 1
  unfold directCircuit
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = (ancillaRotation d c s)ᴴ *
      ((controlledReflection F j)ᴴ * ((ancillaHadamard d)ᴴ * ancillaHadamard d) *
        controlledReflection F j) * ancillaRotation d c s := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hH, Matrix.mul_one, hC, Matrix.mul_one, hR]

def directCos (a : ℝ) : ℝ := (Real.sqrt (1 + a ^ 2))⁻¹

def directSin (a : ℝ) : ℝ := a * directCos a

def directScale (a : ℝ) : ℝ := (Real.sqrt 2)⁻¹ * directCos a

theorem direct_rotation_normalized (a : ℝ) : directCos a ^ 2 + directSin a ^ 2 = 1 := by
  have hp : 0 < 1 + a ^ 2 := by positivity
  have hs : Real.sqrt (1 + a ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hq : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt hp.le
  dsimp [directCos, directSin]
  field_simp
  nlinarith [hq]

theorem directScale_square (a : ℝ) : directScale a * directScale a = (2 * (1 + a ^ 2))⁻¹ := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  calc
    _ = (Real.sqrt 2 ^ 2 * Real.sqrt (1 + a ^ 2) ^ 2)⁻¹ := by
      simp only [directScale, directCos, _root_.mul_inv_rev, pow_two]
      ring
    _ = _ := by rw [h2, ha]

theorem directBranch_normalized {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ) (j : Fin L) (b : Bool) :
    directBranch F (directCos a) (directSin a) j b =
      (directScale a : ℂ) • weakOperator F a j b := by
  rw [directBranch_eq]
  cases b <;> ext i k <;>
    simp only [weakOperator, directCos, directSin, directScale, Bool.false_eq_true, reduceIte,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  all_goals push_cast; ring

theorem directBranch_matches_ideal {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (a : ℝ) (j : Fin L) (b : Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (p.prob j : ℂ) •
      (directBranch F (directCos a) (directSin a) j b * rho *
        (directBranch F (directCos a) (directSin a) j b)ᴴ) =
      (idealInstrument F p a).branch (j,b) rho := by
  rw [directBranch_normalized, idealInstrument_branch_weak]
  have hw : (weakOperator F a j b)ᴴ = weakOperator F a j b := by
    have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
    cases b <;> simp [weakOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hj]
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hw,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  have h := directScale_square a
  exact_mod_cast (show p.prob j * (directScale a * directScale a) = p.prob j / (2 * (1 + a ^ 2)) by
    rw [h, div_eq_mul_inv])

def directProbability (tau : ℝ) : ℝ :=
  (1 - Real.exp (-tau)) ^ 2 / (2 * (1 + Real.exp (-2 * tau)))

private theorem tanh_half_exp (tau : ℝ) :
    Real.tanh (tau / 2) = (1 - Real.exp (-tau)) / (1 + Real.exp (-tau)) := by
  have hp : 0 < Real.exp (tau / 2) + Real.exp (-(tau / 2)) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hq : 0 < 1 + Real.exp (-(tau / 2)) ^ 2 := by positivity
  have he : Real.exp (-tau) = Real.exp (-(tau / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hu : Real.exp (tau / 2) * Real.exp (-(tau / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have huv := congrArg (fun x : ℝ => x * Real.exp (-(tau / 2))) hu
  rw [Real.tanh_eq, he]
  field_simp
  nlinarith [huv]

theorem directSin_sq (a : ℝ) : directSin a ^ 2 = a ^ 2 / (1 + a ^ 2) := by
  have hp : 0 ≤ 1 + a ^ 2 := by positivity
  simp only [directSin, directCos, mul_pow, inv_pow, Real.sq_sqrt hp, div_eq_mul_inv]

theorem directProbability_eq (tau : ℝ) :
    directProbability tau = directSin (Real.tanh (tau / 2)) ^ 2 := by
  have he : Real.exp (-2 * tau) = Real.exp (-tau) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [directSin_sq, tanh_half_exp]
  unfold directProbability
  rw [he]
  have hp : 0 < 1 + Real.exp (-tau) := by positivity
  have hq : 0 < 1 + Real.exp (-tau) ^ 2 := by positivity
  field_simp
  ring

theorem directProbability_amplitudes (tau : ℝ) (htau : 0 ≤ tau) :
    Real.sqrt (1 - directProbability tau) = directCos (Real.tanh (tau / 2)) ∧
      Real.sqrt (directProbability tau) = directSin (Real.tanh (tau / 2)) := by
  have hc : 0 ≤ directCos (Real.tanh (tau / 2)) := by unfold directCos; positivity
  have hs : 0 ≤ directSin (Real.tanh (tau / 2)) := by
    unfold directSin
    apply mul_nonneg _ hc
    rw [tanh_half_exp]
    apply div_nonneg
    · have he : Real.exp (-tau) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_zero] at he
      linarith
    · positivity
  have hcs := direct_rotation_normalized (Real.tanh (tau / 2))
  rw [directProbability_eq]
  constructor
  · have he : 1 - directSin (Real.tanh (tau / 2)) ^ 2 = directCos (Real.tanh (tau / 2)) ^ 2 := by
      linarith
    rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  · rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

end Qatlib.Papers.ThermalDrift26.ThermalSampling
