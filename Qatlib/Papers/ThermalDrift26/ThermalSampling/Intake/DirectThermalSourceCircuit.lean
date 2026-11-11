/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential

/-!
# Direct Thermal Source Circuit

This module gives the block-matrix implementation of the direct weak-measurement source
associated with thermal-drift sampling [JiangEtAl2026]. `directCircuit` composes
`ancillaRotation`, `controlledReflection`, and `ancillaHadamard`; `directBranch` extracts the
live-register map for each Boolean ancilla outcome, and the component isometry lemmas verify the
normalized circuit.

`directCos`, `directSin`, and `directScale` select normalized amplitudes for a weak-operator
parameter. The exact branch identity connects the circuit to `idealInstrument`, while
`directProbability` and its amplitude identities express the thermal preparation using `tanh
(tau / 2)`.

## Main statements

* `directCircuit_blocks` and `directBranch_eq` compute the full circuit blocks and its two
  outcome branches.
- `directCircuit_isometry` proves the circuit is an isometry when `c^2 + s^2 = 1`.
* `directBranch_normalized` and `directBranch_matches_ideal` identify normalized circuit
  branches with the weak operators and the ideal instrument.
* `directProbability_eq` and `directProbability_amplitudes` relate the exponential preparation
  probability to the normalized thermal amplitudes.

## References

* [Jiang et al., 2026][JiangEtAl2026]: Jiyu Jiang, Mingrui Jing, Jizhe Lai, Xin Wang, and Lei
  Zhang. *Thermal-Drift Sampling: Generating Thermal Ensembles for Learning Many-Body Systems*.
  2026.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

/-- The ancilla rotation tensored with the live identity, represented by blocks `[[c I, -s I],
[s I, c I]]` on the two live-register summands. -/
def ancillaRotation (d : ℕ) (c s : ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d)) ((-s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d))
    ((s : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d)) ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d))

/-- The block diagonal matrix that acts as the identity on the first ancilla summand and as
reflection `F.sigma j` on the second. -/
def controlledReflection {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ := Matrix.fromBlocks 1 0 0 (F.sigma j)

/-- The ancilla Hadamard tensored with the live identity, with blocks `[[I, I], [I, -I]]` scaled
by the reciprocal of the square root of two. -/
def ancillaHadamard (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • Matrix.fromBlocks (1 : Qatlib.Foundations.PureStateMath.Operator d) 1 1 (-1)

/-- The joint ancilla-live circuit matrix obtained by applying the ancilla rotation, the
controlled reflection at index `j`, and then the ancilla Hadamard. -/
def directCircuit {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  ancillaHadamard d * controlledReflection F j * ancillaRotation d c s

/-- The live-register branch matrix obtained from the first ancilla input block and the output
ancilla block selected by Boolean outcome `b`. -/
def directBranch {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) (b : Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  fun i k => directCircuit F c s j (if b then Sum.inr i else Sum.inl i) (Sum.inl k)

/-- Expands the direct circuit into its four blocks, each scaled by the reciprocal of the square
root of two: `c I + s sigma`, `-s I + c sigma`, `c I - s sigma`, and `-s I - c sigma`. -/
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

/-- The direct branch is `(c I + s sigma) / sqrt 2` for false and `(c I - s sigma) / sqrt 2` for
true. -/
theorem directBranch_eq {L d : ℕ} (F : ReflectionFamily L d) (c s : ℝ) (j : Fin L) (b : Bool) :
    directBranch F c s j b = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      ((c : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) + ((if b then -s else s : ℝ) : ℂ) • F.sigma j) := by
  unfold directBranch
  rw [directCircuit_blocks]
  cases b <;> ext i k <;> simp [Matrix.fromBlocks, Matrix.smul_apply, sub_eq_add_neg]

/-- The block ancilla rotation is an isometry whenever its real amplitudes satisfy `c^2 + s^2 =
1`. -/
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

/-- The controlled reflection is an isometry because each member of `F` is Hermitian and squares
to the identity. -/
theorem controlledReflection_isometry {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    (controlledReflection F j).Isometry := by
  change (controlledReflection F j)ᴴ * controlledReflection F j = 1
  have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
  simp [controlledReflection, Matrix.fromBlocks_conjTranspose, hj,
    Matrix.fromBlocks_multiply, F.square, Matrix.fromBlocks_one]

/-- The ancilla Hadamard tensored with the live identity is an isometry. -/
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

/-- The direct circuit is an isometry when its ancilla rotation amplitudes satisfy `c^2 + s^2 =
1`. -/
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

/-- The normalized real cosine amplitude `1 / sqrt (1 + a^2)` associated with weak-operator
parameter `a`. -/
def directCos (a : ℝ) : ℝ := (Real.sqrt (1 + a ^ 2))⁻¹

/-- The normalized real sine amplitude `a / sqrt (1 + a^2)` associated with weak-operator
parameter `a`. -/
def directSin (a : ℝ) : ℝ := a * directCos a

/-- The common branch scale `1 / (sqrt 2 * sqrt (1 + a^2))` for the normalized direct circuit. -/
def directScale (a : ℝ) : ℝ := (Real.sqrt 2)⁻¹ * directCos a

/-- The squared normalized amplitudes `directCos a` and `directSin a` sum to one for every real
`a`. -/
theorem direct_rotation_normalized (a : ℝ) : directCos a ^ 2 + directSin a ^ 2 = 1 := by
  have hp : 0 < 1 + a ^ 2 := by positivity
  have hs : Real.sqrt (1 + a ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hq : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt hp.le
  dsimp [directCos, directSin]
  field_simp
  nlinarith [hq]

/-- The square of the common direct-branch scale equals `1 / (2 * (1 + a^2))`. -/
theorem directScale_square (a : ℝ) : directScale a * directScale a = (2 * (1 + a ^ 2))⁻¹ := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  calc
    _ = (Real.sqrt 2 ^ 2 * Real.sqrt (1 + a ^ 2) ^ 2)⁻¹ := by
      simp only [directScale, directCos, _root_.mul_inv_rev, pow_two]
      ring
    _ = _ := by rw [h2, ha]

/-- With amplitudes `directCos a` and `directSin a`, the direct branch equals `directScale a`
times the corresponding weak operator. -/
theorem directBranch_normalized {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ) (j : Fin L) (b : Bool) :
    directBranch F (directCos a) (directSin a) j b =
      (directScale a : ℂ) • weakOperator F a j b := by
  rw [directBranch_eq]
  cases b <;> ext i k <;>
    simp only [weakOperator, directCos, directSin, directScale, Bool.false_eq_true, reduceIte,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  all_goals push_cast; ring

/-- Conjugating any live matrix by a normalized direct branch and weighting by `p.prob j` gives
exactly the `(j, b)` branch of the ideal instrument, identifying the circuit realization
used for thermal-drift sampling [JiangEtAl2026]. -/
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

/-- The thermal ancilla preparation probability `(1 - exp (-tau))^2 / (2 * (1 + exp (-2 *
tau)))`. -/
def directProbability (tau : ℝ) : ℝ :=
  (1 - Real.exp (-tau)) ^ 2 / (2 * (1 + Real.exp (-2 * tau)))

/-- Expresses `tanh (tau / 2)` as `(1 - exp (-tau)) / (1 + exp (-tau))` for every real `tau`. -/
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

/-- The squared normalized sine amplitude equals `a^2 / (1 + a^2)`. -/
theorem directSin_sq (a : ℝ) : directSin a ^ 2 = a ^ 2 / (1 + a ^ 2) := by
  have hp : 0 ≤ 1 + a ^ 2 := by positivity
  simp only [directSin, directCos, mul_pow, inv_pow, Real.sq_sqrt hp, div_eq_mul_inv]

/-- The thermal ancilla probability equals `directSin (tanh (tau / 2))^2`. -/
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

/-- For nonnegative `tau`, the nonnegative square roots of one minus the thermal probability and
of the probability equal the normalized cosine and sine amplitudes at `tanh (tau / 2)`. -/
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
