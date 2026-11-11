/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContourSim25.LcuCircuit.PhaseCounter
import Qatlib.Concepts.BlockEncoding.LCU

/-!
# Correct complex LCU compression for the contour construction

The printed same-state compression is a Born-weighted combination. Two distinct
normalized left/right preparations instead retain the intended complex phases.
This gives an explicit exact-input inner LCU repair on one selector bit, together
with its projected encoding. It does not prove the contour series, QSVT
approximation or end-to-end query complexity.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ContourSim25.LcuCircuit
open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU
open scoped BigOperators

/-- The intended real-axis Hermitian combination of A and A*. -/
def sourceCombination {I : Type} (s : ℝ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ((1-Complex.I*s)/2) • A + ((1+Complex.I*s)/2) • Aᴴ

/-- The positive coefficient normalization in source equation (7). -/
def scale (s : ℝ) : ℝ := Real.sqrt (1+s^2)

/-- The source coefficient phase with unit modulus. -/
def sourcePhase (s : ℝ) : ℂ := (1-Complex.I*s)/(scale s : ℂ)

/-- The intended denominator is strictly positive for every real sample. -/
theorem scale_pos (s : ℝ) : 0<scale s := by
  apply Real.sqrt_pos.2
  positivity

/-- The normalization squares to 1+s^2. -/
theorem scale_sq (s : ℝ) : scale s * scale s=1+s^2 := by
  exact Real.mul_self_sqrt (by positivity)

/-- The coefficient phase has unit modulus, without assuming s positive. -/
theorem sourcePhase_normSq (s : ℝ) : Complex.normSq (sourcePhase s)=1 := by
  have hr : (scale s)^2=1+s^2 := by simpa only [pow_two] using scale_sq s
  have hd : (1+s^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hn : Complex.normSq (1-Complex.I*s)=1+s^2 := by
    simp [Complex.normSq_apply]
    ring
  rw [sourcePhase,Complex.normSq_div,hn,Complex.normSq_ofReal,← pow_two,hr]
  exact div_self hd

/-- The real balanced PREPARE amplitudes on the left. -/
def leftAmplitude (_ : Bool) : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- The phase-bearing amplitudes on the right, on the same one-bit label register. -/
def rightAmplitude (s : ℝ) (b : Bool) : ℂ :=
  (if b then star (sourcePhase s) else sourcePhase s) * leftAmplitude b

/-- The squared balanced amplitude is exactly one half. -/
theorem balanced_square : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹=1/2 := by
  have hsq : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)
  rw [← _root_.mul_inv_rev,hsq]
  norm_num

/-- The unphased left preparation is normalized. -/
theorem left_normalized : ∑ b : Bool,star (leftAmplitude b)*leftAmplitude b=1 := by
  have ha : star ((Real.sqrt 2 : ℂ)⁻¹)=(Real.sqrt 2 : ℂ)⁻¹ := by simp
  simp only [Fintype.sum_bool,leftAmplitude,ha]
  rw [balanced_square]
  norm_num

/-- The phased right preparation is also normalized. -/
theorem right_normalized (s : ℝ) :
    ∑ b : Bool,star (rightAmplitude s b)*rightAmplitude s b=1 := by
  have hq : star (sourcePhase s)*sourcePhase s=1 := by
    change (starRingEnd ℂ) (sourcePhase s)*sourcePhase s=1
    rw [← Complex.normSq_eq_conj_mul_self,sourcePhase_normSq]
    rfl
  have hq' : sourcePhase s * star (sourcePhase s)=1 := by rw [mul_comm,hq]
  have ha : star ((Real.sqrt 2 : ℂ)⁻¹)=(Real.sqrt 2 : ℂ)⁻¹ := by simp
  simp only [Fintype.sum_bool,rightAmplitude,Bool.false_eq_true,if_false,if_true,
    leftAmplitude,star_mul,star_star,ha]
  calc
    _ = (star (sourcePhase s)*sourcePhase s + sourcePhase s*star (sourcePhase s))*
        ((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = 1 := by rw [hq,hq',balanced_square]; norm_num

/-- The exact coefficients recovered by the two preparations. -/
def normalizedCoefficient (s : ℝ) (b : Bool) : ℂ :=
  (if b then (1+Complex.I*s) else (1-Complex.I*s))/(2*(scale s : ℂ))

/-- The left/right factorization retains the complex sign of each source coefficient. -/
theorem amplitude_factorization (s : ℝ) (b : Bool) :
    star (leftAmplitude b)*rightAmplitude s b=normalizedCoefficient s b := by
  have ha : star ((Real.sqrt 2 : ℂ)⁻¹)=(Real.sqrt 2 : ℂ)⁻¹ := by simp
  cases b <;> simp only [leftAmplitude,rightAmplitude,Bool.false_eq_true,if_false,if_true,ha]
  · calc
      _ = sourcePhase s*((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹) := by ring
      _ = normalizedCoefficient s false := by rw [balanced_square]; simp [sourcePhase,normalizedCoefficient]; ring
  · calc
      _ = star (sourcePhase s)*((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹) := by ring
      _ = normalizedCoefficient s true := by rw [balanced_square]; simp [sourcePhase,normalizedCoefficient]; ring

/-- The exact intended A/A* normalized combination is a real-axis Hermitian sample. -/
theorem sourceCombination_eq {I : Type} [Fintype I] (s : ℝ) (A : Matrix I I ℂ) :
    sourceCombination s A = s • ((1/(2*Complex.I):ℂ) • (A-Aᴴ)) + (1/2:ℂ) • (A+Aᴴ) := by
  ext i j
  simp only [sourceCombination,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,
    smul_eq_mul,Complex.real_smul]
  simp [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  ring_nf
  simp

/-- An exact source inner LCU repair using one selector bit and the original oracle/adjoint. -/
theorem corrected_inner_encoding {I : Type} [Fintype I] [DecidableEq I]
    (s : ℝ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding
      ((scale s : ℂ)⁻¹ • sourceCombination s U)
      (select (fun b : Bool => if b then Uᴴ else U))
      (prepareLift (I:=I) leftAmplitude) (prepareLift (I:=I) (rightAmplitude s)) := by
  have hUs : Uᴴ ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hU
  have h := lcu_factorized_projectedUnitaryEncoding leftAmplitude (rightAmplitude s)
    (normalizedCoefficient s) (fun b : Bool => if b then Uᴴ else U)
    left_normalized (right_normalized s) (amplitude_factorization s)
    (fun b => by cases b <;> simp [hU,hUs])
  convert h using 1
  ext i j
  simp only [Fintype.sum_bool,normalizedCoefficient,Bool.false_eq_true,if_false,if_true,
    sourceCombination,Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring
/-- Composing two actual isometric frames preserves their normalization. -/
theorem frame_compose_isometry {J I D : Type} [Fintype J] [Fintype I] [Fintype D]
    [DecidableEq I] [DecidableEq D] (P : Matrix J I ℂ) (E : Matrix I D ℂ)
    (hP : IsIsometry P) (hE : IsIsometry E) : IsIsometry (P*E) := by
  change (P*E)ᴴ*(P*E)=1
  rw [Matrix.conjTranspose_mul]
  calc
    Eᴴ*Pᴴ*(P*E)=Eᴴ*(Pᴴ*P)*E := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hP,Matrix.mul_one,hE]

/-- Compression of the source Hermitian combination commutes with a common input frame. -/
theorem sourceCombination_compress {I D : Type} [Fintype I] [Fintype D]
    [DecidableEq I] [DecidableEq D] (s : ℝ) (E : Matrix I D ℂ) (U : Matrix I I ℂ) :
    compress E (sourceCombination s U) E = sourceCombination s (compress E U E) := by
  unfold sourceCombination
  rw [compress_add,compress_smul,compress_smul,compress_adjoint]

/-- Corrected source equation (7) for an arbitrary exact input block encoding,
including nonunitary encoded A and its original ancillary frame. Only one
additional Boolean selector is added; the printed phase error is not assumed away. -/
theorem corrected_input_block_encoding {I D : Type} [Fintype I] [Fintype D]
    [DecidableEq I] [DecidableEq D] (s α : ℝ) (A : Matrix D D ℂ)
    (U : Matrix I I ℂ) (E : Matrix I D ℂ)
    (h : ProjectedUnitaryEncoding ((α : ℂ)⁻¹ • A) U E E) :
    ProjectedUnitaryEncoding (((scale s*α : ℝ) : ℂ)⁻¹ • sourceCombination s A)
      (select (fun b : Bool => if b then Uᴴ else U))
      (prepareLift (I:=I) leftAmplitude * E)
      (prepareLift (I:=I) (rightAmplitude s) * E) := by
  have inner := corrected_inner_encoding s U h.unitary
  refine ⟨inner.unitary,
    frame_compose_isometry _ E inner.left_isometry h.left_isometry,
    frame_compose_isometry _ E inner.right_isometry h.right_isometry,?_⟩
  have hc : compress (prepareLift leftAmplitude*E)
      (select (fun b : Bool => if b then Uᴴ else U))
      (prepareLift (rightAmplitude s)*E) =
      compress E (compress (prepareLift leftAmplitude)
        (select (fun b : Bool => if b then Uᴴ else U))
        (prepareLift (rightAmplitude s))) E := by
    simp only [compress,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hc,inner.encoded,compress_smul,sourceCombination_compress,h.encoded]
  ext i j
  simp only [sourceCombination,Matrix.add_apply,Matrix.smul_apply,
    Matrix.conjTranspose_smul,smul_eq_mul,Matrix.conjTranspose_apply]
  simp
  ring

end Qatlib.Papers.ContourSim25.LcuCircuit
