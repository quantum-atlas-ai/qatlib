/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.VertexModel.EightVertex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.SixVertex

open Qatlib.Papers.SpinModels08.MainResults
open Qatlib.Papers.SpinModels08.MainResults.VertexModel

def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def tensor2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => A i k * B j l

theorem tensor2_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j k l : Fin 2) :
    tensor2 A B (i, j) (k, l) = A i k * B j l := rfl

def Hex : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tensor2 sigmaX sigmaX + tensor2 sigmaY sigmaY + tensor2 sigmaZ sigmaZ

def swapGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => if i = l ∧ j = k then 1 else 0

theorem swapGate_apply (i j k l : Fin 2) :
    swapGate (i, j) (k, l) = if i = l ∧ j = k then 1 else 0 := rfl

theorem Hex_eq_swap_add_swap_sub_one : Hex = swapGate + swapGate - 1 := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Hex, tensor2, sigmaX, sigmaY, sigmaZ, swapGate, Matrix.add_apply,
      Matrix.sub_apply, Complex.I_mul_I]

theorem Hex_eq_two_swap_sub_one : Hex = (2 : ℂ) • swapGate - 1 := by
  rw [show (2 : ℂ) • swapGate = swapGate + swapGate from two_smul ℂ swapGate]
  exact Hex_eq_swap_add_swap_sub_one

def sixVertexWeight (t : ℝ) : QWeight 2
  | 0, 0, 0, 0 => Complex.exp (2 * (t : ℂ) * Complex.I)
  | 0, 1, 0, 1 => (Real.cos (2 * t) : ℂ)
  | 0, 1, 1, 0 => Complex.I * (Real.sin (2 * t) : ℂ)
  | 1, 0, 0, 1 => Complex.I * (Real.sin (2 * t) : ℂ)
  | 1, 0, 1, 0 => (Real.cos (2 * t) : ℂ)
  | 1, 1, 1, 1 => Complex.exp (2 * (t : ℂ) * Complex.I)
  | _, _, _, _ => 0

theorem sixVertexWeight_0000 (t : ℝ) :
    sixVertexWeight t 0 0 0 0 = Complex.exp (2 * (t : ℂ) * Complex.I) := rfl

theorem sixVertexWeight_1111 (t : ℝ) :
    sixVertexWeight t 1 1 1 1 = Complex.exp (2 * (t : ℂ) * Complex.I) := rfl

theorem sixVertexWeight_0101 (t : ℝ) :
    sixVertexWeight t 0 1 0 1 = (Real.cos (2 * t) : ℂ) := rfl

theorem sixVertexWeight_1010 (t : ℝ) :
    sixVertexWeight t 1 0 1 0 = (Real.cos (2 * t) : ℂ) := rfl

theorem sixVertexWeight_0110 (t : ℝ) :
    sixVertexWeight t 0 1 1 0 = Complex.I * (Real.sin (2 * t) : ℂ) := rfl

theorem sixVertexWeight_1001 (t : ℝ) :
    sixVertexWeight t 1 0 0 1 = Complex.I * (Real.sin (2 * t) : ℂ) := rfl

theorem sixVertexWeight_shape (t : ℝ) : IsSixVertexShape (sixVertexWeight t) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [sixVertexWeight]

theorem sixVertexWeight_phase (t : ℝ) :
    Complex.exp (2 * (t : ℂ) * Complex.I) =
      (Real.cos (2 * t) : ℂ) + (Real.sin (2 * t) : ℂ) * Complex.I := by
  have h : (2 : ℂ) * (t : ℂ) * Complex.I = ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I]

theorem cos2_re (t : ℝ) : (Complex.cos ((2 : ℂ) * (t : ℂ))).re = Real.cos (2 * t) := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.cos_ofReal_re]

theorem cos2_im (t : ℝ) : (Complex.cos ((2 : ℂ) * (t : ℂ))).im = 0 := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.cos_ofReal_im]

theorem sin2_re (t : ℝ) : (Complex.sin ((2 : ℂ) * (t : ℂ))).re = Real.sin (2 * t) := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.sin_ofReal_re]

theorem sin2_im (t : ℝ) : (Complex.sin ((2 : ℂ) * (t : ℂ))).im = 0 := by
  rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.sin_ofReal_im]

theorem sixVertexWeight_unitary (t : ℝ) :
    IsUnitary (twoLocalGate (sixVertexWeight t)) := by
  rw [IsUnitary]
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    rw [Complex.ext_iff] <;> constructor <;>
    simp [twoLocalGate, sixVertexWeight, Matrix.one_apply, sixVertexWeight_phase,
      cos2_re, cos2_im, sin2_re, sin2_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;>
    nlinarith [Real.cos_sq_add_sin_sq (2 * t)]

def encodingWeight : QWeight 2
  | 0, 0, 0, 0 => 1
  | 1, 1, 1, 1 => 1
  | 0, 1, 0, 1 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 1, 0, 1, 0 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 0, 1, 1, 0 => ((Real.sqrt 2)⁻¹ : ℂ)
  | 1, 0, 0, 1 => -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  | _, _, _, _ => 0

theorem encodingWeight_0000 : encodingWeight 0 0 0 0 = 1 := rfl

theorem encodingWeight_1111 : encodingWeight 1 1 1 1 = 1 := rfl

theorem encodingWeight_0101 : encodingWeight 0 1 0 1 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

theorem encodingWeight_1010 : encodingWeight 1 0 1 0 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

theorem encodingWeight_0110 : encodingWeight 0 1 1 0 = ((Real.sqrt 2)⁻¹ : ℂ) := rfl

theorem encodingWeight_1001 : encodingWeight 1 0 0 1 = -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl

theorem encodingWeight_shape : IsSixVertexShape encodingWeight := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [encodingWeight]

def prepGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  twoLocalGate encodingWeight

theorem prepGate_apply (i j k l : Fin 2) :
    prepGate (i, j) (k, l) = encodingWeight i j k l := rfl

def basisPair (a b : Fin 2) : Fin 2 × Fin 2 → ℂ := fun x => if x = (a, b) then 1 else 0

def singlet : Fin 2 × Fin 2 → ℂ := fun (k, l) =>
  if k = 0 ∧ l = 1 then ((Real.sqrt 2)⁻¹ : ℂ)
  else if k = 1 ∧ l = 0 then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

theorem prepGate_mulVec_01 : prepGate.mulVec (basisPair 0 1) = singlet := by
  funext x
  obtain ⟨k, l⟩ := x
  fin_cases k <;> fin_cases l <;>
    simp [prepGate, twoLocalGate, encodingWeight, basisPair, singlet, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

def dot {ι : Type*} [Fintype ι] (a b : ι → ℂ) : ℂ := ∑ i, star (a i) * b i

theorem dot_eq_dotProduct {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    dot a b = star a ⬝ᵥ b := rfl

theorem dot_mulVec {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (v w : ι → ℂ) :
    dot (U.mulVec v) w = dot v (Uᴴ.mulVec w) := by
  rw [dot_eq_dotProduct, dot_eq_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem amplitude_conj {ι : Type*} [Fintype ι] (U C : Matrix ι ι ℂ) (v : ι → ℂ) :
    dot (U.mulVec v) (C.mulVec (U.mulVec v)) = dot v ((Uᴴ * C * U).mulVec v) := by
  rw [dot_mulVec U v (C.mulVec (U.mulVec v))]
  congr 1
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem eq9_amplitude_rewrite {ι : Type*} [Fintype ι]
    (V C : Matrix ι ι ℂ) (w v : ι → ℂ) (h : V.mulVec w = v) :
    dot v (C.mulVec v) = dot w ((Vᴴ * C * V).mulVec w) := by
  rw [← h]
  exact amplitude_conj V C w

theorem eq9_prep_specialization (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    dot singlet (C.mulVec singlet) =
      dot (basisPair 0 1) ((prepGateᴴ * C * prepGate).mulVec (basisPair 0 1)) := by
  rw [← prepGate_mulVec_01]
  exact amplitude_conj prepGate C (basisPair 0 1)

def staggeredConfig (N : ℕ) : Config 2 N := fun r => if r.val % 2 = 0 then 0 else 1

theorem sixVertex_amplitude_eq_partition {N M : ℕ} (t : Fin M → Fin N → ℝ)
    (L R : Config 2 N) :
    matElem (vmCircuit M (fun c r => sixVertexWeight (t c r))) L R =
      vmPartition M (fun c r => sixVertexWeight (t c r)) L R :=
  matElem_vmCircuit_eq_vmPartition M _ L R

theorem sixVertex_staggered_amplitude_eq_partition {N M : ℕ} (t : Fin M → Fin N → ℝ) :
    matElem (vmCircuit M (fun c r => sixVertexWeight (t c r)))
        (staggeredConfig N) (staggeredConfig N) =
      vmPartition M (fun c r => sixVertexWeight (t c r))
        (staggeredConfig N) (staggeredConfig N) :=
  sixVertex_amplitude_eq_partition t _ _

def SixVertexAmplitudeForm : Prop :=
  ∀ (N M : ℕ) (t : Fin M → Fin N → ℝ) (L R : Config 2 N),
    ∃ (C : Matrix (Config 2 N) (Config 2 N) ℂ), matElem C L R =
      vmPartition M (fun c r => sixVertexWeight (t c r)) L R

theorem sixVertex_amplitude_form : SixVertexAmplitudeForm := by
  intro N M t L R
  exact ⟨vmCircuit M (fun c r => sixVertexWeight (t c r)),
    sixVertex_amplitude_eq_partition t L R⟩

end Qatlib.Papers.SpinModels08.MainResults.SixVertex
