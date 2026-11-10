/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def kron (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => A i.1 j.1 * B i.2 j.2

def opXX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliX pauliX

def opYY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliY pauliY

def opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliZ pauliZ

def opII : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1

def expect (O ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := ((O * ρ).trace).re

def corrXX (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opXX ρ

def corrYY (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opYY ρ

def corrZZ (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opZZ ρ

def tParam (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (corrXX ρ + corrYY ρ) / 2

def uPlus : Fin 2 × Fin 2 → ℂ := fun i => if i = (0, 1) ∨ i = (1, 0) then 1 else 0

def uMinus : Fin 2 × Fin 2 → ℂ :=
  fun i => if i = (0, 1) then 1 else if i = (1, 0) then (-1 : ℂ) else 0

def rankOne (u : Fin 2 × Fin 2 → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => u i * u j

lemma plus_decomp :
    (opII + opXX + opYY - opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      rankOne uPlus + rankOne uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opII, opXX, opYY, opZZ, kron, pauliX, pauliY, pauliZ, rankOne, uPlus]

lemma minus_decomp :
    (opII - opXX - opYY - opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      rankOne uMinus + rankOne uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opII, opXX, opYY, opZZ, kron, pauliX, pauliY, pauliZ, rankOne, uMinus] <;> norm_num

lemma expect_add (A B ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expect (A + B) ρ = expect A ρ + expect B ρ := by
  simp [expect, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

lemma expect_sub (A B ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expect (A - B) ρ = expect A ρ - expect B ρ := by
  simp [expect, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

lemma trace_rankOne_mul_uPlus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (rankOne uPlus * ρ).trace =
      ρ (0, 1) (0, 1) + ρ (0, 1) (1, 0) + ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOne, uPlus, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring

lemma dotProduct_uPlus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)) =
      ρ (0, 1) (0, 1) + ρ (0, 1) (1, 0) + ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [dotProduct, Matrix.mulVec, uPlus, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

lemma trace_rankOne_mul_uMinus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (rankOne uMinus * ρ).trace =
      ρ (0, 1) (0, 1) - ρ (0, 1) (1, 0) - ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOne, uMinus, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring

lemma dotProduct_uMinus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)) =
      ρ (0, 1) (0, 1) - ρ (0, 1) (1, 0) - ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [dotProduct, Matrix.mulVec, uMinus, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem lemma3_zz_bound
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    corrZZ ρ ≤ 1 - 2 * |tParam ρ| := by

  have hqPlus : 0 ≤ (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := hρ.re_dotProduct_nonneg uPlus
  have hqMinus : 0 ≤ (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := hρ.re_dotProduct_nonneg uMinus

  have hbridgePlus :
      expect (rankOne uPlus) ρ = (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := by
    simp only [expect]
    rw [trace_rankOne_mul_uPlus, dotProduct_uPlus]
  have hbridgeMinus :
      expect (rankOne uMinus) ρ = (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := by
    simp only [expect]
    rw [trace_rankOne_mul_uMinus, dotProduct_uMinus]

  have hlinPlus :
      expect (opII + opXX + opYY - opZZ) ρ
        = expect opII ρ + expect opXX ρ + expect opYY ρ - expect opZZ ρ := by
    rw [expect_sub, expect_add, expect_add]
  have hlinMinus :
      expect (opII - opXX - opYY - opZZ) ρ
        = expect opII ρ - expect opXX ρ - expect opYY ρ - expect opZZ ρ := by
    rw [expect_sub, expect_sub, expect_sub]
  have hII : expect opII ρ = 1 := by
    simp [expect, opII, htr]

  have hvalPlus :
      expect (opII + opXX + opYY - opZZ) ρ = 2 * (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := by
    rw [plus_decomp, expect_add, hbridgePlus]
    ring
  have hvalMinus :
      expect (opII - opXX - opYY - opZZ) ρ = 2 * (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := by
    rw [minus_decomp, expect_add, hbridgeMinus]
    ring

  have hplus : 0 ≤ 1 + corrXX ρ + corrYY ρ - corrZZ ρ := by
    simp only [corrXX, corrYY, corrZZ]
    rw [← hII, ← hlinPlus, hvalPlus]
    linarith
  have hminus : 0 ≤ 1 - corrXX ρ - corrYY ρ - corrZZ ρ := by
    simp only [corrXX, corrYY, corrZZ]
    rw [← hII, ← hlinMinus, hvalMinus]
    linarith

  have hle1 : corrZZ ρ ≤ 1 + (corrXX ρ + corrYY ρ) := by linarith
  have hle2 : corrZZ ρ ≤ 1 - (corrXX ρ + corrYY ρ) := by linarith
  have hkey : corrZZ ρ ≤ 1 - |corrXX ρ + corrYY ρ| := by
    rcases le_total 0 (corrXX ρ + corrYY ρ) with hs | hs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_nonpos hs]; linarith

  have habs : 2 * |tParam ρ| = |corrXX ρ + corrYY ρ| := by
    simp only [tParam]
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    ring
  rwa [habs]

end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit
