/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Matrix

namespace Qatlib.Papers.JonesPoly06.MainResults

section Density

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def hadamardReduced (ψ w : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ ψ ψ, inner ℂ ψ w; inner ℂ w ψ, inner ℂ w w]

def hadamardDensity (ψ w : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ ψ ψ / 2, inner ℂ ψ w / 2; inner ℂ w ψ / 2, inner ℂ w w / 2]

def matrixForm (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℂ :=
  (star v) ⬝ᵥ (M *ᵥ v)

def bornProb (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℂ :=
  matrixForm M v / ((star v) ⬝ᵥ v)

def gramForm (ψ w : E) (u v : ℂ) : ℂ :=
  (star u) * (u * inner ℂ ψ ψ + v * inner ℂ ψ w)
    + (star v) * (u * inner ℂ w ψ + v * inner ℂ w w)

theorem matrixForm_hadamardReduced_eq_gram (ψ w : E) (u v : ℂ) :
    matrixForm (hadamardReduced ψ w) ![u, v] = gramForm ψ w u v := by
  simp only [matrixForm, hadamardReduced, gramForm, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem gramForm_eq_inner (ψ w : E) (u v : ℂ) :
    gramForm ψ w u v = inner ℂ (u • ψ + v • w) (u • ψ + v • w) := by
  simp only [gramForm, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem gramForm_eq_normSq (ψ w : E) (u v : ℂ) :
    gramForm ψ w u v = ((‖u • ψ + v • w‖ ^ 2 : ℝ) : ℂ) := by
  rw [gramForm_eq_inner, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  exact (Complex.ofReal_pow (‖u • ψ + v • w‖) 2).symm

theorem gramForm_im (ψ w : E) (u v : ℂ) : (gramForm ψ w u v).im = 0 := by
  rw [gramForm_eq_normSq]
  exact Complex.ofReal_im _

theorem gramForm_re_nonneg (ψ w : E) (u v : ℂ) : 0 ≤ (gramForm ψ w u v).re := by
  rw [gramForm_eq_normSq]
  rw [Complex.ofReal_re]
  positivity

theorem hadamardDensity_trace (ψ w : E) (hψ : ‖ψ‖ = 1) (hw : ‖w‖ = 1) :
    Matrix.trace (hadamardDensity ψ w) = 1 := by
  rw [hadamardDensity, Matrix.trace_fin_two_of]
  simp only [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hψ, hw]
  norm_num

theorem hadamardDensity_hermitian (ψ w : E) :
    (hadamardDensity ψ w).conjTranspose = hadamardDensity ψ w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardDensity, Matrix.conjTranspose_apply, inner_conj_symm, star_div₀]

theorem hadamardAmplitude_mem_disk (ψ : E) (hψ : ‖ψ‖ = 1)
    (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    (inner ℂ ψ (U ψ)).re ^ 2 + (inner ℂ ψ (U ψ)).im ^ 2 ≤ 1 := by
  have hz : ‖inner ℂ ψ (U ψ)‖ ≤ 1 := by
    calc ‖inner ℂ ψ (U ψ)‖ ≤ ‖ψ‖ * ‖U ψ‖ := norm_inner_le_norm ψ (U ψ)
      _ = ‖ψ‖ * ‖ψ‖ := by rw [hU ψ]
      _ = 1 := by rw [hψ]; norm_num
  have hz2 : ‖inner ℂ ψ (U ψ)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (inner ℂ ψ (U ψ))]
  rw [Complex.sq_norm, Complex.normSq_apply] at hz2
  simpa [pow_two] using hz2

end Density

def signDensity (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), star z / 2; z / 2, (1 / 2 : ℂ)]

theorem hadamardDensity_eq_signDensity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ψ w : E) (hψ : ‖ψ‖ = 1) (hw : ‖w‖ = 1) :
    hadamardDensity ψ w = signDensity (inner ℂ w ψ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardDensity, signDensity, hψ, hw, inner_conj_symm]

theorem signDensity_trace (z : ℂ) : Matrix.trace (signDensity z) = 1 := by
  rw [signDensity, Matrix.trace_fin_two_of]
  norm_num

theorem matrixForm_signDensity (z u v : ℂ) :
    matrixForm (signDensity z) ![u, v]
      = (star u) * (u / 2 + star z / 2 * v) + (star v) * (z / 2 * u + v / 2) := by
  simp only [matrixForm, signDensity, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem bornProb_xplus (z : ℂ) :
    bornProb (signDensity z) ![1, 1] = ((1 + z.re) / 2 : ℂ) := by
  simp only [bornProb, matrixForm, signDensity, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  norm_num
  rw [Complex.ext_iff]
  constructor
  · simp; ring
  · simp; ring

theorem bornProb_xminus (z : ℂ) :
    bornProb (signDensity z) ![1, -1] = ((1 - z.re) / 2 : ℂ) := by
  simp only [bornProb, matrixForm, signDensity, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  norm_num
  rw [Complex.ext_iff]
  constructor
  · simp; ring
  · simp; ring

theorem bornProb_yplus (z : ℂ) :
    bornProb (signDensity z) ![1, Complex.I] = ((1 + z.im) / 2 : ℂ) := by
  simp only [bornProb, matrixForm, signDensity, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  norm_num
  rw [Complex.ext_iff]
  constructor
  · simp; ring
  · simp

theorem bornProb_yminus (z : ℂ) :
    bornProb (signDensity z) ![1, -Complex.I] = ((1 - z.im) / 2 : ℂ) := by
  simp only [bornProb, matrixForm, signDensity, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  norm_num
  rw [Complex.ext_iff]
  constructor
  · simp; ring
  · simp

theorem x_probs_mem (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    ((1 + z.re) / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1 - z.re) / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 : z.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im, hz]
  have hre : |z.re| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (z.re + 1)], by nlinarith [sq_nonneg (z.re - 1)]⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp hre
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem y_probs_mem (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    ((1 + z.im) / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1 - z.im) / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 : z.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.re, hz]
  have him : |z.im| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (z.im + 1)], by nlinarith [sq_nonneg (z.im - 1)]⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp him
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem x_probs_add (z : ℂ) :
    ((1 + z.re) / 2) + ((1 - z.re) / 2) = 1 := by ring

theorem y_probs_add (z : ℂ) :
    ((1 + z.im) / 2) + ((1 - z.im) / 2) = 1 := by ring

def bornMass (z : ℂ) (x y : ℝ) : ℝ := ((1 + x * z.re) / 2) * ((1 + y * z.im) / 2)

theorem bornMass_nonneg (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) (x y : ℝ)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) : 0 ≤ bornMass z x y := by
  unfold bornMass
  have hx' := x_probs_mem z hz
  have hy' := y_probs_mem z hz
  have hx2 : 0 ≤ (1 + x * z.re) / 2 := by
    rcases hx with hx | hx
    · rw [hx]; simpa using hx'.1.1
    · rw [hx]; simpa using! hx'.2.1
  have hy2 : 0 ≤ (1 + y * z.im) / 2 := by
    rcases hy with hy | hy
    · rw [hy]; simpa using hy'.1.1
    · rw [hy]; simpa using! hy'.2.1
  exact mul_nonneg hx2 hy2

end Qatlib.Papers.JonesPoly06.MainResults
