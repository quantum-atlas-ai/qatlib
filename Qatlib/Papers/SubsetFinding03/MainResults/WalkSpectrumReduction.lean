/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Spectrum of two-dimensional walk blocks

This module defines the explicit two-dimensional walk block `walkBlock`, its phase, and its two
candidate eigenvalues in the subset-finding analysis of [ChildsEisenberg2003]. It verifies the
paper's eigenvectors and factors the characteristic determinant.

When `1 ≤ j` and `4j ≤ M`, the phase is within `(j + 1) / M` of `2√(j / M)`. Under the stated
range condition, the eigenvalues are unit complex exponentials.

## Main statements

* `walkBlockPhase_approx`: bounds the error in the leading phase expression.
* `walkBlock_eigenvector_paper_plus` and `walkBlock_eigenvector_paper_minus`: verify the two
  eigenvector identities.
* `walkBlock_spectrum`: characterizes the zeros of the characteristic determinant.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SubsetFinding03.MainResults.WalkSpectrumReduction

open Complex
open scoped Matrix

/-- The real parameter `1 / (M + 1)` used in the walk blocks. -/
def walkBeta (M : ℕ) : ℝ := 1 / (M + 1)

/-- The phase `2 * arcsin (√(walkBeta M * j))` of the walk block. -/
def walkBlockPhase (M j : ℕ) : ℝ := 2 * Real.arcsin (Real.sqrt (walkBeta M * j))

/-- The diagonal coefficient `1 - 2 * walkBeta M * j`. -/
def walkBlockDiag (M j : ℕ) : ℝ := 1 - 2 * (walkBeta M * j)

/-- The off-diagonal coefficient `2 * √(walkBeta M * j * (1 - walkBeta M * j))`. -/
def walkBlockOffDiag (M j : ℕ) : ℝ := 2 * Real.sqrt (walkBeta M * j * (1 - walkBeta M * j))

/-- The complex two-by-two matrix with diagonal `walkBlockDiag M j` and signed off-diagonal
entries `walkBlockOffDiag M j`. -/
def walkBlock (M j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(walkBlockDiag M j : ℂ), -(walkBlockOffDiag M j : ℂ);
     (walkBlockOffDiag M j : ℂ), (walkBlockDiag M j : ℂ)]

/-- The candidate eigenvalue `walkBlockDiag M j + i * walkBlockOffDiag M j`. -/
def walkBlockEigPlus (M j : ℕ) : ℂ :=
  (walkBlockDiag M j : ℂ) + (walkBlockOffDiag M j : ℂ) * Complex.I

/-- The candidate eigenvalue `walkBlockDiag M j - i * walkBlockOffDiag M j`. -/
def walkBlockEigMinus (M j : ℕ) : ℂ :=
  (walkBlockDiag M j : ℂ) - (walkBlockOffDiag M j : ℂ) * Complex.I

/-- The normalized vector `(i, 1) / √2` used for the plus eigenvalue. -/
def paperKetPlus : Fin 2 → ℂ :=
  ![Complex.I / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]

/-- The normalized vector `(-i, 1) / √2` used for the minus eigenvalue. -/
def paperKetMinus : Fin 2 → ℂ :=
  ![-Complex.I / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]

/-- When `0 ≤ walkBeta M * j ≤ 1`, the cosine of the block phase equals the diagonal
coefficient. -/
lemma walkBlockPhase_cos (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    Real.cos (walkBlockPhase M j) = walkBlockDiag M j := by
  set x : ℝ := walkBeta M * j with hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hcos : Real.cos (Real.arcsin (Real.sqrt x)) = Real.sqrt (1 - x) := by
    rw [Real.cos_arcsin, hsq]
  have h1x : 0 ≤ 1 - x := by linarith
  have hsq' : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt h1x
  calc Real.cos (walkBlockPhase M j) = Real.cos (2 * Real.arcsin (Real.sqrt x)) := by
        rw [walkBlockPhase, ← hx]
    _ = 2 * Real.cos (Real.arcsin (Real.sqrt x)) ^ 2 - 1 := Real.cos_two_mul _
    _ = 2 * Real.sqrt (1 - x) ^ 2 - 1 := by rw [hcos]
    _ = 2 * (1 - x) - 1 := by rw [hsq']
    _ = 1 - 2 * x := by ring
    _ = walkBlockDiag M j := by rw [walkBlockDiag, hx]

/-- When `0 ≤ walkBeta M * j ≤ 1`, the sine of the block phase equals the off-diagonal
coefficient. -/
lemma walkBlockPhase_sin (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    Real.sin (walkBlockPhase M j) = walkBlockOffDiag M j := by
  set x : ℝ := walkBeta M * j with hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hcos : Real.cos (Real.arcsin (Real.sqrt x)) = Real.sqrt (1 - x) := by
    rw [Real.cos_arcsin, hsq]
  have hsin : Real.sin (Real.arcsin (Real.sqrt x)) = Real.sqrt x :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg x])
      (by nlinarith [hsq, hx1, Real.sqrt_nonneg x])
  calc Real.sin (walkBlockPhase M j) = Real.sin (2 * Real.arcsin (Real.sqrt x)) := by
        rw [walkBlockPhase, ← hx]
    _ = 2 * Real.sin (Real.arcsin (Real.sqrt x)) * Real.cos (Real.arcsin (Real.sqrt x)) :=
        Real.sin_two_mul _
    _ = 2 * Real.sqrt x * Real.sqrt (1 - x) := by rw [hsin, hcos]
    _ = 2 * Real.sqrt (x * (1 - x)) := by
        rw [Real.sqrt_mul hx0]; ring
    _ = walkBlockOffDiag M j := by rw [walkBlockOffDiag, hx]

/-- Rewrites `walkBeta M * j` as the real quotient `j / (M + 1)`. -/
lemma walkBeta_mul_eq (M j : ℕ) : walkBeta M * j = (j : ℝ) / ((M : ℝ) + 1) := by
  unfold walkBeta
  field_simp

/-- For `0 ≤ s ≤ 1 / 2`, the absolute difference between `arcsin s` and `s` is at most `s ^ 3`. -/
lemma abs_arcsin_sub_self_le_cube {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    |Real.arcsin s - s| ≤ s ^ 3 := by
  have hs1 : s ≤ 1 := by linarith
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith

  have hlow : s ≤ Real.arcsin s := by
    have h1 : Real.arcsin (Real.sin s) ≤ Real.arcsin s := Real.arcsin_le_arcsin (Real.sin_le hs0)
    have h2 : Real.arcsin (Real.sin s) = s := by
      apply Real.arcsin_sin
      · linarith [Real.neg_one_le_sin s, Real.two_le_pi]
      · linarith [Real.sin_le_one s, Real.two_le_pi]
    linarith

  have hupper : Real.arcsin s ≤ s + s ^ 3 := by
    rcases eq_or_lt_of_le hs0 with hzero | hpos
    · rw [← hzero]
      simp
    · have hy0 : 0 < s + s ^ 3 := by positivity
      have hs3le : s ^ 3 ≤ 1 / 8 := by
        have h := pow_le_pow_left₀ hs0 hs 3
        norm_num at h
        exact h
      have hy1 : s + s ^ 3 ≤ 1 := by linarith
      have hsin : (s + s ^ 3) - (s + s ^ 3) ^ 3 / 4 < Real.sin (s + s ^ 3) := by
        linarith [Real.sin_gt_sub_cube hy0, pow_nonneg hy0.le 3]
      have hcube : (1 + s ^ 2) ^ 3 ≤ 4 := by
        have h1s : 1 + s ^ 2 ≤ 5 / 4 := by linarith
        have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + s ^ 2) h1s 3
        norm_num at h
        linarith
      have hrew : (s + s ^ 3) ^ 3 = s ^ 3 * (1 + s ^ 2) ^ 3 := by ring
      have hs3n : 0 ≤ s ^ 3 := by positivity
      have hmul : s ^ 3 * (1 + s ^ 2) ^ 3 ≤ 4 * s ^ 3 := by
        have := mul_le_mul_of_nonneg_left hcube hs3n
        linarith
      have hlower : s ≤ (s + s ^ 3) - (s + s ^ 3) ^ 3 / 4 := by
        rw [hrew]
        nlinarith [hmul]
      have hy2 : s + s ^ 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.two_le_pi]
      exact (Real.arcsin_le_iff_le_sin ⟨by linarith, hs1⟩ hy2).mpr (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- For `1 ≤ j` and `4 * j ≤ M`, the block phase differs from `2 * √(j / M)` by at most `(j + 1)
/ M` [ChildsEisenberg2003]. -/
lemma walkBlockPhase_approx (M j : ℕ) (hj : 1 ≤ j) (hM : 4 * j ≤ M) :
    |walkBlockPhase M j - 2 * Real.sqrt ((j : ℝ) / (M : ℝ))| ≤
      ((j : ℝ) + 1) / (M : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjM : (j : ℝ) / (M : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hMpos]
    have h4 : (4 : ℝ) * j ≤ M := by exact_mod_cast hM
    linarith
  set s : ℝ := Real.sqrt (walkBeta M * j) with hsdef
  set c : ℝ := Real.sqrt ((j : ℝ) / (M : ℝ)) with hcdef
  have hbeta : walkBeta M * j = (j : ℝ) / ((M : ℝ) + 1) := walkBeta_mul_eq M j
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hsq : s ^ 2 = (j : ℝ) / ((M : ℝ) + 1) := by
    rw [hsdef, hbeta, Real.sq_sqrt]
    positivity
  have hcq : c ^ 2 = (j : ℝ) / (M : ℝ) := by
    rw [hcdef, Real.sq_sqrt]
    positivity
  have hcpos : 0 < c := by
    have : 0 < (j : ℝ) / (M : ℝ) := div_pos hjpos hMpos
    nlinarith [hcq, hc0]
  have hc_le : c ≤ 1 / 2 := by
    have : c ^ 2 ≤ 1 / 4 := by rw [hcq]; exact hjM
    nlinarith [hc0]
  have hs_le : s ≤ 1 / 2 := by
    have hs2 : s ^ 2 ≤ 1 / 4 := by
      rw [hsq]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
      have h4 : (4 : ℝ) * j ≤ M := by exact_mod_cast hM
      linarith
    nlinarith [hs0]
  have harc : |Real.arcsin s - s| ≤ s ^ 3 := abs_arcsin_sub_self_le_cube hs0 hs_le
  have hs3 : s ^ 3 ≤ (j : ℝ) / (2 * (M : ℝ)) := by
    have hjj : (j : ℝ) / ((M : ℝ) + 1) ≤ (j : ℝ) / (M : ℝ) := by
      apply div_le_div_of_nonneg_left (le_of_lt hjpos) hMpos
      linarith
    calc s ^ 3 = s * s ^ 2 := by ring
      _ = s * ((j : ℝ) / ((M : ℝ) + 1)) := by rw [hsq]
      _ ≤ (1 / 2) * ((j : ℝ) / (M : ℝ)) := by
          exact mul_le_mul hs_le hjj (by positivity) (by norm_num)
      _ = (j : ℝ) / (2 * (M : ℝ)) := by
          field_simp [ne_of_gt hMpos]
  have hspc : 0 < s + c := by linarith
  have hdiff : |s - c| * (s + c) = |s ^ 2 - c ^ 2| := by
    have h1 : |s - c| * (s + c) = |(s - c) * (s + c)| := by
      rw [abs_mul, abs_of_pos hspc]
    rw [h1, show (s - c) * (s + c) = s ^ 2 - c ^ 2 by ring]
  have hval : |s ^ 2 - c ^ 2| = (j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)) := by
    have hjj : (j : ℝ) / ((M : ℝ) + 1) ≤ (j : ℝ) / (M : ℝ) := by
      apply div_le_div_of_nonneg_left (le_of_lt hjpos) hMpos
      linarith
    rw [hsq, hcq, abs_of_nonpos (by linarith)]
    field_simp
    ring
  have hsc_eq : |s - c| = ((j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) / (s + c) := by
    have h : |s - c| * (s + c) = (j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)) := by
      rw [hdiff, hval]
    rw [eq_div_iff (ne_of_gt hspc)]
    exact h
  have hnum0 : 0 ≤ (j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)) := by positivity
  have hjc : (M : ℝ) * c ^ 2 = (j : ℝ) := by
    rw [hcq]
    field_simp [ne_of_gt hMpos]
  have hc2M : 2 * (M : ℝ) * c ≤ (M : ℝ) + 1 := by
    have hratio : c ≤ ((M : ℝ) + 1) / (2 * (M : ℝ)) := by
      have hsplit : ((M : ℝ) + 1) / (2 * (M : ℝ)) = 1 / 2 + 1 / (2 * (M : ℝ)) := by
        field_simp [ne_of_gt hMpos]
      have hpos : (0 : ℝ) < 1 / (2 * (M : ℝ)) := by positivity
      linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M : ℝ))] at hratio
    linarith
  have hkey : 2 * (j : ℝ) ≤ c * ((M : ℝ) + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hc2M hc0
    have hjc' : (2 * (M : ℝ) * c) * c = 2 * (j : ℝ) := by
      rw [show (2 * (M : ℝ) * c) * c = 2 * ((M : ℝ) * c ^ 2) by ring, hjc]
    linarith
  have hsc_le : |s - c| ≤ 1 / (2 * (M : ℝ)) := by
    have h1 : |s - c| ≤ ((j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) / c := by
      rw [hsc_eq]
      exact div_le_div_of_nonneg_left hnum0 hcpos (by linarith)
    have h2 : ((j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) / c ≤ 1 / (2 * (M : ℝ)) := by
      rw [div_le_div_iff₀ hcpos (by positivity : (0 : ℝ) < 2 * (M : ℝ))]
      have hL : ((j : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) * (2 * (M : ℝ))
          = 2 * (j : ℝ) / ((M : ℝ) + 1) := by
        field_simp [ne_of_gt hMpos]
      rw [hL]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
      linarith
    linarith
  have hphase_eq : walkBlockPhase M j = 2 * Real.arcsin s := by
    unfold walkBlockPhase
    rw [hsdef]
  rw [hphase_eq]
  have htwo : |2 * Real.arcsin s - 2 * c| = 2 * |Real.arcsin s - c| := by
    rw [show 2 * Real.arcsin s - 2 * c = 2 * (Real.arcsin s - c) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [htwo]
  have htri := abs_sub_le (Real.arcsin s) s c
  have h2s : 2 * s ^ 3 ≤ (j : ℝ) / (M : ℝ) := by
    have h2s' : 2 * s ^ 3 ≤ 2 * ((j : ℝ) / (2 * (M : ℝ))) := by linarith
    have h2s'' : 2 * ((j : ℝ) / (2 * (M : ℝ))) = (j : ℝ) / (M : ℝ) := by
      field_simp [ne_of_gt hMpos]
    linarith
  have step1 : 2 * |Real.arcsin s - c| ≤ 2 * (|Real.arcsin s - s| + |s - c|) := by
    linarith [htri]
  have step2 : 2 * (|Real.arcsin s - s| + |s - c|) ≤ 2 * (s ^ 3 + 1 / (2 * (M : ℝ))) := by
    nlinarith [harc, hsc_le]
  have step3 : 2 * (s ^ 3 + 1 / (2 * (M : ℝ))) ≤ ((j : ℝ) + 1) / (M : ℝ) := by
    have hthis : 2 * (1 / (2 * (M : ℝ))) = 1 / (M : ℝ) := by
      field_simp [ne_of_gt hMpos]
    have hjs : ((j : ℝ) + 1) / (M : ℝ) = (j : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by
      field_simp [ne_of_gt hMpos]
    linarith
  linarith [step1, step2, step3]

/-- When `0 ≤ walkBeta M * j ≤ 1`, the plus eigenvalue equals the complex exponential of `i`
times the block phase. -/
lemma walkBlockEigPlus_eq_exp (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    walkBlockEigPlus M j = Complex.exp ((walkBlockPhase M j : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp [walkBlockEigPlus, Complex.add_re, Complex.mul_re]
    rw [walkBlockPhase_cos M j hx0 hx1]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp [walkBlockEigPlus, Complex.add_im, Complex.mul_im]
    rw [walkBlockPhase_sin M j hx0 hx1]

/-- When `0 ≤ walkBeta M * j ≤ 1`, the minus eigenvalue equals the complex exponential of `-i`
times the block phase. -/
lemma walkBlockEigMinus_eq_exp (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    walkBlockEigMinus M j = Complex.exp (-((walkBlockPhase M j : ℂ)) * Complex.I) := by
  have h : -((walkBlockPhase M j : ℂ)) * Complex.I = ((-walkBlockPhase M j : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp [walkBlockEigMinus, Complex.sub_re, Complex.mul_re, Real.cos_neg]
    rw [walkBlockPhase_cos M j hx0 hx1]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp [walkBlockEigMinus, Complex.sub_im, Complex.mul_im, Real.sin_neg]
    rw [walkBlockPhase_sin M j hx0 hx1]

/-- The plus eigenvalue has norm one when `0 ≤ walkBeta M * j ≤ 1`. -/
lemma walkBlockEigPlus_norm_one (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    ‖walkBlockEigPlus M j‖ = 1 := by
  rw [walkBlockEigPlus_eq_exp M j hx0 hx1]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The minus eigenvalue has norm one when `0 ≤ walkBeta M * j ≤ 1`. -/
lemma walkBlockEigMinus_norm_one (M j : ℕ) (hx0 : 0 ≤ walkBeta M * j)
    (hx1 : walkBeta M * j ≤ 1) :
    ‖walkBlockEigMinus M j‖ = 1 := by
  rw [walkBlockEigMinus_eq_exp M j hx0 hx1]
  have h : -((walkBlockPhase M j : ℂ)) * Complex.I =
      ((-walkBlockPhase M j : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The vector `(i, 1)` is an eigenvector of the matrix with rows `(d, -b)` and `(b, d)`, with
eigenvalue `d + bi`. -/
lemma twoByTwo_mulVec_ketPlus (d b : ℝ) :
    (!![(d : ℂ), -(b : ℂ); (b : ℂ), (d : ℂ)]) *ᵥ (![Complex.I, 1] : Fin 2 → ℂ) =
      ((d : ℂ) + (b : ℂ) * Complex.I) • (![Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b : ℂ)) * Complex.I_sq
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring

/-- The vector `(-i, 1)` is an eigenvector of the matrix with rows `(d, -b)` and `(b, d)`, with
eigenvalue `d - bi`. -/
lemma twoByTwo_mulVec_ketMinus (d b : ℝ) :
    (!![(d : ℂ), -(b : ℂ); (b : ℂ), (d : ℂ)]) *ᵥ (![-Complex.I, 1] : Fin 2 → ℂ) =
      ((d : ℂ) - (b : ℂ) * Complex.I) • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b : ℂ)) * Complex.I_sq
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring

/-- The vector `(i, 1)` satisfies the walk-block eigenvector equation with eigenvalue
`walkBlockEigPlus M j`. -/
lemma walkBlock_mulVec_ketPlus (M j : ℕ) :
    walkBlock M j *ᵥ (![Complex.I, 1] : Fin 2 → ℂ) =
      walkBlockEigPlus M j • (![Complex.I, 1] : Fin 2 → ℂ) := by
  simpa [walkBlock, walkBlockEigPlus] using
    twoByTwo_mulVec_ketPlus (walkBlockDiag M j) (walkBlockOffDiag M j)

/-- The vector `(-i, 1)` satisfies the walk-block eigenvector equation with eigenvalue
`walkBlockEigMinus M j`. -/
lemma walkBlock_mulVec_ketMinus (M j : ℕ) :
    walkBlock M j *ᵥ (![-Complex.I, 1] : Fin 2 → ℂ) =
      walkBlockEigMinus M j • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  simpa [walkBlock, walkBlockEigMinus] using
    twoByTwo_mulVec_ketMinus (walkBlockDiag M j) (walkBlockOffDiag M j)

/-- Expresses `paperKetPlus` as `(i, 1)` scaled by `1 / √2`. -/
lemma paperKetPlus_eq_smul :
    paperKetPlus = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (![Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i <;>
    (simp [paperKetPlus, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring)

/-- Expresses `paperKetMinus` as `(-i, 1)` scaled by `1 / √2`. -/
lemma paperKetMinus_eq_smul :
    paperKetMinus = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i <;>
    (simp [paperKetMinus, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring)

/-- The normalized vector `paperKetPlus` satisfies the walk-block eigenvector equation for the
plus eigenvalue [ChildsEisenberg2003]. -/
lemma walkBlock_eigenvector_paper_plus (M j : ℕ) :
    walkBlock M j *ᵥ paperKetPlus = walkBlockEigPlus M j • paperKetPlus := by
  rw [paperKetPlus_eq_smul, Matrix.mulVec_smul, walkBlock_mulVec_ketPlus]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The normalized vector `paperKetMinus` satisfies the walk-block eigenvector equation for the
minus eigenvalue. -/
lemma walkBlock_eigenvector_paper_minus (M j : ℕ) :
    walkBlock M j *ᵥ paperKetMinus = walkBlockEigMinus M j • paperKetMinus := by
  rw [paperKetMinus_eq_smul, Matrix.mulVec_smul, walkBlock_mulVec_ketMinus]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- Factors the determinant of `walkBlock M j - z • 1` as the product of `z` minus each of the
two explicit eigenvalues. -/
lemma walkBlock_charpoly (M j : ℕ) (z : ℂ) :
    Matrix.det (walkBlock M j - Matrix.scalar (Fin 2) z) =
      (z - walkBlockEigPlus M j) * (z - walkBlockEigMinus M j) := by
  simp [Matrix.det_fin_two, walkBlock, walkBlockEigPlus, walkBlockEigMinus,
    Matrix.sub_apply, Matrix.scalar_apply]
  linear_combination ((walkBlockOffDiag M j : ℂ) ^ 2) * Complex.I_sq

/-- The characteristic determinant of the walk block vanishes exactly at `walkBlockEigPlus M j`
and `walkBlockEigMinus M j` [ChildsEisenberg2003]. -/
theorem walkBlock_spectrum (M j : ℕ) (z : ℂ) :
    Matrix.det (walkBlock M j - Matrix.scalar (Fin 2) z) = 0 ↔
      z = walkBlockEigPlus M j ∨ z = walkBlockEigMinus M j := by
  rw [walkBlock_charpoly]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact Or.inl (sub_eq_zero.1 h')
    · exact Or.inr (sub_eq_zero.1 h')
  · rintro (rfl | rfl)
    · simp
    · simp

end Qatlib.Papers.SubsetFinding03.MainResults.WalkSpectrumReduction
