/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity.Theorem2NormBound
import Qatlib.Papers.ContDiscWalk08.CompressedSim.ArcsinCubic

/-!
# Compressed walk symbols

The scalar functions `sFactor` and `compressedSymbol` encode a square-root weight and a
combination of the two arcsine phases used in the walk simulation analysis of [Childs2010].
Exact identities and norm estimates compare this symbol with both the arcsine evolution and the
linear phase.

## Main statements

* `compressedSymbol_sub_exp`: exact discrepancy from the negative arcsine phase.
* `norm_compressedSymbol_sub_exp_neg_le_cubic`: quadratic and cubic scalar error bound.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.CompressedSim

/-- Defines the nonnegative square root of `1 - lam ^ 2`. -/
def sFactor (lam : ℝ) : ℝ := Real.sqrt (1 - lam ^ 2)

/-- Defines `((1 + s) * exp(-i * t * arcsin lam) - (1 - s) * exp(i * t * arcsin lam)) / 2`,
where `s = sFactor lam`. -/
def compressedSymbol (lam t : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (-(Complex.exp (Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ))) *
        (((1 - sFactor lam : ℝ)) : ℂ)
      + Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ))) *
        (((1 + sFactor lam : ℝ)) : ℂ))

/-- The square-root factor `sFactor lam` is nonnegative. -/
theorem sFactor_nonneg (lam : ℝ) : 0 ≤ sFactor lam := Real.sqrt_nonneg _

/-- If `lam ^ 2 ≤ 1`, then `sFactor lam ≤ 1`. -/
theorem sFactor_le_one {lam : ℝ} (hlam : lam ^ 2 ≤ 1) : sFactor lam ≤ 1 := by
  have hs2 : sFactor lam ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt (by linarith)
  nlinarith [sFactor_nonneg lam]

/-- If `lam ^ 2 ≤ 1`, the deficit `1 - sFactor lam` is at most `lam ^ 2`. -/
theorem one_sub_sFactor_le_sq {lam : ℝ} (hlam : lam ^ 2 ≤ 1) :
    1 - sFactor lam ≤ lam ^ 2 := by
  have hs2 : sFactor lam ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt (by linarith)
  nlinarith [sFactor_nonneg lam]

/-- Expresses the difference between the compressed symbol and the negative arcsine phase as the
cosine multiplied by the negative square-root deficit. This is a scalar identity for the
simulation analysis in [Childs2010]. -/
theorem compressedSymbol_sub_exp (lam t : ℝ) :
    compressedSymbol lam t
        - Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ)))
      = -(((1 - sFactor lam : ℝ)) : ℂ) *
          (Real.cos (t * Real.arcsin lam) : ℂ) := by
  set s := sFactor lam
  set a : ℝ := t * Real.arcsin lam
  set E : ℂ := Complex.exp (Complex.I * (a : ℂ)) with hEdef
  have hE : E = (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I := by
    rw [hEdef]
    rw [mul_comm Complex.I (a : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hEm : Complex.exp (-(Complex.I * (a : ℂ)))
      = (Real.cos a : ℂ) - (Real.sin a : ℂ) * Complex.I := by
    have harg : (-(Complex.I * (a : ℂ))) = ((-a : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hsum : E + Complex.exp (-(Complex.I * (a : ℂ))) = 2 * (Real.cos a : ℂ) := by
    rw [hE, hEm]
    ring
  have hmain : (1 / 2 : ℂ) *
        (-E * (((1 - s : ℝ)) : ℂ) +
          Complex.exp (-(Complex.I * (a : ℂ))) * (((1 + s : ℝ)) : ℂ))
        - Complex.exp (-(Complex.I * (a : ℂ)))
      = -(((1 - s : ℝ)) : ℂ) * (Real.cos a : ℂ) := by
    push_cast
    rw [← Complex.ofReal_cos]
    linear_combination (((s : ℂ) - 1) / 2) * hsum
  simpa [compressedSymbol, hEdef, a, s] using hmain

/-- For `lam ^ 2 ≤ 1`, bounds the discrepancy from the negative arcsine phase by `lam ^ 2`,
uniformly in real time. See [Childs2010]. -/
theorem norm_compressedSymbol_sub_exp_le {lam : ℝ} (hlam : lam ^ 2 ≤ 1) (t : ℝ) :
    ‖compressedSymbol lam t
        - Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ)))‖
      ≤ lam ^ 2 := by
  rw [compressedSymbol_sub_exp, norm_mul]
  have hcos : ‖(Real.cos (t * Real.arcsin lam) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hcoef : ‖-(((1 - sFactor lam : ℝ)) : ℂ)‖ ≤ lam ^ 2 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [sFactor_le_one hlam])]
    exact one_sub_sFactor_le_sq hlam
  calc ‖-(((1 - sFactor lam : ℝ)) : ℂ)‖ *
        ‖(Real.cos (t * Real.arcsin lam) : ℂ)‖
      ≤ lam ^ 2 * 1 := mul_le_mul hcoef hcos (norm_nonneg _) (by positivity)
    _ = lam ^ 2 := by ring

/-- The distance between two negative complex phases is at most the absolute difference of their
real arguments. -/
theorem norm_exp_phase_sub_le (u v : ℝ) :
    ‖Complex.exp (-(Complex.I * (u : ℂ))) - Complex.exp (-(Complex.I * (v : ℂ)))‖
      ≤ |u - v| := by
  have hfac : Complex.exp (-(Complex.I * (u : ℂ))) - Complex.exp (-(Complex.I * (v : ℂ)))
      = Complex.exp (-(Complex.I * (v : ℂ))) *
          (Complex.exp (Complex.I * ((v - u : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    have harg : -(Complex.I * (v : ℂ)) + Complex.I * ((v - u : ℝ) : ℂ)
        = -(Complex.I * (u : ℂ)) := by
      push_cast
      ring
    rw [harg]
  have hnorm : ‖Complex.exp (-(Complex.I * (v : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (v : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero]
  rw [hfac, norm_mul, hnorm, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := v - u)
  rw [abs_sub_comm]
  simpa using h

/-- For `lam ^ 2 ≤ 1`, bounds the discrepancy from the linear phase by `lam ^ 2 + |t| *
|Real.arcsin lam - lam|`. -/
theorem norm_compressedSymbol_sub_exp_neg_le {lam : ℝ} (hlam : lam ^ 2 ≤ 1) (t : ℝ) :
    ‖compressedSymbol lam t
        - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))‖
      ≤ lam ^ 2 + |t| * |Real.arcsin lam - lam| := by
  have hsplit : compressedSymbol lam t
        - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))
      = (compressedSymbol lam t
          - Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ))))
        + (Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ)))
          - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))) := by
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hphase : ‖Complex.exp (-(Complex.I * ((t * Real.arcsin lam : ℝ) : ℂ)))
        - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))‖
      ≤ |t| * |Real.arcsin lam - lam| := by
    have h := norm_exp_phase_sub_le (t * Real.arcsin lam) (t * lam)
    have harg : t * Real.arcsin lam - t * lam = t * (Real.arcsin lam - lam) := by ring
    rwa [harg, abs_mul] at h
  exact add_le_add (norm_compressedSymbol_sub_exp_le hlam t) hphase

/-- For `|lam| ≤ 1`, bounds the discrepancy from the linear phase by `lam ^ 2 * (1 + 2 * |t| *
|lam|)`. This gives a scalar simulation estimate related to [Childs2010]. -/
theorem norm_compressedSymbol_sub_exp_neg_le_cubic {lam : ℝ} (h : |lam| ≤ 1) (t : ℝ) :
    ‖compressedSymbol lam t - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))‖
      ≤ lam ^ 2 * (1 + 2 * |t| * |lam|) := by
  have hlam2 : lam ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one lam).mpr h
  have hbase := norm_compressedSymbol_sub_exp_neg_le hlam2 t
  have hcubic : |t| * |Real.arcsin lam - lam| ≤ |t| * (2 * |lam| ^ 3) :=
    mul_le_mul_of_nonneg_left (abs_arcsin_sub_self_le_two_mul_abs_cube h) (abs_nonneg t)
  calc ‖compressedSymbol lam t - Complex.exp (-(Complex.I * ((t * lam : ℝ) : ℂ)))‖
      ≤ lam ^ 2 + |t| * |Real.arcsin lam - lam| := hbase
    _ ≤ lam ^ 2 + |t| * (2 * |lam| ^ 3) := by linarith
    _ = lam ^ 2 * (1 + 2 * |t| * |lam|) := by
        rw [show |lam| ^ 3 = |lam| * |lam| ^ 2 from by ring, sq_abs]
        ring

end Qatlib.Papers.ContDiscWalk08.CompressedSim
