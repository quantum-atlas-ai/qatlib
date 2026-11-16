/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ShortPathOpt18.MainResults


/-- The binary entropy `S(x) = −x log x − (1 − x) log(1 − x)`, Eq. (54) region,
p. 16.  Natural logarithms are used, as in the paper's Proof of Lemma 11. -/
def binEnt (x : ℝ) : ℝ := -x * Real.log x - (1 - x) * Real.log (1 - x)

/-- The scalar function `x` mapped to `2 * sqrt (x * (1 - x))`. Composition with an inverse binary-entropy branch is not part of this definition. -/
def tauOf (x : ℝ) : ℝ := 2 * Real.sqrt (x * (1 - x))

/-- The scalar function `tauOf` is monotone on the interval `[0, 1 / 2]`. Monotonicity after composition with an inverse entropy branch requires a separate bridge. -/
theorem source_lemma11_tau_monotone {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    tauOf x ≤ tauOf y := by
  unfold tauOf
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hprod : x * (1 - x) ≤ y * (1 - y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith : (0 : ℝ) ≤ 1 - x - y)]
  have hnonneg : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have := Real.sqrt_le_sqrt hprod
  linarith

/-- The scalar value `tauOf x` lies in `[0, 1]` whenever `x` lies in `[0, 1]`. -/
theorem source_lemma11_tau_range {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ tauOf x ∧ tauOf x ≤ 1 := by
  have h1 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have h2 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * x - 1)]
  constructor
  · unfold tauOf
    have := Real.sqrt_nonneg (x * (1 - x))
    linarith
  · unfold tauOf
    have h2' : x * (1 - x) ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    have hs : Real.sqrt (x * (1 - x)) ≤ 1 / 2 := by
      calc Real.sqrt (x * (1 - x)) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h2'
        _ = 1 / 2 := Real.sqrt_sq (by norm_num)
    linarith

end Qatlib.Papers.ShortPathOpt18.MainResults
