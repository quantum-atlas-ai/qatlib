module

import Qatlib.Papers.Schrodinger25.MainResults.Initialization.ErfConstruction
import Mathlib.Tactic.NormNum

open Qatlib.Papers.Schrodinger25.MainResults.Initialization

example (R : ℝ) (p : ℝ) (hp : p ∈ Set.Icc (1 / 2 : ℝ) R) :
    ‖(psiErf (1 / 4) p : ℂ) - Complex.exp (-(p : ℂ))‖ ≤ 1 / 4 := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact (abs_psiErf_sub_exp_neg_le (ε := 1 / 4) (by norm_num) (by norm_num) hp.1).trans
    (by norm_num)
