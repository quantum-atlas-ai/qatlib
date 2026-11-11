/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum

/-!
# Obstruction to the candidate noisy quantum oracle

This module proves `noisyQuantumOracle_obstruction` for the candidate oracle contract in the
ordered search setting of [BenOrHassidim2007]. With one input index, the constant-false
function, and p = 16/25, the two columns of `noisyOracle` have a nonzero inner product,
contradicting the required unitarity.

## Main statements

* `noisyQuantumOracle_obstruction`: `NoisyQuantumOracleContract` is false for the specified
  matrix construction.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition `NoisyQuantumOracleContract` for the matrix construction associated with
[BenOrHassidim2007] is false: at one input index and p = 16/25, its unitarity requirement
fails. -/
theorem noisyQuantumOracle_obstruction : ¬ NoisyQuantumOracleContract := by
  intro h
  have hU := h.1 1 (fun _ => false) (16 / 25) (by norm_num) (by norm_num)
  have hGram := Matrix.mem_unitaryGroup_iff'.mp hU
  have hentry := congrArg
    (fun A : Matrix (Fin 1 × Bool) (Fin 1 × Bool) ℂ => A (0, false) (0, true)) hGram
  have hs16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hs25 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hs9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [noisyOracle, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, Real.sqrt_div, hs16, hs25, hs9, map_ofNat] at hentry

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
