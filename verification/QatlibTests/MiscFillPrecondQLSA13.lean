/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade
public import Qatlib.Papers.PrecondQLSA13.MainResults.FemRatio
public import Qatlib.Papers.PrecondQLSA13.MainResults.TotalCostShape
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# MiscFill PrecondQLSA13 concrete instances

Concrete satisfiable instances for the tilde upgrade and the FEM decay: the
sub-polynomial Suzuki bound taken at the exact regime boundary
`x = exp((2 ln 5 / δ)²)`, the log-only preconditioned scaling with the
boundary regime constant `d`, and the two threshold statements.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
noncomputable section

open Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade
open Qatlib.Papers.PrecondQLSA13.MainResults.FemRatio
open Qatlib.Papers.PrecondQLSA13.MainResults.TotalCostShape
open Qatlib.Papers.PrecondQLSA13.MainResults.Complexity

namespace QatlibTests.MiscFillPrecondQLSA13

/-- The boundary regime `x = exp((2 ln 5 / δ)²)` satisfies the hypothesis
with equality. -/
example : (2 * Real.log 5 / (1 : ℝ)) ^ 2
      ≤ Real.log (Real.exp ((2 * Real.log 5 / (1 : ℝ)) ^ 2)) := by
  rw [Real.log_exp]

/-- The sub-polynomial Suzuki bound instantiated at the regime boundary. -/
example : Real.exp (2 * Real.log 5 * Real.sqrt (Real.log
      (Real.exp ((2 * Real.log 5 / (1 : ℝ)) ^ 2))))
    ≤ (Real.exp ((2 * Real.log 5 / (1 : ℝ)) ^ 2)) ^ (1 : ℝ) :=
  suzukiFactor_subpolylog (Real.exp ((2 * Real.log 5 / (1 : ℝ)) ^ 2)) 1
    (by norm_num)
    (Real.one_le_exp (sq_nonneg _))
    (by rw [Real.log_exp])

/-- The boundary constant `d = sqrt(exp(L)/12)` places `6·d²·K` exactly at
the regime boundary for `K = 2`. -/
example : (2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2
      ≤ Real.log (6 * (Real.sqrt (Real.exp
        ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12)) ^ 2 * 2 / 1 ^ 2) := by
  have h1 : 6 * (Real.sqrt (Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2)
        / 12)) ^ 2 * 2 / 1 ^ 2
      = Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) := by
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2)
        / 12 by positivity)]
    ring
  rw [h1, Real.log_exp]

/-- The preconditioned log-only cost bound instantiated in the boundary
regime with `K = 2`, `N = 4`. -/
example : totalCost (Real.sqrt (Real.exp
        ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12)) 2 4 1
    ≤ (72 * (Real.sqrt (Real.exp
        ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12)) ^ 7 * 2 / 1 ^ 2
        * (6 * (Real.sqrt (Real.exp
        ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12)) ^ 2 * 2 / 1 ^ 2)
          ^ ((1 / 8 : ℝ)))
      * Real.log 4 :=
  preconditioned_cost_log_only _ 2 4 1 (1 / 8 : ℝ)
    (Real.sqrt_pos_of_pos (div_pos (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < 12)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : 6 * (Real.sqrt (Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2)
            / 12)) ^ 2 * 2 / 1 ^ 2
          = Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ Real.exp
              ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12 by positivity)]
        ring
      rw [h1, Real.log_exp])

/-- The scalar cost comparison yields an explicit `N₀` for
concrete boundary-regime parameters and target `e = 1/2`. -/
example : ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    totalCost (Real.sqrt (Real.exp
      ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12)) 2 N 1 / (1 * N) ≤ 1 / 2 :=
  quantum_over_classical_tends_zero _ 2 1 (1 / 8 : ℝ) 1
    (Real.sqrt_pos_of_pos (div_pos (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < 12)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : 6 * (Real.sqrt (Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2)
            / 12)) ^ 2 * 2 / 1 ^ 2
          = Real.exp ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ Real.exp
              ((2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2) / 12 by positivity)]
        ring
      rw [h1, Real.log_exp])
    (1 / 2) (by norm_num)

/-- The eigenvalue-band condition bound on a concrete banded spectrum:
`λmax/λmin = 4/2 ≤ hmax/hmin = 9/1`. -/
example : (4 : ℝ) / 2 ≤ 9 / 1 :=
  eigenBandKappa 2 4 1 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The polylog-versus-linear threshold instantiated at `K = 1/2`, `N = 2`
(where `4K² = 1 ≤ N`): `K log N ≤ N`. -/
example : (1 / 2 : ℝ) * Real.log 2 ≤ 2 :=
  polylogLe (1 / 2) 2 (by norm_num) (by norm_num)

/-- The unpreconditioned 3-D FEM envelope at `d = 1`, `ε = 1`, `N = 8`: the
plain cost with `κ = 8^{2/3}` stays below the linear envelope `3N`. -/
example : qlsaCost 1 ((8 : ℝ) ^ (2 / 3 : ℝ)) 8 1 ≤ 24 :=
  le_trans (fem3dUnprecond 1 8 1 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)

/-- A spectral upper bound cannot be inferred when the proposed upper
endpoint lies below the actual eigenvalue. -/
theorem invalidBand : ¬ ((4 : ℝ) / 2 ≤ 1 / 1) := by
  norm_num

end QatlibTests.MiscFillPrecondQLSA13
