/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Papers.QLinearSolver19.MainResults.Model.AQCQLSPModel

/-!
# Shared calculus and conditioning gadgets for the paper layer of QLinearSolver19.

* `HasConditionNumber A κ` follows the paper's normalization `‖A‖ = 1`, so that the condition
  number equals `‖A⁻¹‖`: every vector satisfies `‖v‖ ≤ κ ‖A v‖` (paper §2, page 5:2).
* `derivMat` / `iteratedDerivMat` take derivatives entrywise, i.e. the `k`-th derivative of a
  finite matrix-valued function.  By finite-dimensionality this is the same as the derivative of
  the matrix as an element of `Matrix ι ι ℂ` with the L2 operator norm (paper notation `H^{(k)}`,
  `R^{(k)}`); we use the entrywise form to avoid imposing a real normed-space structure on the
  matrix space.
* `circleContour` is the (unnormalised) contour integral `∮_{|z|=R} F z dz` used in Eq. (21)-(23).
-/

/-!
# Prelude

Paper-specific definitions and results for QLinearSolver19.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QLinearSolver19.MainResults

set_option autoImplicit false

/-- `κ` is a condition number for `A` in the paper's normalization `‖A‖ = 1`: `A` is invertible
and `‖v‖ ≤ κ ‖A v‖` for every `v` (paper §2, condition number of the QLSP matrix). -/
def HasConditionNumber {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ v : Vec N, ‖v‖ ≤ κ * ‖matCLM A v‖

/-- The first derivative of a matrix-valued function, taken entrywise (paper notation `H^{(1)}`). -/
noncomputable def derivMat {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  fun i j => deriv (fun t => F t i j) s

/-- The `k`-th derivative of a matrix-valued function, taken entrywise (paper notation
`H^{(k)}`, `R^{(k)}`).  For finite matrices this coincides with the `k`-th derivative in the
L2 operator norm. -/
noncomputable def iteratedDerivMat {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (F : ℝ → Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  fun i j => iteratedDeriv k (fun t => F t i j) s

/-- The contour integral `∮_{|z| = R} F z dz` of a matrix-valued function (the contour `Γ(s)` of
the paper is `|z| = Δ(s)/2`, page 5:20). -/
noncomputable def circleContour {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ℂ → Matrix ι ι ℂ) (R : ℝ) : Matrix ι ι ℂ :=
  circleIntegral F 0 R

end Qatlib.Papers.QLinearSolver19.MainResults
