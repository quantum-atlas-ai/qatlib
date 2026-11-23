module

public import Qatlib.Papers.NoGlobalSym14.PerturbBounds.CaseTwoCoupling
public import Qatlib.Papers.NoGlobalSym14.GraphFamilies.ParamFamilies

@[expose] public section

/-!
# Concrete consumer for the NoGlobalSym14 case-two coupling and family parameters

The examples instantiate the exact finite statements on the non-degenerate
parameter sets used in the figures of [JanmarkMeyerWong2014]: the Paley graph
`Paley(101, 50, 24, 25)` (`t = 25`), the Latin-square graph
`LatinSquare(9, 6, 3, 6)` (`t = 3`, `d = 3`), and the Latin-square graph
`LatinSquare(2500, 147, 50, 6)` (`t = 50`, `d = 3`). They exercise the Paley
and Latin-square parameter identities and non-degeneracy, the degree bounds,
the Euclidean coupling-vector norm, the exact shift identity, and the
closed-form normalization of the case-two coupling vector.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.NoGlobalSym14CaseTwoConsumer

open Qatlib.Papers.NoGlobalSym14.PerturbBounds
open Qatlib.Papers.NoGlobalSym14.GraphFamilies

/-- The Paley parameters of `Paley(101, 50, 24, 25)` (`t = 25`) satisfy the
strongly regular counting identity. -/
example : 2 * 25 * (2 * 25 - (25 - 1) - 1) = (4 * 25 + 1 - 2 * 25 - 1) * 25 :=
  paley_param_identity 25 (by norm_num)

/-- The Paley parameters at `t = 25` are non-degenerate. -/
example : 0 < 2 * 25 ∧ 0 < 4 * 25 + 1 - 2 * 25 - 1 :=
  paley_nondegenerate 25 (by norm_num)

/-- The Paley degree bound `√N < k + 1` at `t = 25`. -/
example : Real.sqrt (4 * 25 + 1 : ℝ) < (2 * 25 : ℝ) + 1 :=
  paley_degree_bound 25 (by norm_num)

/-- The Latin-square parameters of `LatinSquare(2500, 147, 50, 6)` (`t = 50`,
`d = 3`) satisfy the strongly regular counting identity over the integers. -/
example : (3 : ℤ) * (50 - 1) * (3 * (50 - 1) - (3 ^ 2 - 3 * 3 + 50) - 1)
    = (50 ^ 2 - 3 * (50 - 1) - 1) * (3 * (3 - 1)) :=
  latin_square_param_identity 3 50

/-- The Latin-square parameters of `LatinSquare(9, 6, 3, 6)` (`t = 3`, `d = 3`)
satisfy the strongly regular counting identity over the integers. -/
example : (3 : ℤ) * (3 - 1) * (3 * (3 - 1) - (3 ^ 2 - 3 * 3 + 3) - 1)
    = (3 ^ 2 - 3 * (3 - 1) - 1) * (3 * (3 - 1)) :=
  latin_square_param_identity 3 3

/-- The Latin-square parameters at `t = 50`, `d = 3` are non-degenerate over
the integers. -/
example : 0 < (3 : ℤ) * (50 - 1) ∧ (0 : ℤ) < 50 ^ 2 - 3 * (50 - 1) - 1 ∧
    (0 : ℤ) ≤ 3 ^ 2 - 3 * 3 + 50 ∧ (0 : ℤ) < 3 * (3 - 1) :=
  latin_square_nondegenerate 3 50 (by norm_num) (by norm_num)

/-- The Latin-square parameters at `t = 50`, `d = 3` are non-degenerate in
natural parameters. -/
example : 0 < 3 * (50 - 1) ∧ 0 < 50 * 50 - 3 * (50 - 1) - 1 ∧
    3 * 3 ≤ 3 * 3 + 50 ∧ 0 < 3 * (3 - 1) :=
  latin_square_nat_nondegenerate 3 50 (by norm_num) (by norm_num)

/-- The Latin-square degree bound `√N < k + 1` at `t = 50`, `d = 3`. -/
example : Real.sqrt ((50 : ℝ) ^ 2) < ((3 * (50 - 1) : ℤ) : ℝ) + 1 :=
  latin_square_degree_bound 3 50 (by norm_num) (by norm_num)

/-- The Euclidean norm of the unnormalized coupling vector at `a = 3`, `k = 4`
evaluates to `√(13/4)`. -/
example : ‖(WithLp.toLp 2 (couplingVec 3 4) : EuclideanSpace ℂ (Fin 3))‖
    = Real.sqrt (13 / 4) := by
  rw [couplingVec_norm 3 (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- The exact shift identity for the `Paley(101, 50, 24, 25)` parameters. -/
example : (50 : ℝ) - 24 + 25 = ((101 : ℝ) - 50 - 1) * 25 / 50 + 25 + 1 :=
  shifted_coupling_identity_nat
    (show 50 * (50 - 24 - 1) = (101 - 50 - 1) * 25 from
      paley_param_identity 25 (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)

/-- The case-two coupling vector for the `LatinSquare(2500, 147, 50, 6)` parameters is
a unit vector with the explicit closed-form normalization constant. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖(C : ℂ) •
        (WithLp.toLp 2 (couplingVec ((147 : ℝ) - 50 + 6) 147) : EuclideanSpace ℂ (Fin 3))‖
      = 1 ∧
    C = 1 / Real.sqrt (1 + (((2500 : ℝ) - 147 - 1) * 6 / 147 + 6 + 1) ^ 2 / 147) :=
  case2_normalization_closed_form
    (show 147 * (147 - 50 - 1) = (2500 - 147 - 1) * 6 by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end QatlibTests.NoGlobalSym14CaseTwoConsumer
