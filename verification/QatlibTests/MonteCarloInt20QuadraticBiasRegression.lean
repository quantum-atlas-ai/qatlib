module

import Qatlib.Papers.MonteCarloInt20.QaeLaw.QuadraticBias
import Mathlib.Tactic.NormNum

/-!
The consumer uses an explicit two-sample, non-constant payoff and the exact
finite source-access threshold.  It is an ordinary module so downstream users
exercise the public declarations through their normal import path.
-/

set_option autoImplicit false

namespace QatlibTests.MonteCarloInt20QuadraticBiasRegression

open Qatlib.Papers.MonteCarloInt20.QaeLaw


noncomputable section

def twoSamples : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

example :
    quadraticPayoffBias (by norm_num : 0 < (2 : ℕ)) 3 2 twoSamples = (1 / 2 : ℝ) := by
  rw [quadratic_payoff_bias_eq_variance (by norm_num : 0 < (2 : ℕ))]
  norm_num [twoSamples, finiteMean]

example : nestedSourceQueries 3 2 < previousSourceQueries 4 2 := by
  exact (nested_source_queries_lt_iff 4 3 2 (by omega) (by omega) (by omega)).2 (by omega)

example : ¬ nestedSourceQueries 5 2 < previousSourceQueries 4 2 := by
  intro h
  have hle := (nested_source_queries_lt_iff 4 5 2 (by omega) (by omega) (by omega)).1 h
  omega

#print axioms quadratic_payoff_bias_eq_variance
#print axioms nested_source_queries_lt_iff

end

end QatlibTests.MonteCarloInt20QuadraticBiasRegression
