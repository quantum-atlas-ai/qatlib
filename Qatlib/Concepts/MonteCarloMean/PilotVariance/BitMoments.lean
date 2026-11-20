/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization

@[expose] public section


/-!
# Executed rational pilot moments

This implementation evaluates the first two empirical moments using the counted
binary rational primitives of `BitRational`. Its cost is the sum of the costs
returned by the operations actually executed, rather than an existential ledger.

The count is the Boolean-gate charge returned by the explicit binary arithmetic
routines, including fraction reduction. Converting between rational values and
bit-word representations is a semantic interpretation here; that conversion,
structural control and container allocation are not instruction-counted.
Sample acquisition and evaluation of an external payoff are also excluded.
Output widths below describe stored rational values, not the peak workspace of a
Turing-machine implementation. Those costs must be proved separately.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments

open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization

/-- Square every supplied rational, retaining the costs returned by binary multiplication. -/
def squares : List ℚ → List ℚ × ℕ
  | [] => ([], 0)
  | a :: as =>
    let head := binomialRatMulBits a a
    let tail := squares as
    (head.1 :: tail.1, head.2 + tail.2)

/-- The two exact empirical moments and their executed binary arithmetic cost. -/
structure Result where
  mean : ℚ
  secondMoment : ℚ
  records : ℕ
  /-- Boolean-gate charges from the binary arithmetic routines, rather than a
  count of all Lean or machine instructions. Representation interpretation,
  structural control and allocation are outside this counter. -/
  bitOps : ℕ

/-- Compute both sums and both divisions with counted binary rational operations.
For an empty input, Lean's total rational division returns zero for both moments. -/
def run (as : List ℚ) : Result :=
  let squared := squares as
  let first := sumBits as
  let second := sumBits squared.1
  let mean := binomialRatDivBits first.1 as.length
  let moment := binomialRatDivBits second.1 as.length
  ⟨mean.1, moment.1, as.length, squared.2 + first.2 + second.2 + mean.2 + moment.2⟩

/-- Squaring preserves the input order and returns the actual squared values. -/
theorem squares_values (as : List ℚ) :
    (squares as).1 = as.map (fun a => a ^ 2) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [squares, List.map_cons, ih, (binomial_rat_mul_bits a a).1, pow_two]

/-- The counted evaluator returns precisely the two empirical rational moments. -/
theorem run_values (as : List ℚ) :
    (run as).mean = as.sum / as.length ∧
      (run as).secondMoment = (as.map (fun a => a ^ 2)).sum / as.length ∧
      (run as).records = as.length := by
  simp only [run, (binomial_rat_div_bits _ _).1, sum_value, squares_values,
    and_self]

/-- Every multiplication pays at least its sign operation, even for a zero sample. -/
theorem squares_cost_lower (as : List ℚ) : as.length ≤ (squares as).2 := by
  induction as with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
    have h : 1 ≤ (binomialRatMulBits a a).2 := by
      dsimp only [binomialRatMulBits]
      omega
    change as.length + 1 ≤ (binomialRatMulBits a a).2 + (squares as).2
    omega

/-- A nonempty pilot cannot be certified by a zero arithmetic-cost ledger. -/
theorem run_cost_lower (as : List ℚ) : as.length ≤ (run as).bitOps := by
  have h := squares_cost_lower as
  dsimp only [run]
  omega

end Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments
