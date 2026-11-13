/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLie
import Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal

/-!
# Evaluating formal word logarithms as matrices

This module identifies the rational algebra word series and logarithm coefficients with the
existing matrix constructions. Evaluation of rationally weighted letter words is compatible with
both identifications.

At positive degree, the formal Dynkin expansion therefore yields `matrix_log_eq_bracket_sum`, a
coefficient weighted sum of right nested matrix commutators. This is the bridge to matrix
estimates in [AftabAnTrivisa2026].

## Main statements

* `wordSeries_eq_suzuki`: identifies the two matrix word series constructions.
* `logCoefficient_eq_existing`: identifies their logarithm coefficient conventions.
* `letterWord_log_map`: transports formal logarithm coefficients to matrices.
* `matrix_log_eq_bracket_sum`: gives the evaluated nested commutator expansion.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHWordEval

open scoped BigOperators MonoidAlgebra Matrix.Norms.L2Operator
open BCHDynkin BCHWordLie
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- Inverse factorial scaling of a complex matrix agrees whether the scalar is taken in the
rationals or the reals. -/
theorem factorial_smul (n : ℕ) (a : Matrix I I ℂ) :
    (n.factorial : ℚ)⁻¹ • a = (n.factorial : ℝ)⁻¹ • a := by
  simpa only [Rat.cast_inv, Rat.cast_natCast] using!
    (Rat.cast_smul_eq_qsmul ℝ ((n.factorial : ℚ)⁻¹) a).symm

/-- The rational algebra word exponential series agrees with the existing matrix word series. -/
theorem wordSeries_eq_suzuki (xs : List (Matrix I I ℂ)) :
    BCHWordLie.wordSeries xs = SubdivisionPolynomial.wordSeries xs := by
  induction xs with
  | nil =>
    apply PowerSeries.ext
    intro n
    cases n <;> simp [BCHWordLie.wordSeries, SubdivisionPolynomial.wordSeries,
      suzukiSeries, PowerSeries.coeff_one]
  | cons X xs ih =>
    apply PowerSeries.ext
    intro n
    rw [SubdivisionPolynomial.wordSeries, PowerSeries.coeff_mk]
    change PowerSeries.coeff n (generatorSeries X * BCHWordLie.wordSeries xs) =
      suzukiSeries (X :: xs) n
    rw [PowerSeries.coeff_mul, suzukiSeries]
    apply Finset.sum_congr rfl
    intro p _
    rw [ih]
    simp only [generatorSeries, PowerSeries.coeff_mk, SubdivisionPolynomial.wordSeries,
      factorial_smul]

/-- The general rational algebra logarithm coefficient agrees with the existing matrix logarithm
coefficient. -/
theorem logCoefficient_eq_existing (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) :
    BCHWordLog.logCoefficient f n = BCHFormal.logCoefficient f n := by
  rw [BCHWordLog.logCoefficient_finite, BCHFormal.logCoefficient_finite]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_add,
    Rat.cast_natCast] using! (Rat.cast_smul_eq_qsmul ℝ ((-1 : ℚ) ^ k / (k + 1))
      (PowerSeries.coeff n ((f - 1) ^ (k + 1)))).symm

/-- Evaluating a rationally weighted letter word series gives the existing matrix word series
with the corresponding weighted matrices. -/
theorem letterWord_map {α : Type} (X : α → Matrix I I ℂ) (xs : List (ℚ × α)) :
    PowerSeries.map (evaluateWords X).toRingHom (letterWord xs) =
      SubdivisionPolynomial.wordSeries (xs.map (fun p => p.1 • X p.2)) := by
  rw [letterWord, wordSeries_map]
  simp only [List.map_map, Function.comp_def, map_smul, evaluateWords_letter]
  exact wordSeries_eq_suzuki _

/-- The logarithm coefficient of a weighted matrix word is the evaluation of the corresponding
formal letter word logarithm coefficient. -/
theorem letterWord_log_map {α : Type} (X : α → Matrix I I ℂ) (xs : List (ℚ × α)) (n : ℕ) :
    BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries
      (xs.map (fun p => p.1 • X p.2))) n =
        evaluateWords X (BCHWordLog.logCoefficient (letterWord xs) n) := by
  rw [← logCoefficient_eq_existing, ← letterWord_map X xs, BCHWordLog.logCoefficient_map]

/-- At positive degree, a weighted matrix word logarithm coefficient is the sum of right nested
matrix brackets weighted by the formal word coefficients divided by that degree. -/
theorem matrix_log_eq_bracket_sum {α : Type} (X : α → Matrix I I ℂ)
    (xs : List (ℚ × α)) (n : ℕ) (hn : 0 < n) :
    BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries
      (xs.map (fun p => p.1 • X p.2))) n =
      ∑ w ∈ (BCHWordLog.logCoefficient (letterWord xs) n).support,
        ((BCHWordLog.logCoefficient (letterWord xs) n) w / (n : ℚ)) •
          rightBracket (w.toList.map X) := by
  rw [letterWord_log_map]
  conv_lhs => rw [letterWord_log_eq_bracket_sum xs n hn]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul, evaluateWords_rightBracket]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHWordEval
