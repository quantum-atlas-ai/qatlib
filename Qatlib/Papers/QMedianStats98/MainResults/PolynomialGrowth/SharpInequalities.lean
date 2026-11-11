/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovDerivative
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovBernstein
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharp Markov and algebraic Bernstein inequalities

This module exposes the two derivative inequalities recorded as Fact A.5 in [NayakWu1998]. A
degree-`d` real polynomial with absolute value at most `C` on `[-1, 1]` satisfies the sharp
Markov bound `|p'(x)| ≤ d²*C` and the weighted algebraic Bernstein bound `sqrt(1 - x²)*|p'(x)| ≤
d*C`.

The statements apply on the entire closed interval and include degree zero. They supply the
derivative control used in the two approximate-degree lower-bound terms.

## Main statements

- `source_fact_A5_markov`: gives the sharp Markov derivative bound.
- `source_fact_A5_bernstein`: gives the weighted algebraic Bernstein bound.
- `source_fact_A5`: packages both inequalities together.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth

open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- A real polynomial of degree at most `d`, bounded in absolute value by `C ≥ 0` on `[-1, 1]`,
satisfies `|p'(x)| ≤ d² * C` throughout that interval. This is the Markov part of Fact A.5
in [NayakWu1998]. -/
theorem source_fact_A5_markov (d : ℕ) (p : Polynomial ℝ) (C : ℝ)
    (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * C :=
  sharp_markov_derivative d p C hdeg hC hb

/-- A real polynomial of degree at most `d`, bounded in absolute value by `C ≥ 0` on `[-1, 1]`,
satisfies `sqrt(1 - x²) * |p'(x)| ≤ d * C` throughout that interval. This is the algebraic
Bernstein part of Fact A.5 in [NayakWu1998]. -/
theorem source_fact_A5_bernstein (d : ℕ) (p : Polynomial ℝ) (C : ℝ)
    (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * C := by
  intro x hx
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst d
    have hzero : p.derivative.eval x = 0 := sharp_markov_degree_zero p hdeg x
    simp [hzero]
  · exact sharpBernstein_interior d p C hdpos hdeg hC hb x hx

/-- A real polynomial of degree at most `d` with interval norm at most `C ≥ 0` satisfies both
the sharp Markov and weighted algebraic Bernstein derivative bounds on `[-1, 1]`. This
packages Fact A.5 of [NayakWu1998]. -/
theorem source_fact_A5 (d : ℕ) (p : Polynomial ℝ) (C : ℝ)
    (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * C) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * C) :=
  ⟨source_fact_A5_markov d p C hdeg hC hb,
    source_fact_A5_bernstein d p C hdeg hC hb⟩

end Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth
