/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Grid ball overlap specification

`gridBall` selects integer vectors in a finite coordinate box using a scaled Euclidean distance
condition. The proposition `gridBallIntersection_ratio` specifies a uniform lower bound for the
relative overlap of the origin-centered and shifted grid balls. See [Regev2004] for the paper
context.

## Main statements

* `gridBall`: The integer vectors with coordinates between `-ceil(R * L)` and `ceil(R * L)`
  satisfying `sqrt(∑ i, ((x i - c i) / L)²) ≤ R`.
* `gridBallIntersection_ratio`: The proposition that a positive constant bounds the loss of
  relative grid ball overlap by `C * sqrt n * sqrt(∑ i, d i²) / R` for `R ≥ 1` and grid
  parameter `2^n`.

## References

* [Regev, 2004][Regev2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The integer vectors with coordinates between `-ceil(R * L)` and `ceil(R * L)` satisfying
`sqrt(∑ i, ((x i - c i) / L)²) ≤ R`. -/
noncomputable def gridBall (n : ℕ) (L : ℕ) (R : ℝ) (c : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset (fun _ : Fin n =>
      Finset.Icc (-(↑⌈R * L⌉₊ : ℤ)) (↑⌈R * L⌉₊ : ℤ))).filter
    (fun x => Real.sqrt (∑ i : Fin n, (((x i : ℝ) - c i) / (L : ℝ)) ^ 2) ≤ R)

/-- The proposition that a positive constant bounds the loss of relative grid ball overlap by `C
* sqrt n * sqrt(∑ i, d i²) / R` for `R ≥ 1` and grid parameter `2^n`. -/
def gridBallIntersection_ratio : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R : ℝ) (d : Fin n → ℝ),
    1 ≤ R →
    (1 - C * Real.sqrt (n : ℝ) * Real.sqrt (∑ i : Fin n, (d i) ^ 2) / R) ≤
      (((gridBall n (2 ^ n) R (fun _ => 0)) ∩ gridBall n (2 ^ n) R d).card : ℝ) /
        ((gridBall n (2 ^ n) R (fun _ => 0)).card : ℝ)

end Qatlib.Papers.QLattice03.MainResults
