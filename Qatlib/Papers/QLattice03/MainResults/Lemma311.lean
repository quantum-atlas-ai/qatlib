/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Cor39

/-!
# Uniform grid ball amplitudes and approximation

`uniformBallAmplitude` assigns the reciprocal square root of the grid ball cardinality on that
ball and zero elsewhere. The proposition `ballSuperposition_efficient` specifies a squared
amplitude approximation bound over the grid ball for an indexed family of amplitudes. See
[Regev2004] for the paper context.

## Main statements

* `uniformBallAmplitude`: The amplitude equal to the reciprocal square root of the
  origin-centered grid ball cardinality on that ball, and zero outside it.
* `ballSuperposition_efficient`: The proposition that a family of amplitudes has squared error
  less than `1 / n^(2c)` on every specified origin-centered grid ball with grid parameter `2^n`,
  positive dimension, and radius at least one.

## References

* [Regev, 2004][Regev2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The amplitude equal to the reciprocal square root of the origin-centered grid ball
cardinality on that ball, and zero outside it. -/
noncomputable def uniformBallAmplitude (n : ℕ) (L : ℕ) (R : ℝ) : (Fin n → ℤ) → ℂ :=
  fun x =>
    if x ∈ gridBall n L R (fun _ => 0) then
      (((Real.sqrt ((gridBall n L R (fun _ => 0)).card : ℝ))⁻¹ : ℝ) : ℂ)
    else 0

/-- The proposition that a family of amplitudes has squared error less than `1 / n^(2c)` on
every specified origin-centered grid ball with grid parameter `2^n`, positive dimension, and
radius at least one. -/
def ballSuperposition_efficient (c : ℝ) (hc : 0 < c) : Prop :=
  ∃ (etat : ∀ n : ℕ, (Fin n → ℤ) → ℂ), ∀ (n : ℕ), 0 < n → ∀ (R : ℝ), 1 ≤ R →
    (∑ x ∈ gridBall n (2 ^ n) R (fun _ => 0),
        ‖etat n x - uniformBallAmplitude n (2 ^ n) R x‖ ^ 2) <
      1 / (n : ℝ) ^ (2 * c)

end Qatlib.Papers.QLattice03.MainResults
