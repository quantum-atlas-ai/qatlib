/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Two-dimensional discrete-logarithm sampling definitions

Defines `dlogTwoDimState` and the centered residue, phase, and good-pair predicates used to
analyze its output. The integer `dlogCprime` and the condition `dlogGoodPair` encode the
rounding relations in the discrete-logarithm algorithm of [Shor1997].

## Main statements

* `dlogTwoDimState`: Defines the two-dimensional Fourier sampling state.
* `dlogGoodPair`: Combines phase proximity with the small-residue condition.
* `dlogCprime`: Defines the integer extracted from the first coordinate.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib

/-- Chooses the ordinary residue of `z` modulo `q` when it is at most `q / 2`, and otherwise
subtracts `q`. -/
def centeredResidue (q : ℤ) (z : ℤ) : ℤ :=
  let r := z % q
  if r ≤ q / 2 then r else r - q

/-- The two-dimensional discrete-logarithm state sums off-grid Fourier phases over exponent
pairs with the prescribed group output, scaled by the reciprocal of `p - 1`. -/
def dlogTwoDimState (p q : ℕ) (g x : ZMod p) :
    QState (Fin q × Fin q × ZMod p) :=
  fun t =>
    ((p - 1 : ℕ) : ℂ)⁻¹ * ∑ a : Fin (p - 1), ∑ b : Fin (p - 1),
      if g ^ (a : ℕ) * x ^ (p - 1 - (b : ℕ)) = t.2.2 then
        offGridPhase q ((a : ℕ) / q) t.1 * offGridPhase q ((b : ℕ) / q) t.2.1
      else 0

/-- The small-residue condition requires the absolute centered residue of `c * (p - 1)` modulo
`q` to be at most `(q : ℝ) / 12`. -/
def dlogSmallResidue (p q : ℕ) (c : Fin q) : Prop :=
  |(centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ)) : ℤ)| ≤ (q : ℝ) / 12

/-- The corrected real phase `r * c + d` minus `r / (p - 1)` times the centered residue of `c *
(p - 1)` modulo `q`. -/
noncomputable def dlogT (p q r : ℕ) (c d : Fin q) : ℝ :=
  (r * (c : ℕ) + (d : ℕ) : ℝ) -
    (r : ℝ) / ((p - 1 : ℕ) : ℝ) *
      ((centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ)) : ℤ) : ℝ)

/-- A good pair has corrected phase within one half of an integer multiple of `q` and satisfies
the small-residue condition. -/
def dlogGoodPair (p q r : ℕ) (c d : Fin q) : Prop :=
  (∃ j : ℤ, |dlogT p q r c d - (j : ℝ) * (q : ℝ)| ≤ 1 / 2) ∧
    dlogSmallResidue p q c

/-- The integer quotient obtained by subtracting the centered residue from `c * (p - 1)` and
dividing by `q`. -/
def dlogCprime (p q : ℕ) (c : Fin q) : ℤ :=
  (((c : ℕ) * (p - 1) : ℤ) -
    centeredResidue (q : ℤ) (((c : ℕ) * (p - 1) : ℤ))) / (q : ℤ)

end Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
