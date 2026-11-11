/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma47

/-!
# R3 output and estimation specification

The function `r3Routine` returns the pair `(q, 0)`. The separate proposition
`lemma49_R3_estimates_qprime_d` specifies an interval for its first output and congruence and
absolute error conditions for its second output. See [Regev2004] for the paper context.

## Main statements

* `r3Routine`: The routine returning the pair `(q, 0)` for the supplied parameters.
* `lemma49_R3_estimates_qprime_d`: The proposition that the R3 output has first coordinate
  between `q` and `logPow N cm * q`, and that its second coordinate differs from the
  corresponding multiple of `d.val` by a multiple of `N` of absolute value at most `N / logPow N
  (cm + 1)`.

## References

* [Regev, 2004][Regev2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The routine returning the pair `(q, 0)` for the supplied parameters. -/
noncomputable def r3Routine (cm : ℕ) (N : ℕ) [NeZero N] (q : ℕ) (d : ZMod N) : ℕ × ℤ :=
  (q, 0)

/-- The proposition that the R3 output has first coordinate between `q` and `logPow N cm * q`,
and that its second coordinate differs from the corresponding multiple of `d.val` by a
multiple of `N` of absolute value at most `N / logPow N (cm + 1)`. -/
def lemma49_R3_estimates_qprime_d
    (cm : ℕ) (hcm : 3 ≤ cm) (N : ℕ) [NeZero N] (q : ℕ) (hq : 0 < q)
    (hqN : q * logPow N cm < N) (d : ZMod N) : Prop :=
  (let r := r3Routine cm N q d
   q ≤ r.1 ∧ r.1 ≤ logPow N cm * q ∧
     ∃ k : ℤ, r.2 - (r.1 : ℤ) * (d.val : ℤ) = k * (N : ℤ) ∧
       |r.2 - (r.1 : ℤ) * (d.val : ℤ)| ≤ (N : ℤ) / (logPow N (cm + 1) : ℤ))

end Qatlib.Papers.QLattice03.MainResults
