/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation

/-!
# A language and promise from spectral forrelation

This module defines membership for families of Boolean oracles using the spectral forrelation
threshold `59 / 100`. It also defines a promise requiring every register size to have spectral
value at least `59 / 100` or at most `57 / 100`. The two thresholds leave a gap for subsequent
verifier and separation arguments.

The underlying quantity is the squared operator norm of a restricted Hadamard transform, in the
finite-dimensional framework of [Watrous2018].

## Key declarations

* `spectralLangMem` is the high-threshold membership predicate at a given size.
* `spectralPromiseComplete` requires one of the two threshold alternatives at every size.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib
set_option autoImplicit false

/-- Membership at size `n` for the oracle families `S` and `U`, defined by spectral forrelation
at least `59 / 100`. -/
def spectralLangMem (S U : ∀ n, Reg n → Bool) (n : ℕ) : Prop :=
  59 / 100 ≤ spectralForrelation n (S n) (U n)

/-- The promise that, at every size, the oracle families have spectral forrelation at least `59
/ 100` or at most `57 / 100`. -/
def spectralPromiseComplete (S U : ∀ n, Reg n → Bool) : Prop :=
  ∀ n : ℕ,
    59 / 100 ≤ spectralForrelation n (S n) (U n) ∨
      spectralForrelation n (S n) (U n) ≤ 57 / 100

end Qatlib.Concepts.WalshMoment.Forrelation
