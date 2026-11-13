/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem51

/-!
# BQP completeness of the Jones promise problem

The theorems `theorem11_bqpHard` and `theorem11_bqpComplete` assemble the parameter-dependent
braid encoding and Jones-value scaling assumptions into the conclusion associated with Theorem
1.1 of [AharonovArad2011]. The completeness statement additionally requires the supplied BQP
membership hypothesis.

## Main statements

* `theorem11_bqpHard`: BQP hardness from a polynomially bounded parameter and an encoding error
  at most `1 / 20`.
* `theorem11_bqpComplete`: BQP completeness after adding membership in BQP.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- Under the parameter, encoding, scaling, and error assumptions, BQP membership of the Jones
promise problem implies its BQP completeness [AharonovArad2011, Theorem
1.1][AharonovArad2011]. -/
theorem theorem11_bqpComplete (p : ℕ → ℕ) (hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n))
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20)
    (hAJL : InBQP (jonesPromise n V (deltaScale (p n) n))) :
    BQPComplete (jonesPromise n V (deltaScale (p n) n)) :=
  ⟨theorem51_bqpHard p hp n hk4 hk6 V E (theorem51_scale_pos p n hk4) hscale heps,
    hAJL⟩

/-- A braid encoding with error at most `1 / 20` and the stated Jones-value scaling yields BQP
hardness for a polynomially bounded parameter greater than four and different from six
[AharonovArad2011, Theorem 1.1][AharonovArad2011]. -/
theorem theorem11_bqpHard (p : ℕ → ℕ) (hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n))
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale (p n) n)) :=
  theorem51_bqpHard p hp n hk4 hk6 V E (theorem51_scale_pos p n hk4) hscale heps

end Qatlib.Papers.BQPJonesPoly06.MainResults
