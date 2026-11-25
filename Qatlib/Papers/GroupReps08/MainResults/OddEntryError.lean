/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroupReps08.MainResults.AlternatingGroup

@[expose] public section

/-!
# Error propagation for odd associator entries

The four matrix elements in the odd case of Section 8.3 enter with
coefficients one, i, i, and minus one, followed by the common factor
one half. The individual phase changes preserve the error norms.
-/

set_option autoImplicit false

open Qatlib.Papers.GroupReps08.MainResults.AlternatingGroup

namespace Qatlib.Papers.GroupReps08.MainResults

/-- Approximating the four entries within a quarter of the requested
tolerance suffices for the odd associator's half-weighted entry. -/
theorem alternating_odd_entry_error (a b c d ea eb ec ed : ℂ) (ε : ℝ)
    (hε : 0 < ε) (ha : ‖ea - a‖ ≤ ε / 4) (hb : ‖eb - b‖ ≤ ε / 4)
    (hc : ‖ec - c‖ ≤ ε / 4) (hd : ‖ed - d‖ ≤ ε / 4) :
    ‖(1 / 2 : ℂ) * (ea + Complex.I * eb + Complex.I * ec - ed) -
      (1 / 2 : ℂ) * (a + Complex.I * b + Complex.I * c - d)‖ ≤ ε := by
  have hb' : ‖Complex.I * eb - Complex.I * b‖ ≤ ε / 4 := by
    rwa [← mul_sub, norm_mul, Complex.norm_I, one_mul]
  have hc' : ‖Complex.I * ec - Complex.I * c‖ ≤ ε / 4 := by
    rwa [← mul_sub, norm_mul, Complex.norm_I, one_mul]
  have hd' : ‖-ed - (-d)‖ ≤ ε / 4 := by
    rwa [show -ed - (-d) = -(ed - d) by ring, norm_neg]
  simpa only [sub_eq_add_neg] using
    alternating_entry_error_eps a (Complex.I * b) (Complex.I * c) (-d)
      ea (Complex.I * eb) (Complex.I * ec) (-ed) ε hε ha hb' hc' hd'

end Qatlib.Papers.GroupReps08.MainResults
