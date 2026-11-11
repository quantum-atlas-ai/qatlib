/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Specification of rounded-numerator period recovery

`LegendreFullBoundary` states the continued-fraction recovery guarantee for samples with small
modular residue distance. It uses the nearest integer to Py/N as the numerator before reducing
modulo the period denominator, matching the corrected recovery interpretation of [Cornwell2014].

## Main statements

* `LegendreFullBoundary`: The modular recovery contract: under P² ≤ N and the stated
  residue-distance bound, the rounded numerator over P reduces to a convergent of y/N with
  positive denominator dividing P.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.LegendreWindow

/-- The modular recovery contract: under P² ≤ N and the stated residue-distance bound, the
rounded numerator over P reduces to a convergent of y/N with positive denominator dividing
P. -/
def LegendreFullBoundary : Prop :=
  ∀ (N P y : ℕ), 0 < N → 0 < P → P ^ 2 ≤ N → 0 < y → y < N →
    let r := (P * y) % N
    let d := min r (N - r)
    let a := (P * y) / N + if r ≤ N - r then 0 else 1
    d ≤ P / 2 →
    ∃ u b : ℕ, 0 < b ∧ Nat.Coprime u b ∧ b ∣ P ∧
      ((u : ℚ) / b = (a : ℚ) / P) ∧
      ∃ n : ℕ, (u : ℚ) / b = ((y : ℝ) / N).convergent n

end Qatlib.Concepts.AmpTransform.LegendreWindow
