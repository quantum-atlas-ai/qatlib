/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogPrimePowerDivisibilityAnsw

/-!
# Divisibility theorem for discrete-logarithm recovery

This module reexports the proved contract `DlogPrimePowerDivisibility`. Under prime `p ≥ 3` and
`p < q < 2 * p`, it gives injectivity of the scaled coefficients on small-residue coordinates,
their range bounds, and the corresponding counts for divisors of `p - 1`.

The theorem supplies the coefficient-divisibility bounds used in the modular recovery setting of
[Shor1997], with the corrected sampling-range hypothesis.

## Main statements

* `DlogPrimePowerDivisibility_proof`: the corrected coefficient and divisibility-count theorem.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

/-- Reexports the corrected small-residue injectivity, range, and divisibility counting bounds
for prime `p ≥ 3` and `p < q < 2 * p` in the discrete-logarithm recovery analysis
[Shor1997]. -/
theorem DlogPrimePowerDivisibility_proof : DlogPrimePowerDivisibility := dlogPrimePowerDivisibility
end Qatlib.Concepts.PeriodSampling.DlogDivBudget
