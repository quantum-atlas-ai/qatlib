/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Dyadic precision for rational budgets

Every positive rational budget bounds some reciprocal power of two from above, and increasing
the exponent decreases this dyadic quantity. The two lemmas support precision selection in
finite-accuracy mixture constructions, including the quantum optimization setting of
[BrandaoSvore2017].

## Main statements

* `one_div_two_pow_le`: a sufficiently small dyadic precision fits any positive rational budget.
* `one_div_two_pow_mono`: reciprocal powers of two decrease with their natural exponent.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

/-- Every positive rational `q` bounds some dyadic reciprocal 1/2^p from above. -/
theorem one_div_two_pow_le (q : ℚ) (hq : 0 < q) :
    ∃ p : ℕ, (1 : ℚ) / 2 ^ p ≤ q := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / q) (show (1 : ℚ) < 2 by norm_num)
  refine ⟨n, ?_⟩
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  have h1 : (1 : ℚ) < 2 ^ n * q := (div_lt_iff₀ hq).mp hn
  rw [div_le_iff₀ h2n, mul_comm]
  exact le_of_lt h1

/-- If `p ≤ q`, then 1/2^q ≤ 1/2^p in the rationals. -/
theorem one_div_two_pow_mono {p q : ℕ} (hpq : p ≤ q) :
    (1 : ℚ) / 2 ^ q ≤ 1 / 2 ^ p :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hpq)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
