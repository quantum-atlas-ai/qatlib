/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

theorem one_div_two_pow_le (q : ℚ) (hq : 0 < q) :
    ∃ p : ℕ, (1 : ℚ) / 2 ^ p ≤ q := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / q) (show (1 : ℚ) < 2 by norm_num)
  refine ⟨n, ?_⟩
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  have h1 : (1 : ℚ) < 2 ^ n * q := (div_lt_iff₀ hq).mp hn
  rw [div_le_iff₀ h2n, mul_comm]
  exact le_of_lt h1

theorem one_div_two_pow_mono {p q : ℕ} (hpq : p ≤ q) :
    (1 : ℚ) / 2 ^ q ≤ 1 / 2 ^ p :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hpq)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
