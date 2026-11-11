/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem3CorrectedStat
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary21CorrectedAfas

/-!
# Corrected real amplitude growth estimate

`theorem3Corrected` proves a strict increase greater than 1/(2√N) in the distinguished amplitude
after a marked phase flip and diffusion. The statement requires N ≥ 8, positive normalized real
amplitudes, and marked amplitude below 1/√2, and also proves positivity of the ordinary update.

For the mathematical background, see [Grover1997].

## Main statements

* `theorem3Corrected`: For N ≥ 8 and positive normalized real amplitudes with k < 1/√2, the
  update from (−k, l) increases the distinguished amplitude over k by more than 1/(2√N) and
  leaves the ordinary amplitude positive.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- If 0 < k < 1/√2, then k² < 1/2. -/
private theorem marked_square_lt_half {k : ℝ} (hk0 : 0 < k)
    (hk : k < 1 / Real.sqrt 2) : k ^ 2 < 1 / 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hks : k * Real.sqrt 2 < 1 := (lt_div_iff₀ hs).mp hk
  have hprod : (k * Real.sqrt 2) * (k * Real.sqrt 2) < (1 : ℝ) * 1 :=
    mul_lt_mul hks (le_of_lt hks) (by positivity) (by norm_num)
  have hsq : (k * Real.sqrt 2) ^ 2 < 1 := by nlinarith only [hprod]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  linarith

/-- For N ≥ 8 and positive normalized real amplitudes with k < 1/√2, the update from (−k, l)
increases the distinguished amplitude over k by more than 1/(2√N) and leaves the ordinary
amplitude positive. See [Grover1997]. -/
theorem theorem3Corrected : Theorem3Corrected := by
  intro N hN k l hk0 hk hl hmass
  have hn : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hn_ne : (N : ℝ) ≠ 0 := ne_of_gt hn0
  have hk2 := marked_square_lt_half hk0 hk
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  change k ^ 2 + ((N : ℝ) - 1) * l ^ 2 = 1 at hmass
  have hmass_lower : (1 : ℝ) / 2 < ((N : ℝ) - 1) * l ^ 2 := by
    linarith
  have hmass_mul := mul_lt_mul_of_pos_left hmass_lower hn1
  have ht0 : 0 < ((N : ℝ) - 1) * l := mul_pos hn1 hl
  have ht2 : ((N : ℝ) - 1) / 2 < (((N : ℝ) - 1) * l) ^ 2 := by
    nlinarith only [hmass_mul]
  have hroot0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hn0
  have hroot_sq : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (le_of_lt hn0)
  have hweighted : Real.sqrt (N : ℝ) / 2 < ((N : ℝ) - 1) * l := by
    nlinarith
  have hkroot : k < Real.sqrt (N : ℝ) / 4 := by
    apply (sq_lt_sq₀ hk0.le (show 0 ≤ Real.sqrt (N : ℝ) / 4 by positivity)).mp
    nlinarith
  have hgap : Real.sqrt (N : ℝ) / 4 < ((N : ℝ) - 1) * l - k := by
    linarith
  have hgain_formula : distinguishedAfter N (-k) l - k =
      2 * (((N : ℝ) - 1) * l - k) / N := by
    unfold distinguishedAfter
    field_simp
    ring
  have hthreshold : 1 / (2 * Real.sqrt (N : ℝ)) =
      2 * (Real.sqrt (N : ℝ) / 4) / N := by
    apply (div_eq_div_iff (by positivity) hn_ne).2
    nlinarith only [hroot_sq]
  constructor
  · rw [hgain_formula, hthreshold]
    exact div_lt_div_of_pos_right (by linarith) hn0
  · have hkl : k < Real.sqrt (N : ℝ) * l := by
      apply (sq_lt_sq₀ hk0.le (mul_pos hroot0 hl).le).mp
      rw [mul_pow, hroot_sq]
      nlinarith
    have hratio : |(-k) / l| < Real.sqrt (N : ℝ) := by
      rw [neg_div, abs_neg, abs_of_pos (div_pos hk0 hl)]
      exact (div_lt_iff₀ hl).mpr hkl
    exact (corollary2_1Corrected N hN (-k) l (by linarith) hl hratio).2

end Qatlib.Concepts.SearchStopping.KnownCount
