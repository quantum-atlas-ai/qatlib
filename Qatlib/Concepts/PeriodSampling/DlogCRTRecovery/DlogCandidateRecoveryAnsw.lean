/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecoveryStat

/-!
# Integer candidates from good discrete-logarithm pairs

This module proves the integer-candidate recovery contract `DlogCandidateRecovery` for good
Fourier-sampling pairs. Centered-residue divisibility gives the exact integer identity for
`dlogCprime`, which rewrites `dlogT` and produces a rounding candidate satisfying the recovery
congruence.

The argument concerns the rounding and modular recovery step of the discrete-logarithm algorithm
in [Shor1997]. The formal conclusion includes the stated candidate existence under a coprimality
hypothesis.

## Main statements

* `dlog_centered_difference_dvd`: divisibility of the difference from a centered residue.
* `dlog_cprime_integrality`: the exact integer formula for the scaled first coordinate.
* `dlogT_cprime_formula`: the corresponding real expression for the good-pair phase.
* `dlogCandidateRecovery`: existence of the rounding and exponent candidates.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
open scoped Classical
set_option autoImplicit false

/-- An integer differs from its centered residue modulo `q` by a multiple of `q`. -/
theorem dlog_centered_difference_dvd (q z : ℤ) : q ∣ z-centeredResidue q z := by
  have he : z-z%q = q*(z/q) := by
    have hh := Int.emod_add_mul_ediv z q
    linarith
  unfold centeredResidue
  (try dsimp only)
  split
  · exact ⟨z/q, he⟩
  · refine ⟨z/q+1, ?_⟩
    rw [mul_add, mul_one]
    linarith

/-- Multiplying `dlogCprime p q c` by `q` gives `c * (p - 1)` minus its centered residue modulo
`q`. -/
theorem dlog_cprime_integrality (p q : ℕ) (c : Fin q) :
    dlogCprime p q c * (q : ℤ) = ((c : ℕ)*(p-1) : ℤ) -
      centeredResidue (q : ℤ) ((c : ℕ)*(p-1) : ℤ) := by
  exact Int.ediv_mul_cancel (dlog_centered_difference_dvd _ _)

/-- For `1 < p`, the quantity `dlogT` equals `d + r * dlogCprime p q c * q / (p - 1)` over the
reals. -/
theorem dlogT_cprime_formula (p q r : ℕ) (hp : 1 < p) (c d : Fin q) :
    dlogT p q r c d = (d : ℕ) +
      (r : ℝ)*(dlogCprime p q c : ℝ)*(q : ℝ)/((p-1 : ℕ) : ℝ) := by
  have hm : (0 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (by omega : 0 < p-1)
  have hi : (dlogCprime p q c : ℝ)*(q : ℝ) =
      (c : ℕ)*((p-1 : ℕ) : ℝ) -
        (centeredResidue (q : ℤ) ((c : ℕ)*(p-1) : ℤ) : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one, Int.cast_one] using
      congrArg (fun z : ℤ => (z : ℝ)) (dlog_cprime_integrality p q c)
  have hc : (centeredResidue (q : ℤ) ((c : ℕ)*(p-1) : ℤ) : ℝ) =
      (c : ℕ)*((p-1 : ℕ) : ℝ) - (dlogCprime p q c : ℝ)*(q : ℝ) := by linarith
  rw [dlogT, hc]
  field_simp [ne_of_gt hm]
  ring

/-- For prime `p ≥ 3`, `p < q`, and `r < p - 1`, a good pair yields an integer within one half
of `d * (p - 1) / q` satisfying the recovery congruence, together with the stated candidate
existence under coprimality [Shor1997]. -/
theorem dlogCandidateRecovery : DlogCandidateRecovery := by
  intro p q r _hprime hp hpq hr c d hgood
  have hm : (0 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (by omega : 0 < p-1)
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmq : ((p-1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : p-1 ≤ q)
  obtain ⟨j, hj⟩ := hgood.1
  let dp : ℤ := j*((p-1 : ℕ) : ℤ) - (r : ℤ)*dlogCprime p q c
  have hs : (dp : ℝ) - (d : ℕ)*((p-1 : ℕ) : ℝ)/(q : ℝ) =
      -(((p-1 : ℕ) : ℝ)/(q : ℝ))*(dlogT p q r c d-(j : ℝ)*(q : ℝ)) := by
    dsimp [dp]
    push_cast
    rw [dlogT_cprime_formula p q r (by omega) c d]
    field_simp [ne_of_gt hm, ne_of_gt hq]
    ring
  have hnear : |(dp : ℝ) - (d : ℕ)*((p-1 : ℕ) : ℝ)/(q : ℝ)| ≤ 1/2 := by
    rw [hs, abs_mul, abs_neg, abs_of_pos (div_pos hm hq)]
    calc
      _ ≤ (((p-1 : ℕ) : ℝ)/(q : ℝ))*(1/2) :=
        mul_le_mul_of_nonneg_left hj (le_of_lt (div_pos hm hq))
      _ ≤ 1/2 := by
        have hh : ((p-1 : ℕ) : ℝ)/(q : ℝ) ≤ 1 := (div_le_one hq).2 hmq
        linarith
  have hd : ((p-1 : ℕ) : ℤ) ∣ dp + (r : ℤ)*dlogCprime p q c := by
    refine ⟨j, ?_⟩
    dsimp [dp]
    ring
  have hmod : (dp+(r : ℤ)*dlogCprime p q c) % ((p-1 : ℕ) : ℤ) = 0 :=
    Int.emod_eq_zero_of_dvd hd
  have hmc : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  refine ⟨dp, by simpa only [hmc] using hnear, hmod, ?_⟩
  intro _hcoprime
  exact ⟨r, hr, by simpa only [add_comm] using hmod, Int.ModEq.refl r⟩

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
