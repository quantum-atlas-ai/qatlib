/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteCounts.SubsetIncidence

/-!
# Incidence and overlap of polynomial interaction supports

This module specializes finite-subset incidence and overlap estimates to interactions on `m + 1`
copies in the setting of [LloydEtAl2020]. The results give the fraction of supports containing
one copy and an upper bound for the fraction intersecting a fixed interaction support.

## Main statements

* `polynomial_incidence`: If `m + 1 ≤ n`, the fraction of size-`m + 1` supports containing a
  specified copy is `(m + 1) / n`.
* `polynomial_overlap_fraction`: For `1 ≤ m` and `m + 1 ≤ n`, the fraction of size-`m + 1`
  supports intersecting a fixed such support is at most `4 * m^2 / n`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
open Qatlib.Foundations.FiniteCounts.SubsetIncidence

/-- If `m + 1 ≤ n`, the fraction of size-`m + 1` supports containing a specified copy is `(m +
1) / n` [LloydEtAl2020]. -/
theorem polynomial_incidence (n m : ℕ) (a : Fin n) (hm : m+1≤n) :
    ((incidentSupports n (m+1) a).card:ℝ)/(Nat.choose n (m+1):ℝ)=((m:ℝ)+1)/n := by
  simpa only [Nat.cast_add,Nat.cast_one] using incidentSupports_fraction n (m+1) a (by omega) hm

/-- For `1 ≤ m` and `m + 1 ≤ n`, the fraction of size-`m + 1` supports intersecting a fixed such
support is at most `4 * m^2 / n` [LloydEtAl2020]. -/
theorem polynomial_overlap_fraction (n m : ℕ) (s : Finset (Fin n))
    (hm : 1 ≤ m) (hmn : m+1 ≤ n) (hs : s.card = m+1) :
    ((overlappingSupports n (m+1) s).card : ℝ) / (Nat.choose n (m+1) : ℝ) ≤
      4 * (m : ℝ)^2 / n := by
  have h := fixed_arity_overlap_fraction n (m+1) s (by omega) hmn hs
  simp only [Nat.cast_add, Nat.cast_one] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n))
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 ≤ ((m : ℝ)-1) * (3*m+1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
