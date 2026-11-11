/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteCounts.ExceptionalBits.Count
import Mathlib.GroupTheory.OrderOfElement

/-!
# Exceptional events in additive-group prefix runs

This module constructs the actual additive-group recurrence `prefixRun` starting from `a • P`.
It identifies `nativeExceptionalSet`, defined by equality of group elements at selected bits,
with the modular scalar event set using `addOrderOf P`.

The theorem `native_exceptional_card_le` transfers the scalar count to this recurrence under the
stated order-width condition. The scalar-multiplication setting is motivated by
[RoettelerEtAl2017].

## Main statements

* `prefixRun_eq`: The prefix run at step `i` equals `(a + prefixValue k i) • P`.
* `nativeExceptionalSet_eq`: The actual exceptional set equals the scalar congruence set with
  modulus `addOrderOf P`.
* `native_exceptional_card_le`: If `n ≥ 1`, `1 ≤ a < addOrderOf P`, and `2^(n-1) ≤ addOrderOf
  P`, the actual exceptional set has cardinality at most `2^(n - Nat.clog 2 a) + 8`.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Foundations.FiniteCounts.ExceptionalBits

variable {G : Type*} [AddCommGroup G]

/-- The additive-group prefix run starting at `a • P` and adding the selected multiples `2^i •
P`. -/
def prefixRun {n : ℕ} (P : G) (a : ℕ) (k : Fin (n+1) → Bool) : ℕ → G
  | 0 => a • P
  | i+1 => prefixRun P a k i + (bitAt k i * 2^i) • P

/-- The prefix run at step `i` equals `(a + prefixValue k i) • P`. -/
theorem prefixRun_eq {n : ℕ} (P : G) (a : ℕ) (k : Fin (n+1) → Bool) (i : ℕ) :
    prefixRun P a k i = (a + prefixValue k i) • P := by
  induction i with
  | zero => simp [prefixRun, prefixValue]
  | succ i ih =>
    simp only [prefixRun, ih, prefixValue, Finset.sum_range_succ]
    rw [← add_nsmul]
    congr 1
    omega

/-- The bit strings with a true bit at a step where the prefix run equals the corresponding
doubling multiple of `P`. -/
noncomputable def nativeExceptionalSet {n : ℕ} (P : G) (a : ℕ) :
    Finset (Fin (n+1) → Bool) := by
  classical
  exact Finset.univ.filter (fun k => ∃ i : Fin (n+1),
    k i = true ∧ prefixRun P a k i = (2^i.val) • P)

/-- The actual exceptional set equals the scalar congruence set with modulus `addOrderOf P`. -/
theorem nativeExceptionalSet_eq {n : ℕ} (P : G) (a : ℕ) :
    nativeExceptionalSet (n:=n) P a = ExceptionalDoublingScalars n a (addOrderOf P) := by
  classical
  ext k
  simp only [nativeExceptionalSet, ExceptionalDoublingScalars, Finset.mem_filter,
    Finset.mem_univ, true_and, prefixRun_eq, nsmul_inj_mod]

/-- If `n ≥ 1`, `1 ≤ a < addOrderOf P`, and `2^(n-1) ≤ addOrderOf P`, the actual exceptional set
has cardinality at most `2^(n - Nat.clog 2 a) + 8`. -/
theorem native_exceptional_card_le {n a : ℕ} (P : G) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (har : a < addOrderOf P) (hwidth : 2^(n-1) ≤ addOrderOf P) :
    (nativeExceptionalSet (n:=n) P a).card ≤ 2^(n-Nat.clog 2 a) + 8 := by
  rw [nativeExceptionalSet_eq]
  exact exceptionalDoubling_card_le_eight n a (addOrderOf P) hn ha har hwidth

end Qatlib.Foundations.FiniteCounts.ExceptionalBits
