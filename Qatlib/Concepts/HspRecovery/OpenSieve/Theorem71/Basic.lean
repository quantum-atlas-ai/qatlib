/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# Abelian hidden-shift recovery endpoints

This module collects abelian hidden-shift recovery results in the setting of Theorem 7.1 of
[Kuperberg2005]. For cyclic groups of power-of-two order, it transports a hidden shift to a
dihedral reflection oracle, excludes incorrect outputs, and bounds failure.

For general finite abelian groups, a supplied difference basis yields the stated exact recovery
mass. The module also records a corresponding resource ledger and a subexponential query bound
for the power-of-two case.

## Main statements

* `theorem71_pow2_zero_error`: incorrect shifts have zero mass.
* `theorem71_pow2_failure_bound`: failure is bounded by `descentFailureBound`.
* `theorem71_general_abelian_recovery`: recovery using a difference basis.
* `theorem71_query_growth`: the power-of-two query growth bound.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Theorem71

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve
open Qatlib.Concepts.HspRecovery.ReductionCore

/-- A hidden shift over `ZMod (2 ^ n)` gives a dihedral oracle hiding the reflection with the
same shift parameter. -/
theorem theorem71_pow2_transport (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    DihedralReflectionHides (2 ^ n) (shiftToDihedralOracle f g) s :=
  walkGoal_abelian_pow2_transport n f g s h

/-- Under the hidden-shift promise, every candidate different from the true shift has zero mass
in the power-of-two recovery run [Kuperberg2005]. -/
theorem theorem71_pow2_zero_error (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) (u : ZMod (2 ^ n)) (hu : u ≠ s) :
    abelianShiftRun n S f g (some u) = 0 :=
  walkGoal_abelian_pow2_wrong_zero n f g s h u hu

/-- Under the hidden-shift promise, the mass of the true shift equals one minus the failure mass
in the power-of-two recovery run [Kuperberg2005]. -/
theorem theorem71_pow2_success_mass (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    abelianShiftRun n S f g (some s) = 1 - abelianShiftRun n S f g none :=
  walkGoal_abelian_pow2_success_mass n f g s h

/-- Under the hidden-shift promise, the power-of-two recovery run's failure mass is at most
`ENNReal.ofReal (descentFailureBound n)` [Kuperberg2005]. -/
theorem theorem71_pow2_failure_bound (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    abelianShiftRun n S f g none ≤ ENNReal.ofReal (descentFailureBound n) :=
  walkGoal_abelian_pow2_failure_bound n f g s h

/-- Every finite abelian group possesses a finite difference basis [Kuperberg2005]. -/
theorem theorem71_difference_basis_exists (A : Type) [AddCommGroup A] [Fintype A] :
    ∃ D : Finset A, AbelianDifferenceBasis D :=
  walkGoal_abelian_difference_basis_exists A

/-- A list forming a difference basis gives zero mass to incorrect shifts and mass at least one
to the true shift under the hidden-shift promise [Kuperberg2005]. -/
theorem theorem71_general_abelian_recovery {A S : Type} [AddCommGroup A] [Fintype A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (s : A) (h : HiddenShift f g s)
    (D : List A) (hD : AbelianDifferenceBasis D.toFinset) :
    (∀ u : A, u ≠ s → abelianBasisShiftRun f g D (some u) = 0) ∧
      ENNReal.ofReal 1 ≤ abelianBasisShiftRun f g D (some s) :=
  walkGoal_abelian_shift_recovery f g s h D hD

/-- The abelian shift ledger has the specified sample and query counts, comparison and
bit-operation bounds, integer size, and positive workspace [Kuperberg2005]. -/
theorem theorem71_abelian_ledger {A : Type} (D : List A) (bits : ℕ) :
    (abelianShiftLedger D bits).samples = abelianShiftQueryCount D ∧
      (abelianShiftLedger D bits).queries = abelianShiftQueryCount D ∧
      abelianShiftCompareCount D ≤ (abelianShiftLedger D bits).comparisons ∧
      sortBitOps (abelianShiftLedger D bits).samples (abelianShiftLedger D bits).integerBits
        ≤ (abelianShiftLedger D bits).bitOps ∧
      (abelianShiftLedger D bits).integerBits = bits ∧
      (abelianShiftLedger D bits).workspaceBits = workspaceBits (max (2 * D.length) 1) bits ∧
      0 < (abelianShiftLedger D bits).workspaceBits :=
  walkGoal_abelian_ledger_account D bits

/-- The power-of-two abelian shift query count is bounded by `C * 2 ^ (c * sqrt (labelBits (2 ^
n)))` for some positive real constants `C` and `c` [Kuperberg2005]. -/
theorem theorem71_query_growth :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (abelianShiftQueries n : ℝ) ≤
        C * (2 : ℝ) ^ (c * Real.sqrt (labelBits (2 ^ n))) :=
  walkGoal_abelian_pow2_query_growth

end Qatlib.Concepts.HspRecovery.OpenSieve.Theorem71
