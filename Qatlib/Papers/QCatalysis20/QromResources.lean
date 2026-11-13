/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.Definitions

/-!
# Conditional sparse lookup resource ledgers

This module records Toffoli counts and clean workspace requirements for sparse lookup using
externally supplied primitive costs. The computation and uncomputation ledgers share prefix and
arithmetic costs and differ in their flat-table query cost. See [VonBurgEtAl2021].

## Main statements

* `conditional_lookup_ledger`: The conditional computation and uncomputation ledgers have the
  stated Toffoli totals and maximum address workspace, and the clean and dirty budgets simplify
  to their displayed formulas.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QCatalysis20.QromResources

/-- A lookup resource entry recording required clean qubits, used dirty qubits, and a Toffoli
count. -/
structure LookupResourceOp where

  cleanRequired : ℕ

  dirtyUsed : ℕ

  toffoli : ℕ

/-- The sum of the Toffoli counts in a resource ledger. -/
def ledgerToffoli (l : List LookupResourceOp) : ℕ :=
  l.foldr (fun op acc => op.toffoli + acc) 0

/-- The maximum clean-qubit requirement among the operations in a resource ledger, with zero for
an empty ledger. -/
def ledgerClean (l : List LookupResourceOp) : ℕ :=
  l.foldr (fun op acc => max op.cleanRequired acc) 0

/-- The dirty-qubit budget `1 + b * (1 + lam)`. -/
def dirtyQubits (b lam : ℕ) : ℕ := 1 + b * (1 + lam)

/-- The maximum of the two ceiling-logarithmic address widths, plus `lam * b` clean qubits. -/
def conditionalCleanBudget (Q J b lam : ℕ) : ℕ :=
  max (Nat.clog 2 Q) (Nat.clog 2 J) + lam * b

/-- The computation ledger combining supplied prefix-query costs, two address adders with
overhead `c`, and the supplied flat-table query cost. -/
def conditionalComputationLedger (Q J _b _lam c DJ DUJ DQ : ℕ) : List LookupResourceOp :=
  [ ⟨Nat.clog 2 J, Nat.clog 2 Q, DJ + DUJ⟩,
    ⟨0, 0, 2 * Nat.clog 2 Q + c⟩,
    ⟨Nat.clog 2 Q, 0, DQ⟩ ]

/-- The uncomputation ledger combining supplied prefix-query costs, two address adders with
overhead `c`, and the supplied flat-table unquery cost. -/
def conditionalUncomputationLedger (Q J _b _lam c DJ DUJ DUQ : ℕ) : List LookupResourceOp :=
  [ ⟨Nat.clog 2 J, Nat.clog 2 Q, DJ + DUJ⟩,
    ⟨0, 0, 2 * Nat.clog 2 Q + c⟩,
    ⟨Nat.clog 2 Q, 0, DUQ⟩ ]

/-- The conditional computation and uncomputation ledgers have the stated Toffoli totals and
maximum address workspace, and the clean and dirty budgets simplify to their displayed
formulas. See [VonBurgEtAl2021]. -/
theorem conditional_lookup_ledger (Q J b lam c DJ DUJ DQ DUQ : ℕ) :
    ledgerToffoli (conditionalComputationLedger Q J b lam c DJ DUJ DQ) =
        DJ + DUJ + DQ + 2 * Nat.clog 2 Q + c ∧
    ledgerToffoli (conditionalUncomputationLedger Q J b lam c DJ DUJ DUQ) =
        DJ + DUJ + DUQ + 2 * Nat.clog 2 Q + c ∧
    ledgerClean (conditionalComputationLedger Q J b lam c DJ DUJ DQ) =
        max (Nat.clog 2 Q) (Nat.clog 2 J) ∧
    ledgerClean (conditionalUncomputationLedger Q J b lam c DJ DUJ DUQ) =
        max (Nat.clog 2 Q) (Nat.clog 2 J) ∧
    conditionalCleanBudget Q J b lam =
        max (Nat.clog 2 Q) (Nat.clog 2 J) + lam * b ∧
    dirtyQubits b lam = 1 + b * (1 + lam) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [ledgerToffoli, conditionalComputationLedger, List.foldr_cons, List.foldr_nil]
    omega
  · simp only [ledgerToffoli, conditionalUncomputationLedger, List.foldr_cons, List.foldr_nil]
    omega
  · simp only [ledgerClean, conditionalComputationLedger, List.foldr_cons, List.foldr_nil]
    rw [max_eq_left (Nat.zero_le _), max_eq_right (Nat.zero_le _), max_comm]
  · simp only [ledgerClean, conditionalUncomputationLedger, List.foldr_cons, List.foldr_nil]
    rw [max_eq_left (Nat.zero_le _), max_eq_right (Nat.zero_le _), max_comm]
  · rfl

end Qatlib.Papers.QCatalysis20.QromResources
