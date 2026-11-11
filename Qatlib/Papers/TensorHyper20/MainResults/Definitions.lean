/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tensor hypercontraction resource formulas

Defines the arithmetic resource model for tensor hypercontraction in [LeeEtAl2021]. The
functions `prepareCost`, `selectCost`, and `reflectionCost` record integer Toffoli costs, while
`stepCost` and `totalToffoli` combine them with a natural-ceiling phase-estimation iteration
count.

The functions `logicalQubitsFormula` and `logicalQubitsParts` give compact and componentwise
logical-qubit counts used in the subsequent resource identities.

## Main statements

* `stepCost`: defines the expanded cost of one qubitization step.
* `totalToffoli`: multiplies the step cost by the phase-estimation iteration count.
* `logicalQubitsFormula`: records the compact logical-qubit formula.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults

/-- The natural-number expression `(a + b - 1) / b`, representing ceiling division when `b` is
positive. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- The natural ceiling logarithm to base two of `M + 1`. -/
def nOf (M : ℕ) : ℕ := Nat.clog 2 (M + 1)

/-- The register-size expression `2 * nOf M + 2 + ℵ`. -/
def mOf (M ℵ : ℕ) : ℕ := 2 * nOf M + 2 + ℵ

/-- The natural ceiling of `π * lam / (2 * eps)` used as the phase-estimation iteration count. -/
noncomputable def qpeIterations (lam eps : ℝ) : ℕ := ⌈Real.pi * lam / (2 * eps)⌉₊

/-- The integer Toffoli cost formula for state preparation, including its two QROM blocking
parameters. -/
def prepareCost (M br ℵ d ks1 ks2 : ℕ) : ℤ :=
  28 * (nOf M : ℤ) + 4 * (br : ℤ) - 18 + 2 * (nOf M : ℤ) ^ 2 + 2 * (ℵ : ℤ)
    + (ceilDiv d ks1 : ℤ) + (mOf M ℵ : ℤ) * ((ks1 : ℤ) - 1)
    + (ceilDiv d ks2 : ℤ) + (ks2 : ℤ)

/-- The integer Toffoli cost formula for SELECT, including the system size, precision, and two
QROM blocking parameters. -/
def selectCost (M N i kr1 kr2 : ℕ) : ℤ :=
  2 * (M : ℤ) + 4 * (N : ℤ) * (i : ℤ) - ((11 * N / 2 : ℕ) : ℤ)
    + (ceilDiv M kr1 : ℤ) + (ceilDiv N (2 * kr1) : ℤ) + (kr1 : ℤ)
    + (ceilDiv M kr2 : ℤ) + (kr2 : ℤ) - 2

/-- The integer reflection cost `2 * nOf M + ℵ + 4`. -/
def reflectionCost (M ℵ : ℕ) : ℤ := 2 * (nOf M : ℤ) + (ℵ : ℤ) + 4

/-- The expanded integer Toffoli cost of a qubitization step as a function of the preparation
and SELECT parameters. -/
def stepCost (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) : ℤ :=
  30 * (nOf M : ℤ) + 4 * (br : ℤ) - 16 + 2 * (nOf M : ℤ) ^ 2 + 3 * (ℵ : ℤ)
    + (ceilDiv d ks1 : ℤ) + (mOf M ℵ : ℤ) * ((ks1 : ℤ) - 1)
    + (ceilDiv d ks2 : ℤ) + (ks2 : ℤ)
    + 2 * (M : ℤ) + 4 * (N : ℤ) * (i : ℤ) - ((11 * N / 2 : ℕ) : ℤ)
    + (ceilDiv M kr1 : ℤ) + (ceilDiv N (2 * kr1) : ℤ) + (kr1 : ℤ)
    + (ceilDiv M kr2 : ℤ) + (kr2 : ℤ)

/-- The total integer Toffoli cost obtained by multiplying `stepCost` by `qpeIterations`. -/
noncomputable def totalToffoli (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) (lam eps : ℝ) : ℤ :=
  (qpeIterations lam eps : ℤ) * stepCost M N br ℵ i d ks1 ks2 kr1 kr2

/-- The compact natural-number logical-qubit formula, including the maximum of the two workspace
expressions. -/
def logicalQubitsFormula (N M I i d ℵ m ks1 : ℕ) : ℕ :=
  2 * Nat.clog 2 (I + 1) + N + 2 * nOf M + i + Nat.clog 2 d + ℵ + 5
    + max (m * ks1 + Nat.clog 2 (ceilDiv d ks1))
        (m + i * N / 2 + i - 2)

/-- The natural-number logical-qubit count expressed as the sum of its register contributions
and maximum workspace requirement. -/
def logicalQubitsParts (N M I i d ℵ m ks1 : ℕ) : ℕ :=
  (2 * Nat.clog 2 (I + 1) - 1) + N + 2 * nOf M + ℵ + 1 + 1 + 2 + 1 + 1
    + i + Nat.clog 2 d
    + max (m * ks1 + Nat.clog 2 (ceilDiv d ks1))
        (m + i * N / 2 + i - 2)

end Qatlib.Papers.TensorHyper20.MainResults
