/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.PairedPrepareAccess
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Quan
import Qatlib.Papers.QLinearODE17.Structure.Theorem9Quan
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux2

/-!
# Resource and finite-digit definitions for ODE construction

This module defines the sparse access quantities, Taylor right-hand-side support, Section 7
parameters, and resource ledgers used in the ODE construction associated with
[BerryEtAl2017ODE]. The query and gate count functions give explicit natural-number expressions
for the chosen parameters.

`FiniteDigit` represents a signed dyadic value, with `roundFiniteDigit` obtained by taking the
floor of a scaled magnitude. The module also defines the fixed and order-dependent constants
used to bound Taylor transition polynomials.

## Main statements

* `Section7Parameters`: Padding, time-step, Taylor-order, and precision parameters.
* `eq112QueryCount`: The explicit query count ledger.
* `FiniteDigit`: Signed dyadic data and its real interpretation.
* `smallOrderUniformConstant`: An order-dependent Taylor bound.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Papers.QLinearODE17.StructureCore

set_option autoImplicit false

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib
open Matrix
open scoped Classical Matrix.Norms.L2Operator BigOperators

/-- The finite set of column indices with a nonzero entry in row `o` of `A`. -/
noncomputable def sparsePositions {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (o : O) : Finset I :=
  Finset.univ.filter fun i => A o i ≠ 0

/-- The sum of the norms of the entries in row `o` of `A`. -/
noncomputable def sparseRowMass {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (o : O) : ℝ :=
  ∑ i, ‖A o i‖

/-- The sum of the norms of the entries in column `i` of `A`. -/
noncomputable def sparseColumnMass {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (i : I) : ℝ :=
  ∑ o, ‖A o i‖

/-- The number of nonzero positions in row `o` of `A`. -/
noncomputable def sparseRowAccessCost {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (o : O) : ℕ :=
  (sparsePositions A o).card

/-- The number of nonzero positions in column `i` of `A`. -/
noncomputable def sparseColumnAccessCost {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (i : I) : ℕ :=
  (Finset.univ.filter fun o => A o i ≠ 0).card

/-- The set containing label zero and each first Taylor-step label i(k + 1) + 1 for i < m. -/
def taylorRHSSupport (m k _p : ℕ) : Finset ℕ :=
  {0} ∪ (Finset.range m).image (fun i => i * (k + 1) + 1)

/-- The preparation column count m + 1. -/
def taylorPreparedColumns (m : ℕ) : ℕ := m + 1

/-- The natural-number parameters `p`, `m`, `k`, and `kq` for the Section 7 construction. -/
structure Section7Parameters where

  p : ℕ

  m : ℕ

  k : ℕ

  kq : ℕ
  deriving DecidableEq, Repr

/-- The padding count 4^kq - ⌈77mg²⌉ - 1, with subtraction taken in the natural numbers. -/
noncomputable def section7PaddingCount (kq m : ℕ) (g : ℝ) : ℕ :=
  4 ^ kq - Nat.ceil (77 * (m : ℝ) * g ^ 2) - 1

/-- The Taylor-system label count m(k + 1) + p + 1 for the given parameters. -/
def section7LabelCount (pars : Section7Parameters) : ℕ :=
  pars.m * (pars.k + 1) + pars.p + 1

/-- The count m(k + 1) of Taylor-step labels before padding. -/
def section7StepCount (pars : Section7Parameters) : ℕ :=
  pars.m * (pars.k + 1)

/-- The query ledger (2nq - 1) + s(m + p + 1), using natural-number subtraction. -/
def eq112QueryCount (pars : Section7Parameters) (s nq : ℕ) : ℕ :=
  (2 * nq - 1) + s * (pars.m + pars.p + 1)

/-- The gate ledger (2nq + 2) + 3(m + 1) + m(k + 1). -/
def eq112GateCount (pars : Section7Parameters) (nq : ℕ) : ℕ :=
  (2 * nq + 2) + 3 * (pars.m + 1) + (pars.m * (pars.k + 1))

/-- The natural ceiling of (π/4 - θ)/(2θ), used as an amplification round count. -/
noncomputable def aaRounds (θ : ℝ) : ℕ := Nat.ceil ((Real.pi / 4 - θ) / (2 * θ))

/-- A signed dyadic datum consisting of a Boolean sign, a natural mantissa, and a natural
precision parameter. -/
structure FiniteDigit where

  sign : Bool

  mantissa : ℕ

  bits : ℕ
  deriving DecidableEq, Repr

/-- The real value of a finite digit, obtained by multiplying its mantissa by its sign and
dividing by 2^bits. -/
noncomputable def FiniteDigit.value (d : FiniteDigit) : ℝ :=
  (if d.sign then -1 else 1) * (d.mantissa : ℝ) / 2 ^ d.bits

/-- The finite digit with the sign of `x` and mantissa ⌊|x| 2^bits⌋. -/
noncomputable def roundFiniteDigit (x : ℝ) (bits : ℕ) : FiniteDigit :=
  { sign := x < 0
    mantissa := Nat.floor (|x| * 2 ^ bits)
    bits := bits }

/-- The defined bit ledger for a finite digit, equal to its precision parameter plus one. -/
def finiteDigitBitCount (d : FiniteDigit) : ℕ := d.bits + 1

/-- The defined gate ledger for a finite digit, equal to its precision parameter. -/
def finiteDigitGateCount (d : FiniteDigit) : ℕ := d.bits

/-- A record of classical bit use, peak classical bit use, quantum queries, and quantum gates. -/
structure FiniteDigitLedger where

  classicalBits : ℕ

  classicalPeakBits : ℕ

  quantumQueries : ℕ

  quantumGates : ℕ
  deriving DecidableEq, Repr

/-- The fixed real constant 31/30 used in Taylor transition estimates. -/
noncomputable def frozenUniformConstant : ℝ := 31 / 30

/-- The order-dependent real bound 1 + b!/(k + 1)!. -/
noncomputable def smallOrderUniformConstant (k b : ℕ) : ℝ :=
  1 + (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ)

end Qatlib.Papers.QLinearODE17.EndToEnd
