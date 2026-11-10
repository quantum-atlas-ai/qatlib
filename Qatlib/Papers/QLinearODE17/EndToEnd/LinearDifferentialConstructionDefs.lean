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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Papers.QLinearODE17.StructureCore

set_option autoImplicit false

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib
open Matrix
open scoped Classical Matrix.Norms.L2Operator BigOperators

noncomputable def sparsePositions {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (o : O) : Finset I :=
  Finset.univ.filter fun i => A o i ≠ 0

noncomputable def sparseRowMass {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (o : O) : ℝ :=
  ∑ i, ‖A o i‖

noncomputable def sparseColumnMass {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (i : I) : ℝ :=
  ∑ o, ‖A o i‖

noncomputable def sparseRowAccessCost {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (o : O) : ℕ :=
  (sparsePositions A o).card

noncomputable def sparseColumnAccessCost {O I : Type} [Fintype O] [Fintype I] [DecidableEq O]
    [DecidableEq I] (A : Matrix O I ℂ) (i : I) : ℕ :=
  (Finset.univ.filter fun o => A o i ≠ 0).card

def taylorRHSSupport (m k _p : ℕ) : Finset ℕ :=
  {0} ∪ (Finset.range m).image (fun i => i * (k + 1) + 1)

def taylorPreparedColumns (m : ℕ) : ℕ := m + 1

structure Section7Parameters where

  p : ℕ

  m : ℕ

  k : ℕ

  kq : ℕ
  deriving DecidableEq, Repr

noncomputable def section7PaddingCount (kq m : ℕ) (g : ℝ) : ℕ :=
  4 ^ kq - Nat.ceil (77 * (m : ℝ) * g ^ 2) - 1

def section7LabelCount (pars : Section7Parameters) : ℕ :=
  pars.m * (pars.k + 1) + pars.p + 1

def section7StepCount (pars : Section7Parameters) : ℕ :=
  pars.m * (pars.k + 1)

def eq112QueryCount (pars : Section7Parameters) (s nq : ℕ) : ℕ :=
  (2 * nq - 1) + s * (pars.m + pars.p + 1)

def eq112GateCount (pars : Section7Parameters) (nq : ℕ) : ℕ :=
  (2 * nq + 2) + 3 * (pars.m + 1) + (pars.m * (pars.k + 1))

noncomputable def aaRounds (θ : ℝ) : ℕ := Nat.ceil ((Real.pi / 4 - θ) / (2 * θ))

structure FiniteDigit where

  sign : Bool

  mantissa : ℕ

  bits : ℕ
  deriving DecidableEq, Repr

noncomputable def FiniteDigit.value (d : FiniteDigit) : ℝ :=
  (if d.sign then -1 else 1) * (d.mantissa : ℝ) / 2 ^ d.bits

noncomputable def roundFiniteDigit (x : ℝ) (bits : ℕ) : FiniteDigit :=
  { sign := x < 0
    mantissa := Nat.floor (|x| * 2 ^ bits)
    bits := bits }

def finiteDigitBitCount (d : FiniteDigit) : ℕ := d.bits + 1

def finiteDigitGateCount (d : FiniteDigit) : ℕ := d.bits

structure FiniteDigitLedger where

  classicalBits : ℕ

  classicalPeakBits : ℕ

  quantumQueries : ℕ

  quantumGates : ℕ
  deriving DecidableEq, Repr

noncomputable def frozenUniformConstant : ℝ := 31 / 30

noncomputable def smallOrderUniformConstant (k b : ℕ) : ℝ :=
  1 + (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ)

end Qatlib.Papers.QLinearODE17.EndToEnd
