/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate

/-!
# Effective access data and program encodings

This module packages normalized dense amplitudes in `DenseAmplitudeData` and finite sparse
tables in `SparseAccessData`. It defines a Householder-based preparation matrix and a
support-marking sparse oracle, together with its controlled and adjoint forms. State preparation
and oracle circuits are standard constructions in [NielsenChuang2010].

`HasEffectiveAccess` specifies uniformly accurate circuit access to these three sparse-oracle
forms with bounded query counts. The module also encodes local QFT gates as bit strings and
defines `EffectiveAccessEmitterTime` through a halting Turing-machine computation with a
polynomial step bound.

## Main statements

* `prepareUnitary`: the dense preparation matrix.
* `HasEffectiveAccess`: circuit approximation and query bounds.
* `localGateProgramBits`: bit encoding of a local gate program.
* `EffectiveAccessEmitterTime`: a bounded-time program emitter specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open Matrix
open Qatlib.Concepts.LocalMachine.LocalTransport (controlOracle)

set_option autoImplicit false

/-- A normalized complex amplitude vector on an `n`-qubit register. -/
structure DenseAmplitudeData (n : ℕ) where

  amp : QState (Reg n)

  normalized : Normalized amp

/-- A finite list of complex entries with distinct indices and a nonnegative bound on their
total squared norm; `b` is an additional size parameter. -/
structure SparseAccessData (N b : ℕ) where

  entries : List (Fin N × ℂ)

  entries_nodup : (entries.map Prod.fst).Nodup

  weightBound : ℝ

  weightBound_nonneg : 0 ≤ weightBound

  weight_le : (entries.map (fun e => ‖e.2‖ ^ 2)).sum ≤ weightBound

/-- Looks up a sparse entry at an index, returning zero when that index is absent. -/
def sparseValue {N b : ℕ} (d : SparseAccessData N b) (i : Fin N) : ℂ :=
  (d.entries.lookup i).getD 0

/-- The matrix that toggles a Boolean target exactly at indices where the sparse value is
nonzero. -/
noncomputable def sparseValueOracle {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Fin N × Bool) (Fin N × Bool) ℂ :=
  Matrix.of fun x y =>
    if x.1 = y.1 ∧ y.2 = Bool.xor x.2 (sparseValue d x.1 ≠ 0) then 1 else 0

/-- The Boolean-controlled form of `sparseValueOracle`. -/
noncomputable def controlledSparseValueOracle {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Bool × (Fin N × Bool)) (Bool × (Fin N × Bool)) ℂ :=
  controlOracle (sparseValueOracle d)

/-- The conjugate transpose of the sparse support-marking oracle. -/
noncomputable def sparseValueOracleAdjoint {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Fin N × Bool) (Fin N × Bool) ℂ :=
  (sparseValueOracle d)ᴴ

/-- Constructs a phase-adjusted Householder matrix from a distinguished basis index and a
vector, using a scalar identity when the reflection vector is zero. -/
noncomputable def householderCompletion {I : Type*} [Fintype I] [DecidableEq I]
    (i₀ : I) (v : QState I) : Matrix I I ℂ :=
  let c : ℂ := Complex.exp (Complex.arg (v i₀) * Complex.I)
  let u : QState I := fun i => c⁻¹ * v i
  let w : QState I := fun i => u i - Qatlib.Foundations.PureStateMath.Ket i₀ i
  let n : ℝ := ∑ i, ‖w i‖ ^ 2
  Matrix.of fun i j =>
    if n = 0 then c * (if i = j then 1 else 0)
    else c * (if i = j then 1 else 0) - ((2 : ℂ) / (n : ℂ)) * c * w i * star (w j)

/-- The Householder preparation matrix associated with the dense amplitudes and the all-zero
register basis index. -/
noncomputable def prepareUnitary {n : ℕ} (d : DenseAmplitudeData n) :
    Matrix (Reg n) (Reg n) ℂ :=
  householderCompletion (ZeroStr n) d.amp

/-- The circuit consisting of a single gate equal to the dense preparation matrix. -/
noncomputable def prepareWordDense {n : ℕ} (d : DenseAmplitudeData n) :
    Circuit (Reg n) :=
  [Step.gate (prepareUnitary d)]

/-- The permutation matrix that, for each index, swaps the zero bit string with its encoding and
fixes other target strings. -/
noncomputable def indexLoadOracle {N b : ℕ} (enc : Fin N → Reg b) :
    Matrix (Fin N × Reg b) (Fin N × Reg b) ℂ :=
  permMatrix fun p =>
    (p.1, if p.2 = ZeroStr b then enc p.1
      else if p.2 = enc p.1 then ZeroStr b else p.2)

/-- Requires nonnegative `ε` and unitary circuits with at most `q` queries approximating the
sparse oracle, its controlled form, and its adjoint within `ε` on every input state. -/
noncomputable def HasEffectiveAccess {N b : ℕ} (d : SparseAccessData N b)
    (ε : ℝ) (q : ℕ) : Prop :=
  0 ≤ ε ∧
    (∃ Csel : Circuit (Fin N × Bool), IsUnitaryCircuit Csel ∧ QueryCount Csel ≤ q ∧
      ∀ ψ : QState (Fin N × Bool),
        ‖Run 1 Csel ψ - sparseValueOracle d *ᵥ ψ‖ ≤ ε) ∧
    (∃ Cctl : Circuit (Bool × (Fin N × Bool)), IsUnitaryCircuit Cctl ∧ QueryCount Cctl ≤ q ∧
      ∀ φ : QState (Bool × (Fin N × Bool)),
        ‖Run 1 Cctl φ - controlledSparseValueOracle d *ᵥ φ‖ ≤ ε) ∧
    (∃ Cadj : Circuit (Fin N × Bool), IsUnitaryCircuit Cadj ∧ QueryCount Cadj ≤ q ∧
      ∀ ψ : QState (Fin N × Bool),
        ‖Run 1 Cadj ψ - sparseValueOracleAdjoint d *ᵥ ψ‖ ≤ ε)

/-- Encodes a natural number by a unary prefix for its bit-list length, a false separator, and
its bit list. -/
def selfDelimitBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- Encodes a local QFT gate as a list of natural-number fields containing its tag and
parameters. -/
def localGateFields {n : ℕ} : LocalQFTGate n → List ℕ
  | .h a => [0, a.val]
  | .cp a c k neg => [1, a.val, c.val, k, if neg then 1 else 0]
  | .swap a c => [2, a.val, c.val]

/-- Encodes the register size, gate count, and local-gate fields using `selfDelimitBits`. -/
def localGateProgramBits {n : ℕ} (gs : List (LocalQFTGate n)) : List Bool :=
  ([n, gs.length] ++ gs.flatMap localGateFields).flatMap selfDelimitBits

/-- Requires a single Turing machine to halt with the encoded gate program on its right tape
within the specified polynomial bound in input, size, precision, and output lengths. -/
def EffectiveAccessEmitterTime (build : (n : ℕ) → ℕ → List (LocalQFTGate n))
    (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
    ∀ (n k : ℕ),
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
        s ≤ C * (1 + (selfDelimitBits n ++ selfDelimitBits k).length + n + k
            + (localGateProgramBits (build n k)).length) ^ D ∧
          BitMachineAfter M ((selfDelimitBits n ++ selfDelimitBits k).map some) s
            = some cfg ∧
          Turing.TM0.step M cfg = none ∧
          (∀ i : ℕ, cfg.Tape.right₀.nth i =
            ((localGateProgramBits (build n k)).map some).getD i none)

end Qatlib.Concepts.ResourceBounds.AsymBounds
