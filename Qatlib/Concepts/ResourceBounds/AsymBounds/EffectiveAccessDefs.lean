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
set_option warningAsError false
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

structure DenseAmplitudeData (n : ℕ) where

  amp : QState (Reg n)

  normalized : Normalized amp

structure SparseAccessData (N b : ℕ) where

  entries : List (Fin N × ℂ)

  entries_nodup : (entries.map Prod.fst).Nodup

  weightBound : ℝ

  weightBound_nonneg : 0 ≤ weightBound

  weight_le : (entries.map (fun e => ‖e.2‖ ^ 2)).sum ≤ weightBound

def sparseValue {N b : ℕ} (d : SparseAccessData N b) (i : Fin N) : ℂ :=
  (d.entries.lookup i).getD 0

noncomputable def sparseValueOracle {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Fin N × Bool) (Fin N × Bool) ℂ :=
  Matrix.of fun x y =>
    if x.1 = y.1 ∧ y.2 = Bool.xor x.2 (sparseValue d x.1 ≠ 0) then 1 else 0

noncomputable def controlledSparseValueOracle {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Bool × (Fin N × Bool)) (Bool × (Fin N × Bool)) ℂ :=
  controlOracle (sparseValueOracle d)

noncomputable def sparseValueOracleAdjoint {N b : ℕ} (d : SparseAccessData N b) :
    Matrix (Fin N × Bool) (Fin N × Bool) ℂ :=
  (sparseValueOracle d)ᴴ

noncomputable def householderCompletion {I : Type*} [Fintype I] [DecidableEq I]
    (i₀ : I) (v : QState I) : Matrix I I ℂ :=
  let c : ℂ := Complex.exp (Complex.arg (v i₀) * Complex.I)
  let u : QState I := fun i => c⁻¹ * v i
  let w : QState I := fun i => u i - Qatlib.Foundations.PureStateMath.Ket i₀ i
  let n : ℝ := ∑ i, ‖w i‖ ^ 2
  Matrix.of fun i j =>
    if n = 0 then c * (if i = j then 1 else 0)
    else c * (if i = j then 1 else 0) - ((2 : ℂ) / (n : ℂ)) * c * w i * star (w j)

noncomputable def prepareUnitary {n : ℕ} (d : DenseAmplitudeData n) :
    Matrix (Reg n) (Reg n) ℂ :=
  householderCompletion (ZeroStr n) d.amp

noncomputable def prepareWordDense {n : ℕ} (d : DenseAmplitudeData n) :
    Circuit (Reg n) :=
  [Step.gate (prepareUnitary d)]

noncomputable def indexLoadOracle {N b : ℕ} (enc : Fin N → Reg b) :
    Matrix (Fin N × Reg b) (Fin N × Reg b) ℂ :=
  permMatrix fun p =>
    (p.1, if p.2 = ZeroStr b then enc p.1
      else if p.2 = enc p.1 then ZeroStr b else p.2)

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

def selfDelimitBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def localGateFields {n : ℕ} : LocalQFTGate n → List ℕ
  | .h a => [0, a.val]
  | .cp a c k neg => [1, a.val, c.val, k, if neg then 1 else 0]
  | .swap a c => [2, a.val, c.val]

def localGateProgramBits {n : ℕ} (gs : List (LocalQFTGate n)) : List Bool :=
  ([n, gs.length] ++ gs.flatMap localGateFields).flatMap selfDelimitBits

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
