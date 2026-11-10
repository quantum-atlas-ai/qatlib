/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.HspRecovery.Reduction.Reductions
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Nat.Bits
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib

def sourceAddressBits (N : ℕ) : ℕ := Nat.log2 (N - 1) + 1

def nativeWidth (N o w : ℕ) : ℕ := sourceAddressBits N + 1 + o + w

def nativeWire (N o w a : ℕ) : Fin (nativeWidth N o w) :=
  ⟨a % nativeWidth N o w, Nat.mod_lt _ (by unfold nativeWidth sourceAddressBits; omega)⟩

noncomputable def nativeInstruction (N o w t : ℕ) : Step (Reg (nativeWidth N o w)) :=
  if t % 4 = 0 then .query else
  if t % 4 = 1 then .gate (localGateMatrix (.h (nativeWire N o w (t / 4)))) else
  if t % 4 = 2 then .gate (localGateMatrix (.cp
    (nativeWire N o w (t / 4)) (nativeWire N o w (t / (4 * nativeWidth N o w)))
    ((t / (4 * nativeWidth N o w ^ 2)) % 4)
    (decide ((t / (16 * nativeWidth N o w ^ 2)) % 2 = 1)))) else
  .gate (localGateMatrix (.swap (nativeWire N o w (t / 4))
    (nativeWire N o w (t / (4 * nativeWidth N o w)))))

noncomputable def nativeCircuit (N o w : ℕ) (code : List ℕ) :
    Circuit (Reg (nativeWidth N o w)) := code.map (nativeInstruction N o w)

def nativeAddress (N o w : ℕ) (x : Reg (nativeWidth N o w)) : ℕ :=
  ∑ i : Fin (sourceAddressBits N),
    (if x (nativeWire N o w i.val) then 1 else 0) * 2 ^ i.val

def nativeOraclePermutation (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o)
    (x : Reg (nativeWidth N o w)) : Reg (nativeWidth N o w) :=
  fun i => if h : sourceAddressBits N + 1 ≤ i.val ∧
      i.val < sourceAddressBits N + 1 + o ∧ nativeAddress N o w x < N then
    x i ^^ f ((nativeAddress N o w x : ZMod N),
      x (nativeWire N o w (sourceAddressBits N)))
      ⟨i.val - (sourceAddressBits N + 1), by omega⟩
  else x i

noncomputable def nativeOracle (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) :
    Matrix (Reg (nativeWidth N o w)) (Reg (nativeWidth N o w)) ℂ :=
  permMatrix (nativeOraclePermutation N o w f)

noncomputable def nativeSlopeProbability (N o w : ℕ) (code : List ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) (s : ZMod N) : ℝ :=
  MeasureProb (Run (nativeOracle N o w f) (nativeCircuit N o w code) (Ket (fun _ => false)))
    (Finset.univ.filter (fun x => decide (nativeAddress N o w x = s.val)))

def sourceEncodeNat (n : ℕ) : List (Option Bool) := (Nat.bits n).map some ++ [none]

def sourceEncodeNats (xs : List ℕ) : List (Option Bool) := xs.flatMap sourceEncodeNat

def sourceEncodeProgram (w : ℕ) (code : List ℕ) : List (Option Bool) :=
  sourceEncodeNats (w :: code.length :: code)

abbrev SourceGenerator (L V : ℕ) :=
  Fin (L + 1) → Turing.TM2.Stmt (fun _ : Fin 3 => Option Bool) (Fin (L + 1)) (Fin (V + 1))

abbrev SourceGeneratorCfg (L V : ℕ) :=
  Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (L + 1)) (Fin (V + 1))

def sourceGeneratorRun {L V : ℕ} (M : SourceGenerator L V) :
    ℕ → SourceGeneratorCfg L V → SourceGeneratorCfg L V
  | 0, cfg => cfg
  | t + 1, cfg => sourceGeneratorRun M t ((Turing.TM2.step M cfg).getD cfg)

def sourceGeneratorStart (L V N o : ℕ) : SourceGeneratorCfg L V :=
  Turing.TM2.init 0 (sourceEncodeNats [N, o])

def NativeConstructed {L V : ℕ} (M : SourceGenerator L V) (N o w : ℕ)
    (code : List ℕ) (t : ℕ) : Prop :=
  let final := sourceGeneratorRun M t (sourceGeneratorStart L V N o)
  final.l = none ∧ final.stk 0 = sourceEncodeProgram w code

end Qatlib.Concepts.HspRecovery.ReductionCore
