/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.HspRecovery.Reduction.Reductions
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Nat.Bits

/-!
# Native circuit and generator endpoints

This module defines a natural-number encoding of circuits on a register containing a dihedral
address, an oracle output, and workspace. `nativeOraclePermutation` performs the oracle XOR on
valid addresses, and `nativeSlopeProbability` measures recovery of a specified address.

`SourceGenerator` and `NativeConstructed` express circuit generation by a finite Turing machine
program, using the computational framework discussed in [KitaevShenVyalyi2002].

## Main statements

* `nativeCircuit`: decodes an instruction list into a circuit.
* `nativeSlopeProbability`: measures a candidate recovered address.
* `NativeConstructed`: states that a generator halts with the encoded program on its output
  stack.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

open Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib

/-- The address width `Nat.log2 (N - 1) + 1` used by the native encoding. -/
def sourceAddressBits (N : ℕ) : ℕ := Nat.log2 (N - 1) + 1

/-- The total native register width consisting of address bits, one reflection bit, output bits,
and workspace bits. -/
def nativeWidth (N o w : ℕ) : ℕ := sourceAddressBits N + 1 + o + w

/-- The native wire obtained by reducing address `a` modulo the register width. -/
def nativeWire (N o w a : ℕ) : Fin (nativeWidth N o w) :=
  ⟨a % nativeWidth N o w, Nat.mod_lt _ (by unfold nativeWidth sourceAddressBits; omega)⟩

/-- The instruction decoded from `t`, selecting a query, Hadamard, controlled phase, or swap
according to `t % 4`. -/
noncomputable def nativeInstruction (N o w t : ℕ) : Step (Reg (nativeWidth N o w)) :=
  if t % 4 = 0 then .query else
  if t % 4 = 1 then .gate (localGateMatrix (.h (nativeWire N o w (t / 4)))) else
  if t % 4 = 2 then .gate (localGateMatrix (.cp
    (nativeWire N o w (t / 4)) (nativeWire N o w (t / (4 * nativeWidth N o w)))
    ((t / (4 * nativeWidth N o w ^ 2)) % 4)
    (decide ((t / (16 * nativeWidth N o w ^ 2)) % 2 = 1)))) else
  .gate (localGateMatrix (.swap (nativeWire N o w (t / 4))
    (nativeWire N o w (t / (4 * nativeWidth N o w)))))

/-- The native circuit obtained by decoding each natural number in the instruction list. -/
noncomputable def nativeCircuit (N o w : ℕ) (code : List ℕ) :
    Circuit (Reg (nativeWidth N o w)) := code.map (nativeInstruction N o w)

/-- The natural number represented by the native address bits in least-significant-bit order. -/
def nativeAddress (N o w : ℕ) (x : Reg (nativeWidth N o w)) : ℕ :=
  ∑ i : Fin (sourceAddressBits N),
    (if x (nativeWire N o w i.val) then 1 else 0) * 2 ^ i.val

/-- The register map XORing the oracle output into the output wires when the encoded address is
less than `N`. -/
def nativeOraclePermutation (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o)
    (x : Reg (nativeWidth N o w)) : Reg (nativeWidth N o w) :=
  fun i => if h : sourceAddressBits N + 1 ≤ i.val ∧
      i.val < sourceAddressBits N + 1 + o ∧ nativeAddress N o w x < N then
    x i ^^ f ((nativeAddress N o w x : ZMod N),
      x (nativeWire N o w (sourceAddressBits N)))
      ⟨i.val - (sourceAddressBits N + 1), by omega⟩
  else x i

/-- The permutation matrix of the native oracle register map. -/
noncomputable def nativeOracle (N o w : ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) :
    Matrix (Reg (nativeWidth N o w)) (Reg (nativeWidth N o w)) ℂ :=
  permMatrix (nativeOraclePermutation N o w f)

/-- The Born probability that the native circuit, run from the all-false state with the given
oracle, returns address `s.val`. -/
noncomputable def nativeSlopeProbability (N o w : ℕ) (code : List ℕ)
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg N → Reg o) (s : ZMod N) : ℝ :=
  MeasureProb (Run (nativeOracle N o w f) (nativeCircuit N o w code) (Ket (fun _ => false)))
    (Finset.univ.filter (fun x => decide (nativeAddress N o w x = s.val)))

/-- The binary digits of a natural number encoded as `some` bits followed by a `none`
terminator. -/
def sourceEncodeNat (n : ℕ) : List (Option Bool) := (Nat.bits n).map some ++ [none]

/-- The concatenation of the terminated bit encodings of a list of natural numbers. -/
def sourceEncodeNats (xs : List ℕ) : List (Option Bool) := xs.flatMap sourceEncodeNat

/-- The terminated bit encoding of the workspace width, instruction count, and instruction list. -/
def sourceEncodeProgram (w : ℕ) (code : List ℕ) : List (Option Bool) :=
  sourceEncodeNats (w :: code.length :: code)

/-- A three-stack `TM2` program over `Option Bool` with finite label and variable types. -/
abbrev SourceGenerator (L V : ℕ) :=
  Fin (L + 1) → Turing.TM2.Stmt (fun _ : Fin 3 => Option Bool) (Fin (L + 1)) (Fin (V + 1))

/-- The configuration type for the finite three-stack source generator. -/
abbrev SourceGeneratorCfg (L V : ℕ) :=
  Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (L + 1)) (Fin (V + 1))

/-- The configuration obtained after `t` generator steps, retaining the current configuration
when no step is available. -/
def sourceGeneratorRun {L V : ℕ} (M : SourceGenerator L V) :
    ℕ → SourceGeneratorCfg L V → SourceGeneratorCfg L V
  | 0, cfg => cfg
  | t + 1, cfg => sourceGeneratorRun M t ((Turing.TM2.step M cfg).getD cfg)

/-- The initial generator configuration at label zero with `N` and `o` encoded as input. -/
def sourceGeneratorStart (L V N o : ℕ) : SourceGeneratorCfg L V :=
  Turing.TM2.init 0 (sourceEncodeNats [N, o])

/-- The predicate that the generator, started on `N` and `o`, is halted after `t` steps and has
`sourceEncodeProgram w code` on stack zero. -/
def NativeConstructed {L V : ℕ} (M : SourceGenerator L V) (N o w : ℕ)
    (code : List ℕ) (t : ℕ) : Prop :=
  let final := sourceGeneratorRun M t (sourceGeneratorStart L V N o)
  final.l = none ∧ final.stk 0 = sourceEncodeProgram w code

end Qatlib.Concepts.HspRecovery.ReductionCore
