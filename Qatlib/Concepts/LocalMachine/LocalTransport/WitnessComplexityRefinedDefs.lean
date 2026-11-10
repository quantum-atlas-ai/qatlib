/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness

def WcWitnessWidth (f : UniformWitnessFamily) (n : ℕ) : ℕ := f.witnessWidth n

def WcOracleAccessCount (f : SharedOracleUniformFamily) (x : List Bool) : ℕ :=
  (oracleAccessLedger (f.generator x)).length

def WcOracleAccessBudget (f : SharedOracleUniformFamily) (x : List Bool) : Prop :=
  WcOracleAccessCount f x ≤ (f.generator x).instructions.length

def WcWitnessLengthLedger (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool, (f.generator x).witnessBits = WcWitnessWidth f x.length

def WcDiagonalDensity {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Prop :=
  ∀ w w' : Reg m, w ≠ w' → σ w w' = 0

def WcClassicalAcceptFunctional (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) : Prop :=
  ∀ σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ,
    acceptProb A p x σ
      = ∑ w : Reg p.witnessBits,
        (σ w w).re * acceptProb A p x (classicalWitnessDensity w)

def WcEmptyWitnessProgram (iB aB oB : ℕ) (instrs : List WitnessInstruction) :
    WitnessVerifierProgram where
  witnessBits := 0
  inputBits := iB
  ancillaBits := aB
  outputWire := oB
  instructions := instrs

def WcDiagonalPart {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  fun i j => if i = j then σ i i else 0

def WcOffDiagonalPart {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg m) (Reg m) ℂ :=
  fun i j => σ i j - (if i = j then σ i i else 0)

def WcWitnessReindex {w g : ℕ} (hw : g = w) : Reg w → Reg g :=
  fun v => fun k => v (Fin.cast hw k)

def WcDiagonalAcceptFamily (f : UniformWitnessFamily) : Prop :=
  ∀ x : List Bool,
    WcClassicalAcceptFunctional (fun _ _ => false) (f.generator x)
      (listToInput (f.generator x) x)

def WcDiagonalAcceptLanguage (L : BitLanguage) : Prop :=
  ∀ (f : UniformWitnessFamily),
    (∀ x : List Bool, L.yes x = true →
      ∃ w : Reg (f.witnessWidth x.length),
        2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w)) →
    (∀ x : List Bool, L.no x = true →
      ∀ w : Reg (f.witnessWidth x.length),
        uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w) ≤ 1 / 3) →
    WcDiagonalAcceptFamily f

end Qatlib.Concepts.LocalMachine.LocalTransport
