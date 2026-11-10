/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BitWordCompiler.WordComposition
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def natBits (n : ℕ) : List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits
def intBits (n : ℤ) : List Bool := decide (n < 0) :: natBits n.natAbs
def ratBits (x : ℚ) : List Bool := intBits x.num ++ natBits x.den
def complexRat (x : ℚ × ℚ) : ℂ := x.1+x.2*Complex.I
def registerBits (h v : ℕ) : Reg h := fun i => v.testBit i.val

structure NativeLinearInput where
  h : ℕ
  inputs : ℕ
  outputs : ℕ
  left : Reg h → Fin outputs → ℚ × ℚ
  right : Reg h → Fin inputs → ℚ × ℚ
  αA : ℚ
  αInv : ℚ
  advice : ℚ

def nativeInputBits (d : NativeLinearInput) : List Bool :=
  [d.h,d.inputs,d.outputs].flatMap natBits ++ ratBits d.αA ++ ratBits d.αInv ++ ratBits d.advice ++
  (List.ofFn (fun z : Fin (2^d.h) =>
    let p := registerBits d.h z.val
    (List.ofFn (fun i : Fin d.outputs => ratBits (d.left p i).1 ++ ratBits (d.left p i).2)).flatten ++
    (List.ofFn (fun i : Fin d.inputs => ratBits (d.right p i).1 ++ ratBits (d.right p i).2)).flatten)).flatten

inductive NativeStep (h a : ℕ) where
  | local : LocalQFTGate (h+a) → NativeStep h a
  | call : Fin 2 → Option (Fin a) → Bool → Bool → NativeStep h a
  deriving DecidableEq

structure NativeProgram (h : ℕ) where
  ancilla : ℕ
  steps : List (NativeStep h ancilla)
  success : List (Reg ancilla)

def fixedGate {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True
def nativeLegal {h : ℕ} (p : NativeProgram h) : Prop :=
  ∀ s ∈ p.steps, match s with | .local g => fixedGate g | .call _ _ _ _ => True
def nativeCalls {h : ℕ} (p : NativeProgram h) (slot : Fin 2) : ℕ :=
  p.steps.countP (fun s => match s with | .call j _ _ _ => j=slot | _ => false)
def nativeGates {h : ℕ} (p : NativeProgram h) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => true | _ => false)

def joinRegisters {h a : ℕ} (x : Reg h) (y : Reg a) : Reg (h+a) :=
  fun i => if hi : i.val < h then x ⟨i.val,hi⟩ else y ⟨i.val-h,by omega⟩
def dataRegister {h a : ℕ} (x : Reg (h+a)) : Reg h := fun i => x ⟨i.val,by omega⟩
def auxRegister {h a : ℕ} (x : Reg (h+a)) : Reg a := fun i => x ⟨h+i.val,by omega⟩
def nativeStepMatrix {h a : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (s : NativeStep h a) : Matrix (Reg (h+a)) (Reg (h+a)) ℂ :=
  match s with
  | .local g => localGateMatrix g
  | .call j c value adj => fun p q =>
    if auxRegister p=auxRegister q then
      let active := match c with | none => true | some wire => auxRegister p wire=value
      if active then
        (if adj then (oracles j)ᴴ else oracles j) (dataRegister p) (dataRegister q)
      else if dataRegister p=dataRegister q then 1 else 0
    else 0
def nativeMatrix {h : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (p : NativeProgram h) : Matrix (Reg (h+p.ancilla)) (Reg (h+p.ancilla)) ℂ :=
  (p.steps.map (nativeStepMatrix oracles)).reverse.prod
def nativeStart (h a : ℕ) : QState (Reg (h+a)) := fun z => if z=ZeroStr (h+a) then 1 else 0
def nativeBranch {h a : ℕ} {I : Type} (R : Matrix (Reg h) I ℂ)
    (ψ : QState (Reg (h+a))) (u : Reg a) : QState I :=
  Rᴴ *ᵥ (fun z => ψ (joinRegisters z u))
def nativeMass {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) : ℝ :=
  ∑ u ∈ p.success.toFinset, normVec (nativeBranch R ψ u)^2
def nativeDensity {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) : Matrix I I ℂ :=
  (nativeMass R p ψ : ℂ)⁻¹ • ∑ u ∈ p.success.toFinset, pureDensity (nativeBranch R ψ u)
def nativeGuarantee {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) (target : QState I) (ε : ℝ) : Prop :=
  1/2 < nativeMass R p ψ ∧ Matrix.traceNorm (nativeDensity R p ψ-pureDensity (normState target)) ≤ ε

def nativeStepFields {h a : ℕ} : NativeStep h a → List ℕ
  | .local (.h x) => [0,x.val]
  | .local (.cp x y k neg) => [1,x.val,y.val,k,if neg then 1 else 0]
  | .local (.swap x y) => [2,x.val,y.val]
  | .call j c value adj => [3,j.val,match c with | none => 0 | some w => w.val+1,
      if value then 1 else 0,if adj then 1 else 0]
def nativeProgramBits {h : ℕ} (p : NativeProgram h) : List Bool :=
  ([h,p.ancilla,p.steps.length] ++ p.steps.flatMap nativeStepFields).flatMap natBits ++
  natBits p.success.length ++ (p.success.map (fun u => (List.ofFn u))).flatten

def nativeCompilerTime
    (build : (d : NativeLinearInput) → Bool → ℕ → NativeProgram d.h) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (d : NativeLinearInput) (simple : Bool) (k : ℕ),
      let p := build d simple k
      let input := (if simple then [true] else [false]) ++ natBits k ++ nativeInputBits d
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+input.length+k+nativeCalls p 0+nativeCalls p 1)^D ∧
        BitMachineAfter M (input.map some) s=some cfg ∧ Turing.TM0.step M cfg=none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i=((nativeProgramBits p).map some).getD i none)

def nativePadding (h a : ℕ) : Matrix (Reg (h+a)) (Reg h) ℂ :=
  fun z x => if z=joinRegisters x (ZeroStr a) then 1 else 0

def nativeSize (d : NativeLinearInput) (k : ℕ) : ℕ := 1+(nativeInputBits d).length+k

def nativeSynthesisTime
    (build : {h : ℕ} → LocalQFTGate h → ℕ → NativeProgram h) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (h : ℕ) (g : LocalQFTGate h) (k : ℕ),
      let p := build g k
      let input := ([h,k] ++ nativeStepFields (NativeStep.local (a := 0) g)).flatMap natBits
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+input.length+h+k)^D ∧
        BitMachineAfter M (input.map some) s=some cfg ∧ Turing.TM0.step M cfg=none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i=((nativeProgramBits p).map some).getD i none)

def nativeTwoStateInput : NativeLinearInput :=
  let F : Reg 1 → Fin 2 → ℚ × ℚ := fun z i =>
    if i.val=(if z 0 then 1 else 0) then (1,0) else (0,0)
  ⟨1,2,2,F,F,1,1,1⟩
def nativeBitPreparation (x : Bool) : Matrix (Reg 1) (Reg 1) ℂ :=
  permMatrix (fun z => fun _ => if x then !(z 0) else z 0)
def nativeBitTarget (x : Bool) : QState (Fin 2) :=
  fun i => if i.val=(if x then 1 else 0) then 1 else 0

end Qatlib.Concepts.BitWordCompiler.WordComposition
