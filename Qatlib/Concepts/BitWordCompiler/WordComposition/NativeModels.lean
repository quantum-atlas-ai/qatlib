/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels

/-!
# Native linear-system inputs and program semantics

`NativeLinearInput` stores rational frame data and scale parameters, while `NativeProgram`
combines local gates, calls to two oracle slots, and selected ancilla outcomes. Explicit
register operations give matrix semantics and postselected output quantities.

Binary encodings and compiler-time predicates express uniform compilation and synthesis costs
for these programs.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `nativeMatrix`: evaluates a program as a matrix product.
* `nativeGuarantee`: requires success mass above one half and a trace-norm output error bound.
* `nativeCompilerTime`: specifies compilation by a single halting binary Turing machine.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

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

/-- Encodes a natural number by a unary prefix for its binary length, a false separator, and its
binary digits. -/
def natBits (n : ℕ) : List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits
/-- Encodes an integer by its sign followed by the natural-number encoding of its absolute
value. -/
def intBits (n : ℤ) : List Bool := decide (n < 0) :: natBits n.natAbs
/-- Encodes a rational number by its signed numerator and natural denominator. -/
def ratBits (x : ℚ) : List Bool := intBits x.num ++ natBits x.den
/-- Forms a complex number from a pair of rational real and imaginary parts. -/
def complexRat (x : ℚ × ℚ) : ℂ := x.1+x.2*Complex.I
/-- Extracts the first `h` binary digits of a natural number as a Boolean register. -/
def registerBits (h v : ℕ) : Reg h := fun i => v.testBit i.val

/-- Rational left and right frame data for a finite native linear-system input, together with
register dimensions, scale parameters, and advice. -/
structure NativeLinearInput where
  h : ℕ
  inputs : ℕ
  outputs : ℕ
  left : Reg h → Fin outputs → ℚ × ℚ
  right : Reg h → Fin inputs → ℚ × ℚ
  αA : ℚ
  αInv : ℚ
  advice : ℚ

/-- Serializes a native linear-system input's dimensions, rational parameters, and frame
entries. -/
def nativeInputBits (d : NativeLinearInput) : List Bool :=
  [d.h,d.inputs,d.outputs].flatMap natBits ++ ratBits d.αA ++ ratBits d.αInv ++ ratBits d.advice ++
  (List.ofFn (fun z : Fin (2^d.h) =>
    let p := registerBits d.h z.val
    (List.ofFn (fun i : Fin d.outputs => ratBits (d.left p i).1 ++ ratBits (d.left p i).2)).flatten ++
    (List.ofFn (fun i : Fin d.inputs => ratBits (d.right p i).1 ++ ratBits (d.right p i).2)).flatten)).flatten

/-- A native instruction is a local gate or a call to one of two oracle slots with optional
ancilla control, control value, and adjoint flag. -/
inductive NativeStep (h a : ℕ) where
  | local : LocalQFTGate (h+a) → NativeStep h a
  | call : Fin 2 → Option (Fin a) → Bool → Bool → NativeStep h a
  deriving DecidableEq

/-- A native program on `h` data qubits, recording an ancilla width, instructions, and
successful ancilla outcomes. -/
structure NativeProgram (h : ℕ) where
  ancilla : ℕ
  steps : List (NativeStep h ancilla)
  success : List (Reg ancilla)

/-- Requires controlled-phase precision to be at most three, with no additional condition on
other local gates. -/
def fixedGate {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True
/-- Requires every local instruction in a native program to satisfy `fixedGate`. -/
def nativeLegal {h : ℕ} (p : NativeProgram h) : Prop :=
  ∀ s ∈ p.steps, match s with | .local g => fixedGate g | .call _ _ _ _ => True
/-- Counts calls to the specified oracle slot in a native program. -/
def nativeCalls {h : ℕ} (p : NativeProgram h) (slot : Fin 2) : ℕ :=
  p.steps.countP (fun s => match s with | .call j _ _ _ => j=slot | _ => false)
/-- Counts local-gate instructions in a native program. -/
def nativeGates {h : ℕ} (p : NativeProgram h) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => true | _ => false)

/-- Concatenates a data register and an auxiliary register. -/
def joinRegisters {h a : ℕ} (x : Reg h) (y : Reg a) : Reg (h+a) :=
  fun i => if hi : i.val < h then x ⟨i.val,hi⟩ else y ⟨i.val-h,by omega⟩
/-- Extracts the data portion of a combined register. -/
def dataRegister {h a : ℕ} (x : Reg (h+a)) : Reg h := fun i => x ⟨i.val,by omega⟩
/-- Extracts the auxiliary portion of a combined register. -/
def auxRegister {h a : ℕ} (x : Reg (h+a)) : Reg a := fun i => x ⟨h+i.val,by omega⟩
/-- Interprets a native instruction as a matrix, applying a chosen oracle or its adjoint subject
to the optional ancilla control. -/
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
/-- Interprets a native program as the reverse-ordered product of its instruction matrices. -/
def nativeMatrix {h : ℕ} (oracles : Fin 2 → Matrix (Reg h) (Reg h) ℂ)
    (p : NativeProgram h) : Matrix (Reg (h+p.ancilla)) (Reg (h+p.ancilla)) ℂ :=
  (p.steps.map (nativeStepMatrix oracles)).reverse.prod
/-- The basis state with every data and auxiliary bit false. -/
def nativeStart (h a : ℕ) : QState (Reg (h+a)) := fun z => if z=ZeroStr (h+a) then 1 else 0
/-- Extracts the branch at an auxiliary outcome and applies the conjugate-transpose frame `R`. -/
def nativeBranch {h a : ℕ} {I : Type} (R : Matrix (Reg h) I ℂ)
    (ψ : QState (Reg (h+a))) (u : Reg a) : QState I :=
  Rᴴ *ᵥ (fun z => ψ (joinRegisters z u))
/-- Sums the squared norms of the distinct successful auxiliary branches. -/
def nativeMass {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) : ℝ :=
  ∑ u ∈ p.success.toFinset, normVec (nativeBranch R ψ u)^2
/-- Normalizes the sum of the successful branch density matrices by their total mass. -/
def nativeDensity {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) : Matrix I I ℂ :=
  (nativeMass R p ψ : ℂ)⁻¹ • ∑ u ∈ p.success.toFinset, pureDensity (nativeBranch R ψ u)
/-- Requires successful branch mass greater than one half and trace-norm error at most `ε` from
the normalized target's pure density matrix. -/
def nativeGuarantee {h : ℕ} {I : Type} [Fintype I] (R : Matrix (Reg h) I ℂ)
    (p : NativeProgram h) (ψ : QState (Reg (h+p.ancilla))) (target : QState I) (ε : ℝ) : Prop :=
  1/2 < nativeMass R p ψ ∧ Matrix.traceNorm (nativeDensity R p ψ-pureDensity (normState target)) ≤ ε

/-- Serializes a native instruction as a tagged list of natural-number fields. -/
def nativeStepFields {h a : ℕ} : NativeStep h a → List ℕ
  | .local (.h x) => [0,x.val]
  | .local (.cp x y k neg) => [1,x.val,y.val,k,if neg then 1 else 0]
  | .local (.swap x y) => [2,x.val,y.val]
  | .call j c value adj => [3,j.val,match c with | none => 0 | some w => w.val+1,
      if value then 1 else 0,if adj then 1 else 0]
/-- Encodes a native program's register sizes, instructions, and successful auxiliary bit
strings. -/
def nativeProgramBits {h : ℕ} (p : NativeProgram h) : List Bool :=
  ([h,p.ancilla,p.steps.length] ++ p.steps.flatMap nativeStepFields).flatMap natBits ++
  natBits p.success.length ++ (p.success.map (fun u => (List.ofFn u))).flatten

/-- Specifies a uniform halting binary compiler with a polynomial bound in input length,
precision, and the two output oracle-call counts. -/
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

/-- The matrix embedding a data register by adjoining an all-false auxiliary register. -/
def nativePadding (h a : ℕ) : Matrix (Reg (h+a)) (Reg h) ℂ :=
  fun z x => if z=joinRegisters x (ZeroStr a) then 1 else 0

/-- The native input encoding length plus precision and one. -/
def nativeSize (d : NativeLinearInput) (k : ℕ) : ℕ := 1+(nativeInputBits d).length+k

/-- Specifies a uniform halting binary machine synthesizing native local-gate programs in time
polynomial in input length, register width, and precision. -/
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

/-- A one-qubit, two-state native input with matching standard-basis left and right frames and
unit rational parameters. -/
def nativeTwoStateInput : NativeLinearInput :=
  let F : Reg 1 → Fin 2 → ℚ × ℚ := fun z i =>
    if i.val=(if z 0 then 1 else 0) then (1,0) else (0,0)
  ⟨1,2,2,F,F,1,1,1⟩
/-- The one-qubit permutation matrix that flips the register exactly when `x` is true. -/
def nativeBitPreparation (x : Bool) : Matrix (Reg 1) (Reg 1) ℂ :=
  permMatrix (fun z => fun _ => if x then !(z 0) else z 0)
/-- The standard basis vector indexed by the Boolean value `x`. -/
def nativeBitTarget (x : Bool) : QState (Fin 2) :=
  fun i => if i.val=(if x then 1 else 0) then 1 else 0

end Qatlib.Concepts.BitWordCompiler.WordComposition
