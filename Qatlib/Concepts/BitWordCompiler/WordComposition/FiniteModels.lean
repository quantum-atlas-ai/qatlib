/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BitWordCompiler.WordComposition
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

structure SourceRationalProblem where
  count : ℕ
  dimension : ℕ
  addresses : ℕ
  alphabet : ℕ
  input : Fin count → Fin addresses → Fin (alphabet+1)
  start : Fin count → Fin dimension → ℚ × ℚ
  target : Fin count → Fin dimension → ℚ × ℚ

def sourceRationalState {h : ℕ} (v : Fin h → ℚ × ℚ) : QState (Fin h) :=
  fun i => (v i).1 + (v i).2 * Complex.I

def sourceNatBits (n : ℕ) : List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits
def sourceIntBits (n : ℤ) : List Bool := decide (n<0) :: sourceNatBits n.natAbs
def sourceRatBits (r : ℚ) : List Bool := sourceIntBits r.num ++ sourceNatBits r.den
def sourceProblemBits (d : SourceRationalProblem) : List Bool :=
  ([d.count,d.dimension,d.addresses,d.alphabet].flatMap sourceNatBits) ++
  (List.ofFn (fun x : Fin d.count =>
    (List.ofFn (fun j : Fin d.addresses => sourceNatBits (d.input x j).val)).flatten ++
    (List.ofFn (fun h : Fin d.dimension => sourceRatBits (d.start x h).1 ++
      sourceRatBits (d.start x h).2 ++ sourceRatBits (d.target x h).1 ++
      sourceRatBits (d.target x h).2)).flatten)).flatten

def sourceRegNumber {n : ℕ} (x : Reg n) : ℕ := ∑ i : Fin n, if x i then 2^i.val else 0
def sourceRegBits (n v : ℕ) : Reg n := fun i => v.testBit i.val
def sourceAddressBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 (d.addresses+1)
def sourceValueBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 (d.alphabet+1)
def sourcePayloadBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 d.dimension

def sourceNativeValueOracle (d : SourceRationalProblem) (x : Fin d.count) :
    Matrix (Reg (sourceAddressBits d+sourceValueBits d))
      (Reg (sourceAddressBits d+sourceValueBits d)) ℂ :=
  permMatrix (fun z =>
    let na := sourceAddressBits d
    let nb := sourceValueBits d
    let j := sourceRegNumber (fun i : Fin na => z ⟨i.val, by omega⟩)
    let a := sourceRegNumber (fun i : Fin nb => z ⟨na+i.val, by omega⟩)
    let v := if h : j<d.addresses then (d.input x ⟨j,h⟩).val else 0
    if a<d.alphabet+1 then sourceRegBits (na+nb) (j+2^na*((a+v)%(d.alphabet+1))) else z)

inductive SourceNativeStep (w : ℕ) where
  | local : LocalQFTGate w → SourceNativeStep w
  | query : List (Fin w) → Bool → SourceNativeStep w
  deriving DecidableEq

structure SourceNativeProgram where
  width : ℕ
  steps : List (SourceNativeStep width)

def sourceFixedGate {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ k _ => k ≤ 3
  | _ => True

def sourceNativeLegal (d : SourceRationalProblem) (p : SourceNativeProgram) : Prop :=
  ∀ s ∈ p.steps, match s with
    | .local g => sourceFixedGate g
    | .query ws _ => ws.Nodup ∧ ws.length=sourceAddressBits d+sourceValueBits d

def sourceNativeCalls (p : SourceNativeProgram) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => false | .query _ _ => true)
def sourceNativeGates (p : SourceNativeProgram) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => true | .query _ _ => false)
def sourceNativePrecision (p : SourceNativeProgram) : ℕ :=
  (p.steps.map (fun s => match s with | .local (.cp _ _ k _) => k | _ => 0)).foldl max 0

def sourceNativeStepMatrix (d : SourceRationalProblem) (x : Fin d.count)
    (w : ℕ) (s : SourceNativeStep w) : Matrix (Reg w) (Reg w) ℂ :=
  match s with
  | .local g => localGateMatrix g
  | .query ws adj =>
      if h : ws.length=sourceAddressBits d+sourceValueBits d then
        let O := sourceNativeValueOracle d x
        let Q := if adj then Oᴴ else O
        fun p t => if ∀ i : Fin w, i ∉ ws → p i=t i then
          Q (fun k => p (ws.get (Fin.cast h.symm k)))
            (fun k => t (ws.get (Fin.cast h.symm k))) else 0
      else 1

def sourceNativeMatrix (d : SourceRationalProblem) (x : Fin d.count)
    (p : SourceNativeProgram) : Matrix (Reg p.width) (Reg p.width) ℂ :=
  (p.steps.map (sourceNativeStepMatrix d x p.width)).reverse.prod

def sourceNativeFrame (d : SourceRationalProblem) (w : ℕ) :
    Matrix (Reg w) (Bool × Fin d.dimension) ℂ := fun p t =>
  if p=sourceRegBits w
      ((if t.1 then 1 else 0)*2^(sourceAddressBits d+sourceValueBits d) +
        t.2.val*2^(sourceAddressBits d+sourceValueBits d+1)) then 1 else 0

def sourceNativeClean (d : SourceRationalProblem) (w : ℕ) (tag : Bool)
    (ψ : QState (Fin d.dimension)) : QState (Reg w) :=
  sourceNativeFrame d w *ᵥ (fun p => if p.1=tag then ψ p.2 else 0)

def sourceNativeStepFields {w : ℕ} : SourceNativeStep w → List ℕ
  | .local (.h a) => [0,a.val]
  | .local (.cp a b k neg) => [1,a.val,b.val,k,if neg then 1 else 0]
  | .local (.swap a b) => [2,a.val,b.val]
  | .query ws adj => [3,if adj then 1 else 0,ws.length] ++ ws.map Fin.val

def sourceNativeProgramBits (p : SourceNativeProgram) : List Bool :=
  ([p.width,p.steps.length] ++ p.steps.flatMap sourceNativeStepFields).flatMap sourceNatBits

def sourceFixedLocalProgram (p : SourceNativeProgram) : Prop :=
  ∀ s ∈ p.steps, match s with | .local g => sourceFixedGate g | .query _ _ => False

def sourceNativeKnownMatrix (p : SourceNativeProgram) : Matrix (Reg p.width) (Reg p.width) ℂ :=
  localProgramMatrix (p.steps.filterMap (fun s => match s with | .local g => some g | _ => none))

def sourcePaddingFrame (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p=(fun i => if h : i.val<w then t ⟨i.val,h⟩ else false) then 1 else 0

def sourceSynthesisCompilerTime
    (build : {w : ℕ} → LocalQFTGate w → ℕ → SourceNativeProgram) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
      let input := ([w,k] ++ sourceNativeStepFields (.local g)).flatMap sourceNatBits
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+input.length+w+k+sourceNativeGates (build g k))^D ∧
        BitMachineAfter M (input.map some) s = some cfg ∧
        Turing.TM0.step M cfg = none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i=
          ((sourceNativeProgramBits (build g k)).map some).getD i none)

def sourceNativeCompilerTime
    (build : SourceRationalProblem → ℕ → SourceNativeProgram) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (d : SourceRationalProblem) (k : ℕ),
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+(sourceProblemBits d).length+k+sourceNativeCalls (build d k))^D ∧
        BitMachineAfter M ((sourceNatBits k++sourceProblemBits d).map some) s = some cfg ∧
        Turing.TM0.step M cfg = none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i = ((sourceNativeProgramBits (build d k)).map some).getD i none)

def sourceMachineBits (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) : List Bool :=
  sourceNatBits q ++ (List.ofFn (fun st : Fin (q+1) =>
    ([none,some false,some true].map (fun c =>
      (match M st c with
        | none => [0]
        | some (next,.move .left) => [1,next.val,0]
        | some (next,.move .right) => [1,next.val,1]
        | some (next,.write c) => [1,next.val,2,
            match c with | none => 0 | some false => 1 | some true => 2]).flatMap sourceNatBits)).flatten)).flatten

structure SourceRealProblem where
  count : ℕ
  dimension : ℕ
  addresses : ℕ
  alphabet : ℕ
  input : Fin count → Fin addresses → Fin (alphabet+1)
  start : Fin count → QState (Fin dimension)
  target : Fin count → QState (Fin dimension)
  evaluatorStates : ℕ
  evaluator : Turing.TM0.Machine (Option Bool) (Fin (evaluatorStates+1))

def sourceRealHeader (d : SourceRealProblem) : SourceRationalProblem :=
  ⟨d.count,d.dimension,d.addresses,d.alphabet,d.input,fun _ _ => (0,0),fun _ _ => (0,0)⟩

def sourceRealBits (d : SourceRealProblem) : List Bool :=
  [d.count,d.dimension,d.addresses,d.alphabet].flatMap sourceNatBits ++
  (List.ofFn (fun x : Fin d.count =>
    (List.ofFn (fun j : Fin d.addresses => sourceNatBits (d.input x j).val)).flatten)).flatten ++
  sourceMachineBits d.evaluatorStates d.evaluator

def sourceCoordinateAfter (d : SourceRealProblem) (x : Fin d.count) (h : Fin d.dimension)
    (target : Bool) (r t : ℕ) : Prop :=
  ∃ (cfg : Turing.TM0.Cfg (Option Bool) (Fin (d.evaluatorStates+1))) (a b : ℚ),
    BitMachineAfter d.evaluator
      (([x.val,h.val,if target then 1 else 0,r].flatMap sourceNatBits).map some) t = some cfg ∧
    Turing.TM0.step d.evaluator cfg = none ∧
    (∀ i : ℕ, cfg.Tape.right₀.nth i = ((sourceRatBits a++sourceRatBits b).map some).getD i none) ∧
    ‖((a : ℂ)+(b : ℂ)*Complex.I) - (if target then d.target x h else d.start x h)‖ ≤ (1/2 : ℝ)^r

def sourceRealAccess (d : SourceRealProblem) : Prop :=
  ∀ x h target r, ∃ t, sourceCoordinateAfter d x h target r t

def sourceCoordinateTime (d : SourceRealProblem) (x : Fin d.count) (h : Fin d.dimension)
    (target : Bool) (r : ℕ) : ℕ :=
  if he : ∃ t, sourceCoordinateAfter d x h target r t then Nat.find he else 0

def sourceEvaluationWork (d : SourceRealProblem) (R : ℕ) : ℕ :=
  let times := (List.range (R+1)).flatMap (fun r =>
    (List.ofFn (fun x : Fin d.count => (List.ofFn (fun h : Fin d.dimension =>
      [sourceCoordinateTime d x h false r,sourceCoordinateTime d x h true r])).flatten)).flatten)
  (1+d.count*d.dimension)*(R+1)*(times.foldl max 0)

def sourceRealSize (d : SourceRealProblem) : ℕ :=
  (sourceRealBits d).length+d.count+d.dimension+d.addresses

def sourceGeneralCompilerTime
    (build : SourceRealProblem → ℕ → SourceNativeProgram) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (d : SourceRealProblem) (k : ℕ), sourceRealAccess d →
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+sourceRealSize d+k+sourceNativeCalls (build d k)+
          sourceEvaluationWork d (C*(1+sourceRealSize d+k)^D))^D ∧
        BitMachineAfter M ((sourceNatBits k++sourceRealBits d).map some) s = some cfg ∧
        Turing.TM0.step M cfg = none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i = ((sourceNativeProgramBits (build d k)).map some).getD i none)

def sourceTwoLabelProblem : SourceRationalProblem :=
  ⟨2, 2, 1, 1, fun x _ => x,
    fun _ h => (if h=0 then 1 else 0, 0),
    fun x h => (if h=x then 1 else 0, 0)⟩

end Qatlib.Concepts.BitWordCompiler.WordComposition
