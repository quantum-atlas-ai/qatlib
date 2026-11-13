/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision

/-!
# Finite source problems and native oracle programs

`SourceRationalProblem` and `SourceRealProblem` describe finite source-state conversion data
with rational coordinates or machine-accessible complex coordinates. The module supplies
explicit binary serializations and a native program language of local gates and value-oracle
calls.

Matrix interpretations, clean-state frames, resource counts, and compiler-time predicates
connect the program representation to finite-dimensional quantum computation.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `sourceNativeMatrix`: interprets a native program as an ordered matrix product.
* `sourceNativeCompilerTime`: specifies a uniform machine compiling rational source problems.
* `sourceGeneralCompilerTime`: includes coordinate-evaluation work in the compilation bound.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BitWordCompiler.WordComposition
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- A finite family of source-state conversion inputs with rational real and imaginary
coordinates for the start and target vectors. -/
structure SourceRationalProblem where
  count : ℕ
  dimension : ℕ
  addresses : ℕ
  alphabet : ℕ
  input : Fin count → Fin addresses → Fin (alphabet+1)
  start : Fin count → Fin dimension → ℚ × ℚ
  target : Fin count → Fin dimension → ℚ × ℚ

/-- Forms a complex-valued state vector from pairs of rational real and imaginary coordinates. -/
def sourceRationalState {h : ℕ} (v : Fin h → ℚ × ℚ) : QState (Fin h) :=
  fun i => (v i).1 + (v i).2 * Complex.I

/-- Encodes a natural number by its unary binary-length prefix, a false separator, and its
binary digits. -/
def sourceNatBits (n : ℕ) : List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits
/-- Encodes an integer by a sign bit followed by the encoding of its absolute value. -/
def sourceIntBits (n : ℤ) : List Bool := decide (n<0) :: sourceNatBits n.natAbs
/-- Encodes a rational number by concatenating its signed numerator and natural denominator
encodings. -/
def sourceRatBits (r : ℚ) : List Bool := sourceIntBits r.num ++ sourceNatBits r.den
/-- Serializes a rational source problem's dimensions, oracle input values, and start and target
coordinates. -/
def sourceProblemBits (d : SourceRationalProblem) : List Bool :=
  ([d.count,d.dimension,d.addresses,d.alphabet].flatMap sourceNatBits) ++
  (List.ofFn (fun x : Fin d.count =>
    (List.ofFn (fun j : Fin d.addresses => sourceNatBits (d.input x j).val)).flatten ++
    (List.ofFn (fun h : Fin d.dimension => sourceRatBits (d.start x h).1 ++
      sourceRatBits (d.start x h).2 ++ sourceRatBits (d.target x h).1 ++
      sourceRatBits (d.target x h).2)).flatten)).flatten

/-- Interprets a Boolean register as a natural number using powers of two. -/
def sourceRegNumber {n : ℕ} (x : Reg n) : ℕ := ∑ i : Fin n, if x i then 2^i.val else 0
/-- Forms a Boolean register from the first `n` binary digits of `v`. -/
def sourceRegBits (n v : ℕ) : Reg n := fun i => v.testBit i.val
/-- The address-register width, defined as the base-two ceiling logarithm of the address count
plus one. -/
def sourceAddressBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 (d.addresses+1)
/-- The value-register width, defined as the base-two ceiling logarithm of the alphabet size
plus one. -/
def sourceValueBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 (d.alphabet+1)
/-- The payload-register width, defined as the base-two ceiling logarithm of the state
dimension. -/
def sourcePayloadBits (d : SourceRationalProblem) : ℕ := Nat.clog 2 d.dimension

/-- The matrix of the value-oracle map that adds the addressed input value modulo the alphabet
size plus one on valid value-register entries. -/
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

/-- A source native instruction is a local quantum Fourier gate or an oracle query on a
specified list of wires with an adjoint flag. -/
inductive SourceNativeStep (w : ℕ) where
  | local : LocalQFTGate w → SourceNativeStep w
  | query : List (Fin w) → Bool → SourceNativeStep w
  deriving DecidableEq

/-- A finite source native program with a register width and a list of instructions at that
width. -/
structure SourceNativeProgram where
  width : ℕ
  steps : List (SourceNativeStep width)

/-- Requires the phase precision of a controlled-phase gate to be at most three, with no further
constraint on other local gates. -/
def sourceFixedGate {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ k _ => k ≤ 3
  | _ => True

/-- Requires local gates to satisfy `sourceFixedGate` and query wire lists to be distinct and of
the expected oracle width. -/
def sourceNativeLegal (d : SourceRationalProblem) (p : SourceNativeProgram) : Prop :=
  ∀ s ∈ p.steps, match s with
    | .local g => sourceFixedGate g
    | .query ws _ => ws.Nodup ∧ ws.length=sourceAddressBits d+sourceValueBits d

/-- Counts oracle-query instructions in a source native program. -/
def sourceNativeCalls (p : SourceNativeProgram) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => false | .query _ _ => true)
/-- Counts local-gate instructions in a source native program. -/
def sourceNativeGates (p : SourceNativeProgram) : ℕ :=
  p.steps.countP (fun s => match s with | .local _ => true | .query _ _ => false)
/-- The maximum controlled-phase precision appearing in a source native program, or zero if none
occurs. -/
def sourceNativePrecision (p : SourceNativeProgram) : ℕ :=
  (p.steps.map (fun s => match s with | .local (.cp _ _ k _) => k | _ => 0)).foldl max 0

/-- Interprets a source native instruction as a matrix, extending a query over its listed wires
and using identity when its wire count is invalid. -/
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

/-- Interprets a source native program as the reverse-ordered product of its instruction
matrices. -/
def sourceNativeMatrix (d : SourceRationalProblem) (x : Fin d.count)
    (p : SourceNativeProgram) : Matrix (Reg p.width) (Reg p.width) ℂ :=
  (p.steps.map (sourceNativeStepMatrix d x p.width)).reverse.prod

/-- Maps tagged payload basis vectors to register bit patterns with zero address and value
registers. -/
def sourceNativeFrame (d : SourceRationalProblem) (w : ℕ) :
    Matrix (Reg w) (Bool × Fin d.dimension) ℂ := fun p t =>
  if p=sourceRegBits w
      ((if t.1 then 1 else 0)*2^(sourceAddressBits d+sourceValueBits d) +
        t.2.val*2^(sourceAddressBits d+sourceValueBits d+1)) then 1 else 0

/-- Forms the register state obtained by applying `sourceNativeFrame` to a payload vector with a
fixed Boolean tag. -/
def sourceNativeClean (d : SourceRationalProblem) (w : ℕ) (tag : Bool)
    (ψ : QState (Fin d.dimension)) : QState (Reg w) :=
  sourceNativeFrame d w *ᵥ (fun p => if p.1=tag then ψ p.2 else 0)

/-- Serializes a source native instruction as a tagged list of natural-number fields. -/
def sourceNativeStepFields {w : ℕ} : SourceNativeStep w → List ℕ
  | .local (.h a) => [0,a.val]
  | .local (.cp a b k neg) => [1,a.val,b.val,k,if neg then 1 else 0]
  | .local (.swap a b) => [2,a.val,b.val]
  | .query ws adj => [3,if adj then 1 else 0,ws.length] ++ ws.map Fin.val

/-- Encodes a source native program's width, step count, and instruction fields as a bit string. -/
def sourceNativeProgramBits (p : SourceNativeProgram) : List Bool :=
  ([p.width,p.steps.length] ++ p.steps.flatMap sourceNativeStepFields).flatMap sourceNatBits

/-- Requires every instruction to be a local gate satisfying `sourceFixedGate`. -/
def sourceFixedLocalProgram (p : SourceNativeProgram) : Prop :=
  ∀ s ∈ p.steps, match s with | .local g => sourceFixedGate g | .query _ _ => False

/-- Interprets the local-gate subsequence of a source native program, discarding query
instructions. -/
def sourceNativeKnownMatrix (p : SourceNativeProgram) : Matrix (Reg p.width) (Reg p.width) ℂ :=
  localProgramMatrix (p.steps.filterMap (fun s => match s with | .local g => some g | _ => none))

/-- The matrix of zero padding from a `w`-bit register to a register of the specified width. -/
def sourcePaddingFrame (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p=(fun i => if h : i.val<w then t ⟨i.val,h⟩ else false) then 1 else 0

/-- Specifies a uniform halting binary machine that synthesizes local-gate programs within a
polynomial bound in input length, width, precision, and output gate count. -/
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

/-- Specifies a uniform halting binary machine that compiles rational source problems within a
polynomial bound in problem encoding length, precision, and output query count. -/
def sourceNativeCompilerTime
    (build : SourceRationalProblem → ℕ → SourceNativeProgram) (C D : ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ (d : SourceRationalProblem) (k : ℕ),
      ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
        s ≤ C*(1+(sourceProblemBits d).length+k+sourceNativeCalls (build d k))^D ∧
        BitMachineAfter M ((sourceNatBits k++sourceProblemBits d).map some) s = some cfg ∧
        Turing.TM0.step M cfg = none ∧
        (∀ i : ℕ, cfg.Tape.right₀.nth i = ((sourceNativeProgramBits (build d k)).map some).getD i none)

/-- Serializes a binary Turing machine's state count and transition table. -/
def sourceMachineBits (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) : List Bool :=
  sourceNatBits q ++ (List.ofFn (fun st : Fin (q+1) =>
    ([none,some false,some true].map (fun c =>
      (match M st c with
        | none => [0]
        | some (next,.move .left) => [1,next.val,0]
        | some (next,.move .right) => [1,next.val,1]
        | some (next,.write c) => [1,next.val,2,
            match c with | none => 0 | some false => 1 | some true => 2]).flatMap sourceNatBits)).flatten)).flatten

/-- A finite source-state conversion problem with complex start and target coordinates and a
binary machine intended to evaluate them. -/
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

/-- Retains a real-coordinate problem's finite input data and replaces its start and target
coordinates with rational zeros. -/
def sourceRealHeader (d : SourceRealProblem) : SourceRationalProblem :=
  ⟨d.count,d.dimension,d.addresses,d.alphabet,d.input,fun _ _ => (0,0),fun _ _ => (0,0)⟩

/-- Serializes a real-coordinate problem's finite input data and coordinate-evaluator machine. -/
def sourceRealBits (d : SourceRealProblem) : List Bool :=
  [d.count,d.dimension,d.addresses,d.alphabet].flatMap sourceNatBits ++
  (List.ofFn (fun x : Fin d.count =>
    (List.ofFn (fun j : Fin d.addresses => sourceNatBits (d.input x j).val)).flatten)).flatten ++
  sourceMachineBits d.evaluatorStates d.evaluator

/-- States that the coordinate evaluator halts at time `t` with rational complex coordinates
approximating the requested start or target coordinate within `2⁻ʳ`. -/
def sourceCoordinateAfter (d : SourceRealProblem) (x : Fin d.count) (h : Fin d.dimension)
    (target : Bool) (r t : ℕ) : Prop :=
  ∃ (cfg : Turing.TM0.Cfg (Option Bool) (Fin (d.evaluatorStates+1))) (a b : ℚ),
    BitMachineAfter d.evaluator
      (([x.val,h.val,if target then 1 else 0,r].flatMap sourceNatBits).map some) t = some cfg ∧
    Turing.TM0.step d.evaluator cfg = none ∧
    (∀ i : ℕ, cfg.Tape.right₀.nth i = ((sourceRatBits a++sourceRatBits b).map some).getD i none) ∧
    ‖((a : ℂ)+(b : ℂ)*Complex.I) - (if target then d.target x h else d.start x h)‖ ≤ (1/2 : ℝ)^r

/-- Requires the evaluator to produce a sufficiently accurate approximation for every
coordinate, target flag, and precision. -/
def sourceRealAccess (d : SourceRealProblem) : Prop :=
  ∀ x h target r, ∃ t, sourceCoordinateAfter d x h target r t

/-- The least time satisfying `sourceCoordinateAfter`, or zero when no such time exists. -/
def sourceCoordinateTime (d : SourceRealProblem) (x : Fin d.count) (h : Fin d.dimension)
    (target : Bool) (r : ℕ) : ℕ :=
  if he : ∃ t, sourceCoordinateAfter d x h target r t then Nat.find he else 0

/-- Bounds coordinate-evaluation work using the maximum evaluation time through precision `R`,
scaled by the number of coordinates and precision levels. -/
def sourceEvaluationWork (d : SourceRealProblem) (R : ℕ) : ℕ :=
  let times := (List.range (R+1)).flatMap (fun r =>
    (List.ofFn (fun x : Fin d.count => (List.ofFn (fun h : Fin d.dimension =>
      [sourceCoordinateTime d x h false r,sourceCoordinateTime d x h true r])).flatten)).flatten)
  (1+d.count*d.dimension)*(R+1)*(times.foldl max 0)

/-- The encoded real problem size augmented by its input count, state dimension, and address
count. -/
def sourceRealSize (d : SourceRealProblem) : ℕ :=
  (sourceRealBits d).length+d.count+d.dimension+d.addresses

/-- Specifies uniform compilation of accessible real-coordinate source problems with a
polynomial time bound that includes coordinate-evaluation work. -/
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

/-- A two-label rational source problem with a common initial basis vector and label-dependent
target basis vectors. -/
def sourceTwoLabelProblem : SourceRationalProblem :=
  ⟨2, 2, 1, 1, fun x _ => x,
    fun _ h => (if h=0 then 1 else 0, 0),
    fun x h => (if h=x then 1 else 0, 0)⟩

end Qatlib.Concepts.BitWordCompiler.WordComposition
