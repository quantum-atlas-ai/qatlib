/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Fixed gate synthesis and mixed word contracts

The definitions describe local gate synthesis with clean auxiliary registers, approximation up
to phase, and explicit Boolean encodings of synthesis inputs and outputs. `SynthCompiler`
supplies emitted words and ancilla counts, while `BitWordMachineModel` specifies time indexed
execution and space accounting; circuit approximation background is available in
[NielsenChuang2010].

Mixed words combine known gates and oracle calls. Their compilation contracts track segment
alignment, dyadic error budgets, preserved access counts, operator and whole state error, clean
pool restoration, and polynomial resource bounds.

## Main statements

* `synthesisApprox`: specifies the semantic requirements for a synthesized gate word.
* `compileWord`: substitutes local segments while retaining oracle calls.
* `WordCompilation` and `BudgetLE`: specify shared ancillas and accumulated tolerances.
* `CompileLedgersOK`: states gate, bit time, and peak space bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.NumericalWord.MixedWordError

open Matrix
open scoped Classical Matrix.Norms.L2Operator

set_option autoImplicit false

noncomputable section

/-- A Boolean encoding of `n` consisting of a unary length prefix, a false separator, and the
bits of `n`. -/
def natBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- The natural number fields encoding a local gate's constructor, register indices, and
controlled phase parameters. -/
def gateFields {w : ℕ} : LocalQFTGate w → List ℕ
  | .h a => [0, a.val]
  | .cp a b e neg => [1, a.val, b.val, e, if neg then 1 else 0]
  | .swap a b => [2, a.val, b.val]

/-- The Boolean synthesis input encoding the register width, requested precision, and gate
fields. -/
def synthInput (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : List Bool :=
  ([w, k] ++ gateFields g).flatMap natBits

/-- The length of the Boolean synthesis input. -/
def synthInputBits (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  (synthInput w g k).length

/-- The Boolean encoding of a synthesized word's width, gate count, and gate fields. -/
def synthWordBits (width : ℕ) (letters : List (LocalQFTGate width)) : List Bool :=
  ([width, letters.length] ++ letters.flatMap gateFields).flatMap natBits

/-- The predicate selecting all Hadamard and swap gates and controlled phase gates with exponent
at most three. -/
def IsFixedPrimitive {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True

/-- The restriction of an `n` bit register to its first `w` bits, given `w ≤ n`. -/
def dataBits {n : ℕ} (w : ℕ) (hw : w ≤ n) (z : Reg n) : Reg w :=
  fun i => z ⟨i.val, by omega⟩

/-- The suffix of a register beginning at index `w`, with width `width - w`. -/
def auxBits {width : ℕ} (w : ℕ) (z : Reg width) : Reg (width - w) :=
  fun i => z ⟨w + i.val, by omega⟩

/-- The matrix mapping a data basis string to the output string that agrees on available data
positions and has false bits at all remaining positions. -/
def padClean (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p = (fun i : Fin width => if h : i.val < w then t ⟨i.val, h⟩ else false)
    then 1 else 0

/-- The operator norm distance `‖A - B‖` between two finite matrices. -/
noncomputable def operatorError {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : ℝ := ‖A - B‖

/-- The condition that `A` is within operator norm tolerance of `B` multiplied by some complex
phase. -/
def ApproxUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∃ θ : ℝ, ‖A - (Complex.exp (θ * Complex.I)) • B‖ ≤ tol

/-- The condition that on every normalized input, the outputs of `A` and `B` differ by at most
the tolerance after a possibly input dependent phase adjustment. -/
def WholeStateUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∀ ψ : QState n, Normalized ψ → ∃ θ : ℝ,
    ‖toEuclidean_fromVec (A *ᵥ ψ - (Complex.exp (θ * Complex.I)) • (B *ᵥ ψ))‖ ≤ tol

/-- The condition that every normalized data input produces a state whose component outside the
all zero auxiliary subspace has norm at most the tolerance. -/
def cleanAncillaRestored {width : ℕ} (w : ℕ)
    (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) : Prop :=
  ∀ ψ : QState (Reg w), Normalized ψ →
    ‖toEuclidean_fromVec (fun z : Reg width =>
      if auxBits w z = ZeroStr (width - w) then 0 else (M *ᵥ ψ) z)‖ ≤ tol

/-- A register width together with a list of local gates acting on that register. -/
structure SynthWord where

  width : ℕ

  letters : List (LocalQFTGate width)

/-- The condition that every letter of a synthesized word is a fixed primitive gate. -/
def synthWordLegal (p : SynthWord) : Prop :=
  ∀ g ∈ p.letters, IsFixedPrimitive g

/-- The number of letters in a synthesized word. -/
def synthWordGates (p : SynthWord) : ℕ := p.letters.length

/-- The oracle call count for a synthesized local gate word, defined to be zero. -/
def synthWordOracleCalls (_p : SynthWord) : ℕ := 0

/-- The synthesis condition combining an expanded register width, fixed primitive legality, zero
oracle calls, operator approximation up to phase, and clean ancilla restoration. -/
def synthesisApprox (w : ℕ) (g : LocalQFTGate w) (p : SynthWord) (tol : ℝ) : Prop :=
  (∃ a : ℕ, p.width = w + a) ∧
  synthWordLegal p ∧
  synthWordOracleCalls p = 0 ∧
  ApproxUpToPhase (localProgramMatrix p.letters * padClean w p.width)
    (padClean w p.width * localGateMatrix g) tol ∧
  cleanAncillaRestored w (localProgramMatrix p.letters * padClean w p.width) tol

/-- The synthesis approximation condition at dyadic tolerance `(1 / 2)^k`. -/
def synthesisWordAccepted (w : ℕ) (g : LocalQFTGate w) (k : ℕ) (p : SynthWord) : Prop :=
  synthesisApprox w g p (((2 : ℝ) ⁻¹) ^ k)

/-- A synthesis compiler specifying an ancilla count and an emitted local gate word for each
input gate and precision. -/
structure SynthCompiler where

  anc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ

  emit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) → List (LocalQFTGate (w + anc w g k))

/-- The synthesized word formed from a compiler's expanded width and emitted letters. -/
def SynthCompiler.Segment (c : SynthCompiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    SynthWord :=
  ⟨w + c.anc w g k, c.emit w g k⟩

/-- The condition that a compiler's segment is accepted as a synthesis of the input gate at
precision `k`. -/
def SynthCompiler.AcceptsAt (c : SynthCompiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    Prop :=
  synthesisWordAccepted w g k (c.Segment w g k)

/-- The existence of common polynomial bounds on a compiler's emitted word length and ancilla
count in the synthesis input length plus precision. -/
def UniformSynthLedger (c : SynthCompiler) : Prop :=
  ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
    (c.emit w g k).length ≤ C * (1 + synthInputBits w g k + k) ^ D ∧
    c.anc w g k ≤ C * (1 + synthInputBits w g k + k) ^ D

/-- The dyadic phase angle of a controlled phase gate, and no angle for other local gate
constructors. -/
def gateAngle {w : ℕ} : LocalQFTGate w → Option ℝ
  | .cp _ _ e neg => some (dyadicPhaseAngle e neg)
  | _ => none

/-- For a gate with an angle, the condition that `q` approximates it within `(1 / 2)^bits` and
is an integer multiple of `1 / 2^bits`; for other gates the condition is true. -/
def angleInputOK {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ) : Prop :=
  match gateAngle g with
  | none => True
  | some θ => |((q : ℝ) - θ)| ≤ ((2 : ℝ) ⁻¹) ^ bits ∧ ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits)

/-- A machine model with a state type, Boolean input initialization, optional next states,
Boolean output, and a natural space cost. -/
structure BitWordMachineModel where

  State : Type

  init : List Bool → State

  step : State → Option State

  emit : State → List Bool

  space : State → ℕ

/-- The optional machine state after a specified number of transitions, starting from the
initialized input state. -/
def BitWordMachineModel.runAt (M : BitWordMachineModel) (input : List Bool) :
    ℕ → Option M.State
  | 0 => some (M.init input)
  | t + 1 => (M.runAt input t).bind M.step

/-- The condition that a state is reached at time `t` and has no next transition. -/
def BitWordMachineModel.HaltsAt (M : BitWordMachineModel) (input : List Bool) (t : ℕ) :
    Prop :=
  ∃ s : M.State, M.runAt input t = some s ∧ M.step s = none

/-- The condition that the machine reaches a halting state at time `t` with the specified
Boolean output. -/
def BitWordMachineModel.emitsAt (M : BitWordMachineModel) (input : List Bool) (t : ℕ)
    (out : List Bool) : Prop :=
  ∃ s : M.State, M.runAt input t = some s ∧ M.step s = none ∧ M.emit s = out

/-- The maximum space cost among states reached from time zero through `t`, assigning zero to
absent states. -/
def BitWordMachineModel.PeakSpace (M : BitWordMachineModel) (input : List Bool) (t : ℕ) :
    ℕ :=
  ((List.range (t + 1)).map (fun i => (M.runAt input i).elim 0 M.space)).foldl max 0

/-- An oracle slot together with flags indicating adjoint access and the presence of a control. -/
structure AccessForm (S : Type) where

  slot : S

  adj : Bool

  controlled : Bool

/-- A step consisting either of a known local gate with a precision label or of an oracle call
with an adjoint flag and optional control bit and value. -/
inductive MixedStep (n w : ℕ) (S : Type) where
  | known : LocalQFTGate n → ℕ → MixedStep n w S
  | call : S → Bool → Option (Fin n × Bool) → MixedStep n w S

/-- The access form of an oracle call, or no access form for a known gate. -/
def MixedStep.form {n w : ℕ} {S : Type} : MixedStep n w S → Option (AccessForm S)
  | .known _ _ => none
  | .call slot adj ctrl => some ⟨slot, adj, ctrl.isSome⟩

/-- The number of known gate steps in a mixed word. -/
def knownCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ :=
  W.countP (fun s => match s with | .known _ _ => true | .call _ _ _ => false)

/-- The number of oracle call steps in a mixed word. -/
def callCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ :=
  W.countP (fun s => match s with | .known _ _ => false | .call _ _ _ => true)

/-- The list of known local gates in a mixed word, in their original order. -/
def knownGates {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : List (LocalQFTGate n) :=
  W.filterMap (fun s => match s with | .known g _ => some g | .call _ _ _ => none)

/-- The list of precision labels on known gates in a mixed word, in their original order. -/
def knownPrecs {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : List ℕ :=
  W.filterMap (fun s => match s with | .known _ m => some m | .call _ _ _ => none)

/-- The number of steps in a mixed word with a specified oracle access form. -/
def accessCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) (φ : AccessForm S) : ℕ :=
  W.countP (fun s => match s.form with
    | some φ' => if φ' = φ then true else false
    | none => false)

/-- The condition that every oracle access form used by the mixed word belongs to the supplied
paid list. -/
def mixedWordLegal {n w : ℕ} {S : Type} (W : List (MixedStep n w S))
    (paid : List (AccessForm S)) : Prop :=
  ∀ s ∈ W, match s.form with | some φ => φ ∈ paid | none => True

/-- The matrix of a mixed step, using the local gate matrix or the optionally adjointed and
controlled oracle on the first `w` bits while preserving the remaining bits. -/
noncomputable def mixedStepMatrix {n w : ℕ} (hw : w ≤ n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) : MixedStep n w S → Matrix (Reg n) (Reg n) ℂ
  | .known g _ => localGateMatrix g
  | .call slot adj ctrl =>
      let Q : Matrix (Reg w) (Reg w) ℂ := if adj then (O slot)ᴴ else O slot
      fun p q =>
        if (∀ i : Fin n, w ≤ i.val → p i = q i) then
          let active := match ctrl with
            | none => true
            | some (c, v) => p c = v
          if active then Q (dataBits w hw p) (dataBits w hw q)
          else if dataBits w hw p = dataBits w hw q then 1 else 0
        else 0

/-- The reverse ordered product of the matrices of a mixed word's steps. -/
noncomputable def mixedWordMatrix {n w : ℕ} (hw : w ≤ n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)) :
    Matrix (Reg n) (Reg n) ℂ :=
  (W.map (mixedStepMatrix hw O)).reverse.prod

/-- The known gate count of a mixed word. -/
def mixedWordGates {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ := knownCount W

/-- The same local gate on a larger register, preserving each register index and phase
parameter. -/
def liftGateTo {n n' : ℕ} (h : n ≤ n') : LocalQFTGate n → LocalQFTGate n'
  | .h a => .h ⟨a.val, by omega⟩
  | .cp a c e neg => .cp ⟨a.val, by omega⟩ ⟨c.val, by omega⟩ e neg
  | .swap a c => .swap ⟨a.val, by omega⟩ ⟨c.val, by omega⟩

/-- The local gate word obtained by lifting every letter to a larger register. -/
def liftWordTo {n n' : ℕ} (h : n ≤ n') (gs : List (LocalQFTGate n)) :
    List (LocalQFTGate n') :=
  gs.map (liftGateTo h)

/-- Replaces known gate steps by successive supplied segments with precision label zero and
lifts oracle control indices to the expanded register. -/
def compileWord {n w A : ℕ} {S : Type}
    (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A)))) :
    List (MixedStep (n + A) w S) :=
  match W with
  | [] => []
  | .known _ _ :: rest =>
      (match segs with
       | s :: segs' => s.map (fun h => .known h 0) ++ compileWord rest segs'
       | [] => compileWord rest [])
  | .call slot adj ctrl :: rest =>
      .call slot adj (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2))) ::
        compileWord rest segs

/-- The condition that the segment and precision lists each have length equal to the known gate
count of the input word. -/
def AlignedWith {n w A : ℕ} {S : Type} (W : List (MixedStep n w S))
    (segs : List (List (LocalQFTGate (n + A)))) (ks : List ℕ) : Prop :=
  segs.length = knownCount W ∧ ks.length = knownCount W

/-- A common auxiliary width and a precision per known gate, with proofs of list length and that
every required ancilla count fits in that width. -/
structure WordCompilation {n w : ℕ} {S : Type} (c : SynthCompiler)
    (W : List (MixedStep n w S)) where

  A : ℕ

  ks : List ℕ

  hlen : ks.length = knownCount W

  hanc : ∀ g k, (g, k) ∈ List.zip (knownGates W) ks → c.anc n g k ≤ A

/-- The condition that each segment is the corresponding compiler output lifted to the common
expanded width at its assigned precision. -/
def SegmentsFrom {n w A : ℕ} {S : Type} (c : SynthCompiler) (W : List (MixedStep n w S))
    (segs : List (List (LocalQFTGate (n + A)))) (ks : List ℕ) : Prop :=
  List.Forall₂ (fun (g : LocalQFTGate n) (sk : List (LocalQFTGate (n + A)) × ℕ) =>
    ∃ h : c.anc n g sk.2 ≤ A,
      sk.1 = (c.emit n g sk.2).map (liftGateTo (Nat.add_le_add_left h n)))
  (knownGates W) (List.zip segs ks)

/-- The condition that the sum of input and synthesis dyadic tolerances over the known gates is
at most `ε`. -/
def BudgetLE {n w : ℕ} {S : Type} {c : SynthCompiler} {W : List (MixedStep n w S)}
    (cmp : WordCompilation c W) (ε : ℝ) : Prop :=
  ((List.zip (knownPrecs W) cmp.ks).map (fun mk =>
    ((2 : ℝ) ⁻¹) ^ mk.1 + ((2 : ℝ) ⁻¹) ^ mk.2)).sum ≤ ε

/-- Equality of every oracle access form count between an original mixed word and its compiled
word. -/
def AccessPreserved {n w A : ℕ} {S : Type} (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) : Prop :=
  ∀ φ : AccessForm S, accessCount W' φ = accessCount W φ

/-- The condition that the compiled and original word matrices, compared through clean padding,
are within operator norm tolerance `ε` up to phase. -/
def CompiledOperatorErrorLE {n w A : ℕ} (hw : w ≤ n) (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  ApproxUpToPhase (mixedWordMatrix hwA O W' * padClean n (n + A))
    (padClean n (n + A) * mixedWordMatrix hw O W) ε

/-- The condition that on every normalized input, the padded compiled and original outputs
differ by at most `ε` after a possibly input dependent phase adjustment. -/
def CompiledWholeStateErrorLE {n w A : ℕ} (hw : w ≤ n) (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  ∀ ψ : QState (Reg n), Normalized ψ → ∃ θ : ℝ,
    ‖toEuclidean_fromVec ((mixedWordMatrix hwA O W' * padClean n (n + A)) *ᵥ ψ -
      (Complex.exp (θ * Complex.I)) • ((padClean n (n + A) * mixedWordMatrix hw O W) *ᵥ ψ))‖
      ≤ ε

/-- The condition that the compiled word restores the added auxiliary pool to zero with leakage
norm at most `ε` on every normalized input. -/
def CompiledCleanPoolLE {n w A : ℕ} (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  cleanAncillaRestored n (mixedWordMatrix hwA O W' * padClean n (n + A)) ε

/-- The condition that gate count and bit time are bounded by a sum of polynomial segment bounds
and peak space by their maximum. -/
def CompileLedgersOK (sizes : List ℕ) (gateCount bitTime peakSpace : ℕ) (C D : ℕ) : Prop :=
  gateCount ≤ (sizes.map (fun s => C * (1 + s) ^ D)).sum ∧
  bitTime ≤ (sizes.map (fun s => C * (1 + s) ^ D)).sum ∧
  peakSpace ≤ (sizes.map (fun s => C * (1 + s) ^ D)).foldl max 0

/-- The synthesis input length of a gate and precision, plus the precision parameter itself. -/
def segmentSize {n : ℕ} (g : LocalQFTGate n) (k : ℕ) : ℕ :=
  synthInputBits n g k + k

end

end Qatlib.Concepts.NumericalWord.MixedWordError
