/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGateDecisionConsumers

/-!
# Uniform finite-gate circuit generators

This module defines bit encodings and bounded Turing-machine generators for finite-gate circuit
families. `UniformBqpGenerator` records a machine and polynomial resource bounds, while
`uniformBqpGeneratorValid` requires successful generation of legal circuits with bounded length,
width, and encoding size. These definitions provide a concrete setting for uniform quantum
computation as studied in [BernsteinVazirani1997].

`uniformBqpAcceptProb` gives the Born probability of observing a true final wire.
`UniformAcceptanceEstimator` specifies machines for approximating this probability, and the
backend predicates describe dyadic approximations and exact finite representations of gate
entries; see [NielsenChuang2010] for the circuit and measurement background.

## Main statements

* `encodeUniformBqpWord` and `decodeUniformBqpWord`: serialization of circuit widths and gate
  lists.
* `uniformBqpGeneratorValid`: successful generation with explicit resource bounds.
* `estimatorAccurate`: signed dyadic approximation of acceptance probabilities.
* `finiteDigitBackendPremise`: exact finite representations of legal gate entries.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs

open Qatlib

/-- Encodes `k` as `k` true bits followed by a false delimiter. -/
def encodeUnaryField (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Parses a false-terminated unary natural number, returning its value and the remaining bits.
Returns `none` if no delimiter is found. -/
private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

/-- Encodes a finite gate using a unary constructor tag followed by unary wire indices. -/
def encodeFiniteGateCode : FiniteGateCode → List Bool
  | .h w => encodeUnaryField 0 ++ encodeUnaryField w
  | .x w => encodeUnaryField 1 ++ encodeUnaryField w
  | .t w => encodeUnaryField 2 ++ encodeUnaryField w
  | .tdg w => encodeUnaryField 3 ++ encodeUnaryField w
  | .cx c t => encodeUnaryField 4 ++ encodeUnaryField c ++ encodeUnaryField t

/-- Parses the wire fields for a gate constructor tag, returning the gate and unused suffix.
Unrecognized tags or incomplete fields produce `none`. -/
private def parseGateCodeFields (tag : ℕ) (bits : List Bool) :
    Option (FiniteGateCode × List Bool) := do
  if tag = 0 then
    let (w, rest) ← parseUnaryField bits
    pure (.h w, rest)
  else if tag = 1 then
    let (w, rest) ← parseUnaryField bits
    pure (.x w, rest)
  else if tag = 2 then
    let (w, rest) ← parseUnaryField bits
    pure (.t w, rest)
  else if tag = 3 then
    let (w, rest) ← parseUnaryField bits
    pure (.tdg w, rest)
  else if tag = 4 then
    let (c, rest) ← parseUnaryField bits
    let (t, tail) ← parseUnaryField rest
    pure (.cx c t, tail)
  else
    none

/-- Parses a concatenated list of gate encodings with a bound on the number of parsing steps.
Succeeds only when all bits are consumed within the fuel bound. -/
private def parseGateCodeListFuel : ℕ → List Bool → Option (List FiniteGateCode)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseUnaryField bits
      let (g, tail) ← parseGateCodeFields tag rest
      let gs ← parseGateCodeListFuel fuel tail
      pure (g :: gs)

/-- Decodes a unary circuit width followed by a list of finite gate codes. Returns `none` when
the encoding cannot be parsed completely. -/
def decodeUniformBqpWord (bits : List Bool) : Option (ℕ × List FiniteGateCode) := do
  let (q, rest) ← parseUnaryField bits
  let gs ← parseGateCodeListFuel rest.length rest
  pure (q, gs)

/-- Serializes a circuit width and gate list by concatenating the unary width with the gate
encodings. -/
def encodeUniformBqpWord (q : ℕ) (gs : List FiniteGateCode) : List Bool :=
  encodeUnaryField q ++ gs.flatMap encodeFiniteGateCode

/-- A finite-control bit Turing machine equipped with coefficients and degrees for polynomial
bounds on generation time, gate count, and circuit width. -/
structure UniformBqpGenerator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  wordCoefficient : ℕ
  wordDegree : ℕ
  spaceCoefficient : ℕ
  spaceDegree : ℕ

/-- The natural-number resource bound `c * (n + 1) ^ d`. -/
def uniformBqpPolynomial (c d n : ℕ) : ℕ := c * (n + 1) ^ d

/-- The generation-time bound specified by the generator's time coefficient and degree. -/
def uniformBqpTimeBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.timeCoefficient g.timeDegree n

/-- The gate-count bound specified by the generator's word coefficient and degree. -/
def uniformBqpWordBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.wordCoefficient g.wordDegree n

/-- The circuit-width bound specified by the generator's space coefficient and degree. -/
def uniformBqpSpaceBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.spaceCoefficient g.spaceDegree n

/-- Runs a Turing machine from a configuration for at most the supplied number of transitions.
Returns the halted configuration, or `none` if it has not halted within the bound. -/
private def runUntilHaltWithin {k : ℕ}
    (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0, cfg => if Turing.TM0.step machine cfg = none then some cfg else none
  | fuel + 1, cfg =>
      match Turing.TM0.step machine cfg with
      | none => some cfg
      | some next => runUntilHaltWithin machine fuel next

/-- Reads at most the supplied number of Boolean symbols from a tape, stopping at the first
blank. Returns `none` when another nonblank symbol remains after the allowed symbols have
been read. -/
private def readOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool)
  | 0, tape => if tape.nth 0 = none then some [] else none
  | fuel + 1, tape =>
      match tape.nth 0 with
      | none => some []
      | some bit => (readOutputUntilBlank fuel tape.tail).map (bit :: ·)

/-- The unary input consisting of `n` nonblank true symbols. -/
def uniformBqpUnaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

/-- Runs the generator on unary input `n` within its time bound, reads a bounded output segment,
and decodes a circuit width and gate list. Any failure in this process yields `none`. -/
noncomputable def uniformBqpGeneratedAt (g : UniformBqpGenerator) (n : ℕ) :
    Option (ℕ × List FiniteGateCode) :=
  (runUntilHaltWithin g.machine (uniformBqpTimeBound g n)
    (Turing.TM0.init (uniformBqpUnaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀).bind
        decodeUniformBqpWord

/-- The generated circuit at input length `n`, defaulting to width zero and an empty gate list
when bounded generation fails. -/
noncomputable def uniformBqpGeneratedTotal (g : UniformBqpGenerator) (n : ℕ) :
    ℕ × List FiniteGateCode :=
  (uniformBqpGeneratedAt g n).getD (0, [])

/-- Requires successful generation of a legal circuit at every input length, with a halting
witness within the time bound. Gate count, circuit width, and encoded output length must
also satisfy the stated bounds. -/
def uniformBqpGeneratorValid (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∃ (q : ℕ) (gs : List FiniteGateCode),
    uniformBqpGeneratedAt g n = some (q, gs) ∧
      (∃ t ≤ uniformBqpTimeBound g n,
        BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t) ∧
      finiteWordLegal q gs = true ∧
      gs.length ≤ uniformBqpWordBound g n ∧
      q ≤ uniformBqpSpaceBound g n ∧
      (encodeUniformBqpWord q gs).length ≤ n + uniformBqpTimeBound g n

/-- Runs the finite gate circuit on the computational basis state indexed by `x`, using the
identity oracle matrix. -/
noncomputable def uniformBqpRun (q : ℕ) (gs : List FiniteGateCode) (x : Reg q) :
    QState (Reg q) :=
  Run (1 : Matrix (Reg q) (Reg q) ℂ) (finiteCodeCircuit q gs) (Qatlib.Foundations.PureStateMath.Ket x)

/-- The basis configurations whose last wire is true. For a zero-width register, the event is
empty. -/
def uniformBqpOutputEvent (q : ℕ) : Finset (Reg q) :=
  if h : 0 < q then
    Finset.univ.filter fun z : Reg q => z ⟨q - 1, by omega⟩ = true
  else ∅

/-- The Born probability that running the gate list on basis input `x` produces a configuration
in `uniformBqpOutputEvent`. -/
noncomputable def uniformBqpAcceptProb (q : ℕ) (gs : List FiniteGateCode)
    (x : Reg q) : ℝ :=
  MeasureProb (uniformBqpRun q gs x) (uniformBqpOutputEvent q)

/-- Encodes a circuit, a unary separator tag, the input register bits, and the requested
precision as nonblank tape symbols. -/
def encodeEstimatorInput (q : ℕ) (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) :
    List (Option Bool) :=
  (encodeUniformBqpWord q gs ++ encodeUnaryField 5 ++ List.ofFn x ++ encodeUnaryField k).map
    (fun b => some b)

/-- A finite-control bit Turing machine equipped with a polynomial time-bound coefficient and
degree for acceptance-probability estimation. -/
structure UniformAcceptanceEstimator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ

/-- The estimator's polynomial time bound evaluated at the sum of `2 ^ q` and the encoded
estimator input length. -/
def uniformEstimatorTimeBound (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) : ℕ :=
  uniformBqpPolynomial e.timeCoefficient e.timeDegree
    (2 ^ q + (encodeEstimatorInput q gs x k).length)

/-- Runs the estimator on the encoded circuit, input, and precision within its prescribed time
bound, then reads its bounded Boolean output. Returns `none` if execution or output reading
fails. -/
noncomputable def uniformEstimatorOutput (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) : Option (List Bool) :=
  (runUntilHaltWithin e.machine (uniformEstimatorTimeBound e q gs x k)
    (Turing.TM0.init (encodeEstimatorInput q gs x k))).bind fun cfg =>
      (readOutputUntilBlank
        ((encodeEstimatorInput q gs x k).length +
          uniformEstimatorTimeBound e q gs x k + 1) cfg.Tape.right₀)

/-- Interprets a Boolean list as a signed binary integer, with a true leading bit indicating a
negative sign. The empty list represents zero. -/
def signedDyadicNumeral (bits : List Bool) : ℤ :=
  match bits with
  | [] => 0
  | sign :: rest =>
      (if sign then (-1 : ℤ) else 1) *
        rest.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

/-- Requires an output at every precision `k` whose signed numerator has absolute value at most
`2 ^ k`. Dividing that numerator by `2 ^ k` must approximate the acceptance probability
within `2 ^ (-k)`. -/
def estimatorAccurate (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) : Prop :=
  ∀ k : ℕ, ∃ out : List Bool,
    uniformEstimatorOutput e q gs x k = some out ∧
      |signedDyadicNumeral out| ≤ (2 ^ k : ℕ) ∧
      |(signedDyadicNumeral out : ℝ) / (2 ^ k : ℕ) -
          uniformBqpAcceptProb q gs x| ≤ (2 : ℝ) ^ (-(k : ℤ))

/-- A family assigning a circuit width and a finite gate list to each natural-number input
length. -/
abbrev StandardWordFamily := ℕ → ℕ × List FiniteGateCode

/-- Requires every gate list in the family to be legal for its associated circuit width. -/
def standardFamilyLegal (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, finiteWordLegal (W n).1 (W n).2 = true

/-- Requires polynomial bounds on the gate count and circuit width of every member of a word
family. -/
def standardFamilyBounded (cW dW cS dS : ℕ) (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, (W n).2.length ≤ uniformBqpPolynomial cW dW n ∧
    (W n).1 ≤ uniformBqpPolynomial cS dS n

/-- Requires the bounded native generator to return exactly the specified word family at every
input length. -/
def nativeRealizes (g : UniformBqpGenerator) (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, uniformBqpGeneratedAt g n = some (W n)

/-- A one-state generator that continually moves right, equipped with linear resource bounds. -/
def uniformBqpDivergingGenerator : UniformBqpGenerator where
  controlBound := 0
  machine := fun _ _ => some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩
  timeCoefficient := 1
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 1
  spaceDegree := 1

/-- A one-state machine that moves right over nonblank symbols and halts on a blank. -/
private def uniformBqpClockMachine : Turing.TM0.Machine (Option Bool) (Fin 1) :=
  fun _ a => if a = none then none else some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩

/-- The blank-stopping rightward clock machine packaged as a generator with linear resource
bounds. -/
def uniformBqpClockGenerator : UniformBqpGenerator where
  controlBound := 0
  machine := uniformBqpClockMachine
  timeCoefficient := 1
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 1
  spaceDegree := 1

/-- A finite-control machine that scans to a blank, writes the prescribed Boolean word, and
moves back toward its beginning before halting. -/
private def uniformBqpWordPrinterMachine (bs : List Bool) :
    Turing.TM0.Machine (Option Bool) (Fin (3 * bs.length + 1)) := fun q a =>
  have hq := q.isLt
  if h0 : q.val = 0 ∧ a = none ∧ 1 ≤ bs.length then
    some ⟨⟨1, by omega⟩,
      Turing.TM0.Stmt.write (some (bs.getD 0 false))⟩
  else if q.val = 0 ∧ a = none then
    none
  else if q.val = 0 then
    some ⟨⟨0, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩
  else if h2 : 2 ≤ q.val ∧ q.val % 2 = 0 ∧ q.val ≤ 2 * bs.length - 2 then
    some ⟨⟨q.val + 1, by omega⟩,
      Turing.TM0.Stmt.write (some (bs.getD (q.val / 2) false))⟩
  else if h3 : q.val % 2 = 1 ∧ q.val ≤ 2 * bs.length - 3 then
    some ⟨⟨q.val + 1, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.right⟩
  else if h4 : 1 ≤ q.val ∧ 2 * bs.length - 1 ≤ q.val ∧ q.val ≤ 3 * bs.length - 3 then
    some ⟨⟨q.val + 1, by omega⟩, Turing.TM0.Stmt.move Turing.Dir.left⟩
  else none

/-- Packages the printer for a fixed encoded circuit as a generator, with explicit linear bounds
depending on the encoding length and circuit width. -/
def uniformBqpWordPrinter (q : ℕ) (gs : List FiniteGateCode) : UniformBqpGenerator where
  controlBound := 3 * (encodeUniformBqpWord q gs).length
  machine := uniformBqpWordPrinterMachine (encodeUniformBqpWord q gs)
  timeCoefficient := 3 * (encodeUniformBqpWord q gs).length + 2
  timeDegree := 1
  wordCoefficient := (encodeUniformBqpWord q gs).length + 1
  wordDegree := 1
  spaceCoefficient := q + 1
  spaceDegree := 1

/-- Requires every circuit successfully returned by bounded generation to have a legal gate list
for its reported width. -/
def generatorWellformed (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∀ (q : ℕ) (gs : List FiniteGateCode),
    uniformBqpGeneratedAt g n = some (q, gs) → finiteWordLegal q gs = true

/-- Requires any two move transitions from the same control state to move in the same direction,
regardless of the scanned symbol. -/
def tm0Unidirectional {k : ℕ}
    (m : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) : Prop :=
  ∀ (q : Fin (k + 1)) (a b : Option Bool)
      (r s : Fin (k + 1) × Turing.TM0.Stmt (Option Bool)),
    m q a = some r → m q b = some s →
      (∃ d₁ : Turing.Dir, r.2 = Turing.TM0.Stmt.move d₁) →
      (∃ d₂ : Turing.Dir, s.2 = Turing.TM0.Stmt.move d₂) → r.2 = s.2

/-- The condition that the generator's underlying Turing machine is unidirectional. -/
def generatorNormalForm (g : UniformBqpGenerator) : Prop :=
  tm0Unidirectional g.machine

/-- Requires a polynomial bound within which the generator machine halts on every unary input. -/
def generatorClocked (g : UniformBqpGenerator) : Prop :=
  ∃ c d : ℕ, ∀ n : ℕ, ∃ t ≤ uniformBqpPolynomial c d n,
    BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t

/-- Requires the generator machine to halt after some finite number of steps on every unary
input. -/
def generatorHaltsEffectively (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t

/-- Doubles the circuit width and appends a copy of the gate list shifted onto the second
register block. -/
def duplicateWord (q : ℕ) (gs : List FiniteGateCode) : ℕ × List FiniteGateCode :=
  (2 * q, gs ++ gs.map (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q))

/-- Requires integer numerators approximating the real and imaginary parts of `z` with
denominator `2 ^ lam` and error at most `2 ^ (-lam)` in each component. -/
def HasDyadicDigit (lam : ℕ) (z : ℂ) : Prop :=
  ∃ m : ℤ × ℤ,
    |(m.1 : ℝ) / (2 ^ lam : ℕ) - z.re| ≤ (2 : ℝ) ^ (-(lam : ℤ)) ∧
      |(m.2 : ℝ) / (2 ^ lam : ℕ) - z.im| ≤ (2 : ℝ) ^ (-(lam : ℤ))

/-- Requires a legal gate word whose gate-matrix entries all possess dyadic approximations at
precision `lam`. -/
def dyadicBackendPremise (lam : ℕ) (w : ℕ × List FiniteGateCode) : Prop :=
  finiteWordLegal w.1 w.2 = true ∧
    ∀ g ∈ w.2, ∀ i j : Reg w.1, HasDyadicDigit lam (finiteCodeMatrix w.1 g i j)

/-- Finite data representing a Gaussian integer multiplied by an optional factor of the square
root of two and divided by a power of two. -/
structure FiniteDigitAmplitude where
  re : ℤ
  im : ℤ
  sqrt2Factor : Bool
  denomExp : ℕ

/-- The complex value `(re + im * I)` times the selected square-root factor, divided by `2 ^
denomExp`. -/
noncomputable def finiteDigitVal (r : FiniteDigitAmplitude) : ℂ :=
  ((r.re : ℂ) + (r.im : ℂ) * Complex.I) *
    (if r.sqrt2Factor then Real.sqrt 2 else 1) / ((2 ^ r.denomExp : ℕ) : ℂ)

/-- Requires a legal gate word with an exact `FiniteDigitAmplitude` representation for every
entry of each gate matrix. -/
def finiteDigitBackendPremise (w : ℕ × List FiniteGateCode) : Prop :=
  finiteWordLegal w.1 w.2 = true ∧
    ∀ g ∈ w.2, ∀ i j : Reg w.1,
      ∃ r : FiniteDigitAmplitude, finiteDigitVal r = finiteCodeMatrix w.1 g i j

/-- Requires halting on every unary input and a polynomial bound on the encoding length of the
totalized generated circuit family. -/
def bitTmBackendPremise (g : UniformBqpGenerator) : Prop :=
  generatorHaltsEffectively g ∧
    ∃ c d : ℕ, ∀ n : ℕ,
      (encodeUniformBqpWord (uniformBqpGeneratedTotal g n).1
        (uniformBqpGeneratedTotal g n).2).length ≤ uniformBqpPolynomial c d n

end Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
