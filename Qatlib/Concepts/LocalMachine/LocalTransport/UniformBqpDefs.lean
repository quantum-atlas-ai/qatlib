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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs

open Qatlib

def encodeUnaryField (k : ℕ) : List Bool := List.replicate k true ++ [false]

private def parseUnaryField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryField rest).map fun (k, tail) => (k + 1, tail)

def encodeFiniteGateCode : FiniteGateCode → List Bool
  | .h w => encodeUnaryField 0 ++ encodeUnaryField w
  | .x w => encodeUnaryField 1 ++ encodeUnaryField w
  | .t w => encodeUnaryField 2 ++ encodeUnaryField w
  | .tdg w => encodeUnaryField 3 ++ encodeUnaryField w
  | .cx c t => encodeUnaryField 4 ++ encodeUnaryField c ++ encodeUnaryField t

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

private def parseGateCodeListFuel : ℕ → List Bool → Option (List FiniteGateCode)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, bits => do
      let (tag, rest) ← parseUnaryField bits
      let (g, tail) ← parseGateCodeFields tag rest
      let gs ← parseGateCodeListFuel fuel tail
      pure (g :: gs)

def decodeUniformBqpWord (bits : List Bool) : Option (ℕ × List FiniteGateCode) := do
  let (q, rest) ← parseUnaryField bits
  let gs ← parseGateCodeListFuel rest.length rest
  pure (q, gs)

def encodeUniformBqpWord (q : ℕ) (gs : List FiniteGateCode) : List Bool :=
  encodeUnaryField q ++ gs.flatMap encodeFiniteGateCode

structure UniformBqpGenerator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ
  wordCoefficient : ℕ
  wordDegree : ℕ
  spaceCoefficient : ℕ
  spaceDegree : ℕ

def uniformBqpPolynomial (c d n : ℕ) : ℕ := c * (n + 1) ^ d

def uniformBqpTimeBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.timeCoefficient g.timeDegree n

def uniformBqpWordBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.wordCoefficient g.wordDegree n

def uniformBqpSpaceBound (g : UniformBqpGenerator) (n : ℕ) : ℕ :=
  uniformBqpPolynomial g.spaceCoefficient g.spaceDegree n

private def runUntilHaltWithin {k : ℕ}
    (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) :
    ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) →
      Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0, cfg => if Turing.TM0.step machine cfg = none then some cfg else none
  | fuel + 1, cfg =>
      match Turing.TM0.step machine cfg with
      | none => some cfg
      | some next => runUntilHaltWithin machine fuel next

private def readOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool)
  | 0, tape => if tape.nth 0 = none then some [] else none
  | fuel + 1, tape =>
      match tape.nth 0 with
      | none => some []
      | some bit => (readOutputUntilBlank fuel tape.tail).map (bit :: ·)

def uniformBqpUnaryInput (n : ℕ) : List (Option Bool) :=
  List.replicate n (some true)

noncomputable def uniformBqpGeneratedAt (g : UniformBqpGenerator) (n : ℕ) :
    Option (ℕ × List FiniteGateCode) :=
  (runUntilHaltWithin g.machine (uniformBqpTimeBound g n)
    (Turing.TM0.init (uniformBqpUnaryInput n))).bind fun cfg =>
      (readOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀).bind
        decodeUniformBqpWord

noncomputable def uniformBqpGeneratedTotal (g : UniformBqpGenerator) (n : ℕ) :
    ℕ × List FiniteGateCode :=
  (uniformBqpGeneratedAt g n).getD (0, [])

def uniformBqpGeneratorValid (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∃ (q : ℕ) (gs : List FiniteGateCode),
    uniformBqpGeneratedAt g n = some (q, gs) ∧
      (∃ t ≤ uniformBqpTimeBound g n,
        BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t) ∧
      finiteWordLegal q gs = true ∧
      gs.length ≤ uniformBqpWordBound g n ∧
      q ≤ uniformBqpSpaceBound g n ∧
      (encodeUniformBqpWord q gs).length ≤ n + uniformBqpTimeBound g n

noncomputable def uniformBqpRun (q : ℕ) (gs : List FiniteGateCode) (x : Reg q) :
    QState (Reg q) :=
  Run (1 : Matrix (Reg q) (Reg q) ℂ) (finiteCodeCircuit q gs) (Qatlib.Foundations.PureStateMath.Ket x)

def uniformBqpOutputEvent (q : ℕ) : Finset (Reg q) :=
  if h : 0 < q then
    Finset.univ.filter fun z : Reg q => z ⟨q - 1, by omega⟩ = true
  else ∅

noncomputable def uniformBqpAcceptProb (q : ℕ) (gs : List FiniteGateCode)
    (x : Reg q) : ℝ :=
  MeasureProb (uniformBqpRun q gs x) (uniformBqpOutputEvent q)

def encodeEstimatorInput (q : ℕ) (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) :
    List (Option Bool) :=
  (encodeUniformBqpWord q gs ++ encodeUnaryField 5 ++ List.ofFn x ++ encodeUnaryField k).map
    (fun b => some b)

structure UniformAcceptanceEstimator where
  controlBound : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (controlBound + 1))
  timeCoefficient : ℕ
  timeDegree : ℕ

def uniformEstimatorTimeBound (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) : ℕ :=
  uniformBqpPolynomial e.timeCoefficient e.timeDegree
    (2 ^ q + (encodeEstimatorInput q gs x k).length)

noncomputable def uniformEstimatorOutput (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) (k : ℕ) : Option (List Bool) :=
  (runUntilHaltWithin e.machine (uniformEstimatorTimeBound e q gs x k)
    (Turing.TM0.init (encodeEstimatorInput q gs x k))).bind fun cfg =>
      (readOutputUntilBlank
        ((encodeEstimatorInput q gs x k).length +
          uniformEstimatorTimeBound e q gs x k + 1) cfg.Tape.right₀)

def signedDyadicNumeral (bits : List Bool) : ℤ :=
  match bits with
  | [] => 0
  | sign :: rest =>
      (if sign then (-1 : ℤ) else 1) *
        rest.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

def estimatorAccurate (e : UniformAcceptanceEstimator) (q : ℕ)
    (gs : List FiniteGateCode) (x : Reg q) : Prop :=
  ∀ k : ℕ, ∃ out : List Bool,
    uniformEstimatorOutput e q gs x k = some out ∧
      |signedDyadicNumeral out| ≤ (2 ^ k : ℕ) ∧
      |(signedDyadicNumeral out : ℝ) / (2 ^ k : ℕ) -
          uniformBqpAcceptProb q gs x| ≤ (2 : ℝ) ^ (-(k : ℤ))

abbrev StandardWordFamily := ℕ → ℕ × List FiniteGateCode

def standardFamilyLegal (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, finiteWordLegal (W n).1 (W n).2 = true

def standardFamilyBounded (cW dW cS dS : ℕ) (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, (W n).2.length ≤ uniformBqpPolynomial cW dW n ∧
    (W n).1 ≤ uniformBqpPolynomial cS dS n

def nativeRealizes (g : UniformBqpGenerator) (W : StandardWordFamily) : Prop :=
  ∀ n : ℕ, uniformBqpGeneratedAt g n = some (W n)

def uniformBqpDivergingGenerator : UniformBqpGenerator where
  controlBound := 0
  machine := fun _ _ => some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩
  timeCoefficient := 1
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 1
  spaceDegree := 1

private def uniformBqpClockMachine : Turing.TM0.Machine (Option Bool) (Fin 1) :=
  fun _ a => if a = none then none else some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩

def uniformBqpClockGenerator : UniformBqpGenerator where
  controlBound := 0
  machine := uniformBqpClockMachine
  timeCoefficient := 1
  timeDegree := 1
  wordCoefficient := 1
  wordDegree := 1
  spaceCoefficient := 1
  spaceDegree := 1

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

def uniformBqpWordPrinter (q : ℕ) (gs : List FiniteGateCode) : UniformBqpGenerator where
  controlBound := 3 * (encodeUniformBqpWord q gs).length
  machine := uniformBqpWordPrinterMachine (encodeUniformBqpWord q gs)
  timeCoefficient := 3 * (encodeUniformBqpWord q gs).length + 2
  timeDegree := 1
  wordCoefficient := (encodeUniformBqpWord q gs).length + 1
  wordDegree := 1
  spaceCoefficient := q + 1
  spaceDegree := 1

def generatorWellformed (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∀ (q : ℕ) (gs : List FiniteGateCode),
    uniformBqpGeneratedAt g n = some (q, gs) → finiteWordLegal q gs = true

def tm0Unidirectional {k : ℕ}
    (m : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) : Prop :=
  ∀ (q : Fin (k + 1)) (a b : Option Bool)
      (r s : Fin (k + 1) × Turing.TM0.Stmt (Option Bool)),
    m q a = some r → m q b = some s →
      (∃ d₁ : Turing.Dir, r.2 = Turing.TM0.Stmt.move d₁) →
      (∃ d₂ : Turing.Dir, s.2 = Turing.TM0.Stmt.move d₂) → r.2 = s.2

def generatorNormalForm (g : UniformBqpGenerator) : Prop :=
  tm0Unidirectional g.machine

def generatorClocked (g : UniformBqpGenerator) : Prop :=
  ∃ c d : ℕ, ∀ n : ℕ, ∃ t ≤ uniformBqpPolynomial c d n,
    BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t

def generatorHaltsEffectively (g : UniformBqpGenerator) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, BitMachineHaltsAt g.machine (uniformBqpUnaryInput n) t

def duplicateWord (q : ℕ) (gs : List FiniteGateCode) : ℕ × List FiniteGateCode :=
  (2 * q, gs ++ gs.map (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q))

def HasDyadicDigit (lam : ℕ) (z : ℂ) : Prop :=
  ∃ m : ℤ × ℤ,
    |(m.1 : ℝ) / (2 ^ lam : ℕ) - z.re| ≤ (2 : ℝ) ^ (-(lam : ℤ)) ∧
      |(m.2 : ℝ) / (2 ^ lam : ℕ) - z.im| ≤ (2 : ℝ) ^ (-(lam : ℤ))

def dyadicBackendPremise (lam : ℕ) (w : ℕ × List FiniteGateCode) : Prop :=
  finiteWordLegal w.1 w.2 = true ∧
    ∀ g ∈ w.2, ∀ i j : Reg w.1, HasDyadicDigit lam (finiteCodeMatrix w.1 g i j)

structure FiniteDigitAmplitude where
  re : ℤ
  im : ℤ
  sqrt2Factor : Bool
  denomExp : ℕ

noncomputable def finiteDigitVal (r : FiniteDigitAmplitude) : ℂ :=
  ((r.re : ℂ) + (r.im : ℂ) * Complex.I) *
    (if r.sqrt2Factor then Real.sqrt 2 else 1) / ((2 ^ r.denomExp : ℕ) : ℂ)

def finiteDigitBackendPremise (w : ℕ × List FiniteGateCode) : Prop :=
  finiteWordLegal w.1 w.2 = true ∧
    ∀ g ∈ w.2, ∀ i j : Reg w.1,
      ∃ r : FiniteDigitAmplitude, finiteDigitVal r = finiteCodeMatrix w.1 g i j

def bitTmBackendPremise (g : UniformBqpGenerator) : Prop :=
  generatorHaltsEffectively g ∧
    ∃ c d : ℕ, ∀ n : ℕ,
      (encodeUniformBqpWord (uniformBqpGeneratedTotal g n).1
        (uniformBqpGeneratedTotal g n).2).length ≤ uniformBqpPolynomial c d n

end Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
