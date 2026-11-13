/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridgesDefs
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.HhlAlgorithms.RationalProgram
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers

/-!
# Quantization and implementation contracts

This module defines precision, inversion, reflection synthesis, sparse access, and arithmetic
machine contracts for risk estimation implementations. `PhaseInverse.Correct` specifies exact
inversion of legal gate words, while `UniformFixedGate.Correct` specifies embedded unitary
execution and resource counts in the circuit framework of [NielsenChuang2010].

The real and complex quantizers use the natural floor based `dyadicRat`; the definitions do not
assert uniform approximation bounds on arbitrary signed inputs. Separate structures record
preparation parameters, sparse loading costs, and uniform greatest common divisor computation.

## Main definitions

* `complexQuantize`: componentwise dyadic quantization.
* `UniformFixedGate`: reflection word synthesis data.
* `MachineComputesGcd`: halting computation with decoded greatest common divisor output.
* `LoadLedger.Correct`: matching matrix and derived quantity loading costs.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Quantizes a real number using the natural floor based rational function `dyadicRat`. -/
noncomputable def realQuantize (k : ℕ) (x : ℝ) : ℚ := dyadicRat k x

/-- The difference between a real input and its rational quantization cast to the reals. -/
noncomputable def realQuantizeSlack (k : ℕ) (x : ℝ) : ℝ :=
  x - (realQuantize k x : ℝ)

/-- The bit budget expression `2 * (k + 1)` for precision `k`. -/
def realQuantizeBits (k : ℕ) : ℕ := 2 * (k + 1)

/-- Requires the unit complex exponential of the rational angle `a` to approximate `z` within `2
^ (-k)`. -/
def EffectiveAngle (k : ℕ) (z : ℂ) (a : ℚ) : Prop :=
  ‖z - Complex.exp (((a : ℝ) : ℂ) * Complex.I)‖ ≤ (1 / 2 : ℝ) ^ k

/-- A function assigning a rational angle to each complex input and natural precision. -/
structure AngleFinder where

  find : ℂ → ℕ → ℚ

/-- Requires the returned rational angle to satisfy `EffectiveAngle` for every unit modulus
input and precision. -/
def AngleFinder.Correct (A : AngleFinder) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ k : ℕ, EffectiveAngle k z (A.find z k)

/-- A transformation producing a finite gate word from a width and an input word. -/
structure PhaseInverse where

  invert : ℕ → List FiniteGateCode → List FiniteGateCode

/-- Requires the transformed word to be legal and of equal length, and to invert the input word
in either concatenation order on every state. -/
def PhaseInverse.Correct (P : PhaseInverse) : Prop :=
  ∀ (n : ℕ) (gs : List FiniteGateCode), finiteWordLegal n gs = true →
    (P.invert n gs).length = gs.length ∧
      finiteWordLegal n (P.invert n gs) = true ∧
      ∀ ψ : QState (Reg n),
        finiteWordRun n (gs ++ P.invert n gs) ψ = some ψ ∧
          finiteWordRun n (P.invert n gs ++ gs) ψ = some ψ

/-- Applies dyadic quantization of precision `d` independently to the real and imaginary
components. -/
noncomputable def complexQuantize (d : ℕ) (z : ℂ) : ℂ :=
  PrepareDigits.roundComplex (⟨d, 0⟩ : PrepareDigits) z

/-- Applies `complexQuantize d` to every entry of a matrix. -/
noncomputable def quantizeFrame {R C : Type*} (d : ℕ) (F : Matrix R C ℂ) :
    Matrix R C ℂ := fun i j => complexQuantize d (F i j)

/-- Applies `complexQuantize d` to every coordinate of a vector. -/
noncomputable def quantizeVector {D : Type*} (d : ℕ) (v : D → ℂ) : D → ℂ :=
  fun i => complexQuantize d (v i)

/-- The expression `2 * ε + ε ^ 2` with `ε = sqrt (2 * R * C) * (1 / 2) ^ d`. -/
noncomputable def frameGramDefect (R C : ℕ) (d : ℕ) : ℝ :=
  let ε := Real.sqrt (2 * R * C) * (1 / 2 : ℝ) ^ d
  2 * ε + ε ^ 2

/-- Preparation data recording dyadic precision, register width, and a real error parameter. -/
structure PrepareParameter where

  digits : ℕ

  width : ℕ

  error : ℝ

/-- Requires positive precision and width and fixes the error to `sqrt (2 * D) * (1 / 2) ^
digits`. -/
def PrepareParameter.Reliable (p : PrepareParameter) (D : ℕ) : Prop :=
  0 < p.digits ∧ 0 < p.width ∧
    p.error = Real.sqrt (2 * D) * (1 / 2 : ℝ) ^ p.digits

/-- The rational HHL result rotation at scale `d`, input `x`, and precision `k`. -/
noncomputable def resultRotation (d x : ℚ) (k : ℕ) : Matrix Bool Bool ℂ :=
  rationalHHLRotation d x k

/-- The block diagonal result rotation controlled by a finite label decoded to a rational input. -/
noncomputable def layeredResultRotation {Y : Type*} [Fintype Y] [DecidableEq Y]
    (decode : Y → ℚ) (d : ℚ) (k : ℕ) : Matrix (Y × Bool) (Y × Bool) ℂ :=
  fun a b => if a.1 = b.1 then rationalHHLRotation d (decode a.1) k a.2 b.2 else 0

/-- A family of reflection word generators for qubit matrices, with a width dependent length
budget. -/
structure UniformFixedGate where

  generate : (w : ℕ) → Matrix (Reg w) (Reg w) ℂ → List (ReflectionGate (w + (w + 1)))

  budget : ℕ → ℕ

/-- Requires legal words within budget that execute each unitary on the embedded register, with
zero queries and gate count equal to word length. -/
def UniformFixedGate.Correct (G : UniformFixedGate) : Prop :=
  ∀ (w : ℕ) (V : Matrix (Reg w) (Reg w) ℂ), V ∈ Matrix.unitaryGroup (Reg w) ℂ →
    reflectionLegal (G.generate w V) ∧
      (G.generate w V).length ≤ G.budget w ∧
      QueryCount (reflectionCompile (G.generate w V)) = 0 ∧
      GateCount (reflectionCompile (G.generate w V)) = (G.generate w V).length ∧
      ∀ ψ : QState (Reg w),
        Run 1 (reflectionCompile (G.generate w V)) (knownFrameEmbed w ψ) =
          knownFrameEmbed w (V *ᵥ ψ)

/-- Requires the synthesis budget at width `w` to be at most `128 * (w + 1) ^ 2 * 4 ^ w`. -/
def UniformFixedGate.Uniform (G : UniformFixedGate) : Prop :=
  ∀ w : ℕ, G.budget w ≤ 128 * (w + 1) ^ 2 * 4 ^ w

/-- Sparse oracle data equipped with elementary gate and classical bit operation counts. -/
structure TwoQueryEncoding (O I : Type) where

  data : SparseOracleData O I

  gates : ℕ

  bitOps : ℕ

/-- Requires the recorded gate and bit costs to equal the costs specified by the sparse oracle
data. -/
def TwoQueryEncoding.Correct {O I : Type} (e : TwoQueryEncoding O I) : Prop :=
  e.gates = e.data.rowCallGates + e.data.valueCallGates ∧
    e.bitOps = e.data.arithBits

/-- The constant query count two assigned to a sparse encoding. -/
def TwoQueryEncoding.queryCount {O I : Type} (_e : TwoQueryEncoding O I) : ℕ := 2

/-- The sparse pipeline consisting of one row call followed by one value call. -/
def twoQueryPipeline (n : ℕ) : List (SparsePipelineStep n) :=
  [SparsePipelineStep.rowCall, SparsePipelineStep.valueCall]

/-- Requires every encoded natural pair to reach a halting configuration whose decoded value is
its greatest common divisor. -/
def MachineComputesGcd {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (encode : ℕ × ℕ → List Γ)
    (decode : Turing.TM0.Cfg Γ Λ → ℕ) : Prop :=
  ∀ a b : ℕ, ∃ t final,
    BitMachineAfter M (encode (a, b)) t = some final ∧
      Turing.TM0.step M final = none ∧ decode final = Nat.gcd a b

/-- A size indexed family of Turing machines with input encoders and output decoders. -/
structure GcdNativeGenerator (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  machine : ℕ → Turing.TM0.Machine Γ Λ

  encode : ℕ → ℕ × ℕ → List Γ

  decode : ℕ → Turing.TM0.Cfg Γ Λ → ℕ

/-- Requires each generated machine to compute the greatest common divisor under its associated
encoder and decoder. -/
def GcdNativeGenerator.Correct {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (G : GcdNativeGenerator Γ Λ) : Prop :=
  ∀ N : ℕ, MachineComputesGcd (G.machine N) (G.encode N) (G.decode N)

/-- Requires every generated machine to halt on every tape input within a common polynomial
bound in input length. -/
def GcdNativeGenerator.Uniform {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (G : GcdNativeGenerator Γ Λ) : Prop :=
  ∃ c e : ℕ, ∀ (N : ℕ) (input : List Γ), ∃ t final,
    BitMachineAfter (G.machine N) input t = some final ∧
      Turing.TM0.step (G.machine N) final = none ∧
      t ≤ c * input.length ^ e + c

/-- States the existence of inhabited symbol and control types and a correct, uniformly bounded
greatest common divisor generator. -/
def UniformGcdGeneration : Prop :=
  ∃ (Γ Λ : Type) (iΓ : Inhabited Γ) (iΛ : Inhabited Λ),
    ∃ G : @GcdNativeGenerator Γ Λ iΓ iΛ,
      (∀ N : ℕ,
        @MachineComputesGcd Γ Λ iΓ iΛ (G.machine N) (G.encode N) (G.decode N)) ∧
        @GcdNativeGenerator.Uniform Γ Λ iΓ iΛ G

/-- The largest recorded live word count multiplied by word length, using a maximum fold over
the event indices. -/
def peakSpaceOf (wordLen events : ℕ) (live : ℕ → ℕ) : ℕ :=
  (List.range events).foldr (fun i acc => max (live i) acc) 0 * wordLen

/-- The sum of forward, backward, and controlled call counts of a compiled access. -/
def paidAccessTotal {H : Type} (c : CompiledAccess H) : ℕ :=
  c.callCounts.1 + c.callCounts.2.1 + c.callCounts.2.2

/-- A pair of classical cost entries for matrix loading and derived square root loading. -/
structure LoadLedger where

  matrixLoad : ℕ

  sqrtLoad : ℕ

/-- Requires the ledger entries to match the quantized matrix read cost and the derived quantity
bit cost. -/
def LoadLedger.Correct {O I : Type} [Fintype O] [Fintype I]
    (L : LoadLedger) (q : QuantizedMatrixInput O I) (entries bits : ℕ) : Prop :=
  L.matrixLoad = QuantizedMatrixInput.readBitCost q ∧
    L.sqrtLoad = derivedQuantityBitCost entries bits

end Qatlib.Concepts.RiskEstimation.PopulationGap
