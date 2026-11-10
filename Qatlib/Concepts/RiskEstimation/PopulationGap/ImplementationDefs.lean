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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

noncomputable def realQuantize (k : ℕ) (x : ℝ) : ℚ := dyadicRat k x

noncomputable def realQuantizeSlack (k : ℕ) (x : ℝ) : ℝ :=
  x - (realQuantize k x : ℝ)

def realQuantizeBits (k : ℕ) : ℕ := 2 * (k + 1)

def EffectiveAngle (k : ℕ) (z : ℂ) (a : ℚ) : Prop :=
  ‖z - Complex.exp (((a : ℝ) : ℂ) * Complex.I)‖ ≤ (1 / 2 : ℝ) ^ k

structure AngleFinder where

  find : ℂ → ℕ → ℚ

def AngleFinder.Correct (A : AngleFinder) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ k : ℕ, EffectiveAngle k z (A.find z k)

structure PhaseInverse where

  invert : ℕ → List FiniteGateCode → List FiniteGateCode

def PhaseInverse.Correct (P : PhaseInverse) : Prop :=
  ∀ (n : ℕ) (gs : List FiniteGateCode), finiteWordLegal n gs = true →
    (P.invert n gs).length = gs.length ∧
      finiteWordLegal n (P.invert n gs) = true ∧
      ∀ ψ : QState (Reg n),
        finiteWordRun n (gs ++ P.invert n gs) ψ = some ψ ∧
          finiteWordRun n (P.invert n gs ++ gs) ψ = some ψ

noncomputable def complexQuantize (d : ℕ) (z : ℂ) : ℂ :=
  PrepareDigits.roundComplex (⟨d, 0⟩ : PrepareDigits) z

noncomputable def quantizeFrame {R C : Type*} (d : ℕ) (F : Matrix R C ℂ) :
    Matrix R C ℂ := fun i j => complexQuantize d (F i j)

noncomputable def quantizeVector {D : Type*} (d : ℕ) (v : D → ℂ) : D → ℂ :=
  fun i => complexQuantize d (v i)

noncomputable def frameGramDefect (R C : ℕ) (d : ℕ) : ℝ :=
  let ε := Real.sqrt (2 * R * C) * (1 / 2 : ℝ) ^ d
  2 * ε + ε ^ 2

structure PrepareParameter where

  digits : ℕ

  width : ℕ

  error : ℝ

def PrepareParameter.Reliable (p : PrepareParameter) (D : ℕ) : Prop :=
  0 < p.digits ∧ 0 < p.width ∧
    p.error = Real.sqrt (2 * D) * (1 / 2 : ℝ) ^ p.digits

noncomputable def resultRotation (d x : ℚ) (k : ℕ) : Matrix Bool Bool ℂ :=
  rationalHHLRotation d x k

noncomputable def layeredResultRotation {Y : Type*} [Fintype Y] [DecidableEq Y]
    (decode : Y → ℚ) (d : ℚ) (k : ℕ) : Matrix (Y × Bool) (Y × Bool) ℂ :=
  fun a b => if a.1 = b.1 then rationalHHLRotation d (decode a.1) k a.2 b.2 else 0

structure UniformFixedGate where

  generate : (w : ℕ) → Matrix (Reg w) (Reg w) ℂ → List (ReflectionGate (w + (w + 1)))

  budget : ℕ → ℕ

def UniformFixedGate.Correct (G : UniformFixedGate) : Prop :=
  ∀ (w : ℕ) (V : Matrix (Reg w) (Reg w) ℂ), V ∈ Matrix.unitaryGroup (Reg w) ℂ →
    reflectionLegal (G.generate w V) ∧
      (G.generate w V).length ≤ G.budget w ∧
      QueryCount (reflectionCompile (G.generate w V)) = 0 ∧
      GateCount (reflectionCompile (G.generate w V)) = (G.generate w V).length ∧
      ∀ ψ : QState (Reg w),
        Run 1 (reflectionCompile (G.generate w V)) (knownFrameEmbed w ψ) =
          knownFrameEmbed w (V *ᵥ ψ)

def UniformFixedGate.Uniform (G : UniformFixedGate) : Prop :=
  ∀ w : ℕ, G.budget w ≤ 128 * (w + 1) ^ 2 * 4 ^ w

structure TwoQueryEncoding (O I : Type) where

  data : SparseOracleData O I

  gates : ℕ

  bitOps : ℕ

def TwoQueryEncoding.Correct {O I : Type} (e : TwoQueryEncoding O I) : Prop :=
  e.gates = e.data.rowCallGates + e.data.valueCallGates ∧
    e.bitOps = e.data.arithBits

def TwoQueryEncoding.queryCount {O I : Type} (_e : TwoQueryEncoding O I) : ℕ := 2

def twoQueryPipeline (n : ℕ) : List (SparsePipelineStep n) :=
  [SparsePipelineStep.rowCall, SparsePipelineStep.valueCall]

def MachineComputesGcd {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (encode : ℕ × ℕ → List Γ)
    (decode : Turing.TM0.Cfg Γ Λ → ℕ) : Prop :=
  ∀ a b : ℕ, ∃ t final,
    BitMachineAfter M (encode (a, b)) t = some final ∧
      Turing.TM0.step M final = none ∧ decode final = Nat.gcd a b

structure GcdNativeGenerator (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  machine : ℕ → Turing.TM0.Machine Γ Λ

  encode : ℕ → ℕ × ℕ → List Γ

  decode : ℕ → Turing.TM0.Cfg Γ Λ → ℕ

def GcdNativeGenerator.Correct {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (G : GcdNativeGenerator Γ Λ) : Prop :=
  ∀ N : ℕ, MachineComputesGcd (G.machine N) (G.encode N) (G.decode N)

def GcdNativeGenerator.Uniform {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (G : GcdNativeGenerator Γ Λ) : Prop :=
  ∃ c e : ℕ, ∀ (N : ℕ) (input : List Γ), ∃ t final,
    BitMachineAfter (G.machine N) input t = some final ∧
      Turing.TM0.step (G.machine N) final = none ∧
      t ≤ c * input.length ^ e + c

def UniformGcdGeneration : Prop :=
  ∃ (Γ Λ : Type) (iΓ : Inhabited Γ) (iΛ : Inhabited Λ),
    ∃ G : @GcdNativeGenerator Γ Λ iΓ iΛ,
      (∀ N : ℕ,
        @MachineComputesGcd Γ Λ iΓ iΛ (G.machine N) (G.encode N) (G.decode N)) ∧
        @GcdNativeGenerator.Uniform Γ Λ iΓ iΛ G

def peakSpaceOf (wordLen events : ℕ) (live : ℕ → ℕ) : ℕ :=
  (List.range events).foldr (fun i acc => max (live i) acc) 0 * wordLen

def paidAccessTotal {H : Type} (c : CompiledAccess H) : ℕ :=
  c.callCounts.1 + c.callCounts.2.1 + c.callCounts.2.2

structure LoadLedger where

  matrixLoad : ℕ

  sqrtLoad : ℕ

def LoadLedger.Correct {O I : Type} [Fintype O] [Fintype I]
    (L : LoadLedger) (q : QuantizedMatrixInput O I) (entries bits : ℕ) : Prop :=
  L.matrixLoad = QuantizedMatrixInput.readBitCost q ∧
    L.sqrtLoad = derivedQuantityBitCost entries bits

end Qatlib.Concepts.RiskEstimation.PopulationGap
