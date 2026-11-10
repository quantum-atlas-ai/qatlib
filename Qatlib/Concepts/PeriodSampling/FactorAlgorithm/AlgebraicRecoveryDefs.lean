/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Concepts.HspRecovery.CfOrder.CountedContinuedFractionDecoder
import Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelianState
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.HspRecovery.AbelianSampling.ClassicalBasisRecovery
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib.Concepts.RiskEstimation.PopulationGap Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.HspRecovery.AbelianSampling
open scoped Classical

def cfStageCount (M : ℕ) : ℕ := cfDepth M + 1

def IsCompactPresentation {k : ℕ} (A : IMat k) : Prop := A.det ≠ 0

def IsFactorChain {k : ℕ} (d : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, (i : ℕ) + 1 = j → d j ∣ d i

def IsSmithForm {k : ℕ} (A : IMat k) (d : Fin k → ℕ) : Prop :=
  ∃ U V : IMat k,
    U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧
      ∀ i j : Fin k, (U * A * V) i j = if i = j then (d i : ℤ) else 0

structure CompactAbelianDecoder (k : ℕ) where

  decompose : IMat k → Option (Fin k → ℕ)

  toCoords : IMat k → (Fin k → ℤ) → Option (Fin k → ℕ)

  fromCoords : IMat k → (Fin k → ℕ) → Option (Fin k → ℤ)

  bitCost : IMat k → ℕ

  bitSpace : IMat k → ℕ

def CompactAbelianDecoder.Correct {k : ℕ} (c : CompactAbelianDecoder k) : Prop :=
  ∀ A : IMat k, IsCompactPresentation A →
    ∃ d : Fin k → ℕ,
      c.decompose A = some d ∧
      IsFactorChain d ∧
      (List.ofFn d).prod = A.det.natAbs ∧
      (∀ x : Fin k → ℤ, (c.toCoords A x).isSome) ∧
      (∀ (x y : Fin k → ℤ) (cs : Fin k → ℕ),
        c.toCoords A x = some cs → c.toCoords A y = some cs → x - y ∈ colSpan A) ∧
      (∀ (x : Fin k → ℤ) (cs : Fin k → ℕ),
        c.toCoords A x = some cs →
          ∃ y : Fin k → ℤ, c.fromCoords A cs = some y ∧ y - x ∈ colSpan A) ∧
      (∀ (cs : Fin k → ℕ) (y : Fin k → ℤ),
        c.fromCoords A cs = some y → c.toCoords A y = some cs)

def CompactAbelianDecoder.SmithSound {k : ℕ} (c : CompactAbelianDecoder k) : Prop :=
  ∀ (A : IMat k) (d : Fin k → ℕ), IsCompactPresentation A →
    c.decompose A = some d → IsSmithForm A d

def CompactAbelianDecoder.PolyBounded {k : ℕ} (c : CompactAbelianDecoder k) : Prop :=
  ∃ C e : ℕ, ∀ A : IMat k,
    c.bitCost A ≤ C * (inputBitLength A + 1) ^ e ∧
      c.bitSpace A ≤ C * (inputBitLength A + 1) ^ e

structure TwoDimDlogDecoder where

  decode :
    (p q m : ℕ) → (g x : ZMod p) → (Fin m → Fin q × Fin q) → Option ℕ

def TwoDimDlogDecoder.Correct (dec : TwoDimDlogDecoder) : Prop :=
  ∀ (p q m : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → (p : ℕ) < q →
    orderOf g = p - 1 →
    (∀ (ω : Fin m → Fin q × Fin q) (r' : ℕ),
      dec.decode p q m g x ω = some r' → r' < p - 1 ∧ g ^ r' = x) ∧
    (∀ (r : ℕ) (ω : Fin m → Fin q × Fin q), r < p - 1 → x = g ^ r →
      (∃ i : Fin m,
        dlogGoodPair p q r (ω i).1 (ω i).2 ∧
          Nat.gcd (dlogCprime p q (ω i).1).natAbs (p - 1) = 1) →
      dec.decode p q m g x ω = some r)

def encodeBits (n x : ℕ) : Reg n := fun i => x.testBit i

def encodeTriple (b a c d : ℕ) : Reg (3 * b) := fun i =>
  if (i : ℕ) < b then a.testBit i
  else if (i : ℕ) < 2 * b then c.testBit (i - b)
  else d.testBit (i - 2 * b)

def RealizesModAdd (b : ℕ) (word : Circuit (Reg (3 * b))) : Prop :=
  ∀ a c : ℕ, a < 2 ^ b → c < 2 ^ b →
    Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ) word
        (Ket (encodeTriple b a c 0)) =
      Ket (encodeTriple b a c ((a + c) % 2 ^ b))

def RealizesModMul (b : ℕ) (word : Circuit (Reg (3 * b))) : Prop :=
  ∀ a c : ℕ, a < 2 ^ b → c < 2 ^ b →
    Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ) word
        (Ket (encodeTriple b a c 0)) =
      Ket (encodeTriple b a c ((a * c) % 2 ^ b))

structure ReversibleArithmetic where

  add : (b : ℕ) → Circuit (Reg (3 * b))

  mul : (b : ℕ) → Circuit (Reg (3 * b))

  addElem : ℕ → ℕ

  mulElem : ℕ → ℕ

  add_macros : ∀ b : ℕ, GateCount (add b) ≤ 2 * b + 2

  mul_macros : ∀ b : ℕ, GateCount (mul b) ≤ schoolbookMulModBitCost b

  queries : ∀ b : ℕ, QueryCount (add b) = 0 ∧ QueryCount (mul b) = 0

  unitary : ∀ b : ℕ, IsUnitaryCircuit (add b) ∧ IsUnitaryCircuit (mul b)

  realizes : ∀ b : ℕ, RealizesModAdd b (add b) ∧ RealizesModMul b (mul b)

  elem_poly : ∃ C e : ℕ, ∀ b : ℕ, addElem b ≤ C * (b + 1) ^ e ∧ mulElem b ≤ C * (b + 1) ^ e

def ReversibleArithmetic.PolyBounded (ar : ReversibleArithmetic) : Prop :=
  ∃ C e : ℕ, ∀ b : ℕ,
    schoolbookMulModBitCost b ≤ C * (b + 1) ^ e ∧
      3 * b ≤ C * (b + 1) ^ e ∧
      ar.addElem b + ar.mulElem b ≤ C * (b + 1) ^ e

structure JointRecovery where

  factoring : (N : ℕ) → (m : ℕ) → (Fin m → ZMod N) → Option ℕ

  dlog : TwoDimDlogDecoder

  bitCost : (N p q m : ℕ) → ℕ

  bitSpace : (N p q m : ℕ) → ℕ

def JointRecovery.Correct (J : JointRecovery) : Prop :=
  (∀ (N m : ℕ) [NeZero N] (ω : Fin m → ZMod N) (d : ℕ),
    J.factoring N m ω = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
  (∀ (N m : ℕ) [NeZero N] (ω : Fin m → ZMod N),
    (∃ i : Fin m, (residueClassicalFactor N (ω i)).isSome) →
      (J.factoring N m ω).isSome) ∧
  (J.dlog.Correct) ∧
  (∃ C e : ℕ, ∀ N p q m : ℕ,
    J.bitCost N p q m ≤ C * (shorBitLength N + shorBitLength p + m + 1) ^ e ∧
      J.bitSpace N p q m ≤ C * (shorBitLength N + shorBitLength p + m + 1) ^ e)

structure FinitePrecisionMeasurement (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) where

  cond : ↥H → FinDist G

  measure : FinDist G

  accuracy : ℝ

  mixture : ∀ g : G, measure.prob g =
    (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g

  accuracy_nonneg : 0 ≤ accuracy

  identify : ∀ h' : ↥H, 1 - accuracy ≤ (cond h').prob (h' : G)

structure TorEncoding (k n : ℕ) where

  encode : (Fin k → Fin (2 ^ n)) → Reg (k * n)

  injective : Function.Injective encode

def torPack (k n : ℕ) (x : Fin k → Fin (2 ^ n)) : Reg (k * n) := fun i =>
  if h : i.val / n < k then (x ⟨i.val / n, h⟩).val.testBit (i.val % n) else false

def intToBinaryList (z : ℤ) : List (Option Bool) :=
  (List.range (Nat.log 2 z.natAbs + 2)).map fun i =>
    if i = 0 then some (decide (z < 0)) else some (z.natAbs.testBit (i - 1))

def presentationTape {k : ℕ} (A : IMat k) : List (Option Bool) :=
  (List.finRange k).flatMap fun i =>
    (List.finRange k).flatMap fun j => intToBinaryList (A i j)

def HasAspQueryBudget (k n q : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ q ≤ C * k * n ^ 2 * (Nat.log 2 (k * n + 2) + 1)

structure AspConstruction (k n : ℕ) where

  samples : ℕ

  queries : ℕ

  gates : ℕ

  space : ℕ

  encode : TorEncoding k n

  postprocess : IMat k → Option (IMat k)

  postprocess_correct : ∀ (A : IMat k), IsCompactPresentation A →
    ∃ B : IMat k,
      postprocess A = some B ∧
        IsCanonicalHNF B ∧
        colSpan B = colSpan A ∧
        (∀ i j : Fin k, (B i j).natAbs ≤ 2 ^ (2 * (inputBitLength A) ^ 2))

def AspConstruction.PolyBounded {k n : ℕ} (c : AspConstruction k n) : Prop :=
  ∃ C e : ℕ,
    c.gates ≤ C * (k * n + 1) ^ e ∧
      c.space ≤ C * (k * n + 1) ^ e ∧
      (k * n : ℕ) ≤ C * (k * n + 1) ^ e

def UniformCanonicalBasisMachine : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → List ℤ),
    BitMachinePolynomialTime machine ∧
      ∀ (k : ℕ) (A : IMat k), ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (presentationTape A) t = some c ∧
          Turing.TM0.step machine c = none ∧
          out c = (List.finRange k).flatMap fun i =>
            (List.finRange k).map fun j => classicalCanonicalize A i j

def EffectiveAbelianQFT : Prop :=
  ∃ C d : ℕ,
    ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
      ∃ (e : G ≃ AddChar G ℂ) (word : Circuit G),
        IsUnitaryCircuit word ∧
          QueryCount word = 0 ∧
          GateCount word ≤ C * (compactWidth (Fintype.card G) + 1) ^ d ∧
          (∀ ψ : QState G,
            Run (1 : Matrix G G ℂ) word ψ = ApplyGate (fourierGate e) ψ)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
