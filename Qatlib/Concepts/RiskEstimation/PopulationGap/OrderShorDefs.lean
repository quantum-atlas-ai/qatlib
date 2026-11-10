/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.RiskEstimation.PopulationGap.ResidueFactoringPrograms
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.RiskEstimation.PopulationGap Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Matrix
open scoped ENNReal Classical

noncomputable def nativeResidueRun (N k fuel : ℕ) [NeZero N] :
    CostedLaw (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration Unit (ZMod N)) :=
  (finiteCoinRun k N fuel).map fun x =>
    (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
      (fun _ : Unit => Sum.inr ()) x.1, x.2)

def nativeResidueBitBudget (k fuel : ℕ) : ℕ := fuel * k

def shorBitLength (N : ℕ) : ℕ := Nat.log2 N + 1

def polyLogBound (c d N : ℕ) : ℕ := c * (shorBitLength N + 1) ^ d

def natToBinaryList (N : ℕ) : List (Option Bool) :=
  (List.range (shorBitLength N)).map fun i => some (N.testBit i)

def binaryListValue : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * binaryListValue rest

noncomputable def shorPreprocessFactor (N : ℕ) : ℕ :=
  match shorPreprocess N with
  | ShorPreResult.factor d => d
  | ShorPreResult.residue => 0

def ClassicalPolyDecision (D : ℕ → Bool) : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → Bool),
    BitMachinePolynomialTime machine ∧
      ∀ N : ℕ, ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (natToBinaryList N) t = some c ∧
          Turing.TM0.step machine c = none ∧ out c = D N

def ClassicalPolySearch (w : ℕ → ℕ) : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (val : Turing.TM0.Cfg (Option Bool) (Fin 2) → ℕ),
    BitMachinePolynomialTime machine ∧
      ∀ N : ℕ, ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (natToBinaryList N) t = some c ∧
          Turing.TM0.step machine c = none ∧ val c = w N

def schoolbookMulModBitCost (b : ℕ) : ℕ := 2 * b * b + b

def modExpBits (e : ℕ) : List Bool :=
  (List.range (Nat.log2 e + 1)).map fun i => e.testBit i

def modExpCostedStep (N : ℕ) (acc : ℕ × ℕ × ℕ) (bit : Bool) : ℕ × ℕ × ℕ :=
  ((acc.1 * acc.1) % N,
    if bit then (acc.2.1 * acc.1) % N else acc.2.1,
    acc.2.2 + (if bit then 2 else 1) * schoolbookMulModBitCost (shorBitLength N))

def modExpCosted (N a e : ℕ) : ℕ × ℕ × ℕ :=
  (modExpBits e).foldl (modExpCostedStep N) (a % N, 1 % N, 0)

def modExpResult (N a e : ℕ) : ℕ := (modExpCosted N a e).2.1

def modExpRealizedBitCost (N a e : ℕ) : ℕ := (modExpCosted N a e).2.2

def modExpSpaceCost (N e : ℕ) : ℕ := 3 * shorBitLength N + shorBitLength e

def qftGateCount (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

def qftSpaceCost (n : ℕ) : ℕ := n

def cfBitCost (M : ℕ) : ℕ :=
  (cfDepth M + 1) * schoolbookMulModBitCost (shorBitLength M)

def cfSpaceCost (M : ℕ) : ℕ := 3 * shorBitLength M

def euclidGcd : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else euclidGcd fuel b (a % b)

def euclidStepBound (N : ℕ) : ℕ := 2 * shorBitLength N + 1

def euclidStepBitCost (N : ℕ) : ℕ := schoolbookMulModBitCost (shorBitLength N)

def gcdBitCost (N : ℕ) : ℕ := euclidStepBound N * euclidStepBitCost N

def gcdSpaceCost (N : ℕ) : ℕ := 2 * shorBitLength N

def attemptOutcomeLedger (N M k : ℕ) (t : residueAttemptOutcome N M k) :
    ℕ × ℕ × ℕ × ℕ :=
  match t with
  | Sum.inl _ => (k, 0, 0, k)
  | Sum.inr (Sum.inl _) =>
      (k + gcdBitCost N, 0, 0, k + gcdSpaceCost N)
  | Sum.inr (Sum.inr _) =>
      (k + cfBitCost M + 2 * gcdBitCost N,
        2 * (M * (M - 1) / 2),
        2 * (M * (M - 1) + 2),
        k + 2 * shorBitLength M + 2 * shorBitLength N)

def attemptLedgerBound (N M k : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (k + cfBitCost M + 2 * gcdBitCost N,
    2 * (M * (M - 1) / 2),
    2 * (M * (M - 1) + 2),
    k + 2 * shorBitLength M + 2 * shorBitLength N)

noncomputable def attemptOutcomeFactor (N M k : ℕ) [NeZero N]
    (t : residueAttemptOutcome N M k) : Option ℕ :=
  match t with
  | Sum.inl _ => none
  | Sum.inr (Sum.inl y) => residueClassicalFactor N y
  | Sum.inr (Sum.inr (a, y, z)) => attemptFactor N M a (y, z)

def firstSuccessAt (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k) (j : Fin R) : Prop :=
  residueAttemptSuccessEvent N M k (ω j) ∧
    ∀ (i : ℕ) (hi : i < j.val),
      ¬ residueAttemptSuccessEvent N M k
          (ω ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_of_lt j.isLt)⟩)

def trajectoryLedgerSum (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k)
    (f : residueAttemptOutcome N M k → ℕ) (bound : ℕ) : ℕ :=
  ∑ j ∈ Finset.range bound, if h : j < R then f (ω ⟨j, h⟩) else 0

structure FirstSuccessReceipt (N M k R : ℕ) [NeZero N] where

  trajectory : Fin R → residueAttemptOutcome N M k

  first : Fin R

  first_success : firstSuccessAt N M k R trajectory first

inductive FactorTree where

  | leaf (p : ℕ)

  | node (n d : ℕ) (left right : FactorTree)

def FactorTree.root : FactorTree → ℕ
  | .leaf p => p
  | .node n _ _ _ => n

def FactorTree.leaves : FactorTree → List ℕ
  | .leaf p => [p]
  | .node _ _ l r => FactorTree.leaves l ++ FactorTree.leaves r

def nodeSplitWitness (M : ℕ) (n d : ℕ) (hd : 1 < d) (hn : d < n) : Prop := by
  haveI : NeZero n := NeZero.of_pos (by omega)
  exact ShorPreResult.factor d = shorPreprocess n ∨
    (∃ y : ZMod n, residueClassicalFactor n y = some d) ∨
    (∃ a : (ZMod n)ˣ, ∃ yz : Fin M × Fin M, attemptFactor n M a yz = some d)

def FactorTree.splitSound (M : ℕ) : FactorTree → Prop
  | .leaf p => Nat.Prime p
  | .node n d l r =>
      ∀ h : 1 < d ∧ d < n ∧ d ∣ n,
        nodeSplitWitness M n d h.1 h.2.1 ∧
          FactorTree.root l = d ∧ FactorTree.root r = n / d ∧
          FactorTree.splitSound M l ∧ FactorTree.splitSound M r

def FactorTree.complete (t : FactorTree) : Prop :=
  (FactorTree.leaves t).prod = FactorTree.root t ∧
    ∀ p : ℕ, (FactorTree.leaves t).count p = (FactorTree.root t).factorization p

section Asp

variable {Ω H : Type} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]

def IsComputationIsometry (V : Matrix H Ω ℂ) : Prop := Vᴴ * V = 1

def IsMeasurementOperatorFamily {O : Type} [Fintype O]
    (T : O → Matrix Ω Ω ℂ) : Prop := ∑ ω, (T ω)ᴴ * (T ω) = 1

noncomputable def measurementMass {O : Type} [Fintype O]
    (T : O → Matrix Ω Ω ℂ) (ψ : QState Ω) (ω : O) : ℝ :=
  ∑ i, ‖((T ω) *ᵥ ψ) i‖ ^ 2

noncomputable def measurementSynthesisError {O : Type} [Fintype O] [DecidableEq O]
    (T T' : O → Matrix Ω Ω ℂ) : ℝ≥0∞ :=
  ∑ ω, ∑ i, ∑ j, (‖(T' ω i j - T ω i j : ℂ)‖).toNNReal

noncomputable def compiledMeasurementMass {O : Type} [Fintype O]
    (V : Matrix H Ω ℂ) (T : O → Matrix Ω Ω ℂ) (φ : QState H) (ω : O) : ℝ :=
  ∑ i, ‖((V * (T ω) * Vᴴ) *ᵥ φ) i‖ ^ 2

end Asp

def compactWidth (m : ℕ) : ℕ := shorResidueBits m

def HasCompactEncoding (X : Type) [Fintype X] : Prop :=
  ∃ encode : X → Reg (compactWidth (Fintype.card X)), Function.Injective encode

def HasCostedNearUniformGeneration (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (δ : ℝ) : Prop :=
  ∃ (q : CostedLaw G) (μ : FinDist G) (c d : ℕ),
    (∀ g : G, Real.toNNReal (μ.prob g) = ∑' n, q (g, n)) ∧
      (∀ L : Finset ↥H,
        |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy q c ∧
        c ≤ d * (compactWidth (Fintype.card G) + 1) ^ 12

def ShorOriginalQ (N q : ℕ) : Prop :=
  ∃ t : ℕ, q = 2 ^ t ∧ N ^ 2 ≤ q ∧ q < 2 * N ^ 2

def boundedPairsList (B : ℕ) : List (ℕ × ℕ) :=
  (List.range (B + 1)).flatMap fun v => (List.range v).map fun u => (u, v)

def originalWindowAccept (M y : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (Nat.Coprime p.1 p.2 ∧
    2 * (((y : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (M : ℤ)).natAbs) ≤ p.2)

def originalWindowDecode (B M y : ℕ) : Option (ℕ × ℕ) :=
  ((boundedPairsList B).filter (originalWindowAccept M y)).head?

def verifiedOrderDecodeOriginal (N q : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y : Fin q) : Option ℕ :=
  match originalWindowDecode (N - 1) q y.val with
  | none => none
  | some (_, r) => if orderVerificationProduct N a r = 1 then some r else none

def HasDlogGoodConditional (p q r : ℕ) [NeZero p] (g x : ZMod p) : Prop :=
  ∃ (hnorm : Normalized (dlogTwoDimState p q g x))
      (cond : FinDist (Fin q × Fin q × ZMod p)),
    (0 < (dlogBornLaw p q g x hnorm).probEvent (L := 1)
        (fun ω => dlogGoodOutcome p q r (ω 0))) ∧
      (∀ o, cond.prob o = (dlogBornLaw p q g x hnorm).prob o /
        (dlogBornLaw p q g x hnorm).probEvent (L := 1)
          (fun ω => dlogGoodOutcome p q r (ω 0))) ∧
      (∀ o, ¬ dlogGoodOutcome p q r o → cond.prob o = 0)

def DlogOriginal480Budget : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → orderOf g = p - 1 → x = g ^ r → q ≤ 2 * (p - 1) →
    ∀ (hnorm : Normalized (dlogTwoDimState p q g x)) (t : ℕ),
      (dlogBornLaw p q g x hnorm).probEvent (L := 480 * t)
          (fun ω => dlogGoodCountGE p q r t (480 * t) ω)
        ≥ 1 / 2

noncomputable def smallPrimePowerList (m : ℕ) : List ℕ :=
  ((Finset.range (m + 1)).filter fun w =>
    ∃ ℓ a : ℕ, Nat.Prime ℓ ∧ ℓ ≤ 18 ∧ w = ℓ ^ a ∧ w ∣ m ∧ ¬ (ℓ * w ∣ m)).toList

noncomputable def smallPrimePart (m : ℕ) : ℕ := (smallPrimePowerList m).prod

noncomputable def effectiveCrtCandidates (p : ℕ) (t : ℕ) (c' d' : Fin t → ℤ) : List ℕ :=
  ((Finset.range (p - 1)).filter fun r' =>
    ∀ i : Fin t, (d' i + ((r' : ℕ) : ℤ) * c' i) % (((p - 1 : ℕ) : ℤ)) = 0).toList

end Qatlib.Concepts.RiskEstimation.PopulationGap
