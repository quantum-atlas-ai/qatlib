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

/-!
# Order finding and factoring resource specifications

This module defines costed residue sampling, bit operation and space expressions, factor
extraction receipts, and factor tree predicates for order finding and factoring in the setting
of [Shor1997]. Classical polynomial computation is expressed using explicit Turing machine
encoders and decoders.

Additional contracts describe isometric computation embeddings, measurement completeness and
synthesis error, bounded rational decoding, and discrete logarithm sampling budgets. These are
data and specifications rather than proofs that all stated budgets or recovery properties hold.

## Main definitions

* `modExpCosted`: modular exponentiation with an accumulated bit cost.
* `FirstSuccessReceipt`: a trajectory with its first successful attempt.
* `FactorTree.complete`: leaf product and prime multiplicity requirements.
* `ShorOriginalQ`: the power of two sampling window condition.
* `DlogOriginal480Budget`: a repeated discrete logarithm sampling success specification.

## References

* [Shor, 1997][Shor1997]
-/

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

/-- Maps finite coin execution outputs to residue or failure configurations over `ZMod N`,
preserving their recorded costs. -/
noncomputable def nativeResidueRun (N k fuel : ℕ) [NeZero N] :
    CostedLaw (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration Unit (ZMod N)) :=
  (finiteCoinRun k N fuel).map fun x =>
    (Sum.elim (fun i : Fin N => Sum.inl ((i : ZMod N)))
      (fun _ : Unit => Sum.inr ()) x.1, x.2)

/-- The bit budget `fuel * k` for at most `fuel` draws of `k` bits. -/
def nativeResidueBitBudget (k fuel : ℕ) : ℕ := fuel * k

/-- The integer size expression `Nat.log2 N + 1`. -/
def shorBitLength (N : ℕ) : ℕ := Nat.log2 N + 1

/-- The bound expression `c * (shorBitLength N + 1) ^ d`. -/
def polyLogBound (c d N : ℕ) : ℕ := c * (shorBitLength N + 1) ^ d

/-- Encodes a natural number as a list of present Boolean bits in least significant first order. -/
def natToBinaryList (N : ℕ) : List (Option Bool) :=
  (List.range (shorBitLength N)).map fun i => some (N.testBit i)

/-- Decodes a Boolean list as a binary natural number in least significant first order. -/
def binaryListValue : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * binaryListValue rest

/-- Returns the factor produced by Shor preprocessing, or zero when preprocessing requests
residue sampling. -/
noncomputable def shorPreprocessFactor (N : ℕ) : ℕ :=
  match shorPreprocess N with
  | ShorPreResult.factor d => d
  | ShorPreResult.residue => 0

/-- States that a Boolean function is computed on binary inputs by a polynomial time Turing
machine with a Boolean output decoder. -/
def ClassicalPolyDecision (D : ℕ → Bool) : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → Bool),
    BitMachinePolynomialTime machine ∧
      ∀ N : ℕ, ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (natToBinaryList N) t = some c ∧
          Turing.TM0.step machine c = none ∧ out c = D N

/-- States that a natural valued function is computed on binary inputs by a polynomial time
Turing machine with a natural output decoder. -/
def ClassicalPolySearch (w : ℕ → ℕ) : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (val : Turing.TM0.Cfg (Option Bool) (Fin 2) → ℕ),
    BitMachinePolynomialTime machine ∧
      ∀ N : ℕ, ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (natToBinaryList N) t = some c ∧
          Turing.TM0.step machine c = none ∧ val c = w N

/-- The modular multiplication bit cost expression `2 * b * b + b`. -/
def schoolbookMulModBitCost (b : ℕ) : ℕ := 2 * b * b + b

/-- Lists the exponent bits from least to most significant through index `Nat.log2 e`. -/
def modExpBits (e : ℕ) : List Bool :=
  (List.range (Nat.log2 e + 1)).map fun i => e.testBit i

/-- Squares the current modular power, conditionally updates the result for the input bit, and
adds the corresponding multiplication cost. -/
def modExpCostedStep (N : ℕ) (acc : ℕ × ℕ × ℕ) (bit : Bool) : ℕ × ℕ × ℕ :=
  ((acc.1 * acc.1) % N,
    if bit then (acc.2.1 * acc.1) % N else acc.2.1,
    acc.2.2 + (if bit then 2 else 1) * schoolbookMulModBitCost (shorBitLength N))

/-- Folds modular exponentiation steps over the exponent bits, returning the current power,
result, and accumulated bit cost. -/
def modExpCosted (N a e : ℕ) : ℕ × ℕ × ℕ :=
  (modExpBits e).foldl (modExpCostedStep N) (a % N, 1 % N, 0)

/-- Extracts the modular exponentiation result component from `modExpCosted`. -/
def modExpResult (N a e : ℕ) : ℕ := (modExpCosted N a e).2.1

/-- Extracts the accumulated bit cost from `modExpCosted`. -/
def modExpRealizedBitCost (N a e : ℕ) : ℕ := (modExpCosted N a e).2.2

/-- The space cost expression `3 * shorBitLength N + shorBitLength e`. -/
def modExpSpaceCost (N e : ℕ) : ℕ := 3 * shorBitLength N + shorBitLength e

/-- The QFT gate count expression `n + n * (n - 1) / 2 + n / 2`. -/
def qftGateCount (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

/-- The QFT space cost expression of `n` qubits. -/
def qftSpaceCost (n : ℕ) : ℕ := n

/-- The continued fraction cost expression given by one plus `cfDepth M` times the modular
multiplication cost at the bit length of `M`. -/
def cfBitCost (M : ℕ) : ℕ :=
  (cfDepth M + 1) * schoolbookMulModBitCost (shorBitLength M)

/-- The continued fraction space cost expression `3 * shorBitLength M`. -/
def cfSpaceCost (M : ℕ) : ℕ := 3 * shorBitLength M

/-- The fuelled Euclidean algorithm, returning the first input when fuel is exhausted or the
second input is zero. -/
def euclidGcd : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else euclidGcd fuel b (a % b)

/-- The Euclidean iteration budget `2 * shorBitLength N + 1`. -/
def euclidStepBound (N : ℕ) : ℕ := 2 * shorBitLength N + 1

/-- The bit cost assigned to one Euclidean step at the bit length of `N`. -/
def euclidStepBitCost (N : ℕ) : ℕ := schoolbookMulModBitCost (shorBitLength N)

/-- The Euclidean step budget multiplied by its assigned step bit cost. -/
def gcdBitCost (N : ℕ) : ℕ := euclidStepBound N * euclidStepBitCost N

/-- The greatest common divisor space expression `2 * shorBitLength N`. -/
def gcdSpaceCost (N : ℕ) : ℕ := 2 * shorBitLength N

/-- Assigns each residue attempt outcome a tuple of classical bit, query, gate, and space costs
according to its execution branch. -/
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

/-- The full branch cost tuple used as a reference bound for residue attempts. -/
def attemptLedgerBound (N M k : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (k + cfBitCost M + 2 * gcdBitCost N,
    2 * (M * (M - 1) / 2),
    2 * (M * (M - 1) + 2),
    k + 2 * shorBitLength M + 2 * shorBitLength N)

/-- Extracts no factor from failure, a classical residue factor from the classical branch, or an
order based factor from the quantum branch. -/
noncomputable def attemptOutcomeFactor (N M k : ℕ) [NeZero N]
    (t : residueAttemptOutcome N M k) : Option ℕ :=
  match t with
  | Sum.inl _ => none
  | Sum.inr (Sum.inl y) => residueClassicalFactor N y
  | Sum.inr (Sum.inr (a, y, z)) => attemptFactor N M a (y, z)

/-- States that attempt `j` succeeds and every earlier attempt in the trajectory fails. -/
def firstSuccessAt (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k) (j : Fin R) : Prop :=
  residueAttemptSuccessEvent N M k (ω j) ∧
    ∀ (i : ℕ) (hi : i < j.val),
      ¬ residueAttemptSuccessEvent N M k
          (ω ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_of_lt j.isLt)⟩)

/-- Sums a supplied outcome cost over indices below `bound`, counting only indices within the
trajectory. -/
def trajectoryLedgerSum (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k)
    (f : residueAttemptOutcome N M k → ℕ) (bound : ℕ) : ℕ :=
  ∑ j ∈ Finset.range bound, if h : j < R then f (ω ⟨j, h⟩) else 0

/-- A finite attempt trajectory equipped with an index certified to be its first success. -/
structure FirstSuccessReceipt (N M k R : ℕ) [NeZero N] where

  trajectory : Fin R → residueAttemptOutcome N M k

  first : Fin R

  first_success : firstSuccessAt N M k R trajectory first

/-- A tree with natural number leaves and internal nodes recording an integer, a splitting
candidate, and two subtrees. -/
inductive FactorTree where

  | leaf (p : ℕ)

  | node (n d : ℕ) (left right : FactorTree)

/-- The natural number recorded at the root of a factor tree. -/
def FactorTree.root : FactorTree → ℕ
  | .leaf p => p
  | .node n _ _ _ => n

/-- The list of leaf labels of a factor tree in left to right order. -/
def FactorTree.leaves : FactorTree → List ℕ
  | .leaf p => [p]
  | .node _ _ l r => FactorTree.leaves l ++ FactorTree.leaves r

/-- States that a proposed nontrivial split arises from preprocessing, classical residue
extraction, or quantum attempt factor extraction. -/
def nodeSplitWitness (M : ℕ) (n d : ℕ) (hd : 1 < d) (hn : d < n) : Prop := by
  haveI : NeZero n := NeZero.of_pos (by omega)
  exact ShorPreResult.factor d = shorPreprocess n ∨
    (∃ y : ZMod n, residueClassicalFactor n y = some d) ∨
    (∃ a : (ZMod n)ˣ, ∃ yz : Fin M × Fin M, attemptFactor n M a yz = some d)

/-- Requires prime leaf labels and, whenever an internal split is a proper divisor, a split
witness, matching child roots, and recursively sound children. -/
def FactorTree.splitSound (M : ℕ) : FactorTree → Prop
  | .leaf p => Nat.Prime p
  | .node n d l r =>
      ∀ h : 1 < d ∧ d < n ∧ d ∣ n,
        nodeSplitWitness M n d h.1 h.2.1 ∧
          FactorTree.root l = d ∧ FactorTree.root r = n / d ∧
          FactorTree.splitSound M l ∧ FactorTree.splitSound M r

/-- Requires the leaf product to equal the root and each leaf multiplicity to equal the root's
prime factorization multiplicity. -/
def FactorTree.complete (t : FactorTree) : Prop :=
  (FactorTree.leaves t).prod = FactorTree.root t ∧
    ∀ p : ℕ, (FactorTree.leaves t).count p = (FactorTree.root t).factorization p

section Asp

variable {Ω H : Type} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]

/-- States the matrix isometry identity `Vᴴ * V = 1`. -/
def IsComputationIsometry (V : Matrix H Ω ℂ) : Prop := Vᴴ * V = 1

/-- States that the sum of the measurement operators' conjugate transpose products is the
identity. -/
def IsMeasurementOperatorFamily {O : Type} [Fintype O]
    (T : O → Matrix Ω Ω ℂ) : Prop := ∑ ω, (T ω)ᴴ * (T ω) = 1

/-- The sum of squared coordinate norms after applying the selected measurement operator to the
input vector. -/
noncomputable def measurementMass {O : Type} [Fintype O]
    (T : O → Matrix Ω Ω ℂ) (ψ : QState Ω) (ω : O) : ℝ :=
  ∑ i, ‖((T ω) *ᵥ ψ) i‖ ^ 2

/-- The extended nonnegative sum of entrywise norm differences between two finite measurement
operator families. -/
noncomputable def measurementSynthesisError {O : Type} [Fintype O] [DecidableEq O]
    (T T' : O → Matrix Ω Ω ℂ) : ℝ≥0∞ :=
  ∑ ω, ∑ i, ∑ j, (‖(T' ω i j - T ω i j : ℂ)‖).toNNReal

/-- The sum of squared coordinate norms after applying the embedded operator `V * T ω * Vᴴ` to
the input vector. -/
noncomputable def compiledMeasurementMass {O : Type} [Fintype O]
    (V : Matrix H Ω ℂ) (T : O → Matrix Ω Ω ℂ) (φ : QState H) (ω : O) : ℝ :=
  ∑ i, ‖((V * (T ω) * Vᴴ) *ᵥ φ) i‖ ^ 2

end Asp

/-- The residue register width `shorResidueBits m`. -/
def compactWidth (m : ℕ) : ℕ := shorResidueBits m

/-- States that a finite type has an injective encoding into a Boolean register of width
determined by its cardinality. -/
def HasCompactEncoding (X : Type) [Fintype X] : Prop :=
  ∃ encode : X → Reg (compactWidth (Fintype.card X)), Function.Injective encode

/-- Requires a bounded costed law with a matching finite distribution whose masses on subgroup
subsets differ from uniform masses by at most `δ`. -/
def HasCostedNearUniformGeneration (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (δ : ℝ) : Prop :=
  ∃ (q : CostedLaw G) (μ : FinDist G) (c d : ℕ),
    (∀ g : G, Real.toNNReal (μ.prob g) = ∑' n, q (g, n)) ∧
      (∀ L : Finset ↥H,
        |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy q c ∧
        c ≤ d * (compactWidth (Fintype.card G) + 1) ^ 12

/-- Requires a power of two sampling size `q` satisfying `N ^ 2 ≤ q < 2 * N ^ 2`, as in
[Shor1997]. -/
def ShorOriginalQ (N q : ℕ) : Prop :=
  ∃ t : ℕ, q = 2 ^ t ∧ N ^ 2 ≤ q ∧ q < 2 * N ^ 2

/-- Lists all natural pairs `(u, v)` with `u < v ≤ B`, ordered by the denominator and then
numerator. -/
def boundedPairsList (B : ℕ) : List (ℕ × ℕ) :=
  (List.range (B + 1)).flatMap fun v => (List.range v).map fun u => (u, v)

/-- Tests coprimality and the integer approximation inequality `2 * |y * v - u * M| ≤ v` for a
candidate pair `(u, v)`. -/
def originalWindowAccept (M y : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (Nat.Coprime p.1 p.2 ∧
    2 * (((y : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (M : ℤ)).natAbs) ≤ p.2)

/-- Returns the first bounded numerator and denominator pair passing `originalWindowAccept`, if
one exists. -/
def originalWindowDecode (B M y : ℕ) : Option (ℕ × ℕ) :=
  ((boundedPairsList B).filter (originalWindowAccept M y)).head?

/-- Decodes a candidate denominator and returns it only when its order verification product
equals one. -/
def verifiedOrderDecodeOriginal (N q : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y : Fin q) : Option ℕ :=
  match originalWindowDecode (N - 1) q y.val with
  | none => none
  | some (_, r) => if orderVerificationProduct N a r = 1 then some r else none

/-- Requires positive good outcome probability and a distribution equal to Born weights divided
by that probability and supported on good outcomes. -/
def HasDlogGoodConditional (p q r : ℕ) [NeZero p] (g x : ZMod p) : Prop :=
  ∃ (hnorm : Normalized (dlogTwoDimState p q g x))
      (cond : FinDist (Fin q × Fin q × ZMod p)),
    (0 < (dlogBornLaw p q g x hnorm).probEvent (L := 1)
        (fun ω => dlogGoodOutcome p q r (ω 0))) ∧
      (∀ o, cond.prob o = (dlogBornLaw p q g x hnorm).prob o /
        (dlogBornLaw p q g x hnorm).probEvent (L := 1)
          (fun ω => dlogGoodOutcome p q r (ω 0))) ∧
      (∀ o, ¬ dlogGoodOutcome p q r o → cond.prob o = 0)

/-- Specifies probability at least one half of obtaining at least `t` good outcomes in `480 * t`
samples under the stated discrete logarithm hypotheses [Shor1997]. -/
def DlogOriginal480Budget : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → orderOf g = p - 1 → x = g ^ r → q ≤ 2 * (p - 1) →
    ∀ (hnorm : Normalized (dlogTwoDimState p q g x)) (t : ℕ),
      (dlogBornLaw p q g x hnorm).probEvent (L := 480 * t)
          (fun ω => dlogGoodCountGE p q r t (480 * t) ω)
        ≥ 1 / 2

/-- Lists maximal prime power divisors of `m` whose prime base is at most eighteen. -/
noncomputable def smallPrimePowerList (m : ℕ) : List ℕ :=
  ((Finset.range (m + 1)).filter fun w =>
    ∃ ℓ a : ℕ, Nat.Prime ℓ ∧ ℓ ≤ 18 ∧ w = ℓ ^ a ∧ w ∣ m ∧ ¬ (ℓ * w ∣ m)).toList

/-- The product of the maximal small prime power divisors listed by `smallPrimePowerList`. -/
noncomputable def smallPrimePart (m : ℕ) : ℕ := (smallPrimePowerList m).prod

/-- Lists residues below `p - 1` satisfying all supplied linear congruences modulo `p - 1`. -/
noncomputable def effectiveCrtCandidates (p : ℕ) (t : ℕ) (c' d' : Fin t → ℤ) : List ℕ :=
  ((Finset.range (p - 1)).filter fun r' =>
    ∀ i : Fin t, (d' i + ((r' : ℕ) : ℤ) * c' i) % (((p - 1 : ℕ) : ℤ)) = 0).toList

end Qatlib.Concepts.RiskEstimation.PopulationGap
