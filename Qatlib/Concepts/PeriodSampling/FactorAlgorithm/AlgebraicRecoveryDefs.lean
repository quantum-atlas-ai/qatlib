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

/-!
# Algebraic recovery interfaces and resource predicates

Defines interfaces for compact abelian decoding, two-dimensional discrete-logarithm recovery,
reversible modular arithmetic, and joint recovery. These interfaces record the exact correctness
and assigned resource requirements used in the algorithmic framework associated with [Shor1997].

It also defines finite-precision subgroup measurements, register and presentation encodings,
canonical-basis machine requirements, and a finite abelian Fourier-circuit existence predicate.

## Main statements

* `CompactAbelianDecoder`: Packages decomposition, coordinate conversion, and resource
  functions.
* `ReversibleArithmetic`: Packages modular arithmetic circuits and their required properties.
* `UniformCanonicalBasisMachine`: Specifies a uniform machine for the chosen presentation
  encoding.
* `EffectiveAbelianQFT`: Specifies uniformly bounded finite abelian Fourier circuits.

## References

* [Shor, 1997][Shor1997]
-/

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

/-- The number of continued-fraction stages, defined as `cfDepth M + 1`. -/
def cfStageCount (M : ℕ) : ℕ := cfDepth M + 1

/-- A compact integer presentation is a square integer matrix with nonzero determinant. -/
def IsCompactPresentation {k : ℕ} (A : IMat k) : Prop := A.det ≠ 0

/-- A descending factor chain requires each entry to divide the preceding entry. -/
def IsFactorChain {k : ℕ} (d : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, (i : ℕ) + 1 = j → d j ∣ d i

/-- An integer matrix has the stated Smith form if left and right integer transformations of
determinant absolute value one carry it to the diagonal with entries `d`. -/
def IsSmithForm {k : ℕ} (A : IMat k) (d : Fin k → ℕ) : Prop :=
  ∃ U V : IMat k,
    U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧
      ∀ i j : Fin k, (U * A * V) i j = if i = j then (d i : ℤ) else 0

/-- Data for decomposing an integer presentation and converting between integer and natural
coordinate vectors, together with assigned bit-cost and bit-space functions. -/
structure CompactAbelianDecoder (k : ℕ) where

  decompose : IMat k → Option (Fin k → ℕ)

  toCoords : IMat k → (Fin k → ℤ) → Option (Fin k → ℕ)

  fromCoords : IMat k → (Fin k → ℕ) → Option (Fin k → ℤ)

  bitCost : IMat k → ℕ

  bitSpace : IMat k → ℕ

/-- Requires a full-rank presentation to yield a factor chain with determinant product, total
forward coordinates, collision soundness modulo the column span, and compatible coordinate
round trips. -/
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

/-- Requires every successful decomposition of a compact presentation to satisfy `IsSmithForm`. -/
def CompactAbelianDecoder.SmithSound {k : ℕ} (c : CompactAbelianDecoder k) : Prop :=
  ∀ (A : IMat k) (d : Fin k → ℕ), IsCompactPresentation A →
    c.decompose A = some d → IsSmithForm A d

/-- Requires the decoder's assigned bit cost and space to be bounded by one polynomial in the
presentation input bit length. -/
def CompactAbelianDecoder.PolyBounded {k : ℕ} (c : CompactAbelianDecoder k) : Prop :=
  ∃ C e : ℕ, ∀ A : IMat k,
    c.bitCost A ≤ C * (inputBitLength A + 1) ^ e ∧
      c.bitSpace A ≤ C * (inputBitLength A + 1) ^ e

/-- An interface taking the modulus, Fourier size, sample count, group elements, and sample
pairs to an optional discrete logarithm. -/
structure TwoDimDlogDecoder where

  decode :
    (p q m : ℕ) → (g x : ZMod p) → (Fin m → Fin q × Fin q) → Option ℕ

/-- Requires every decoded exponent to be correct and below `p - 1`, and requires recovery of
such an exponent when a good sample has `dlogCprime` coprime to `p - 1`. -/
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

/-- Encodes a natural number in an `n`-bit register by its test bits. -/
def encodeBits (n x : ℕ) : Reg n := fun i => x.testBit i

/-- Encodes three natural numbers into consecutive `b`-bit blocks. -/
def encodeTriple (b a c d : ℕ) : Reg (3 * b) := fun i =>
  if (i : ℕ) < b then a.testBit i
  else if (i : ℕ) < 2 * b then c.testBit (i - b)
  else d.testBit (i - 2 * b)

/-- Requires a circuit to preserve two bounded `b`-bit operands and write their sum modulo `2 ^
b` into an initially zero third register. -/
def RealizesModAdd (b : ℕ) (word : Circuit (Reg (3 * b))) : Prop :=
  ∀ a c : ℕ, a < 2 ^ b → c < 2 ^ b →
    Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ) word
        (Ket (encodeTriple b a c 0)) =
      Ket (encodeTriple b a c ((a + c) % 2 ^ b))

/-- Requires a circuit to preserve two bounded `b`-bit operands and write their product modulo
`2 ^ b` into an initially zero third register. -/
def RealizesModMul (b : ℕ) (word : Circuit (Reg (3 * b))) : Prop :=
  ∀ a c : ℕ, a < 2 ^ b → c < 2 ^ b →
    Run (1 : Matrix (Reg (3 * b)) (Reg (3 * b)) ℂ) word
        (Ket (encodeTriple b a c 0)) =
      Ket (encodeTriple b a c ((a * c) % 2 ^ b))

/-- Packages modular addition and multiplication circuits with macro-count bounds, zero queries,
unitarity, realization equations, and polynomially bounded assigned elementary counts. -/
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

/-- Requires polynomial bounds in the bit width for schoolbook multiplication cost, register
width, and the sum of the assigned elementary arithmetic counts. -/
def ReversibleArithmetic.PolyBounded (ar : ReversibleArithmetic) : Prop :=
  ∃ C e : ℕ, ∀ b : ℕ,
    schoolbookMulModBitCost b ≤ C * (b + 1) ^ e ∧
      3 * b ≤ C * (b + 1) ^ e ∧
      ar.addElem b + ar.mulElem b ≤ C * (b + 1) ^ e

/-- Data combining a residue-based factoring function, a two-dimensional discrete-logarithm
decoder, and assigned resource functions. -/
structure JointRecovery where

  factoring : (N : ℕ) → (m : ℕ) → (Fin m → ZMod N) → Option ℕ

  dlog : TwoDimDlogDecoder

  bitCost : (N p q m : ℕ) → ℕ

  bitSpace : (N p q m : ℕ) → ℕ

/-- Requires sound factor outputs, success when a sampled residue has a classical factor,
discrete-logarithm correctness, and polynomial bounds on the assigned resource functions. -/
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

/-- A subgroup-indexed family of conditional distributions and its uniform mixture, with
nonnegative error parameter bounding the probability of misidentifying each subgroup
element. -/
structure FinitePrecisionMeasurement (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) where

  cond : ↥H → FinDist G

  measure : FinDist G

  accuracy : ℝ

  mixture : ∀ g : G, measure.prob g =
    (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g

  accuracy_nonneg : 0 ≤ accuracy

  identify : ∀ h' : ↥H, 1 - accuracy ≤ (cond h').prob (h' : G)

/-- An injective encoding of `k` coordinates of `n` bits each into a register of length `k * n`. -/
structure TorEncoding (k n : ℕ) where

  encode : (Fin k → Fin (2 ^ n)) → Reg (k * n)

  injective : Function.Injective encode

/-- Packs `k` bounded `n`-bit coordinates into consecutive bit blocks using the quotient and
remainder of each register index by `n`. -/
def torPack (k n : ℕ) (x : Fin k → Fin (2 ^ n)) : Reg (k * n) := fun i =>
  if h : i.val / n < k then (x ⟨i.val / n, h⟩).val.testBit (i.val % n) else false

/-- Encodes an integer as a sign bit followed by the binary bits of its absolute value,
represented as nonblank optional bits. -/
def intToBinaryList (z : ℤ) : List (Option Bool) :=
  (List.range (Nat.log 2 z.natAbs + 2)).map fun i =>
    if i = 0 then some (decide (z < 0)) else some (z.natAbs.testBit (i - 1))

/-- Serializes an integer matrix by concatenating the signed binary encodings of its entries in
row order. -/
def presentationTape {k : ℕ} (A : IMat k) : List (Option Bool) :=
  (List.finRange k).flatMap fun i =>
    (List.finRange k).flatMap fun j => intToBinaryList (A i j)

/-- Requires a positive constant `C` for which `q ≤ C * k * n ^ 2 * (Nat.log 2 (k * n + 2) +
1)`. -/
def HasAspQueryBudget (k n q : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ q ≤ C * k * n ^ 2 * (Nat.log 2 (k * n + 2) + 1)

/-- Packages sample and resource counts, an injective register encoding, and a postprocessor
producing a canonical full-rank presentation with the same column span and bounded entries. -/
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

/-- Requires polynomial bounds in `k * n + 1` for the construction's assigned gate count, space,
and register width. -/
def AspConstruction.PolyBounded {k n : ℕ} (c : AspConstruction k n) : Prop :=
  ∃ C e : ℕ,
    c.gates ≤ C * (k * n + 1) ^ e ∧
      c.space ≤ C * (k * n + 1) ^ e ∧
      (k * n : ℕ) ≤ C * (k * n + 1) ^ e

/-- Requires one polynomial-time binary-tape machine with a configuration readout returning the
flattened classical canonicalization of every presentation supplied through
`presentationTape`. -/
def UniformCanonicalBasisMachine : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → List ℤ),
    BitMachinePolynomialTime machine ∧
      ∀ (k : ℕ) (A : IMat k), ∃ (t : ℕ) (c : Turing.TM0.Cfg (Option Bool) (Fin 2)),
        BitMachineAfter machine (presentationTape A) t = some c ∧
          Turing.TM0.step machine c = none ∧
          out c = (List.finRange k).flatMap fun i =>
            (List.finRange k).map fun j => classicalCanonicalize A i j

/-- Requires uniform polynomial gate bounds in the compact group width for query-free unitary
circuits realizing a finite abelian Fourier gate for some group-to-character equivalence. -/
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
