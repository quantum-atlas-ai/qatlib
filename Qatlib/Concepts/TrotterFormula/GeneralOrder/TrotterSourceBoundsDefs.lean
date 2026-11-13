/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Concepts.TrotterFormula.ImaginaryTime.FiniteImaginaryProduct
import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScaling
import Qatlib.Concepts.TrotterFormula.GeneralOrder.OrderedCommutatorAlpha
import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrderConsumers
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Specifications for product-formula source bounds

This module defines the propositions used to formulate product-formula remainder identities,
Suzuki word bounds, support-based costs, imaginary-time consumption, and local gate synthesis.
The commutator-based simulation setting is motivated by [ChildsEtAl2021Trotter].

The definitions include explicit words, support cones, and truncations. They state proposed
properties without establishing them; proofs and counterexamples are supplied separately.

## Main statements

* `FourthOrderWordBoundSpec`: unitarity, length, error, remainder, and price requirements for
  fourth-order words.
* `GeneralOrderWordBoundSpec`: corresponding requirements for recursive Suzuki words.
* `LocalTerm`: an operator equipped with a label and finite support.
* `LightConeObservableSpec`: the proposed cone-filtered observable and size bounds.
* `NormalizedGibbsConsumptionSpec`: normalized imaginary-time output and repetition
  requirements.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
* [Suzuki, 1990][Suzuki1990]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.FiniteStrang
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.LchsRep
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {D : ℕ}
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The compositions of total degree `p` into `len + 1` entries whose final entry is nonzero. -/
def eq47Compositions (len p : ℕ) : Finset (Fin (len + 1) → ℕ) :=
  (pfCompositions (len + 1) p).filter (fun q => q (Fin.last len) ≠ 0)

/-- The time power indexed by `q` times the nested commutator beginning with `H` and continuing
with the ordered composition word from `xs`. -/
noncomputable def eq47CompositionTerm (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (q : Fin (xs.length + 1) → ℕ) (t : ℝ) : Matrix I I ℂ :=
  t ^ (∑ i, q i) • pfNestedCommList (H :: pfOrderedCompositionWord xs (fun i => q i.castSucc))

/-- The finite sum of equation-47 composition terms weighted by inverse products of factorials. -/
noncomputable def eq47Remainder (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (t : ℝ) : Matrix I I ℂ :=
  ∑ q ∈ eq47Compositions xs.length p,
    (∏ i, ((q i).factorial : ℝ))⁻¹ • eq47CompositionTerm xs H q t

/-- The grouped remainder expression, defined to equal `eq47Remainder`. -/
noncomputable def groupedIntegralRemainder (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (t : ℝ) : Matrix I I ℂ :=
  eq47Remainder xs H p t

/-- The proposed truncated-series identity and ordered-commutator remainder bound for
coefficient-matched anti-Hermitian generators, including negative times. -/
def Eq47IdentitySpec : Prop :=
  ∀ (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ),
    1 ≤ p → (∀ X ∈ xs, Xᴴ = -X) → Hᴴ = -H →
    (∀ n, n < p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) →
    ∀ t : ℝ,
    (suzukiExponentialWord xs t - ∑ n ∈ Finset.range p, t ^ n • suzukiSeries xs n =
        eq47Remainder xs H p t) ∧
    (∀ t' : ℝ, t' < 0 →
      suzukiExponentialWord xs t' - ∑ n ∈ Finset.range p, t' ^ n • suzukiSeries xs n =
        eq47Remainder xs H p t') ∧
    (‖eq47Remainder xs H p t‖ ≤ pfOrderedAdBudget xs H p LinearMap.id * |t| ^ p)

/-- The fifteen slot labels obtained by repeating `[0, 1, 0]` five times. -/
def suzuki4SlotLabels : List ℕ :=
  (List.replicate 5 [0, 1, 0]).flatten

/-- The proposition combining fourth-order Suzuki unitarity, word length, norm and commutator
error bounds, a conjugation remainder bound, and slot-price accounting. -/
def FourthOrderWordBoundSpec : Prop :=
  ∀ (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) (price : ℕ → ℕ),
    A.IsHermitian → B.IsHermitian → 0 < r →
    let X : Matrix I I ℂ := (-Complex.I) • A
    let Y : Matrix I I ℂ := (-Complex.I) • B
    (suzuki4Run A B t r ∈ Matrix.unitaryGroup I ℂ) ∧
    ((List.replicate r (suzuki4Word A B (t / r))).flatten).length = 15 * r ∧
    (‖suzuki4Run A B t r - HamiltonianEvolution (A + B) t‖ ≤
      100 * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / (r : ℝ) ^ 4) ∧
    (‖suzuki4Run A B t r - HamiltonianEvolution (A + B) t‖ ≤
      (Nat.factorial 4 : ℝ) * pfCommAlphaSelf (suzuki4Generators X Y) 5 * |t| ^ 5 /
        ((Nat.factorial 5 : ℝ) * (r : ℝ) ^ 4)) ∧
    (‖pfConjWord (suzuki4Generators X Y) (X + Y) (t / r) -
        pfConjTrunc (suzuki4Generators X Y) (X + Y) 6 (t / r)‖ ≤
      pfCommAlphaOrderedV2 (suzuki4Generators X Y) (X + Y) 6 * |t / r| ^ 6 /
        (Nat.factorial 6 : ℝ)) ∧
    ((List.replicate r suzuki4SlotLabels).flatten).length = 15 * r ∧
    (((List.replicate r suzuki4SlotLabels).flatten.map price).sum =
      r * (10 * price 0 + 5 * price 1))

/-- The proposition combining recursive Suzuki unitarity, word length, exponential-tail and
commutator error bounds, and repeated slot-price accounting. -/
def GeneralOrderWordBoundSpec : Prop :=
  ∀ (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ) (price : ℕ → ℕ),
    (∀ X ∈ hs, Xᴴ = -X) → 0 < r →
    let w := recursiveSuzukiWord hs k t r
    let L := (3 : ℝ) ^ k * suzukiMass hs + ‖hs.sum‖
    (w.prod ∈ Matrix.unitaryGroup I ℂ) ∧
    (w.length = r * (2 * hs.length * 5 ^ k)) ∧
    (‖w.prod - NormedSpace.exp (t • hs.sum)‖ ≤
      2 * (r : ℝ) * Real.exp (L * |t / r|) * (L * |t / r|) ^ (2 * k + 3) /
        (Nat.factorial (2 * k + 3) : ℝ)) ∧
    (‖w.prod - NormedSpace.exp (t • hs.sum)‖ ≤
      (Nat.factorial (2 * (k + 1)) : ℝ) *
        pfCommAlphaSelf (recursiveSuzukiGenerators hs k) (2 * (k + 1) + 1) *
        |t| ^ (2 * (k + 1) + 1) /
        ((Nat.factorial (2 * (k + 1) + 1) : ℝ) * (r : ℝ) ^ (2 * (k + 1)))) ∧
    (((List.replicate r (List.range (2 * hs.length * 5 ^ k))).flatten.map price).sum =
      r * ((List.range (2 * hs.length * 5 ^ k)).map price).sum)

/-- An operator on dimension `D` equipped with a natural-number label and a finite support in
`Fin Λ`. -/
structure LocalTerm (D Λ : ℕ) where

  label : ℕ

  support : Finset (Fin Λ)

  op : Operator D

/-- The property that operators with disjoint assigned supports have zero commutator. -/
def IsFiniteRangeFamily {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : Prop :=
  ∀ i j : Fin Λ, Disjoint (F i).support (F j).support →
    pfComm ((F i).op) ((F j).op) = 0

/-- Uniform bounds on operator norms, support cardinalities, and the number of terms containing
any site. -/
def FiniteRangeBounded {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (b : ℝ) (d occ : ℕ) : Prop :=
  (∀ i, ‖(F i).op‖ ≤ b) ∧ (∀ i, (F i).support.card ≤ d) ∧
    (∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ)

/-- The segment count `max 1 ⌈t² * (2 * Λ² * b²) / ε⌉` used for the finite-range error estimate. -/
def finiteRangeSegments (Λ : ℕ) (b t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (t ^ 2 * (2 * (Λ : ℝ) ^ 2 * b ^ 2) / ε))

/-- The finite-range specification combining a commutator bound, simulation accuracy, word
length, a disjoint-support schedule, and labelled price accounting. -/
def GeometricCostSpec : Prop :=
  ∀ (D Λ r : ℕ) (b : ℝ) (d occ : ℕ) (F : Fin Λ → LocalTerm D Λ) (t ε : ℝ)
      (price : ℕ → ℕ),
    IsFiniteRangeFamily F → FiniteRangeBounded F b d occ →
    (∀ i, ((F i).op).IsHermitian) → 0 < r → 0 < ε →
    (pfCommutatorSum (fun i => (F i).op) ≤ 2 * (Λ : ℝ) ^ 2 * b ^ 2) ∧
    (‖pfFamily (fun i => (F i).op) t r - HamiltonianEvolution (∑ i, (F i).op) t‖ ≤
      t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (fun i => (F i).op)) ∧
    (‖pfFamily (fun i => (F i).op) t (finiteRangeSegments Λ b t ε) -
        HamiltonianEvolution (∑ i, (F i).op) t‖ ≤ ε ∧
      (pfFamilyWord (fun i => (F i).op) t (finiteRangeSegments Λ b t ε)).length =
        Λ * finiteRangeSegments Λ b t ε) ∧
    (∃ schedule : List (List (Fin Λ)),
      (∀ i : Fin Λ, i ∈ schedule.flatten) ∧
      (∀ l ∈ schedule, ∀ i ∈ l, ∀ j ∈ l, i ≠ j →
        Disjoint (F i).support (F j).support) ∧
      schedule.length ≤ Λ) ∧
    ((pfFamilyWord (fun i => (F i).op) t r).map (fun x => price x.2)).sum =
      r * ∑ i : Fin Λ, price i.val

/-- The integer-valued cyclic distance between two sites in `Fin Λ`. -/
def torusDist (Λ : ℕ) (x y : Fin Λ) : ℤ :=
  min |(x : ℤ) - (y : ℤ)| ((Λ : ℤ) - |(x : ℤ) - (y : ℤ)|)

/-- The property that `C ≥ 0`, `α > 0`, and pair-interaction norms are bounded by `C / (1 +
torusDist) ^ α`. -/
def LongRangeFamily (D Λ : ℕ) (C α : ℝ) (H : Fin Λ → Fin Λ → Operator D) : Prop :=
  0 ≤ C ∧ 0 < α ∧ ∀ x y : Fin Λ,
    ‖H x y‖ ≤ C / (1 + (torusDist Λ x y : ℝ)) ^ α

/-- The pair-interaction family obtained by setting interactions beyond torus distance `R` to
zero. -/
def longRangeTruncated (D Λ : ℕ) (R : ℕ) (H : Fin Λ → Fin Λ → Operator D) :
    Fin Λ → Fin Λ → Operator D :=
  fun x y => if torusDist Λ x y ≤ R then H x y else 0

/-- The distance-truncated pair-interaction family reindexed by `Fin (Λ * Λ)`. -/
def longRangeFlat (D Λ : ℕ) (R : ℕ) (H : Fin Λ → Fin Λ → Operator D) :
    Fin (Λ * Λ) → Operator D :=
  fun ij => longRangeTruncated D Λ R H (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2

/-- The proposed long-range specification combining truncation and simulation error bounds,
neighborhood cardinalities, word length, and price accounting. -/
def LongRangeCostSpec : Prop :=
  ∀ (D Λ r R : ℕ) (η C α : ℝ) (H : Fin Λ → Fin Λ → Operator D) (t ε : ℝ)
      (price : ℕ → ℕ),
    LongRangeFamily D Λ C α H → (∀ x y : Fin Λ, (H x y).IsHermitian) →
    0 < η → 2 + η ≤ α → 0 < r → 0 < ε →
    (‖(∑ x, ∑ y, H x y) - (∑ x, ∑ y, longRangeTruncated D Λ R H x y)‖ ≤
      (Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α) ∧
    (∀ x : Fin Λ,
      (Finset.univ.filter (fun y => torusDist Λ x y ≤ R)).card ≤ 2 * R + 1) ∧
    (‖pfFamily (longRangeFlat D Λ R H) t r - HamiltonianEvolution (∑ x, ∑ y, H x y) t‖ ≤
      (Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α +
        t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (longRangeFlat D Λ R H)) ∧
    ((pfFamilyWord (longRangeFlat D Λ R H) t r).length = Λ * Λ * r ∧
      ((pfFamilyWord (longRangeFlat D Λ R H) t r).map (fun x => price x.2)).sum =
        r * ∑ ij : Fin (Λ * Λ), price ij.val)

/-- The union of `S` with all term supports intersecting `S`. -/
def supportThickening {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (S : Finset (Fin Λ)) :
    Finset (Fin Λ) :=
  S ∪ (Finset.univ.filter (fun i => ¬Disjoint (F i).support S)).biUnion
    (fun i => (F i).support)

/-- The support region obtained by iterating `supportThickening`, starting from `S`. -/
def lightConeSites {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (S : Finset (Fin Λ)) :
    ℕ → Finset (Fin Λ)
  | 0 => S
  | n + 1 => supportThickening F (lightConeSites F S n)

/-- The term indices whose supports intersect the `r`-step thickening of `S`. -/
def coneLabels {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (S : Finset (Fin Λ)) (r : ℕ) :
    Finset (Fin Λ) :=
  Finset.univ.filter (fun i => ¬Disjoint (F i).support (lightConeSites F S r))

/-- The family product-formula word filtered to labels in the `r`-step support cone of `S`. -/
def coneWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (t : ℝ) (r : ℕ)
    (S : Finset (Fin Λ)) : List (Operator D × ℕ) :=
  (pfFamilyWord (fun i => (F i).op) t r).filter
    (fun x => x.2 ∈ (coneLabels F S r).image Fin.val)

/-- The proposed specification asserting equality of full and cone-filtered conjugations,
simulation and observable error bounds, and cone size and length bounds. -/
def LightConeObservableSpec : Prop :=
  ∀ (D Λ r : ℕ) (b : ℝ) (d occ : ℕ) (F : Fin Λ → LocalTerm D Λ) (t : ℝ)
      (O : Operator D) (S : Finset (Fin Λ)),
    IsFiniteRangeFamily F → FiniteRangeBounded F b d occ →
    (∀ i, ((F i).op).IsHermitian) → 0 < r →
    (∀ i : Fin Λ, Disjoint (F i).support S → pfComm ((F i).op) O = 0) →
    let W := pfInterpret (pfFamilyWord (fun i => (F i).op) t r)
    let Wc := pfInterpret (coneWord F t r S)
    let U := HamiltonianEvolution (∑ i, (F i).op) t
    (Wᴴ * O * W = Wcᴴ * O * Wc) ∧
    (‖W - U‖ ≤ t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (fun i => (F i).op)) ∧
    (‖Wᴴ * O * W - Uᴴ * O * U‖ ≤
      2 * ‖O‖ * (t ^ 2 / (2 * (r : ℝ)) * pfCommutatorSum (fun i => (F i).op))) ∧
    ((coneLabels F S r).card ≤ S.card * occ * (d * occ) ^ r) ∧
    ((coneWord F t r S).length = r * (coneLabels F S r).card)

/-- Half the Schatten one-norm of `ρ - σ`. -/
noncomputable def trotterTraceDistance (ρ σ : Operator D) : ℝ :=
  SchattenOne (ρ - σ) / 2

/-- The proposition requiring success-norm, normalized-output, trace-distance, and repetition
bounds for positive-semidefinite imaginary-time product formulas. -/
def NormalizedGibbsConsumptionSpec : Prop :=
  ∀ (D : ℕ) (A B : Operator D) (R β : ℝ) (r : ℕ) (ψ : Fin D → ℂ),
    A.PosSemidef → B.PosSemidef → ‖A + B‖ ≤ R → 0 ≤ β → 0 < r →
    ‖stateVector ψ‖ = 1 →
    let Y := imaginaryRun A B β r
    let U := NormedSpace.exp (-(β) • (A + B))
    let η := β ^ 2 * ‖A * B - B * A‖ / (2 * (r : ℝ))
    let v := stateVector (U *ᵥ ψ)
    let y := stateVector (Y *ᵥ ψ)
    let p := ‖y‖ ^ 2
    η < ‖v‖ →
    ((‖v‖ - η) ^ 2 ≤ ‖y‖ ^ 2 ∧ ‖y‖ ≤ 1 ∧
      ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ≤ 2 * η / ‖v‖) ∧
    (trotterTraceDistance (outerProduct (WithLp.ofLp (NormedSpace.normalize y)))
        (outerProduct (WithLp.ofLp (NormedSpace.normalize v))) ≤
      2 * (η / ‖v‖) + 2 * Real.sqrt (1 - p)) ∧
    (0 < p → 0 < η → η < 1 →
      ∃ m : ℕ, (1 - p) ^ m ≤ η ∧ (m : ℝ) * p ≤ Real.log (1 / η) + 1)

/-- The phase precision index of a controlled-phase local gate, with value zero for Hadamard and
swap gates. -/
def localGateBits {n : ℕ} : LocalQFTGate n → ℕ
  | .cp _ _ k _ => k
  | .h _ => 0
  | .swap _ _ => 0

/-- The proposed uniform local-gate synthesis specification for recursive Suzuki factors,
including precision, length, adjoint, accumulated error, space, and compilation bounds. -/
def ExponentialSynthesisSpec : Prop :=
  ∀ (n : ℕ) (k r : ℕ) (xs : List (Matrix (Reg n) (Reg n) ℂ)) (t δ : ℝ),
    (∀ X ∈ xs, Xᴴ = -X) → 0 < r → 0 < δ →
    let word := recursiveSuzukiWord xs k t r
    ∃ (synth : Matrix (Reg n) (Reg n) ℂ → List (LocalQFTGate n))
      (bits space compile : ℕ),
      (∀ U ∈ word,
        (∀ g ∈ synth U, localGateBits g ≤ bits) ∧
        (synth U).length ≤ 120 * (bits + 1) ^ 5 ∧
        (localProgramAdjoint (synth U)).length = (synth U).length ∧
        localProgramMatrix (synth U) ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
        ‖localProgramMatrix (synth U) - U‖ ≤ δ ∧
        ‖localProgramMatrix (localProgramAdjoint (synth U)) - Uᴴ‖ ≤ δ) ∧
      (‖(word.map (fun U => localProgramMatrix (synth U))).prod - word.prod‖ ≤
        (word.length : ℝ) * δ) ∧
      (space = n ∧ compile ≤ 200 * (bits + 1) ^ 6 * (word.length + 1))

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
