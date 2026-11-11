/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21StrictSeparationStat

/-!
# General adversary and query model definitions

This module defines phase oracles, POVM readout probabilities, and bounded error query runs. It
introduces the general adversary value `advPmValue` and weighted variants based on nonnegative
real or Hermitian complex matrices, following the negative weight adversary framework
[HoyerLeeSpalek2007].

It also defines minimax witnesses, composition data, Boolean certificates and iterates, and a
filtered Gram distance for coherent state conversion. The measurement conventions agree with
[Watrous2018].

## Main definitions

* `IsBoundedErrorRun`: a unitary query circuit with normalized input and successful POVM
  readout.
* `advPmValue`: the supremum of admissible Hermitian witness ratios.
* `IsMinimaxOptimal`: a probability family attaining the minimax value.
* `stateQueryDistance`: the filtered gamma two value of a Gram matrix difference.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The diagonal phase query oracle with phase `exp (2πi * input(i) * a / q)` on an index,
answer, and workspace basis vector. -/
noncomputable def phaseOracle {q n : ℕ} [NeZero q] {W : Type}
    (input : Fin n → Fin q) : Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ :=
  Matrix.of fun p p' =>
    if p = p' then
      Complex.exp ((2 * Real.pi * Complex.I) *
        (((input p.1.1).val : ℝ) * ((p.1.2.val : ℝ) / (q : ℝ))))
    else 0

/-- The predicate that each output operator is positive semidefinite and their sum is the
identity. -/
def IsPovm {H Y : Type} [Fintype H] [Fintype Y] (out : Y → Matrix H H ℂ) : Prop :=
  (∀ y, Matrix.PosSemidef (out y)) ∧ (∑ y, out y) = 1

/-- The real part of the quadratic form of an output operator on a pure state. -/
noncomputable def povmProb {H Y : Type} [Fintype H] (out : Y → Matrix H H ℂ)
    (y : Y) (ψ : QState H) : ℝ :=
  (Inner ψ (out y *ᵥ ψ)).re

/-- A unitary query circuit with normalized input, POVM outputs, error in `[0, 1 / 2]`, and
success probability at least one minus the error. -/
def IsBoundedErrorRun {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ) : Prop :=
  IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧ 0 ≤ eps ∧ eps ≤ 1 / 2 ∧
    ∀ x, 1 - eps ≤ povmProb out (f x) (Run (phaseOracle (W := W) (input x)) C psi)

/-- Retain exactly the matrix entries whose two inputs differ at the selected coordinate. -/
def genAdvFilter {X κ A γ : Type} [Zero γ] [DecidableEq A]
    (input : X → κ → A) (Γ : Matrix X X γ) (i : κ) : Matrix X X γ :=
  fun x y => if input x i ≠ input y i then Γ x y else 0

/-- The supremum of the operator norms of all coordinate filters of a complex adversary matrix. -/
noncomputable def maxFilterNorm {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) : ℝ :=
  ⨆ i : κ, ‖genAdvFilter input Γ i‖

/-- The supremum of the operator norms of all coordinate filters of a real adversary matrix. -/
noncomputable def maxFilterNormR {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℝ) : ℝ :=
  ⨆ i : κ, ‖genAdvFilter input Γ i‖

/-- The extended nonnegative ratio of a complex witness norm to its maximum coordinate filter
norm. -/
noncomputable def advPmWitnessValue {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal (maxFilterNorm input Γ)

/-- The supremum of witness ratios over nonzero Hermitian matrices vanishing on pairs with equal
function outputs [HoyerLeeSpalek2007]. -/
noncomputable def advPmValue {X Y κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (f : X → Y) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧ (∀ x y, f x = f y → Γ x y = 0) ∧ Γ ≠ 0},
    advPmWitnessValue input Γ.1

/-- The infimum of cost times witness norm divided by coordinate filter norm for a real matrix,
evaluated in `ENNReal`. -/
noncomputable def advAlphaWitnessR {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (Γ : Matrix X X ℝ) : ℝ≥0∞ :=
  ⨅ i : κ, ENNReal.ofReal (α i) * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

/-- The infimum of extended coordinate costs times a complex witness norm divided by the
corresponding filter norm. -/
noncomputable def advAlphaPmWitness {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (β : κ → ℝ≥0∞) (Γ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ i : κ, β i * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

/-- The infimum of extended coordinate costs times a real witness norm divided by the
corresponding filter norm. -/
noncomputable def advAlphaENNWitness {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (β : κ → ℝ≥0∞) (Γ : Matrix X X ℝ) : ℝ≥0∞ :=
  ⨅ i : κ, β i * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

/-- The weighted adversary supremum over nonzero symmetric entrywise nonnegative matrices
separating opposite Boolean outputs, using real costs. -/
noncomputable def advAlphaR {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧
      (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    advAlphaWitnessR input α Γ.1

/-- The weighted adversary supremum over nonzero Hermitian matrices separating opposite Boolean
outputs, using extended nonnegative costs. -/
noncomputable def advAlphaPmENN {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β : κ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧ (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    (⨅ i : κ, β i * ENNReal.ofReal ‖Γ.1‖ / ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖)

/-- The weighted adversary supremum over nonzero symmetric entrywise nonnegative matrices
separating opposite Boolean outputs, using extended costs. -/
noncomputable def advAlphaENN {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β : κ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧
      (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    (⨅ i : κ, β i * ENNReal.ofReal ‖Γ.1‖ / ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖)

/-- The nonnegative weighted adversary value with every coordinate cost equal to one. -/
noncomputable def advValue {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) : ℝ≥0∞ :=
  advAlphaR input g (fun _ => 1)

/-- The predicate that each input indexes a nonnegative coordinate distribution summing to one. -/
def IsProbabilityFamily {X κ : Type} [Fintype X] [Fintype κ] [DecidableEq κ]
    (p : X → κ → ℝ) : Prop :=
  (∀ x i, 0 ≤ p x i) ∧ (∀ x, ∑ i, p x i = 1)

/-- The reciprocal of the embedded infimum of weighted minimax overlap terms over input pairs
with opposite outputs. -/
noncomputable def minimaxWitnessValue {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (p : X → κ → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal
    (⨅ xy : {xy : X × X // g xy.1 ≠ g xy.2},
      Qatlib.Concepts.AdversaryBounds.OptimizedAdv.advMinimaxTerm input α p xy.val.1 xy.val.2))⁻¹

/-- A coordinate probability family whose witness value equals `minimaxAlpha`. -/
def IsMinimaxOptimal {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (p : X → κ → ℝ) : Prop :=
  IsProbabilityFamily p ∧ minimaxWitnessValue input g α p =
    Qatlib.Concepts.AdversaryBounds.OptimizedAdv.minimaxAlpha input g α

/-- Multiply the outer block probability by the selected block's inner coordinate probability. -/
def composeMinimaxWitness {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    (g : ∀ i, X i → Bool)
    (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i, X i → Fin (n i) → ℝ) :
    ((i : Fin k) → X i) → ((i : Fin k) × Fin (n i)) → ℝ :=
  fun x c => pf (fun i => g i (x i)) c.1 * pg c.1 (x c.1) c.2

/-- The extended nonnegative adversary value of each inner Boolean function with its assigned
coordinate costs. -/
noncomputable def blockCosts {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) : Fin k → ℝ≥0∞ :=
  fun i => advAlphaENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))

/-- The extended general adversary value of each inner Boolean function with its assigned
coordinate costs. -/
noncomputable def blockCostsPm {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) : Fin k → ℝ≥0∞ :=
  fun i => advAlphaPmENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))

/-- The block indexed input map for a family of inner Boolean input encodings. -/
abbrev composedInput {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    (gin : ∀ i, X i → Fin (n i) → Bool) :
    ((i : Fin k) → X i) → ((i : Fin k) × Fin (n i)) → Bool :=
  Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvInput gin

/-- Apply each inner Boolean function to its input block and then apply the outer function to
their outputs. -/
def composedFunction {k : ℕ} {X : Fin k → Type}
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool) :
    ((i : Fin k) → X i) → Bool :=
  fun x => f (fun i => g i (x i))

/-- The adversary matrix generated by the weighted composition construction from outer and inner
witnesses. -/
noncomputable def composedAdversary {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) :
    Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ :=
  Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvGamma g f Gf Gg

/-- Require outer, inner, and generated adversary matrices to be nonzero Hermitian witnesses
vanishing on equal output pairs. -/
def GeneratedCompositionWitness {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) : Prop :=
  Gf.IsHermitian ∧ (∀ u v, f u = f v → Gf u v = 0) ∧ Gf ≠ 0 ∧
    (∀ i, (Gg i).IsHermitian) ∧ (∀ i u v, g i u = g i v → Gg i u v = 0) ∧ (∀ i, Gg i ≠ 0) ∧
    (composedAdversary g f Gf Gg).IsHermitian ∧
    (∀ x y, composedFunction g f x = composedFunction g f y →
      composedAdversary g f Gf Gg x y = 0) ∧
    composedAdversary g f Gf Gg ≠ 0

/-- The partial six bit Kushilevitz function restricted to words of weight three. -/
noncomputable def sixBitF (w : Fin 6 → Bool) : Option Bool :=
  if Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzWeightOf w = 3
  then some (Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzIsOneWord w)
  else none

/-- The monotone six bit Kushilevitz function used for certificate and adversary comparisons. -/
noncomputable def monotoneSixBitG (w : Fin 6 → Bool) : Bool :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzMonotone w

/-- The Boolean predicate that a four bit word is sorted in either nondecreasing or
nonincreasing order. -/
def ambainisSorted4 (w : Fin 4 → Bool) : Bool :=
  ((!w 0 || w 1) && (!w 1 || w 2) && (!w 2 || w 3)) ||
    ((!w 1 || w 0) && (!w 2 || w 1) && (!w 3 || w 2))

/-- The number of coordinates at which two Boolean words differ. -/
def hamming {m : ℕ} (x y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin m => x i ≠ y i).card

/-- The predicate that agreement with an input on the chosen coordinates forces the same Boolean
function output. -/
def IsCertificate {m : ℕ} (h : (Fin m → Bool) → Bool) (x : Fin m → Bool)
    (S : Finset (Fin m)) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → h y = h x

/-- The infimum of certificate cardinalities at an input, with noncertificates assigned top in
`WithTop ℕ`. -/
noncomputable def minCertSize {m : ℕ} (h : (Fin m → Bool) → Bool)
    (x : Fin m → Bool) : WithTop ℕ :=
  ⨅ S : Finset (Fin m), if IsCertificate h x S then (S.card : WithTop ℕ) else ⊤

/-- The supremum of minimum certificate sizes over inputs with the specified Boolean output,
using zero for other inputs. -/
noncomputable def certComplexity {m : ℕ} (h : (Fin m → Bool) → Bool) (b : Bool) : WithTop ℕ :=
  ⨆ x : Fin m → Bool, if h x = b then minCertSize h x else 0

/-- The infimum Hamming distance between false and true inputs of a partial function, divided by
the input length, with zero for length zero. -/
noncomputable def relativeHamming {m : ℕ} (h : (Fin m → Bool) → Option Bool) : ℝ :=
  if m = 0 then 0
  else
    (⨅ w : {w : (Fin m → Bool) × (Fin m → Bool) //
        h w.1 = some false ∧ h w.2 = some true},
      ((hamming w.val.1 w.val.2 : ℕ) : ℝ)) / (m : ℝ)

/-- Split an index of a depth successor word into a previous depth index and a block index. -/
def powIndexSplit (n d : ℕ) : Fin (n^(d+1)) ≃ Fin (n^d) × Fin n :=
  (Equiv.cast (congrArg Fin (Nat.pow_succ n d))).trans (finProdFinEquiv (m := n^d) (n := n)).symm

/-- Collect optional Boolean coordinates into a Boolean word when all are present, and return
`none` otherwise. -/
def forceAll {n : ℕ} (bs : Fin n → Option Bool) : Option (Fin n → Bool) :=
  if h : ∀ i, (bs i).isSome then some (fun i => Option.get _ (h i)) else none

/-- Iterate a partial Boolean function on flattened input blocks, propagating undefined results
and using the single bit at depth zero. -/
def iterateFlat {n : ℕ} (f : (Fin n → Bool) → Option Bool) :
    (d : ℕ) → (Fin (n^d) → Bool) → Option Bool
  | 0, w => some (w ⟨0, by rw [Nat.pow_zero]; exact Nat.one_pos⟩)
  | d + 1, w =>
    (forceAll fun i : Fin n =>
      iterateFlat f d (fun j : Fin (n^d) => w ((powIndexSplit n d).symm (j, i)))) >>= f

/-- Iterate a total Boolean function through `iterateFlat`, extracting the Boolean result with
false as the default. -/
noncomputable def iterateTotal {n : ℕ} (g : (Fin n → Bool) → Bool) (d : ℕ) :
    (Fin (n^d) → Bool) → Bool :=
  fun w => (iterateFlat (fun v => some (g v)) d w).getD false

/-- Extract the Boolean value of a partial function on the subtype of inputs where it is
defined. -/
noncomputable def domValue {m : ℕ} (h : (Fin m → Bool) → Option Bool)
    (w : {w : Fin m → Bool // h w ≠ none}) : Bool :=
  (h w.val).getD false

/-- The zero one matrix marking pairs of inputs that differ at each coordinate. -/
def genFilterDelta {X κ A : Type} [DecidableEq A]
    (input : X → κ → A) : κ → Matrix X X ℂ :=
  fun j x y => if input x j = input y j then (0 : ℂ) else 1

/-- The filtered gamma two value of the matrix difference with respect to coordinate
disagreement filters. -/
noncomputable def stateQueryDistance {X A : Type} [Fintype X] [DecidableEq X] [DecidableEq A]
    {n : ℕ} (input : X → Fin n → A) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  filteredGamma2 (ρ - σ) (genFilterDelta input)

/-- The predicate that each pair of corresponding states has real inner product at least `sqrt
(1 - eps)`. -/
noncomputable def CoherentConverts {X H : Type} [Fintype H]
    (fin σ : X → QState H) (eps : ℝ) : Prop :=
  ∀ x, Real.sqrt (1 - eps) ≤ (Inner (fin x) (σ x)).re

/-- The predicate that an extended nonnegative source value is strictly positive and finite. -/
def SourceValueNondegenerate (v : ℝ≥0∞) : Prop := 0 < v ∧ v < ⊤

end Qatlib.Concepts.AdversaryBounds.AdvDuality
