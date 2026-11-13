/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.OrderedCommutatorAlpha
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorSegments
import Qatlib.Concepts.TrotterFormula.TimeOrdered.TrotterErrorTypes
import Qatlib.Concepts.TrotterFormula.ImaginaryTime.FiniteImaginaryProduct
import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.Basic
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticLCHSConsumers
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Simulation budgets and resource records

This module defines the data used to express grouped commutator remainders, repeated exponential
words, and family-dependent budgets. The definitions `groupedIntegralRemainder`, `segmentWord`,
and `IsMatchedOrder` support general-order product-formula estimates in the setting of
[ChildsEtAl2021Trotter].

It also supplies support geometry, local-observable truncations, multiplicative defects, Gibbs
normalization, time-sampling budgets, and LCHS access records. These definitions specify
quantities and predicates for later results; the resource structures record their respective
counts and errors.

## Main statements

* `groupedIntegralRemainder`: sum of grouped commutator integrals.
* `familyOrderedBudget`: multinomial family commutator budget.
* `SupportChain`: overlap condition for successive term supports.
* `segmentMultiplicativeDefect`: relative segmented evolution defect.
* `GibbsOutputLedger`: preparation, amplification, and readout counts.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.FiniteStrang
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.TimeOrdered
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The generator at index `xs.length - j`, with zero as the default for an out-of-range lookup. -/
def srcGen {I : Type} [Fintype I] (xs : List (Matrix I I ℂ)) (j : ℕ) :
    Matrix I I ℂ :=
  xs.getD (xs.length - j) 0

/-- The finite set of length-`k` lists with entries at most `p`, total sum `p`, and nonzero last
entry. -/
def groupedCompositions (p k : ℕ) : Finset (List ℕ) :=
  (((Finset.univ : Finset (Fin k → Fin (p + 1))).image
      (fun f => List.ofFn (fun i => (f i).val))).filter
    (fun q => q.sum = p ∧ q.getLastD 0 ≠ 0))

/-- The generator list obtained by repeating the reverse-indexed source generators with the
multiplicities recorded in `q`. -/
def groupedRepetition {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (q : List ℕ) : List (Matrix I I ℂ) :=
  ((List.finRange q.length).flatMap fun i =>
    List.replicate (q.getD i.val 0) (srcGen xs (i.val + 1)))

/-- The scalar Taylor weight associated with a grouped composition, using its last part and the
factorials of the preceding parts. -/
noncomputable def groupedScalar (p : ℕ) (q : List ℕ) (t τ : ℝ) : ℝ :=
  let qk := q.getLastD 0
  ((t - τ) ^ (qk - 1) * t ^ (p - qk)) /
    (((qk - 1).factorial : ℝ) * ((q.dropLast.map Nat.factorial).prod : ℝ))

/-- A grouped remainder term obtained by integrating a conjugated nested commutator with weight
`groupedScalar`, then conjugating by the remaining prefix. -/
noncomputable def groupedIntegralTerm {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (q : List ℕ)
    (t : ℝ) : Matrix I I ℂ :=
  let k := q.length
  let inner := pfNestedCommList (B :: groupedRepetition xs q)
  let body := ∫ τ in 0..t,
    (groupedScalar p q t τ) • pfConjWord [srcGen xs k] inner τ
  pfConjWord (xs.take (xs.length - k)) body t

/-- The sum of grouped integral terms over levels from one to the generator-list length and
grouped compositions of total order `p`. -/
noncomputable def groupedIntegralRemainder {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    Matrix I I ℂ :=
  ∑ k ∈ Finset.Icc 1 xs.length, ∑ q ∈ groupedCompositions p k,
    groupedIntegralTerm xs B p q t

/-- The list of exponential factors obtained by repeating the step with generators scaled by
`t/r` exactly `r` times. -/
noncomputable def segmentWord {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ) :=
  (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten

/-- The condition that each entry of `xs` is the specified real scalar multiple of the family
member selected by its label. -/
def IsFamilyWord {D m : ℕ} (H : Fin m → Operator D) (xs : List (Operator D))
    (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ) : Prop :=
  ∀ i : Fin xs.length, xs.get i = (c i) • H (lab i)

/-- The nested commutator of the family operators selected by a finite tuple of labels. -/
noncomputable def familyNestedComm {D m k : ℕ} (H : Fin m → Operator D)
    (idx : Fin k → Fin m) : Operator D :=
  pfNestedCommList (List.ofFn (fun j => H (idx j)))

/-- The nested commutator of the family operators selected by a list of labels. -/
noncomputable def familyNestedCommList {D m : ℕ} (H : Fin m → Operator D)
    (w : List (Fin m)) : Operator D :=
  pfNestedCommList (w.map H)

/-- The sum of norms of family nested commutators over all label tuples of length `k`. -/
noncomputable def familyNestedBudget {D m : ℕ} (H : Fin m → Operator D)
    (k : ℕ) : ℝ :=
  ∑ idx : Fin k → Fin m, ‖familyNestedComm H idx‖

/-- The label word formed in reverse index order, repeating each label according to its
composition multiplicity. -/
def familyCompositionWord {m n : ℕ} (lab : Fin n → Fin m)
    (q : Fin n → ℕ) : List (Fin m) :=
  (List.ofFn (fun i : Fin n => (lab i, q i))).reverse.flatMap
    (fun kc => List.replicate kc.2 kc.1)

/-- The sum of family nested commutator norms over ordered compositions, weighted by multinomial
coefficients and absolute scalar products. -/
noncomputable def familyOrderedBudget {D m n : ℕ} (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions n k,
    ((k.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
      |∏ i, (c i) ^ (q i)| *
      ‖familyNestedCommList H (familyCompositionWord lab q)‖

/-- The ceiling of the family-budget expression raised to `(1:ℝ)/p`, bounded below by one, used
to select a segment count. -/
noncomputable def familyOrderedSegments {D m n : ℕ} (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (((p.factorial : ℝ) * familyOrderedBudget H lab c (p + 1) * |t| ^ (p + 1) /
      (((p + 1).factorial : ℝ) * ε)) ^ ((1 : ℝ) / p)))

/-- The number of visits to a label in `r` repetitions, computed as `r` times its multiplicity
in the base word. -/
def segmentLabelVisits {I : Type} [Fintype I] {m : ℕ}
    (xs : List (Matrix I I ℂ)) (lab : Fin xs.length → Fin m) (r : ℕ) (j : Fin m) : ℕ :=
  r * ((List.finRange xs.length).filter (fun i => lab i = j)).length

/-- The sum of label prices multiplied by their visit counts in the segmented word. -/
def segmentLabelTariff {I : Type} [Fintype I] {m : ℕ}
    (xs : List (Matrix I I ℂ)) (lab : Fin xs.length → Fin m) (_t : ℝ) (r : ℕ)
    (price : Fin m → ℕ) : ℕ :=
  ((List.finRange m).map (fun j => price j * segmentLabelVisits xs lab r j)).sum

/-- The condition that every entry after the first has support intersecting the support of an
earlier entry. -/
def SupportChain {S ι : Type} [Fintype ι] (supp : ι → Finset S)
    {ℓ : ℕ} (idx : Fin ℓ → ι) : Prop :=
  ∀ j : Fin ℓ, j.val = 0 ∨ ∃ i : Fin ℓ, i.val < j.val ∧
    (supp (idx i) ∩ supp (idx j)).Nonempty

/-- The number of label tuples of length `ℓ` satisfying `SupportChain`. -/
noncomputable def supportChainCount {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun idx : Fin ℓ → ι => SupportChain supp idx)).card

/-- The number of other labels whose supports intersect the support of a given label. -/
noncomputable def overlapDegree {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : ι =>
    j ≠ i ∧ (supp i ∩ supp j).Nonempty)).card

/-- The maximum support overlap degree, computed by a fold with initial value zero. -/
noncomputable def maxOverlapDegree {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) : ℕ :=
  (List.finRange (Fintype.card ι)).foldl
    (fun acc i => max acc (overlapDegree supp (Fintype.equivFin ι |>.symm i))) 0

/-- The condition that distinct terms assigned to the same layer have disjoint supports. -/
def IsParallelSchedule {S ι : Type} {L : ℕ} (supp : ι → Finset S)
    (layer : ι → Fin L) : Prop :=
  ∀ i j : ι, layer i = layer j → i = j ∨ Disjoint (supp i) (supp j)

/-- The maximum of zero and all pairwise distances between sites in the given support. -/
noncomputable def routingSpan {S : Type} [Fintype S] (dist : S → S → ℝ)
    (supp : Finset S) : ℝ :=
  supp.fold (fun a b => max a b) 0 fun i =>
    supp.fold (fun a b => max a b) 0 fun j => dist i j

/-- Resource counts for a finite-range simulation: segments, gates per step, depth per step, and
routing swaps per step. -/
structure FiniteRangeLedger where
  segments : ℕ
  gatesPerStep : ℕ
  depthPerStep : ℕ
  routingSwapsPerStep : ℕ

/-- A weight predicate with a diagonal unit bound and an off-diagonal power-law implication
nested under the diagonal equality hypothesis. -/
noncomputable def IsPowerLawWeight {S : Type} (dist : S → S → ℝ)
    (w : S → S → ℝ) (α : ℝ) : Prop :=
  ∀ i j : S, i = j → |w i j| ≤ 1 ∧
    (i ≠ j → 0 < dist i j ∧ |w i j| ≤ (dist i j) ^ (-(α : ℝ)))

/-- The sum of absolute weights over ordered site pairs whose distance exceeds the cutoff. -/
noncomputable def truncationTail {S : Type} [Fintype S] (dist : S → S → ℝ)
    (w : S → S → ℝ) (ℓ : ℝ) : ℝ :=
  ∑ i : S, ∑ j : S, if ℓ < dist i j then |w i j| else 0

/-- A resource record containing the segment count, distance cutoff, gates per step, and tail
cost. -/
structure LongRangeLedger where
  segments : ℕ
  cutoff : ℝ
  gatesPerStep : ℕ
  tailCost : ℝ

/-- Membership of a site in the half-open distance shell from `γ * ℓ` to `(γ+1) * ℓ`. -/
def shellMem {S : Type} (distToObs : S → ℝ) (ℓ : ℝ) (γ : ℕ) (i : S) : Prop :=
  (γ : ℝ) * ℓ ≤ distToObs i ∧ distToObs i < ((γ : ℝ) + 1) * ℓ

/-- The shell-index order that lists odd shells before even shells when `υ` is odd, and even
shells before odd shells otherwise. -/
def shellSpecialOrder (Γ υ : ℕ) : List (Fin Γ) :=
  if υ % 2 = 1 then
    (List.finRange Γ).filter (fun g => g.val % 2 = 1) ++
      (List.finRange Γ).filter (fun g => g.val % 2 = 0)
  else
    (List.finRange Γ).filter (fun g => g.val % 2 = 0) ++
      (List.finRange Γ).filter (fun g => g.val % 2 = 1)

/-- A record of light-cone radius, reduced word length, gate count, and output error for a
local-observable calculation. -/
structure LocalObservableLedger where
  lightConeRadius : ℝ
  reducedLength : ℕ
  gates : ℕ
  outputError : ℝ

/-- The ordered evolution generated by the negative word multiplicative field, minus the
identity. -/
noncomputable def multiplicativeDefect {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun τ => -(pfWordMultiplicativeField xs H τ)) 0 t - 1

/-- The segmented product multiplied on the left by the inverse target exponential, minus the
identity. -/
noncomputable def segmentMultiplicativeDefect {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    Matrix I I ℂ :=
  Ring.inverse (NormedSpace.exp (t • H)) * (segmentWord xs t r).prod - 1

/-- The condition `η < 1` used for inverse perturbation estimates. -/
def inversePropagationWindow (η : ℝ) : Prop := η < 1

/-- The reciprocal factor `(1 - η)⁻¹` in inverse perturbation bounds. -/
noncomputable def inverseStabilityFactor (η : ℝ) : ℝ := (1 - η)⁻¹

/-- The power of two obtained from the binary ceiling logarithm of `max 1 (Nat.ceil x)`. -/
noncomputable def nextPow2 (x : ℝ) : ℕ :=
  2 ^ (Nat.clog 2 (max 1 (Nat.ceil x)))

/-- A power-of-two segment choice formed from the generator norms and two nested-commutator
square-root expressions. -/
noncomputable def tfimSegmentChoice {D : ℕ} (A B : Operator D) (t ε : ℝ) : ℕ :=
  nextPow2
    (max (4 * t * (‖A‖ + ‖B‖))
      (max (Real.sqrt (t ^ 3 * ‖pfComm A (pfComm A B)‖ / ε))
        (Real.sqrt (2 * t ^ 3 * ‖pfComm B (pfComm B A)‖ / (3 * ε)))))

/-- One symmetric exponential step `exp ((t/(2*r)) • A) * exp ((t/r) • B) * exp ((t/(2*r)) •
A)`. -/
noncomputable def tfimStrangWord {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ) :
    Operator D :=
  NormedSpace.exp ((t / (2 * (r : ℝ))) • A) * NormedSpace.exp ((t / (r : ℝ)) • B) *
    NormedSpace.exp ((t / (2 * (r : ℝ))) • A)

/-- The trace of the `r`th power of the symmetric exponential step. -/
noncomputable def tfimPartitionCandidate {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℂ :=
  Matrix.trace (tfimStrangWord A B t r ^ r)

/-- The trace of the ideal exponential `exp (t • (A+B))`. -/
noncomputable def tfimIdealPartition {D : ℕ} (A B : Operator D) (t : ℝ) : ℂ :=
  Matrix.trace (NormedSpace.exp (t • (A + B)))

/-- The condition that `soft ≥ 1`, the tolerance is positive, and runtime is at most `soft *
n^17 * r^14 * ε⁻²`. -/
noncomputable def fprasRuntimeAssumption (n r : ℕ) (ε soft runtime : ℝ) : Prop :=
  1 ≤ soft ∧ 0 < ε ∧ runtime ≤ soft * ((n : ℝ) ^ 17 * (r : ℝ) ^ 14 * ε ^ (-(2 : ℝ)))

/-- A record containing a sample count and a real-valued runtime. -/
structure FprasCostLedger where
  samples : ℕ
  runtime : ℝ

/-- The unnormalized Gibbs operator `exp ((-β) • H)`. -/
noncomputable def gibbsUnnormalized {D : ℕ} (H : Operator D) (β : ℝ) :
    Operator D :=
  NormedSpace.exp ((-β) • H)

/-- The trace of the unnormalized Gibbs operator. -/
noncomputable def gibbsPartition {D : ℕ} (H : Operator D) (β : ℝ) : ℂ :=
  Matrix.trace (gibbsUnnormalized H β)

/-- The unnormalized Gibbs operator scaled by the reciprocal of its partition function. -/
noncomputable def gibbsDensity {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (gibbsPartition H β)⁻¹ • gibbsUnnormalized H β

/-- An operator scaled by the reciprocal of its trace. -/
noncomputable def normalizedDensity {D : ℕ} (M : Operator D) : Operator D :=
  (Matrix.trace M)⁻¹ • M

/-- Resource counts for Gibbs output preparation, amplification rounds, and readout shots. -/
structure GibbsOutputLedger where
  prepCalls : ℕ
  amplificationRounds : ℕ
  readoutShots : ℕ

/-- The pairwise bound `‖H s - H t‖ ≤ L * |s-t|` for all real times. -/
def IsLipschitzGenerator {I : Type} [Fintype I] (H : ℝ → Matrix I I ℂ)
    (L : ℝ) : Prop :=
  ∀ s t : ℝ, ‖H s - H t‖ ≤ L * |s - t|

/-- The condition that `Hd t` is the derivative of `H` at every time and that its norm is
bounded by `L`. -/
def IsC1Generator {I : Type} [Fintype I] (H Hd : ℝ → Matrix I I ℂ)
    (L : ℝ) : Prop :=
  (∀ t : ℝ, HasDerivAt H (Hd t) t) ∧ (∀ t : ℝ, ‖Hd t‖ ≤ L)

/-- A record of time nodes, node-query count, and exponential-macro count. -/
structure TimeEvalAccess where
  nodes : List ℝ
  nodeQueries : ℕ
  exponentialMacros : ℕ

/-- The list of exponential steps obtained by evaluating the generator at the midpoints of `N`
equal time intervals. -/
noncomputable def expMidpointWord {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : List (Matrix I I ℂ) :=
  (List.range N).map (fun j =>
    NormedSpace.exp ((T / (N : ℝ)) •
      H ((j : ℝ) * (T / (N : ℝ)) + T / (2 * (N : ℝ)))))

/-- The list of exponential steps obtained by evaluating the generator at the left endpoints of
`N` equal time intervals. -/
noncomputable def expLeftEndpointWord {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : List (Matrix I I ℂ) :=
  (List.range N).map (fun j =>
    NormedSpace.exp ((T / (N : ℝ)) • H ((j : ℝ) * (T / (N : ℝ)))))

/-- The sum of commutator norms over all ordered pairs of times in the node list. -/
noncomputable def timeNodeCommutatorBudget {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (ts : List ℝ) : ℝ :=
  (ts.map (fun s => (ts.map (fun u => ‖pfComm (H s) (H u)‖)).sum)).sum

/-- The scalar frozen-generator budget `L * h^2 / 2`. -/
noncomputable def frozenSegmentBudget (L h : ℝ) : ℝ := L * h ^ 2 / 2

/-- The complex generator `L u + i • H u` used in the forced LCHS construction. -/
noncomputable def lchsForcedGenerator {I : Type} [Fintype I]
    (L H : ℝ → Matrix I I ℂ) (u : ℝ) : Matrix I I ℂ :=
  L u + Complex.I • H u

/-- A record of homogeneous labels, source labels, preparation calls, and amplification rounds
for LCHS access. -/
structure LchsAccessLedger where
  homogeneousLabels : ℕ
  sourceLabels : ℕ
  preparationCalls : ℕ
  amplificationRounds : ℕ

/-- The amplification-round count multiplied by the total number of homogeneous and source
labels. -/
def LchsAccessLedger.exponentialAccesses (Λ : LchsAccessLedger) : ℕ :=
  Λ.amplificationRounds * (Λ.homogeneousLabels + Λ.sourceLabels)

/-- The condition that the sum of the norms of the LCHS coefficients is strictly positive. -/
def lchsCoefficientsNormalized {J : Type} [Fintype J] (γ : J → ℂ) : Prop :=
  0 < ∑ j : J, ‖γ j‖

/-- The condition that each preparation matrix maps the reference basis state to the normalized
forcing vector at its node whenever that vector is nonzero. -/
def IsForcingPreparation {I : Type} [Fintype I] [DecidableEq I] {Mt : ℕ}
    (P : Fin Mt → Matrix I I ℂ) (b : ℝ → QState I) (node : Fin Mt → ℝ)
    (i₀ : I) : Prop :=
  ∀ l : Fin Mt, b (node l) ≠ 0 →
    P l *ᵥ Ket i₀ =
      (((‖toEuclidean_fromVec (b (node l))‖⁻¹ : ℝ) : ℂ)) • b (node l)

/-- A record of success mass and output error for an LCHS construction. -/
structure LchsOutputCheck where
  successMass : ℝ
  outputError : ℝ

/-- The condition that the product-word coefficients through degree `p` equal the corresponding
coefficients of the target exponential. -/
def IsMatchedOrder {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (Htot : Matrix I I ℂ) (p : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ p → suzukiSeries xs k = ((k.factorial : ℝ)⁻¹) • Htot ^ k

/-- The condition that each site belongs to at most `τ` supports. -/
def IsTermPacking {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (τ : ℕ) : Prop :=
  ∀ x : S, (Finset.univ.filter (fun i : ι => x ∈ supp i)).card ≤ τ

/-- The routing budget `2 * supp.card * Nat.ceil (routingSpan dist supp)`. -/
noncomputable def supportSwapBudget {S : Type} [Fintype S] (dist : S → S → ℝ)
    (supp : Finset S) : ℕ :=
  2 * supp.card * Nat.ceil (routingSpan dist supp)

/-- A positive growth constant together with the bound `C * (1+r)^d` on the number of sites
within every nonnegative radius. -/
noncomputable def IsPolynomialGrowth {S : Type} [Fintype S] (dist : S → S → ℝ)
    (C : ℝ) (d : ℕ) : Prop :=
  0 < C ∧ ∀ o : S, ∀ r : ℝ, 0 ≤ r →
    ((Finset.univ : Finset S).filter (fun x => dist o x ≤ r)).card ≤
      C * (1 + r) ^ (d : ℝ)

/-- The scalar tail expression `C * (1+ℓ)^(d-α) / (α-d)`. -/
noncomputable def powerLawTailBound (C d α ℓ : ℝ) : ℝ :=
  C * (1 + ℓ) ^ ((d : ℝ) - α) / (α - d)

/-- The number of ordered term pairs possessing support sites at distance at most the cutoff. -/
noncomputable def cutoffPairCount {S ι : Type} [Fintype S] [Fintype ι]
    (dist : S → S → ℝ) (supp : ι → Finset S) (ℓ : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : ι × ι =>
    ∃ x ∈ supp p.1, ∃ y ∈ supp p.2, dist x y ≤ ℓ)).card

/-- The minimum distance from a site to a nonempty support, with value zero for an empty
support. -/
noncomputable def distToSupport {S : Type} [Fintype S] (dist : S → S → ℝ)
    (suppO : Finset S) (x : S) : ℝ :=
  if h : suppO.Nonempty then suppO.inf' h (fun y => dist x y) else 0

/-- The minimum observable-distance value on a term's support, with value zero for an empty
support. -/
noncomputable def termDistToObs {S ι : Type} [Fintype S] (distToObs : S → ℝ)
    (supp : ι → Finset S) (i : ι) : ℝ :=
  if h : (supp i).Nonempty then (supp i).inf' h distToObs else 0

/-- The finite set of terms whose support distance to the observable is at most the cutoff. -/
noncomputable def lightConeTerms {S ι : Type} [Fintype S] [Fintype ι]
    (distToObs : S → ℝ) (supp : ι → Finset S) (ℓ : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => termDistToObs distToObs supp i ≤ ℓ)

/-- The operator family obtained by keeping the light-cone terms and replacing all other terms
by zero. -/
noncomputable def truncatedFamily {S : Type} [Fintype S] {ι D : ℕ}
    (distToObs : S → ℝ) (supp : Fin ι → Finset S) (ℓ : ℝ)
    (H : Fin ι → Operator D) : Fin ι → Operator D :=
  fun i => if i ∈ lightConeTerms distToObs supp ℓ then H i else 0

/-- Membership of a term's support distance in the half-open shell from `γ * ℓ` to `(γ+1) * ℓ`. -/
def termShellMem {S ι : Type} [Fintype S] (distToObs : S → ℝ) (ℓ : ℝ)
    (supp : ι → Finset S) (γ : ℕ) (i : ι) : Prop :=
  (γ : ℝ) * ℓ ≤ termDistToObs distToObs supp i ∧
    termDistToObs distToObs supp i < ((γ : ℝ) + 1) * ℓ

/-- The repeated exponential word formed by ordering terms by the parity-based shell sequence
and retaining those in the light cone. -/
noncomputable def shellOrderedWord {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (ℓ T : ℝ) (r : ℕ) (H : Fin m → Operator D)
    (supp : Fin m → Finset S) (Γ υ : ℕ) : List (Operator D) :=
  let shells := (shellSpecialOrder Γ υ).flatMap (fun g =>
    (List.finRange m).filter (fun i => termShellMem distToObs ℓ supp g.val i))
  let order := shells.filter (fun i => i ∈ lightConeTerms distToObs supp ℓ)
  (List.replicate r (order.map (fun i =>
    NormedSpace.exp ((T / (r : ℝ)) • truncatedFamily distToObs supp ℓ H i)))).flatten

/-- The sum of the norms of commutators with `O` over terms outside the light cone. -/
noncomputable def observableTailMass {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (ℓ : ℝ) (H : Fin m → Operator D)
    (supp : Fin m → Finset S) (O : Operator D) : ℝ :=
  ∑ i : Fin m, if i ∉ lightConeTerms distToObs supp ℓ then ‖pfComm (H i) O‖ else 0

/-- The operator norm of the difference between conjugating `O` by `U` and by `V`. -/
noncomputable def observableConjugationError {D : ℕ} (O U V : Operator D) : ℝ :=
  ‖Uᴴ * O * U - Vᴴ * O * V‖

/-- The bound of each term-observable commutator norm by `κ * (1 + termDistToObs)^(-α)`. -/
noncomputable def IsObservableDecay {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (supp : Fin m → Finset S) (H : Fin m → Operator D)
    (O : Operator D) (κ α : ℝ) : Prop :=
  ∀ i : Fin m, ‖pfComm (H i) O‖ ≤
    κ * (1 + termDistToObs distToObs supp i) ^ (-(α : ℝ))

/-- The condition that every matrix entry has zero imaginary part and nonnegative real part. -/
def IsEntrywiseNonnegative {D : ℕ} (M : Operator D) : Prop :=
  ∀ i j : Fin D, (M i j).im = 0 ∧ 0 ≤ (M i j).re

/-- Bidirectional matching of characteristic-polynomial roots, with error at most `ε` times the
norm of the matching root. -/
def IsRelativeSpectrum {D : ℕ} (M N : Operator D) (ε : ℝ) : Prop :=
  (∀ μ ∈ (Matrix.charpoly M).rootSet ℂ, ∃ ν ∈ (Matrix.charpoly N).rootSet ℂ,
      ‖μ - ν‖ ≤ ε * ‖ν‖) ∧
  (∀ ν ∈ (Matrix.charpoly N).rootSet ℂ, ∃ μ ∈ (Matrix.charpoly M).rootSet ℂ,
      ‖μ - ν‖ ≤ ε * ‖μ‖)

/-- The ceiling of `log δ / log (1-p)`, bounded below by one, used for the repetition count. -/
noncomputable def gibbsAmplificationRounds (p δ : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log δ / Real.log (1 - p)))

/-- The ceiling of `log (2/δ) / (2*ε^2)`, bounded below by one, used for the readout shot count. -/
noncomputable def gibbsReadoutShots (ε δ : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log (2 / δ) / (2 * ε ^ 2)))

/-- The midpoints of the `N` equal subintervals of the time interval from zero to `T`. -/
noncomputable def midpointNodes (T : ℝ) (N : ℕ) : List ℝ :=
  (List.range N).map (fun j => (j : ℝ) * (T / (N : ℝ)) + T / (2 * (N : ℝ)))

/-- The scalar midpoint budget `T^3 * (L + commMass/2) / (24*N^2)`. -/
noncomputable def midpointSecondOrderBudget (L commMass T : ℝ) (N : ℕ) : ℝ :=
  (T ^ 3 / (24 * (N : ℝ) ^ 2)) * (L + commMass / 2)

/-- The square-root ceiling selector formed from the midpoint error coefficient and tolerance,
bounded below by one. -/
noncomputable def midpointSegments (L commMass T ε : ℝ) : ℕ :=
  max 1 (Nat.ceil ((T ^ 3 * (L + commMass / 2) / (24 * ε)) ^ ((1 : ℝ) / 2)))

/-- The rank-one outer product of `ψ` with its conjugate, scaled by the reciprocal of its
squared Euclidean norm. -/
noncomputable def forcedOutputDensity {I : Type} [Fintype I] (ψ : QState I) :
    Matrix I I ℂ :=
  (‖toEuclidean_fromVec ψ‖ ^ 2 : ℝ)⁻¹ •
    (Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j))

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
