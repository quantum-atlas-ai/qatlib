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
set_option warningAsError false
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

def srcGen {I : Type} [Fintype I] (xs : List (Matrix I I ℂ)) (j : ℕ) :
    Matrix I I ℂ :=
  xs.getD (xs.length - j) 0

def groupedCompositions (p k : ℕ) : Finset (List ℕ) :=
  (((Finset.univ : Finset (Fin k → Fin (p + 1))).image
      (fun f => List.ofFn (fun i => (f i).val))).filter
    (fun q => q.sum = p ∧ q.getLastD 0 ≠ 0))

def groupedRepetition {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (q : List ℕ) : List (Matrix I I ℂ) :=
  ((List.finRange q.length).flatMap fun i =>
    List.replicate (q.getD i.val 0) (srcGen xs (i.val + 1)))

noncomputable def groupedScalar (p : ℕ) (q : List ℕ) (t τ : ℝ) : ℝ :=
  let qk := q.getLastD 0
  ((t - τ) ^ (qk - 1) * t ^ (p - qk)) /
    (((qk - 1).factorial : ℝ) * ((q.dropLast.map Nat.factorial).prod : ℝ))

noncomputable def groupedIntegralTerm {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (q : List ℕ)
    (t : ℝ) : Matrix I I ℂ :=
  let k := q.length
  let inner := pfNestedCommList (B :: groupedRepetition xs q)
  let body := ∫ τ in 0..t,
    (groupedScalar p q t τ) • pfConjWord [srcGen xs k] inner τ
  pfConjWord (xs.take (xs.length - k)) body t

noncomputable def groupedIntegralRemainder {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    Matrix I I ℂ :=
  ∑ k ∈ Finset.Icc 1 xs.length, ∑ q ∈ groupedCompositions p k,
    groupedIntegralTerm xs B p q t

noncomputable def segmentWord {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ) :=
  (List.replicate r (xs.map (fun X => NormedSpace.exp ((t / r) • X)))).flatten

def IsFamilyWord {D m : ℕ} (H : Fin m → Operator D) (xs : List (Operator D))
    (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ) : Prop :=
  ∀ i : Fin xs.length, xs.get i = (c i) • H (lab i)

noncomputable def familyNestedComm {D m k : ℕ} (H : Fin m → Operator D)
    (idx : Fin k → Fin m) : Operator D :=
  pfNestedCommList (List.ofFn (fun j => H (idx j)))

noncomputable def familyNestedCommList {D m : ℕ} (H : Fin m → Operator D)
    (w : List (Fin m)) : Operator D :=
  pfNestedCommList (w.map H)

noncomputable def familyNestedBudget {D m : ℕ} (H : Fin m → Operator D)
    (k : ℕ) : ℝ :=
  ∑ idx : Fin k → Fin m, ‖familyNestedComm H idx‖

def familyCompositionWord {m n : ℕ} (lab : Fin n → Fin m)
    (q : Fin n → ℕ) : List (Fin m) :=
  (List.ofFn (fun i : Fin n => (lab i, q i))).reverse.flatMap
    (fun kc => List.replicate kc.2 kc.1)

noncomputable def familyOrderedBudget {D m n : ℕ} (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions n k,
    ((k.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
      |∏ i, (c i) ^ (q i)| *
      ‖familyNestedCommList H (familyCompositionWord lab q)‖

noncomputable def familyOrderedSegments {D m n : ℕ} (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (((p.factorial : ℝ) * familyOrderedBudget H lab c (p + 1) * |t| ^ (p + 1) /
      (((p + 1).factorial : ℝ) * ε)) ^ ((1 : ℝ) / p)))

def segmentLabelVisits {I : Type} [Fintype I] {m : ℕ}
    (xs : List (Matrix I I ℂ)) (lab : Fin xs.length → Fin m) (r : ℕ) (j : Fin m) : ℕ :=
  r * ((List.finRange xs.length).filter (fun i => lab i = j)).length

def segmentLabelTariff {I : Type} [Fintype I] {m : ℕ}
    (xs : List (Matrix I I ℂ)) (lab : Fin xs.length → Fin m) (_t : ℝ) (r : ℕ)
    (price : Fin m → ℕ) : ℕ :=
  ((List.finRange m).map (fun j => price j * segmentLabelVisits xs lab r j)).sum

def SupportChain {S ι : Type} [Fintype ι] (supp : ι → Finset S)
    {ℓ : ℕ} (idx : Fin ℓ → ι) : Prop :=
  ∀ j : Fin ℓ, j.val = 0 ∨ ∃ i : Fin ℓ, i.val < j.val ∧
    (supp (idx i) ∩ supp (idx j)).Nonempty

noncomputable def supportChainCount {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun idx : Fin ℓ → ι => SupportChain supp idx)).card

noncomputable def overlapDegree {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : ι =>
    j ≠ i ∧ (supp i ∩ supp j).Nonempty)).card

noncomputable def maxOverlapDegree {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) : ℕ :=
  (List.finRange (Fintype.card ι)).foldl
    (fun acc i => max acc (overlapDegree supp (Fintype.equivFin ι |>.symm i))) 0

def IsParallelSchedule {S ι : Type} {L : ℕ} (supp : ι → Finset S)
    (layer : ι → Fin L) : Prop :=
  ∀ i j : ι, layer i = layer j → i = j ∨ Disjoint (supp i) (supp j)

noncomputable def routingSpan {S : Type} [Fintype S] (dist : S → S → ℝ)
    (supp : Finset S) : ℝ :=
  supp.fold (fun a b => max a b) 0 fun i =>
    supp.fold (fun a b => max a b) 0 fun j => dist i j

structure FiniteRangeLedger where
  segments : ℕ
  gatesPerStep : ℕ
  depthPerStep : ℕ
  routingSwapsPerStep : ℕ

noncomputable def IsPowerLawWeight {S : Type} (dist : S → S → ℝ)
    (w : S → S → ℝ) (α : ℝ) : Prop :=
  ∀ i j : S, i = j → |w i j| ≤ 1 ∧
    (i ≠ j → 0 < dist i j ∧ |w i j| ≤ (dist i j) ^ (-(α : ℝ)))

noncomputable def truncationTail {S : Type} [Fintype S] (dist : S → S → ℝ)
    (w : S → S → ℝ) (ℓ : ℝ) : ℝ :=
  ∑ i : S, ∑ j : S, if ℓ < dist i j then |w i j| else 0

structure LongRangeLedger where
  segments : ℕ
  cutoff : ℝ
  gatesPerStep : ℕ
  tailCost : ℝ

def shellMem {S : Type} (distToObs : S → ℝ) (ℓ : ℝ) (γ : ℕ) (i : S) : Prop :=
  (γ : ℝ) * ℓ ≤ distToObs i ∧ distToObs i < ((γ : ℝ) + 1) * ℓ

def shellSpecialOrder (Γ υ : ℕ) : List (Fin Γ) :=
  if υ % 2 = 1 then
    (List.finRange Γ).filter (fun g => g.val % 2 = 1) ++
      (List.finRange Γ).filter (fun g => g.val % 2 = 0)
  else
    (List.finRange Γ).filter (fun g => g.val % 2 = 0) ++
      (List.finRange Γ).filter (fun g => g.val % 2 = 1)

structure LocalObservableLedger where
  lightConeRadius : ℝ
  reducedLength : ℕ
  gates : ℕ
  outputError : ℝ

noncomputable def multiplicativeDefect {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun τ => -(pfWordMultiplicativeField xs H τ)) 0 t - 1

noncomputable def segmentMultiplicativeDefect {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    Matrix I I ℂ :=
  Ring.inverse (NormedSpace.exp (t • H)) * (segmentWord xs t r).prod - 1

def inversePropagationWindow (η : ℝ) : Prop := η < 1

noncomputable def inverseStabilityFactor (η : ℝ) : ℝ := (1 - η)⁻¹

noncomputable def nextPow2 (x : ℝ) : ℕ :=
  2 ^ (Nat.clog 2 (max 1 (Nat.ceil x)))

noncomputable def tfimSegmentChoice {D : ℕ} (A B : Operator D) (t ε : ℝ) : ℕ :=
  nextPow2
    (max (4 * t * (‖A‖ + ‖B‖))
      (max (Real.sqrt (t ^ 3 * ‖pfComm A (pfComm A B)‖ / ε))
        (Real.sqrt (2 * t ^ 3 * ‖pfComm B (pfComm B A)‖ / (3 * ε)))))

noncomputable def tfimStrangWord {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ) :
    Operator D :=
  NormedSpace.exp ((t / (2 * (r : ℝ))) • A) * NormedSpace.exp ((t / (r : ℝ)) • B) *
    NormedSpace.exp ((t / (2 * (r : ℝ))) • A)

noncomputable def tfimPartitionCandidate {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℂ :=
  Matrix.trace (tfimStrangWord A B t r ^ r)

noncomputable def tfimIdealPartition {D : ℕ} (A B : Operator D) (t : ℝ) : ℂ :=
  Matrix.trace (NormedSpace.exp (t • (A + B)))

noncomputable def fprasRuntimeAssumption (n r : ℕ) (ε soft runtime : ℝ) : Prop :=
  1 ≤ soft ∧ 0 < ε ∧ runtime ≤ soft * ((n : ℝ) ^ 17 * (r : ℝ) ^ 14 * ε ^ (-(2 : ℝ)))

structure FprasCostLedger where
  samples : ℕ
  runtime : ℝ

noncomputable def gibbsUnnormalized {D : ℕ} (H : Operator D) (β : ℝ) :
    Operator D :=
  NormedSpace.exp ((-β) • H)

noncomputable def gibbsPartition {D : ℕ} (H : Operator D) (β : ℝ) : ℂ :=
  Matrix.trace (gibbsUnnormalized H β)

noncomputable def gibbsDensity {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (gibbsPartition H β)⁻¹ • gibbsUnnormalized H β

noncomputable def normalizedDensity {D : ℕ} (M : Operator D) : Operator D :=
  (Matrix.trace M)⁻¹ • M

structure GibbsOutputLedger where
  prepCalls : ℕ
  amplificationRounds : ℕ
  readoutShots : ℕ

def IsLipschitzGenerator {I : Type} [Fintype I] (H : ℝ → Matrix I I ℂ)
    (L : ℝ) : Prop :=
  ∀ s t : ℝ, ‖H s - H t‖ ≤ L * |s - t|

def IsC1Generator {I : Type} [Fintype I] (H Hd : ℝ → Matrix I I ℂ)
    (L : ℝ) : Prop :=
  (∀ t : ℝ, HasDerivAt H (Hd t) t) ∧ (∀ t : ℝ, ‖Hd t‖ ≤ L)

structure TimeEvalAccess where
  nodes : List ℝ
  nodeQueries : ℕ
  exponentialMacros : ℕ

noncomputable def expMidpointWord {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : List (Matrix I I ℂ) :=
  (List.range N).map (fun j =>
    NormedSpace.exp ((T / (N : ℝ)) •
      H ((j : ℝ) * (T / (N : ℝ)) + T / (2 * (N : ℝ)))))

noncomputable def expLeftEndpointWord {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (T : ℝ) (N : ℕ) : List (Matrix I I ℂ) :=
  (List.range N).map (fun j =>
    NormedSpace.exp ((T / (N : ℝ)) • H ((j : ℝ) * (T / (N : ℝ)))))

noncomputable def timeNodeCommutatorBudget {I : Type} [Fintype I]
    (H : ℝ → Matrix I I ℂ) (ts : List ℝ) : ℝ :=
  (ts.map (fun s => (ts.map (fun u => ‖pfComm (H s) (H u)‖)).sum)).sum

noncomputable def frozenSegmentBudget (L h : ℝ) : ℝ := L * h ^ 2 / 2

noncomputable def lchsForcedGenerator {I : Type} [Fintype I]
    (L H : ℝ → Matrix I I ℂ) (u : ℝ) : Matrix I I ℂ :=
  L u + Complex.I • H u

structure LchsAccessLedger where
  homogeneousLabels : ℕ
  sourceLabels : ℕ
  preparationCalls : ℕ
  amplificationRounds : ℕ

def LchsAccessLedger.exponentialAccesses (Λ : LchsAccessLedger) : ℕ :=
  Λ.amplificationRounds * (Λ.homogeneousLabels + Λ.sourceLabels)

def lchsCoefficientsNormalized {J : Type} [Fintype J] (γ : J → ℂ) : Prop :=
  0 < ∑ j : J, ‖γ j‖

def IsForcingPreparation {I : Type} [Fintype I] [DecidableEq I] {Mt : ℕ}
    (P : Fin Mt → Matrix I I ℂ) (b : ℝ → QState I) (node : Fin Mt → ℝ)
    (i₀ : I) : Prop :=
  ∀ l : Fin Mt, b (node l) ≠ 0 →
    P l *ᵥ Ket i₀ =
      (((‖toEuclidean_fromVec (b (node l))‖⁻¹ : ℝ) : ℂ)) • b (node l)

structure LchsOutputCheck where
  successMass : ℝ
  outputError : ℝ

def IsMatchedOrder {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (Htot : Matrix I I ℂ) (p : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ p → suzukiSeries xs k = ((k.factorial : ℝ)⁻¹) • Htot ^ k

def IsTermPacking {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (τ : ℕ) : Prop :=
  ∀ x : S, (Finset.univ.filter (fun i : ι => x ∈ supp i)).card ≤ τ

noncomputable def supportSwapBudget {S : Type} [Fintype S] (dist : S → S → ℝ)
    (supp : Finset S) : ℕ :=
  2 * supp.card * Nat.ceil (routingSpan dist supp)

noncomputable def IsPolynomialGrowth {S : Type} [Fintype S] (dist : S → S → ℝ)
    (C : ℝ) (d : ℕ) : Prop :=
  0 < C ∧ ∀ o : S, ∀ r : ℝ, 0 ≤ r →
    ((Finset.univ : Finset S).filter (fun x => dist o x ≤ r)).card ≤
      C * (1 + r) ^ (d : ℝ)

noncomputable def powerLawTailBound (C d α ℓ : ℝ) : ℝ :=
  C * (1 + ℓ) ^ ((d : ℝ) - α) / (α - d)

noncomputable def cutoffPairCount {S ι : Type} [Fintype S] [Fintype ι]
    (dist : S → S → ℝ) (supp : ι → Finset S) (ℓ : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : ι × ι =>
    ∃ x ∈ supp p.1, ∃ y ∈ supp p.2, dist x y ≤ ℓ)).card

noncomputable def distToSupport {S : Type} [Fintype S] (dist : S → S → ℝ)
    (suppO : Finset S) (x : S) : ℝ :=
  if h : suppO.Nonempty then suppO.inf' h (fun y => dist x y) else 0

noncomputable def termDistToObs {S ι : Type} [Fintype S] (distToObs : S → ℝ)
    (supp : ι → Finset S) (i : ι) : ℝ :=
  if h : (supp i).Nonempty then (supp i).inf' h distToObs else 0

noncomputable def lightConeTerms {S ι : Type} [Fintype S] [Fintype ι]
    (distToObs : S → ℝ) (supp : ι → Finset S) (ℓ : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => termDistToObs distToObs supp i ≤ ℓ)

noncomputable def truncatedFamily {S : Type} [Fintype S] {ι D : ℕ}
    (distToObs : S → ℝ) (supp : Fin ι → Finset S) (ℓ : ℝ)
    (H : Fin ι → Operator D) : Fin ι → Operator D :=
  fun i => if i ∈ lightConeTerms distToObs supp ℓ then H i else 0

def termShellMem {S ι : Type} [Fintype S] (distToObs : S → ℝ) (ℓ : ℝ)
    (supp : ι → Finset S) (γ : ℕ) (i : ι) : Prop :=
  (γ : ℝ) * ℓ ≤ termDistToObs distToObs supp i ∧
    termDistToObs distToObs supp i < ((γ : ℝ) + 1) * ℓ

noncomputable def shellOrderedWord {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (ℓ T : ℝ) (r : ℕ) (H : Fin m → Operator D)
    (supp : Fin m → Finset S) (Γ υ : ℕ) : List (Operator D) :=
  let shells := (shellSpecialOrder Γ υ).flatMap (fun g =>
    (List.finRange m).filter (fun i => termShellMem distToObs ℓ supp g.val i))
  let order := shells.filter (fun i => i ∈ lightConeTerms distToObs supp ℓ)
  (List.replicate r (order.map (fun i =>
    NormedSpace.exp ((T / (r : ℝ)) • truncatedFamily distToObs supp ℓ H i)))).flatten

noncomputable def observableTailMass {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (ℓ : ℝ) (H : Fin m → Operator D)
    (supp : Fin m → Finset S) (O : Operator D) : ℝ :=
  ∑ i : Fin m, if i ∉ lightConeTerms distToObs supp ℓ then ‖pfComm (H i) O‖ else 0

noncomputable def observableConjugationError {D : ℕ} (O U V : Operator D) : ℝ :=
  ‖Uᴴ * O * U - Vᴴ * O * V‖

noncomputable def IsObservableDecay {S : Type} [Fintype S] {D m : ℕ}
    (distToObs : S → ℝ) (supp : Fin m → Finset S) (H : Fin m → Operator D)
    (O : Operator D) (κ α : ℝ) : Prop :=
  ∀ i : Fin m, ‖pfComm (H i) O‖ ≤
    κ * (1 + termDistToObs distToObs supp i) ^ (-(α : ℝ))

def IsEntrywiseNonnegative {D : ℕ} (M : Operator D) : Prop :=
  ∀ i j : Fin D, (M i j).im = 0 ∧ 0 ≤ (M i j).re

def IsRelativeSpectrum {D : ℕ} (M N : Operator D) (ε : ℝ) : Prop :=
  (∀ μ ∈ (Matrix.charpoly M).rootSet ℂ, ∃ ν ∈ (Matrix.charpoly N).rootSet ℂ,
      ‖μ - ν‖ ≤ ε * ‖ν‖) ∧
  (∀ ν ∈ (Matrix.charpoly N).rootSet ℂ, ∃ μ ∈ (Matrix.charpoly M).rootSet ℂ,
      ‖μ - ν‖ ≤ ε * ‖μ‖)

noncomputable def gibbsAmplificationRounds (p δ : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log δ / Real.log (1 - p)))

noncomputable def gibbsReadoutShots (ε δ : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log (2 / δ) / (2 * ε ^ 2)))

noncomputable def midpointNodes (T : ℝ) (N : ℕ) : List ℝ :=
  (List.range N).map (fun j => (j : ℝ) * (T / (N : ℝ)) + T / (2 * (N : ℝ)))

noncomputable def midpointSecondOrderBudget (L commMass T : ℝ) (N : ℕ) : ℝ :=
  (T ^ 3 / (24 * (N : ℝ) ^ 2)) * (L + commMass / 2)

noncomputable def midpointSegments (L commMass T ε : ℝ) : ℕ :=
  max 1 (Nat.ceil ((T ^ 3 * (L + commMass / 2) / (24 * ε)) ^ ((1 : ℝ) / 2)))

noncomputable def forcedOutputDensity {I : Type} [Fintype I] (ψ : QState I) :
    Matrix I I ℂ :=
  (‖toEuclidean_fromVec ψ‖ ^ 2 : ℝ)⁻¹ •
    (Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j))

end Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
