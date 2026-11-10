/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBounds
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCore
import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

def compositionSupport {s : ℕ} (q : Fin s → ℕ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => q i ≠ 0)

def sourceParts (s : ℕ) (q : Fin s → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin s => q ⟨s - 1 - i.val, by omega⟩)

noncomputable def compositionLevel {s : ℕ} (q : Fin s → ℕ) : ℕ :=
  if h : (compositionSupport q).Nonempty then
    s - (compositionSupport q).min' h
  else 0

noncomputable def compositionGroup {s : ℕ} (q : Fin s → ℕ) : List ℕ :=
  (sourceParts s q).take (compositionLevel q)

def groupedLift (s k : ℕ) (q' : List ℕ) : Fin s → ℕ :=
  fun i => if s - i.val ≤ k then q'.getD (s - i.val - 1) 0 else 0

def groupedLevel (q' : List ℕ) : ℕ := q'.length

noncomputable def groupedSourceParts (s k : ℕ) (q' : List ℕ) : List ℕ :=
  sourceParts s (groupedLift s k q')

noncomputable def groupedOrderedAdBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (xs.length + 1), ∑ q' ∈ groupedCompositions p k,
    ((q'.map (fun j => (j.factorial : ℝ))).prod)⁻¹ *
      ‖pfNestedCommList (B :: groupedRepetition xs q')‖

noncomputable def flatOrderedAdBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  pfOrderedAdBudget xs B p LinearMap.id

noncomputable def groupedLevelCard (p k : ℕ) : ℕ :=
  (groupedCompositions p k).card

noncomputable def groupedTermCard (p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (p + 1), groupedLevelCard p k

noncomputable def groupedWeight (q' : List ℕ) : ℝ :=
  ((q'.map (fun j => (j.factorial : ℝ))).prod)⁻¹

noncomputable def flatWeight {s : ℕ} (q : Fin s → ℕ) : ℝ :=
  (∏ i, ((q i).factorial : ℝ))⁻¹

noncomputable def groupedLevelBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) : ℝ :=
  ∑ q' ∈ groupedCompositions p k,
    groupedWeight q' * ‖pfNestedCommList (B :: groupedRepetition xs q')‖

noncomputable def flatLevelBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions xs.length p,
    (if compositionLevel q = k then
      flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖
    else 0)

noncomputable def sourceBlockWord (xs : List (Matrix I I ℂ))
    (q : Fin xs.length → ℕ) : List (Matrix I I ℂ) :=
  (List.finRange xs.length).flatMap fun i =>
    List.replicate (q ⟨xs.length - 1 - i.val, by omega⟩) (srcGen xs (i.val + 1))

noncomputable def orderedOuterRemainder (X : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    Matrix I I ℂ :=
  ∑ k : Fin p, t ^ k.val •
    (pfConjExp X (pfConjCoeff xs B k.val) t -
      pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p - k.val) t)

noncomputable def orderedRemainderLevel (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) (t : ℝ) : Matrix I I ℂ :=
  pfConjWord (xs.take k)
    (orderedOuterRemainder (xs.getD k 0) (xs.drop (k + 1)) B p t) t

noncomputable def orderedRemainder (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) : Matrix I I ℂ :=
  pfConjWord xs B t - pfConjTrunc xs B p t

noncomputable def scaleProduct {n : ℕ} (c : Fin n → ℝ) (q : Fin n → ℕ) : ℝ :=
  ∏ i, c i ^ (q i)

noncomputable def orderedAdBudgetOverFactorial (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  flatOrderedAdBudget xs B p / (p.factorial : ℝ)

noncomputable def familyOrderedBudgetOverFactorial {D m n : ℕ}
    (H : Fin m → Operator D) (lab : Fin n → Fin m) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  familyOrderedBudget H lab c k / (k.factorial : ℝ)

def clause50PositionGroups {n : ℕ} (q : Fin n → ℕ) : List (Fin n × ℕ) :=
  (List.ofFn (fun i : Fin n => (i, q i))).reverse

def clause50FirstPositive {α : Type} : List (α × ℕ) → Option (α × ℕ)
  | [] => none
  | kc :: t => if 0 < kc.2 then some kc else clause50FirstPositive t

noncomputable def clause50FamilyHead {m n : ℕ} (lab : Fin n → Fin m) (q : Fin n → ℕ)
    (hne : ∃ i, 0 < q i) : Fin m :=
  match clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse with
  | some kc => kc.1
  | none => lab (Classical.choose hne)

noncomputable def clause50FamilyHeadTotal {m n : ℕ} (hn : 0 < n) (lab : Fin n → Fin m)
    (q : Fin n → ℕ) : Fin m :=
  match clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse with
  | some kc => kc.1
  | none => lab ⟨n - 1, by omega⟩

noncomputable def clause50SeededFamilyBudget {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions n p,
    ((p.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
      |∏ i, (c i) ^ (q i)| *
      ‖pfNestedCommList (B :: (familyCompositionWord lab q).map H)‖

def clause50FamilyAlignmentStatement : Prop :=
  ∀ {D m : ℕ} (H : Fin m → Operator D) (B : Operator D) (L : Operator D →ₗ[ℝ] Operator D)
    (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ) (p : ℕ),
    IsFamilyWord H xs lab c →
    ((∀ (q : Fin xs.length → ℕ),
      pfNestedCommList (B :: pfOrderedCompositionWord xs q) =
        scaleProduct c q • pfNestedCommList (B :: (familyCompositionWord lab q).map H)) ∧
     (p.factorial : ℝ) * pfOrderedAdBudget xs B p L =
      ∑ q ∈ pfCompositions xs.length p,
        (p.factorial : ℝ) * (∏ i, ((q i).factorial : ℝ))⁻¹ *
          |scaleProduct c q| *
          ‖L (pfNestedCommList (B :: (familyCompositionWord lab q).map H))‖)

def clause50SeedConversionStatement : Prop :=
  ∀ {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D) (lab : Fin n → Fin m)
    (q : Fin n → ℕ) (hne : (∃ i, 0 < q i)),
    (pfNestedCommList (B :: (familyCompositionWord lab q).map H) =
      pfNestedCommList (pfComm (H (clause50FamilyHead lab q hne)) B ::
        ((familyCompositionWord lab q).map H).tail) ∧
     (familyNestedCommList H (familyCompositionWord lab q) =
      pfNestedCommList (H (clause50FamilyHead lab q hne) ::
        ((familyCompositionWord lab q).map H).tail)))

noncomputable def trotterCubicDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 3 - (((3 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 3

noncomputable def trotterQuadraticDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2

noncomputable def trotterQuarticDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 4 - (((4 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 4

noncomputable def trotterDeviation (n : ℕ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] n - ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n

noncomputable def twoGeneratorOrderedWords (n : ℕ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ m ∈ Finset.range (n + 1),
    ((m.factorial : ℝ)⁻¹ • X ^ m) * (((n - m).factorial : ℝ)⁻¹ • Y ^ (n - m))

noncomputable def nestedSupport {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (B : Finset (Fin Λ)) (w : List (Fin Λ)) : Finset (Fin Λ) :=
  w.foldl (fun acc i => acc ∪ (F i).support) B

noncomputable def supportOccupancy {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) : ℕ :=
  (Finset.univ.filter (fun i => ¬Disjoint (F i).support S)).card

noncomputable def supportGrowthBound (d occ : ℕ) : ℕ :=
  d * occ

noncomputable def torusPairCount (Λ d : ℕ) : ℕ :=
  if d = 0 then Λ else if 2 * d ≤ Λ then 2 * d else 0

noncomputable def longRangeTailSum (Λ : ℕ) (C α : ℝ) (d : ℕ) : ℝ :=
  C * (torusPairCount Λ d : ℝ) / (1 + d) ^ α

def longRangeSummable (α : ℝ) : Prop := 1 < α

noncomputable def longRangeGap {D Λ : ℕ} (R : ℕ)
    (H : Fin Λ → Fin Λ → Operator D) : Operator D :=
  ∑ x, ∑ y, (H x y - longRangeTruncated D Λ R H x y)

noncomputable def lightConeSiteCount {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) (r : ℕ) : ℕ :=
  (lightConeSites F S r).card

noncomputable def lightConeLabelCount {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) (r : ℕ) : ℕ :=
  (coneLabels F S r).card

noncomputable def multiplicativeTransportFactor {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) : ℝ :=
  ‖segmentMultiplicativeDefect xs H t r‖

noncomputable def inversePropagationFactor (η : ℝ) : ℝ :=
  inverseStabilityFactor η

noncomputable def tfimRelativePartitionError {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℝ :=
  ‖tfimPartitionCandidate A B t r - tfimIdealPartition A B t‖ /
    ‖tfimIdealPartition A B t‖

noncomputable def tfimAdditivePartitionError {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℂ :=
  tfimPartitionCandidate A B t r - tfimIdealPartition A B t

noncomputable def gibbsOutputNorm {D : ℕ} (H : Operator D) (β : ℝ) : ℝ :=
  ‖gibbsUnnormalized H β‖

noncomputable def gibbsNormalisationFactor {D : ℕ} (H : Operator D) (β : ℝ) : ℂ :=
  (gibbsPartition H β)⁻¹

structure GibbsConsumptionLedger where

  prepCalls : ℕ

  amplificationRounds : ℕ

  readoutShots : ℕ

  outputNorm : ℝ

noncomputable def timeDependentSegments (L t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)))

noncomputable def timeDependentSegmentBudget (L t r : ℕ) : ℝ :=
  let τ := t / (r : ℝ)
  L ^ 2 * |τ| ^ 3 / 3

structure SynthesisLedger where

  numericBits : ℕ

  primitiveGates : ℕ

  numericError : ℝ

  gateError : ℝ

noncomputable def synthesisError (l : SynthesisLedger) : ℝ :=
  l.numericError + l.gateError

structure LchsInterfaceLedger where

  exponentials : ℕ

  timePoints : ℕ

  accessGates : ℕ

  normalisation : ℝ

  successProbability : ℝ

structure FerroLedger where

  layers : ℕ

  trotterError : ℝ

  synthesisError : ℝ

noncomputable def ferroRelativeError (l : FerroLedger) : ℝ :=
  l.trotterError + l.synthesisError

def clause52Conflict {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i j : Fin Λ) : Prop :=
  ¬ Disjoint (F i).support (F j).support

theorem clause52FreeExists (used : Finset ℕ) : ∃ c, c ∉ used := by
  by_contra hcon
  push Not at hcon
  have hsub : Finset.range (used.card + 1) ⊆ used := by
    intro c hc
    exact hcon c
  have h2 : used.card + 1 ≤ used.card := by
    simpa using! Finset.card_le_card hsub
  omega

def clause52LeastFree (used : Finset ℕ) : ℕ := Nat.find (clause52FreeExists used)

def clause52UsedLayers {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    (Fin Λ → Option ℕ) → Finset ℕ :=
  fun a => (Finset.univ.filter
    (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j ∧ a j ≠ none)).image (fun j => (a j).getD 0)

def clause52FirstFit {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    (Fin Λ → Option ℕ) → ℕ :=
  fun a => clause52LeastFree (clause52UsedLayers F i a)

def clause52ColourUpTo {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    (k : ℕ) → (hk : k ≤ Λ) → (Fin Λ → Option ℕ) → (Fin Λ → Option ℕ)
  | 0, _, a => a
  | k+1, hk, a =>
      let s := clause52ColourUpTo F k (by omega) a
      fun j => if j.val = k then some (clause52FirstFit F ⟨k, by omega⟩ s) else s j

def clause52Colouring {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : Fin Λ → Option ℕ :=
  clause52ColourUpTo F Λ (by omega) (fun _ => none)

def clause52Layer {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (clause52Colouring F i).getD 0

def clause52Proper {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (a : Fin Λ → Option ℕ) : Prop :=
  ∀ (i j : Fin Λ) (ci cj : ℕ),
    a i = some ci → a j = some cj → i ≠ j → clause52Conflict F i j → ci ≠ cj

def clause52FamilyWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : List (Operator D) :=
  (List.finRange Λ).map (fun i => (F i).op)

def clause52MacroWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : List (Operator D) :=
  recursiveSuzukiGenerators (clause52FamilyWord F) k

def clause52MacroGates {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : ℕ :=
  (clause52MacroWord F k).length

def clause52MacroTotalGates {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k segments : ℕ) : ℕ :=
  segments * clause52MacroGates F k

def clause52LayerFin {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (d occ : ℕ)
    (hlayer : ∀ i, clause52Layer F i ≤ d * (occ - 1)) (i : Fin Λ) : Fin (d * (occ - 1) + 1) :=
  ⟨clause52Layer F i, by have h := hlayer i; omega⟩

def clause52ConflictDegree {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j)).card

def clause52Schedule {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ) : List (List (Fin Λ)) :=
  (List.range L).map (fun c => (List.finRange Λ).filter (fun i => clause52Layer F i = c))

def clause52ScaleStage {Λ : ℕ} (m : ℝ) (st : ℝ × List (Fin Λ)) : ℝ × List (Fin Λ) :=
  (m * st.1, st.2)

def clause52MacroStageList {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : ℕ →
    List (ℝ × List (Fin Λ))
  | 0 => [(1 / 2, (List.finRange Λ)), (1 / 2, (List.finRange Λ).reverse)]
  | k+1 =>
      (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k)) ++
      (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k)) ++
      (clause52MacroStageList F k).map
        (clause52ScaleStage (1 - 4 * recursiveSuzukiScale k)) ++
      (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k)) ++
      (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k))

def clause52StageWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (st : ℝ × List (Fin Λ)) :
    List (Operator D) :=
  (st.2).map (fun i => st.1 • (F i).op)

def clause52MacroStageWords {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    List (List (Operator D)) :=
  (clause52MacroStageList F k).map (clause52StageWord F)

def clause52StageCount : ℕ → ℕ
  | 0 => 2
  | k+1 => 5 * clause52StageCount k

def clause52MacroDepth (k L : ℕ) : ℕ := clause52StageCount k * L

def clause52TermRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (F i).support.card - 1

def clause52LayerRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (l : List (Fin Λ)) : ℕ :=
  Finset.sum l.toFinset (fun i => clause52TermRouteSwaps F i)

def clause52FamilyRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : ℕ :=
  ∑ i : Fin Λ, clause52TermRouteSwaps F i

def clause52MacroRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : ℕ :=
  clause52StageCount k * clause52FamilyRouteSwaps F

end Qatlib.Concepts.TrotterFormula.GeneralOrder
