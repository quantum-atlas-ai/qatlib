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

/-!
# Data for refined commutator expansions

This module defines the composition, word, and budget data used to refine ordered commutator
expansions in the setting of [ChildsEtAl2021Trotter]. `compositionLevel`, `compositionGroup`,
and `groupedLift` connect flat multiplicities with grouped source parts, while
`orderedRemainder` and its level contributions describe conjugation truncation errors.

The remaining definitions record family scaling, coefficient deviations, local support growth,
long-range gaps, and application error ledgers. A first-fit support-conflict coloring and
recursive Suzuki stage representation provide explicit schedules and gate, depth, and routing
counts.

## Main statements

* `groupedLift`: embeds grouped parts into reversed flat coordinates.
* `orderedRemainderLevel`: isolates a conjugation remainder contribution.
* `clause50SeededFamilyBudget`: records multinomially weighted seeded commutator norms.
* `clause52Colouring`: constructs the first-fit support-conflict coloring.
* `clause52MacroStageList`: records the recursive Suzuki stages.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

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

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The finite support of a natural-valued composition, consisting of its nonzero coordinates. -/
def compositionSupport {s : ℕ} (q : Fin s → ℕ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => q i ≠ 0)

/-- The composition coordinates listed in reverse source order. -/
def sourceParts (s : ℕ) (q : Fin s → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin s => q ⟨s - 1 - i.val, by omega⟩)

/-- The source level of a composition, equal to `s` minus its first nonzero index, or zero for
empty support. -/
noncomputable def compositionLevel {s : ℕ} (q : Fin s → ℕ) : ℕ :=
  if h : (compositionSupport q).Nonempty then
    s - (compositionSupport q).min' h
  else 0

/-- The reversed source parts truncated at the composition level. -/
noncomputable def compositionGroup {s : ℕ} (q : Fin s → ℕ) : List ℕ :=
  (sourceParts s q).take (compositionLevel q)

/-- The flat composition obtained by placing grouped parts in reversed source order within the
last `k` positions and using zero elsewhere. -/
def groupedLift (s k : ℕ) (q' : List ℕ) : Fin s → ℕ :=
  fun i => if s - i.val ≤ k then q'.getD (s - i.val - 1) 0 else 0

/-- The level of a grouped list, defined as its length. -/
def groupedLevel (q' : List ℕ) : ℕ := q'.length

/-- The source parts of the flat composition obtained by `groupedLift`. -/
noncomputable def groupedSourceParts (s k : ℕ) (q' : List ℕ) : List ℕ :=
  sourceParts s (groupedLift s k q')

/-- The sum of reciprocal-factorial-weighted nested commutator norms over grouped compositions
and levels. -/
noncomputable def groupedOrderedAdBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (xs.length + 1), ∑ q' ∈ groupedCompositions p k,
    ((q'.map (fun j => (j.factorial : ℝ))).prod)⁻¹ *
      ‖pfNestedCommList (B :: groupedRepetition xs q')‖

/-- The ordered adjoint budget with the identity linear map. -/
noncomputable def flatOrderedAdBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  pfOrderedAdBudget xs B p LinearMap.id

/-- The number of grouped compositions of degree `p` and length `k`. -/
noncomputable def groupedLevelCard (p k : ℕ) : ℕ :=
  (groupedCompositions p k).card

/-- The sum of grouped level cardinalities over levels from zero through `p`. -/
noncomputable def groupedTermCard (p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (p + 1), groupedLevelCard p k

/-- The reciprocal of the product of the factorials of the grouped parts. -/
noncomputable def groupedWeight (q' : List ℕ) : ℝ :=
  ((q'.map (fun j => (j.factorial : ℝ))).prod)⁻¹

/-- The reciprocal of the product of the factorials of all composition coordinates. -/
noncomputable def flatWeight {s : ℕ} (q : Fin s → ℕ) : ℝ :=
  (∏ i, ((q i).factorial : ℝ))⁻¹

/-- The reciprocal-factorial-weighted nested commutator budget for grouped compositions at one
level. -/
noncomputable def groupedLevelBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) : ℝ :=
  ∑ q' ∈ groupedCompositions p k,
    groupedWeight q' * ‖pfNestedCommList (B :: groupedRepetition xs q')‖

/-- The flat ordered commutator budget restricted to compositions of level `k`. -/
noncomputable def flatLevelBudget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions xs.length p,
    (if compositionLevel q = k then
      flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖
    else 0)

/-- The source-ordered generator word formed by repeating each reversed source generator
according to its composition coordinate. -/
noncomputable def sourceBlockWord (xs : List (Matrix I I ℂ))
    (q : Fin xs.length → ℕ) : List (Matrix I I ℂ) :=
  (List.finRange xs.length).flatMap fun i =>
    List.replicate (q ⟨xs.length - 1 - i.val, by omega⟩) (srcGen xs (i.val + 1))

/-- The sum of time-weighted conjugation Taylor remainders for one outer generator acting on
coefficients from the remaining generators. -/
noncomputable def orderedOuterRemainder (X : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    Matrix I I ℂ :=
  ∑ k : Fin p, t ^ k.val •
    (pfConjExp X (pfConjCoeff xs B k.val) t -
      pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p - k.val) t)

/-- The remainder contribution at index `k`, transported by conjugation through the preceding
generators. -/
noncomputable def orderedRemainderLevel (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p k : ℕ) (t : ℝ) : Matrix I I ℂ :=
  pfConjWord (xs.take k)
    (orderedOuterRemainder (xs.getD k 0) (xs.drop (k + 1)) B p t) t

/-- The difference between the conjugation word and its Taylor truncation before order `p`. -/
noncomputable def orderedRemainder (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) : Matrix I I ℂ :=
  pfConjWord xs B t - pfConjTrunc xs B p t

/-- The product of the real scales raised to their composition multiplicities. -/
noncomputable def scaleProduct {n : ℕ} (c : Fin n → ℝ) (q : Fin n → ℕ) : ℝ :=
  ∏ i, c i ^ (q i)

/-- The flat ordered adjoint budget divided by `p!`. -/
noncomputable def orderedAdBudgetOverFactorial (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  flatOrderedAdBudget xs B p / (p.factorial : ℝ)

/-- The family ordered budget divided by the factorial of its degree. -/
noncomputable def familyOrderedBudgetOverFactorial {D m n : ℕ}
    (H : Fin m → Operator D) (lab : Fin n → Fin m) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  familyOrderedBudget H lab c k / (k.factorial : ℝ)

/-- The reversed list of position and multiplicity pairs for a composition. -/
def clause50PositionGroups {n : ℕ} (q : Fin n → ℕ) : List (Fin n × ℕ) :=
  (List.ofFn (fun i : Fin n => (i, q i))).reverse

/-- The first pair with positive multiplicity in a list, or `none` if no such pair exists. -/
def clause50FirstPositive {α : Type} : List (α × ℕ) → Option (α × ℕ)
  | [] => none
  | kc :: t => if 0 < kc.2 then some kc else clause50FirstPositive t

/-- The family label of the first positive block in reversed source order for a composition with
a positive coordinate. -/
noncomputable def clause50FamilyHead {m n : ℕ} (lab : Fin n → Fin m) (q : Fin n → ℕ)
    (hne : ∃ i, 0 < q i) : Fin m :=
  match clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse with
  | some kc => kc.1
  | none => lab (Classical.choose hne)

/-- The first positive-block family label in reversed source order, with the last position's
label as fallback. -/
noncomputable def clause50FamilyHeadTotal {m n : ℕ} (hn : 0 < n) (lab : Fin n → Fin m)
    (q : Fin n → ℕ) : Fin m :=
  match clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse with
  | some kc => kc.1
  | none => lab ⟨n - 1, by omega⟩

/-- The multinomially weighted sum of scaled nested commutator norms with initial matrix `B`. -/
noncomputable def clause50SeededFamilyBudget {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions n p,
    ((p.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
      |∏ i, (c i) ^ (q i)| *
      ‖pfNestedCommList (B :: (familyCompositionWord lab q).map H)‖

/-- The proposition asserting scale alignment of family commutators and the associated
ordered-budget identity. -/
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

/-- The proposition asserting the seeded and unseeded family-word conversions using the first
positive-block generator. -/
def clause50SeedConversionStatement : Prop :=
  ∀ {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D) (lab : Fin n → Fin m)
    (q : Fin n → ℕ) (hne : (∃ i, 0 < q i)),
    (pfNestedCommList (B :: (familyCompositionWord lab q).map H) =
      pfNestedCommList (pfComm (H (clause50FamilyHead lab q hne)) B ::
        ((familyCompositionWord lab q).map H).tail) ∧
     (familyNestedCommList H (familyCompositionWord lab q) =
      pfNestedCommList (H (clause50FamilyHead lab q hne) ::
        ((familyCompositionWord lab q).map H).tail)))

/-- The cubic coefficient of the two-generator product minus the cubic coefficient of the
exponential of their sum. -/
noncomputable def trotterCubicDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 3 - (((3 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 3

/-- The quadratic coefficient of the two-generator product minus the quadratic coefficient of
the exponential of their sum. -/
noncomputable def trotterQuadraticDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 2 - (((2 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2

/-- The quartic coefficient of the two-generator product minus the quartic coefficient of the
exponential of their sum. -/
noncomputable def trotterQuarticDeviation (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] 4 - (((4 : ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 4

/-- The degree-`n` coefficient deviation between the two-generator product and the exponential
of their sum. -/
noncomputable def trotterDeviation (n : ℕ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  suzukiSeries [X, Y] n - ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n

/-- The degree-`n` sum of ordered monomials `X ^ m * Y ^ (n - m)` with reciprocal factorial
weights. -/
noncomputable def twoGeneratorOrderedWords (n : ℕ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ m ∈ Finset.range (n + 1),
    ((m.factorial : ℝ)⁻¹ • X ^ m) * (((n - m).factorial : ℝ)⁻¹ • Y ^ (n - m))

/-- The union of the initial support with the supports of all local terms selected by a word. -/
noncomputable def nestedSupport {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (B : Finset (Fin Λ)) (w : List (Fin Λ)) : Finset (Fin Λ) :=
  w.foldl (fun acc i => acc ∪ (F i).support) B

/-- The number of local terms whose supports intersect `S`. -/
noncomputable def supportOccupancy {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) : ℕ :=
  (Finset.univ.filter (fun i => ¬Disjoint (F i).support S)).card

/-- The product `d * occ` used as a support-growth bound. -/
noncomputable def supportGrowthBound (d occ : ℕ) : ℕ :=
  d * occ

/-- The piecewise torus pair-count quantity, equal to `Λ` at zero distance, `2 * d` when `2 * d
≤ Λ`, and zero otherwise. -/
noncomputable def torusPairCount (Λ d : ℕ) : ℕ :=
  if d = 0 then Λ else if 2 * d ≤ Λ then 2 * d else 0

/-- The decay contribution `C * torusPairCount Λ d / (1 + d) ^ α` at distance parameter `d`. -/
noncomputable def longRangeTailSum (Λ : ℕ) (C α : ℝ) (d : ℕ) : ℝ :=
  C * (torusPairCount Λ d : ℝ) / (1 + d) ^ α

/-- The condition `1 < α` on the long-range decay exponent. -/
def longRangeSummable (α : ℝ) : Prop := 1 < α

/-- The sum of the differences between all original pair terms and their range-`R` truncations. -/
noncomputable def longRangeGap {D Λ : ℕ} (R : ℕ)
    (H : Fin Λ → Fin Λ → Operator D) : Operator D :=
  ∑ x, ∑ y, (H x y - longRangeTruncated D Λ R H x y)

/-- The number of sites in the light cone after `r` steps. -/
noncomputable def lightConeSiteCount {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) (r : ℕ) : ℕ :=
  (lightConeSites F S r).card

/-- The number of local-term labels in the light cone after `r` steps. -/
noncomputable def lightConeLabelCount {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (S : Finset (Fin Λ)) (r : ℕ) : ℕ :=
  (coneLabels F S r).card

/-- The norm of the segment multiplicative defect. -/
noncomputable def multiplicativeTransportFactor {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) : ℝ :=
  ‖segmentMultiplicativeDefect xs H t r‖

/-- The inverse stability factor used for propagation. -/
noncomputable def inversePropagationFactor (η : ℝ) : ℝ :=
  inverseStabilityFactor η

/-- The norm of the partition-function discrepancy divided by the norm of the ideal partition
function. -/
noncomputable def tfimRelativePartitionError {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℝ :=
  ‖tfimPartitionCandidate A B t r - tfimIdealPartition A B t‖ /
    ‖tfimIdealPartition A B t‖

/-- The complex difference between the candidate and ideal partition functions. -/
noncomputable def tfimAdditivePartitionError {D : ℕ} (A B : Operator D)
    (t : ℝ) (r : ℕ) : ℂ :=
  tfimPartitionCandidate A B t r - tfimIdealPartition A B t

/-- The norm of the unnormalized Gibbs operator. -/
noncomputable def gibbsOutputNorm {D : ℕ} (H : Operator D) (β : ℝ) : ℝ :=
  ‖gibbsUnnormalized H β‖

/-- The reciprocal of the Gibbs partition function. -/
noncomputable def gibbsNormalisationFactor {D : ℕ} (H : Operator D) (β : ℝ) : ℂ :=
  (gibbsPartition H β)⁻¹

/-- A record of preparation calls, amplification rounds, readout shots, and output norm for
Gibbs-state consumption. -/
structure GibbsConsumptionLedger where

  prepCalls : ℕ

  amplificationRounds : ℕ

  readoutShots : ℕ

  outputNorm : ℝ

/-- The maximum of one and the ceiling of `L ^ 2 * |t| ^ 3 / (3 * ε)`. -/
noncomputable def timeDependentSegments (L t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)))

/-- The single-segment budget `L ^ 2 * |t / r| ^ 3 / 3` for natural-valued parameters. -/
noncomputable def timeDependentSegmentBudget (L t r : ℕ) : ℝ :=
  let τ := t / (r : ℝ)
  L ^ 2 * |τ| ^ 3 / 3

/-- A record of numeric precision, primitive gate count, numeric error, and gate error. -/
structure SynthesisLedger where

  numericBits : ℕ

  primitiveGates : ℕ

  numericError : ℝ

  gateError : ℝ

/-- The sum of the numeric and gate errors in a synthesis ledger. -/
noncomputable def synthesisError (l : SynthesisLedger) : ℝ :=
  l.numericError + l.gateError

/-- A record of exponential, time-point, and access-gate counts together with normalization and
success probability. -/
structure LchsInterfaceLedger where

  exponentials : ℕ

  timePoints : ℕ

  accessGates : ℕ

  normalisation : ℝ

  successProbability : ℝ

/-- A record of layer count, Trotter error, and synthesis error for the ferromagnetic
construction. -/
structure FerroLedger where

  layers : ℕ

  trotterError : ℝ

  synthesisError : ℝ

/-- The sum of the Trotter and synthesis errors in a ferromagnetic ledger. -/
noncomputable def ferroRelativeError (l : FerroLedger) : ℝ :=
  l.trotterError + l.synthesisError

/-- The predicate that two local terms have intersecting supports. -/
def clause52Conflict {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i j : Fin Λ) : Prop :=
  ¬ Disjoint (F i).support (F j).support

/-- Every finite set of natural numbers leaves some natural number unused. -/
theorem clause52FreeExists (used : Finset ℕ) : ∃ c, c ∉ used := by
  by_contra hcon
  push Not at hcon
  have hsub : Finset.range (used.card + 1) ⊆ used := by
    intro c hc
    exact hcon c
  have h2 : used.card + 1 ≤ used.card := by
    simpa using! Finset.card_le_card hsub
  omega

/-- The least natural number outside a given finite used set. -/
def clause52LeastFree (used : Finset ℕ) : ℕ := Nat.find (clause52FreeExists used)

/-- The set of assigned layers occupied by distinct terms conflicting with the selected term. -/
def clause52UsedLayers {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    (Fin Λ → Option ℕ) → Finset ℕ :=
  fun a => (Finset.univ.filter
    (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j ∧ a j ≠ none)).image (fun j => (a j).getD 0)

/-- The least layer not occupied by an assigned conflicting term. -/
def clause52FirstFit {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    (Fin Λ → Option ℕ) → ℕ :=
  fun a => clause52LeastFree (clause52UsedLayers F i a)

/-- The partial coloring obtained by applying first-fit updates to the first `k` terms in order. -/
def clause52ColourUpTo {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    (k : ℕ) → (hk : k ≤ Λ) → (Fin Λ → Option ℕ) → (Fin Λ → Option ℕ)
  | 0, _, a => a
  | k+1, hk, a =>
      let s := clause52ColourUpTo F k (by omega) a
      fun j => if j.val = k then some (clause52FirstFit F ⟨k, by omega⟩ s) else s j

/-- The complete first-fit coloring starting from an entirely unassigned family. -/
def clause52Colouring {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : Fin Λ → Option ℕ :=
  clause52ColourUpTo F Λ (by omega) (fun _ => none)

/-- The layer assigned by the complete coloring, with zero as the default. -/
def clause52Layer {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (clause52Colouring F i).getD 0

/-- The condition that distinct conflicting terms with assigned colors have different colors. -/
def clause52Proper {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (a : Fin Λ → Option ℕ) : Prop :=
  ∀ (i j : Fin Λ) (ci cj : ℕ),
    a i = some ci → a j = some cj → i ≠ j → clause52Conflict F i j → ci ≠ cj

/-- The operator word listing the local family in index order. -/
def clause52FamilyWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : List (Operator D) :=
  (List.finRange Λ).map (fun i => (F i).op)

/-- The recursive Suzuki generator word built from the local-family word. -/
def clause52MacroWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : List (Operator D) :=
  recursiveSuzukiGenerators (clause52FamilyWord F) k

/-- The length of the recursive Suzuki macro word. -/
def clause52MacroGates {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : ℕ :=
  (clause52MacroWord F k).length

/-- The macro gate count multiplied by the number of segments. -/
def clause52MacroTotalGates {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k segments : ℕ) : ℕ :=
  segments * clause52MacroGates F k

/-- The selected layer regarded as an element of the finite range supplied by the occupancy
bound. -/
def clause52LayerFin {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (d occ : ℕ)
    (hlayer : ∀ i, clause52Layer F i ≤ d * (occ - 1)) (i : Fin Λ) : Fin (d * (occ - 1) + 1) :=
  ⟨clause52Layer F i, by have h := hlayer i; omega⟩

/-- The number of distinct local terms conflicting with the selected term. -/
def clause52ConflictDegree {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j)).card

/-- The list of term lists obtained by grouping terms by each layer below `L`. -/
def clause52Schedule {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ) : List (List (Fin Λ)) :=
  (List.range L).map (fun c => (List.finRange Λ).filter (fun i => clause52Layer F i = c))

/-- A stage with its scalar coefficient multiplied by `m` and its term list preserved. -/
def clause52ScaleStage {Λ : ℕ} (m : ℝ) (st : ℝ × List (Fin Λ)) : ℝ × List (Fin Λ) :=
  (m * st.1, st.2)

/-- The recursive Suzuki stage list, starting with forward and reverse half-scaled passes and
using five scaled copies at each recursion. -/
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

/-- The operator word obtained by applying a stage's scalar coefficient to its listed local
terms. -/
def clause52StageWord {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (st : ℝ × List (Fin Λ)) :
    List (Operator D) :=
  (st.2).map (fun i => st.1 • (F i).op)

/-- The list of operator words associated with the recursive macro stages. -/
def clause52MacroStageWords {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    List (List (Operator D)) :=
  (clause52MacroStageList F k).map (clause52StageWord F)

/-- The recursively defined stage count, starting at two and multiplied by five at each level. -/
def clause52StageCount : ℕ → ℕ
  | 0 => 2
  | k+1 => 5 * clause52StageCount k

/-- The stage count multiplied by the number of parallel layers. -/
def clause52MacroDepth (k L : ℕ) : ℕ := clause52StageCount k * L

/-- The term routing-swap count, defined as its support cardinality minus one using natural
subtraction. -/
def clause52TermRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) : ℕ :=
  (F i).support.card - 1

/-- The sum of term routing-swap counts over the distinct indices in a layer list. -/
def clause52LayerRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (l : List (Fin Λ)) : ℕ :=
  Finset.sum l.toFinset (fun i => clause52TermRouteSwaps F i)

/-- The sum of routing-swap counts over all family terms. -/
def clause52FamilyRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) : ℕ :=
  ∑ i : Fin Λ, clause52TermRouteSwaps F i

/-- The family routing-swap count multiplied by the recursive macro stage count. -/
def clause52MacroRouteSwaps {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) : ℕ :=
  clause52StageCount k * clause52FamilyRouteSwaps F

end Qatlib.Concepts.TrotterFormula.GeneralOrder
