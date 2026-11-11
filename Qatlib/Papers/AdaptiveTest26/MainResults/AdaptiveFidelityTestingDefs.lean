/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Finite strategy models for fidelity equivalence testing

`RootFidelity` and `IsH1` define the fidelity separation used in equivalence testing. The finite
strategy structures specify single-copy measurements with fixed schedules, finite randomization,
or history-dependent choices, together with acceptance expressions, admissibility, and
correctness at success floor `99 / 100`.

`CopyLedger` and the strategy-specific ledger definitions record stream usage. The module also
defines pointwise logarithmic upper- and lower-bound predicates and the dimension-dependent
expressions `nonAdaptiveLowerBoundTarget` and `adaptiveEquivalenceBudget`. The development
follows [SeyfriedSenTomamichel2026].

## Main statements

* `IsCorrectNonAdaptiveEquivalenceTester`: specifies randomized nonadaptive equivalence-testing
  correctness.
* `IsCorrectAdaptiveEquivalenceTester`: specifies adaptive equivalence-testing correctness.
* `adaptiveEquivalenceBudget`: takes the minimum of the two displayed copy-budget expressions.

## References

* [Seyfried et al., 2026][SeyfriedSenTomamichel2026]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Papers.AdaptiveTest26.MainResults

set_option autoImplicit false

open scoped BigOperators
open scoped ComplexOrder

variable {D O : ℕ}

/-- The Schatten one norm of the product of the matrix square roots of `ρ` and `σ`. -/
noncomputable def RootFidelity (ρ σ : Operator D) : ℝ :=
  SchattenOne (cfc Real.sqrt ρ * cfc Real.sqrt σ)

/-- The alternative-hypothesis predicate `RootFidelity ρ σ ≤ 1 - ε`. -/
def IsH1 (ε : ℝ) (ρ σ : Operator D) : Prop :=
  RootFidelity ρ σ ≤ 1 - ε

/-- The required success probability `99 / 100`. -/
noncomputable def SuccessFloor : ℝ := (99 : ℝ) / 100

/-- An `O`-outcome family of operators on a `D`-dimensional space. -/
abbrev PovmEffects (D O : ℕ) := Fin O → Operator D

/-- The assertion that all effects are positive semidefinite and their sum is the identity. -/
def IsPovmEffects {D O : ℕ} (E : PovmEffects D O) : Prop :=
  (∀ i : Fin O, (E i).PosSemidef) ∧ ∑ i : Fin O, E i = 1

/-- The real part of `trace (E i * ρ)`, giving the weight of outcome `i`. -/
noncomputable def outcomeProb {D O : ℕ} (E : PovmEffects D O)
    (ρ : Operator D) (i : Fin O) : ℝ :=
  ((E i * ρ).trace).re

/-- The choice of which of the two input-state streams supplies the next copy. -/
inductive StreamTag where
  | rho
  | sigma
  deriving DecidableEq, Repr

/-- Selects `ρ` or `σ` according to the stream tag. -/
def stateFor {D : ℕ} (tag : StreamTag) (ρ σ : Operator D) : Operator D :=
  match tag with
  | .rho => ρ
  | .sigma => σ

/-- A complete sequence of `steps` measurement outcomes, each in `Fin O`. -/
abbrev OutcomeRecord (O steps : ℕ) := Fin steps → Fin O

/-- A fixed-length measurement strategy with predetermined stream and effect choices and a
Boolean decision on the complete outcome record. -/
structure NonAdaptiveStrategy (D O : ℕ) where

  steps : ℕ

  stream : Fin steps → StreamTag

  povm : Fin steps → PovmEffects D O

  decide : OutcomeRecord O steps → Bool

/-- The assertion that every measurement in a nonadaptive strategy is a valid POVM. -/
def IsAdmissibleNonAdaptive {D O : ℕ} (S : NonAdaptiveStrategy D O) : Prop :=
  ∀ t : Fin S.steps, IsPovmEffects (S.povm t)

/-- The sum of the product outcome weights over records accepted by a nonadaptive strategy. -/
noncomputable def nonAdaptiveAcceptProb {D O : ℕ} (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) : ℝ :=
  ∑ h : OutcomeRecord O S.steps,
    (if S.decide h then 1 else 0) *
      ∏ t : Fin S.steps,
        outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)

/-- The nonadaptive acceptance expression when both input streams supply the same operator `ρ`. -/
noncomputable def sharedNullAcceptProb {D O : ℕ} (S : NonAdaptiveStrategy D O)
    (ρ : Operator D) : ℝ :=
  nonAdaptiveAcceptProb S ρ ρ

/-- A finite probability mixture of nonadaptive strategies, with nonnegative weights summing to
one. -/
structure RandomizedNonAdaptiveStrategy (D O : ℕ) where

  support : ℕ

  weight : Fin support → ℝ

  component : Fin support → NonAdaptiveStrategy D O

  weight_nonneg : ∀ i : Fin support, 0 ≤ weight i

  weight_sum : ∑ i : Fin support, weight i = 1

/-- The assertion that every component of the randomized nonadaptive strategy uses valid POVMs. -/
def IsAdmissibleRandomizedNonAdaptive {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : Prop :=
  ∀ i : Fin S.support, IsAdmissibleNonAdaptive (S.component i)

/-- The weighted average of the component nonadaptive acceptance expressions. -/
noncomputable def randomizedAcceptProb {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ρ σ : Operator D) : ℝ :=
  ∑ i : Fin S.support, S.weight i * nonAdaptiveAcceptProb (S.component i) ρ σ

/-- The randomized nonadaptive acceptance expression when both streams supply the same operator
`ρ`. -/
noncomputable def randomizedSharedNullAcceptProb {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ρ : Operator D) : ℝ :=
  randomizedAcceptProb S ρ ρ

/-- The assertion that a randomized nonadaptive strategy is admissible, accepts every shared
density operator with probability at least `SuccessFloor`, and accepts each `IsH1 ε`
density-operator pair with probability at most `1 - SuccessFloor`. -/
def IsCorrectNonAdaptiveEquivalenceTester {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ε : ℝ) : Prop :=
  IsAdmissibleRandomizedNonAdaptive S ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      SuccessFloor ≤ randomizedSharedNullAcceptProb S ρ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      IsH1 ε ρ σ → randomizedAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- The pair of natural-number copy counts for the `rho` and `sigma` streams. -/
structure CopyLedger where

  rho : ℕ

  sigma : ℕ

/-- The sum of the two stream-specific copy counts. -/
def CopyLedger.total (c : CopyLedger) : ℕ := c.rho + c.sigma

/-- The copy ledger counting the steps assigned to each stream in a nonadaptive strategy. -/
def NonAdaptiveStrategy.ledger {D O : ℕ} (S : NonAdaptiveStrategy D O) : CopyLedger where
  rho := (Finset.univ.filter (fun t : Fin S.steps => S.stream t = .rho)).card
  sigma := (Finset.univ.filter (fun t : Fin S.steps => S.stream t = .sigma)).card

/-- The ledger obtained by maximizing each stream-specific copy count separately over all
randomized components. -/
def RandomizedNonAdaptiveStrategy.worstLedger {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : CopyLedger where
  rho := Finset.univ.sup (fun i : Fin S.support => (S.component i).ledger.rho)
  sigma := Finset.univ.sup (fun i : Fin S.support => (S.component i).ledger.sigma)

/-- The maximum number of measurement steps among the randomized nonadaptive components. -/
def RandomizedNonAdaptiveStrategy.worstTotalCopies {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : ℕ :=
  Finset.univ.sup (fun i : Fin S.support => (S.component i).steps)

/-- A fixed-length measurement strategy whose stream and effect choices depend on the previous
outcomes, with a final Boolean decision on the complete record. -/
structure AdaptiveStrategy (D O : ℕ) where

  steps : ℕ

  stream : (t : Fin steps) → (Fin t.val → Fin O) → StreamTag

  povm : (t : Fin steps) → (Fin t.val → Fin O) → PovmEffects D O

  decide : OutcomeRecord O steps → Bool

/-- Restricts a complete outcome record to the outcomes strictly before step `t`. -/
def recordPrefix {O steps : ℕ} (h : OutcomeRecord O steps) (t : Fin steps) :
    Fin t.val → Fin O :=
  fun u => h ⟨u.val, lt_trans u.2 t.2⟩

/-- The assertion that the measurement chosen at every step and every preceding history is a
valid POVM. -/
def IsAdmissibleAdaptive {D O : ℕ} (S : AdaptiveStrategy D O) : Prop :=
  ∀ (t : Fin S.steps) (hist : Fin t.val → Fin O), IsPovmEffects (S.povm t hist)

/-- The sum over accepted records of the products of outcome weights from the measurements and
streams selected by each record prefix. -/
noncomputable def adaptiveAcceptProb {D O : ℕ} (S : AdaptiveStrategy D O)
    (ρ σ : Operator D) : ℝ :=
  ∑ h : OutcomeRecord O S.steps,
    (if S.decide h then 1 else 0) *
      ∏ t : Fin S.steps,
        outcomeProb (S.povm t (recordPrefix h t))
          (stateFor (S.stream t (recordPrefix h t)) ρ σ) (h t)

/-- The adaptive acceptance expression when both streams supply the same operator `ρ`. -/
noncomputable def adaptiveSharedNullAcceptProb {D O : ℕ} (S : AdaptiveStrategy D O)
    (ρ : Operator D) : ℝ :=
  adaptiveAcceptProb S ρ ρ

/-- The assertion that an adaptive strategy is admissible, accepts every shared density operator
with probability at least `SuccessFloor`, and accepts each `IsH1 ε` density-operator pair
with probability at most `1 - SuccessFloor`. -/
def IsCorrectAdaptiveEquivalenceTester {D O : ℕ} (S : AdaptiveStrategy D O)
    (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      SuccessFloor ≤ adaptiveSharedNullAcceptProb S ρ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      IsH1 ε ρ σ → adaptiveAcceptProb S ρ σ ≤ 1 - SuccessFloor)

/-- The number of steps using the `rho` stream along the specified complete outcome record. -/
def AdaptiveStrategy.rhoUses {D O : ℕ} (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : ℕ :=
  (Finset.univ.filter
    (fun t : Fin S.steps => S.stream t (recordPrefix h t) = .rho)).card

/-- The number of steps using the `sigma` stream along the specified complete outcome record. -/
def AdaptiveStrategy.sigmaUses {D O : ℕ} (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : ℕ :=
  (Finset.univ.filter
    (fun t : Fin S.steps => S.stream t (recordPrefix h t) = .sigma)).card

/-- The ledger maximizing each stream-use count separately over all complete outcome records. -/
def AdaptiveStrategy.worstLedger {D O : ℕ} (S : AdaptiveStrategy D O) : CopyLedger where
  rho := Finset.univ.sup (fun h : OutcomeRecord O S.steps => S.rhoUses h)
  sigma := Finset.univ.sup (fun h : OutcomeRecord O S.steps => S.sigmaUses h)

/-- The pointwise upper-bound predicate asserting that `N ≤ C * B * log (d / ε) ^ k` for some
positive real `C` and natural `k`. -/
def IsTildeOBound (N : ℕ) (B : ℝ) (d ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, (N : ℝ) ≤ C * B * (Real.log (d / ε)) ^ k

/-- The pointwise lower-bound predicate asserting that `c * B / log (d / ε) ^ k ≤ N` for some
positive real `c` and natural `k`. -/
def IsTildeOmegaLowerBound (N : ℕ) (B : ℝ) (d ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, c * B / (Real.log (d / ε)) ^ k ≤ (N : ℝ)

/-- The parameter relation `2 ≤ d` and `ε = d ^ (-α)`. -/
def InPowerLawRegime (d : ℕ) (ε α : ℝ) : Prop :=
  2 ≤ d ∧ ε = (d : ℝ) ^ (-α)

/-- The dimension and separation expression `d ^ (3 / 2) / ε ^ 2`. -/
noncomputable def nonAdaptiveLowerBoundTarget (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) ^ ((3 : ℝ) / 2) / ε ^ 2

/-- The minimum of `d ^ (3 / 2) / ε ^ 2` and `d ^ (9 / 4) / ε`. -/
noncomputable def adaptiveEquivalenceBudget (d : ℕ) (ε : ℝ) : ℝ :=
  min (nonAdaptiveLowerBoundTarget d ε) ((d : ℝ) ^ ((9 : ℝ) / 4) / ε)

end Qatlib.Papers.AdaptiveTest26.MainResults
