/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MatrixWeights.WeightsCore
import Qatlib.Concepts.MatrixWeights.StoppingRule
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationInterfaces
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.SdpDuality.ConeSeparation.Macros
import Qatlib.Concepts.SdpDuality.ConeSeparation.SdpRunMacros
import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpResidualMacros

/-!
# Shared matrix optimization definitions

This module defines matrix trace expressions, approximate-round error budgets, finite sampling
trees, and resource receipts used by SDP algorithms. `ApproxRound.wellFormed` records state and
payoff accuracy, while `SamplerTree`, `RejectTrial`, and `MixedReceipt` describe sampling
behavior and implementation costs.

`Step2Search` packages empirical search data, and `correctedNoCheapSeparator` and
`dualMixtureVector` express the separator and dual-output quantities used in the quantum SDP
framework of [BrandaoSvore2017].

## Main definitions

* `psdGTInfimum`: regularized logarithmic trace infimum.
* `Step2Search.goodEvent`: simultaneous sampling, measurement, and sparsification bounds.
* `totalInputLength`: rational input encoding size.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped Matrix.Norms.L2Operator

/-- The matrix underlying the spectral logarithm of the Hermitian matrix `A`. -/
noncomputable def spectralLog {n : ℕ} (A : HermitianMat (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (HermitianMat.log A).mat

/-- The difference Re tr(exp H exp K) − Re tr(exp(H + K)) used in the Golden–Thompson
inequality. -/
noncomputable def gtHermitianGap {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp H * NormedSpace.exp K)).re -
    (Matrix.trace (NormedSpace.exp (H + K))).re

/-- The real trace of the exponential of the sum of the spectral logarithms of `A` and `B`. -/
noncomputable def logInputGT {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp (spectralLog A + spectralLog B))).re

/-- The logarithmic Golden–Thompson trace expression after adding `ε` times the identity to both
inputs. -/
noncomputable def psdRegularizedGT {n : ℕ} (A B : HermitianMat (Fin n) ℂ) (ε : ℝ) : ℝ :=
  logInputGT (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ))
    (B + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ))

/-- The iterated real infimum `⨅ ε ∈ Set.Ioi (0 : ℝ), psdRegularizedGT A B ε`. -/
noncomputable def psdGTInfimum {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  ⨅ ε ∈ Set.Ioi (0 : ℝ), psdRegularizedGT A B ε

/-- The real trace of `(A + ε • 1) * (B + ε • 1)`. -/
noncomputable def psdRegularizedProductTrace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : ℝ :=
  (Matrix.trace
    ((A + ε • (1 : Matrix (Fin n) (Fin n) ℂ)) *
      (B + ε • (1 : Matrix (Fin n) (Fin n) ℂ)))).re

/-- Data for an approximate optimization round, consisting of a matrix, a recorded payoff, and
state and measurement error allowances. -/
structure ApproxRound (D : ℕ) where

  approx : Operator D

  recorded : ℝ

  xi : ℝ

  zeta : ℝ

/-- Requires the approximate matrix to be a density operator, the error allowances to be
nonnegative, and the state and recorded payoff errors to satisfy their prescribed bounds. -/
def ApproxRound.wellFormed {D : ℕ} (M ρ : Operator D) (r : ApproxRound D) : Prop :=
  IsDensityOperator r.approx ∧ 0 ≤ r.xi ∧ 0 ≤ r.zeta ∧
    Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance r.approx ρ ≤ r.xi ∧
    |r.recorded - (Matrix.trace (M * r.approx)).re| ≤ r.zeta

/-- The regret allowance ηT + log(D)/η plus the sum of the state error penalties `2 * xi t` and
measurement penalties `zeta t`. -/
noncomputable def robustRegretBound {T : ℕ} (η : ℝ) (D : ℕ)
    (xi zeta : Fin T → ℝ) : ℝ :=
  η * T + Real.log D / η + ∑ t : Fin T, (2 * xi t + zeta t)

/-- The regret allowance ηT + log(D)/η plus twice the sum of the state error allowances. -/
noncomputable def robustRegretBoundActual {T : ℕ} (η : ℝ) (D : ℕ)
    (xi : Fin T → ℝ) : ℝ :=
  η * T + Real.log D / η + ∑ t : Fin T, (2 * xi t)

/-- The width budget `α * (1 + 2 * R * ε)`. -/
noncomputable def sourceWidthBudget (α R ε : ℝ) : ℝ := α * (1 + 2 * R * ε)

/-- The real payoff trace Re tr(Cv ρ) reduced by `2 * α * ε`. -/
noncomputable def sourcePayoffTarget (D : ℕ) (Cv : Operator D) (ρ : Operator D)
    (α ε : ℝ) : ℝ :=
  (Matrix.trace (Cv * ρ)).re - 2 * α * ε

/-- The shifted payoff matrix `(∑ i, y i • A i - Cv + (2 * α) • 1)` scaled by the inverse of `4
* α`. -/
noncomputable def sourceScaledPayoff {D m : ℕ}
    (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ) (y : Fin m → ℝ) :
    Operator D :=
  ((4 * α : ℝ))⁻¹ • ((∑ i, y i • A i) - Cv + (2 * α) • (1 : Operator D))

/-- The additive width slack `2 * α * R * ε`. -/
noncomputable def exactWidthSlack (α R ε : ℝ) : ℝ := 2 * α * R * ε

/-- A record of the number of bisection calls and their failure and error masses. -/
structure BisectionBudget where

  calls : ℕ

  failMass : ℝ

  errorMass : ℝ

/-- Requires nonnegative failure and error masses bounded by the supplied total allowances. -/
def BisectionBudget.legal (B : BisectionBudget) (totalFail totalError : ℝ) : Prop :=
  0 ≤ B.failMass ∧ 0 ≤ B.errorMass ∧ B.failMass ≤ totalFail ∧ B.errorMass ≤ totalError

/-- Rescaling data consisting of a new constraint vector, a scale, and a value error allowance
for the given SDP input. -/
structure Lemma2Rescale {D m : ℕ} (A : Fin m → Operator D) (b : Fin m → ℝ) where

  bp : Fin m → ℝ

  r : ℝ

  valueError : ℝ

/-- Requires a positive rescaling factor, rescaled constraint entries at least one, and a
nonnegative value error allowance. -/
def Lemma2Rescale.legal {D m : ℕ} (A : Fin m → Operator D) (b : Fin m → ℝ)
    (S : Lemma2Rescale A b) : Prop :=
  0 < S.r ∧ (∀ i, 1 ≤ S.bp i) ∧ 0 ≤ S.valueError

/-- A finite fair-bit sampling tree whose leaves either emit an outcome or signal failure. -/
inductive SamplerTree (O : Type) where

  | emit (o : O)

  | fail

  | bit (left right : SamplerTree O)

namespace SamplerTree

variable {O : Type}

/-- The failure mass of a sampling tree, averaging equally over the two children of each bit
node. -/
noncomputable def failProb : SamplerTree O → ℝ
  | .emit _ => 0
  | .fail => 1
  | .bit l r => (failProb l + failProb r) / 2

/-- The output mass function of a sampling tree, assigning zero mass to failure leaves and
averaging at bit nodes. -/
noncomputable def law [DecidableEq O] : SamplerTree O → O → ℝ
  | .emit o' => fun o => if o = o' then 1 else 0
  | .fail => fun _ => 0
  | .bit l r => fun o => (law l o + law r o) / 2

/-- The maximum number of bit nodes encountered along a path in the sampling tree. -/
def maxDepth : SamplerTree O → ℕ
  | .emit _ => 0
  | .fail => 0
  | .bit l r => max (maxDepth l) (maxDepth r) + 1

/-- The expected number of fair bits consumed by the sampling tree. -/
noncomputable def expDepth : SamplerTree O → ℝ
  | .emit _ => 0
  | .fail => 0
  | .bit l r => 1 + (expDepth l + expDepth r) / 2

/-- The probability that the sampling tree uses more than the specified number of fair bits. -/
noncomputable def tail : SamplerTree O → ℕ → ℝ
  | .emit _, _ => 0
  | .fail, _ => 0
  | .bit _ _, 0 => 1
  | .bit l r, k + 1 => (tail l k + tail r k) / 2

end SamplerTree

/-- A single rejection sampling trial, specified by a sampling tree and a Boolean acceptance
test. -/
structure RejectTrial (O : Type) where

  tree : SamplerTree O

  accept : O → Bool

namespace RejectTrial

variable {O : Type} [Fintype O] [DecidableEq O]

/-- The total mass of outcomes satisfying the acceptance test. -/
noncomputable def acceptMass (S : RejectTrial O) : ℝ :=
  ∑ o : O, if S.accept o then S.tree.law o else 0

/-- The sum of the tree failure mass and the mass of outcomes failing the acceptance test. -/
noncomputable def rejectProb (S : RejectTrial O) : ℝ :=
  S.tree.failProb + ∑ o : O, if S.accept o then 0 else S.tree.law o

/-- The accepted output mass normalized by the acceptance mass, with value zero when acceptance
mass is not positive. -/
noncomputable def law (S : RejectTrial O) : O → ℝ :=
  fun o => if S.accept o ∧ 0 < S.acceptMass
    then S.tree.law o / S.acceptMass
    else 0

/-- The reciprocal of the acceptance mass when it is positive, and zero otherwise. -/
noncomputable def expectedTrials (S : RejectTrial O) : ℝ :=
  if 0 < S.acceptMass then S.acceptMass⁻¹ else 0

end RejectTrial

/-- The finite weighted sum of the component output mass functions `q` with weights `w`. -/
noncomputable def mixtureLaw {n m : ℕ} (w : Fin n → ℝ) (q : Fin n → Fin m → ℝ) :
    Fin m → ℝ :=
  fun j => ∑ i : Fin n, w i * q i j

/-- States that all entries of `w` are nonnegative and their sum is one. -/
def IsWeighting {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i : Fin n, w i) = 1

/-- Descriptors for constraint entries, sparse rows, payoff entries, Gibbs state preparation,
and observable measurements. -/
inductive QueryDesc where

  | entry (D m : ℕ) (A : Fin m → Operator D) (i : Fin m) (r c : Fin D)

  | sparseRow (D m : ℕ) (A : Fin m → Operator D) (i : Fin m) (r : Fin D)

  | payoffEntry (D : ℕ) (Cv : Operator D) (r c : Fin D)

  | gibbsPrepare (D : ℕ) (H : Operator D) (β : ℚ)

  | measure (D : ℕ) (M : Operator D)

/-- Integer resource counts for queries, gates, bit time, and peak space. -/
structure IntCost where

  queries : ℕ

  gates : ℕ

  bitTime : ℕ

  peakSpace : ℕ

/-- Componentwise comparison of query, gate, bit time, and peak space costs. -/
def IntCost.le (c B : IntCost) : Prop :=
  c.queries ≤ B.queries ∧ c.gates ≤ B.gates ∧
    c.bitTime ≤ B.bitTime ∧ c.peakSpace ≤ B.peakSpace

/-- A backend program description containing a register width, gate and query lists, and an
output sampling tree. -/
structure BackendProgram (O : Type) where

  width : ℕ

  gates : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode

  queries : List QueryDesc

  out : SamplerTree O

/-- Counts queries and gates by list length, bit time by maximum sampling depth, and peak space
by register width. -/
def BackendProgram.cost {O : Type} (P : BackendProgram O) : IntCost where
  queries := P.queries.length
  gates := P.gates.length
  bitTime := P.out.maxDepth
  peakSpace := P.width

/-- States that the program's finite gate word is legal for its declared width. -/
def BackendProgram.legal {O : Type} (P : BackendProgram O) : Prop :=
  Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal P.width P.gates = true

/-- A probability mass function on a finite type with nonnegative entries summing to one. -/
structure FiniteSupportSpace (Ω : Type) [Fintype Ω] where

  prob : Ω → ℝ

  prob_nonneg : ∀ ω, 0 ≤ prob ω

  prob_sum : (∑ ω : Ω, prob ω) = 1

namespace FiniteSupportSpace

variable {Ω : Type} [Fintype Ω]

/-- The sum of the probability masses of outcomes belonging to the event `E`. -/
noncomputable def eventProb (S : FiniteSupportSpace Ω) (E : Set Ω) : ℝ :=
  letI := Classical.decPred (· ∈ E)
  ∑ ω : Ω, if ω ∈ E then S.prob ω else 0

/-- The probability of the complement of the event `E`. -/
noncomputable def failProb (S : FiniteSupportSpace Ω) (E : Set Ω) : ℝ :=
  S.eventProb (Set.univ \ E)

end FiniteSupportSpace

/-- An event together with a proposed upper bound on its failure probability. -/
structure GoodEventLedger (Ω : Type) [Fintype Ω] where

  good : Set Ω

  failBound : ℝ

/-- Requires a nonnegative failure bound that dominates the probability of the complement of the
good event. -/
def GoodEventLedger.legal {Ω : Type} [Fintype Ω]
    (S : FiniteSupportSpace Ω) (L : GoodEventLedger Ω) : Prop :=
  0 ≤ L.failBound ∧ S.failProb L.good ≤ L.failBound

/-- The sum of a finite family of failure allowances. -/
def sumFailBound {n : ℕ} (f : Fin n → ℝ) : ℝ := ∑ i : Fin n, f i

/-- The rank-one density matrix with entries `ψ i * starRingEnd ℂ (ψ j)` associated with the
quantum state `ψ`. -/
noncomputable def densityOf {I : Type} [Fintype I] (ψ : QState I) : Matrix I I ℂ :=
  fun i j => ψ i * starRingEnd ℂ (ψ j)

/-- The ordered product of the finite gate matrices, multiplying each successive gate on the
left. -/
noncomputable def gateWordUnitary (n : ℕ) (gs : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ :=
  gs.foldl (fun acc g => finiteCodeMatrix n g * acc) 1

/-- Conjugation of `ρ` by the matrix product of the gate word. -/
noncomputable def gateWordChannel (n : ℕ) (gs : List FiniteGateCode)
    (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  gateWordUnitary n gs * ρ * (gateWordUnitary n gs).conjTranspose

/-- Requires a legal finite gate word whose successful state executions agree with conjugation
of the corresponding density matrices. -/
def gateWordExecutes (n : ℕ) (gs : List FiniteGateCode) : Prop :=
  finiteWordLegal n gs = true ∧
    ∀ (ψ ψ' : QState (Reg n)), finiteWordRun n gs ψ = some ψ' →
      densityOf ψ' = gateWordChannel n gs (densityOf ψ)

/-- Requires a legal gate word whose adjoint word has matrix equal to the conjugate transpose of
the original word's matrix. -/
def gateWordAdjointExecutes (n : ℕ) (gs : List FiniteGateCode) : Prop :=
  finiteWordLegal n gs = true ∧
    gateWordUnitary n (finiteWordAdjoint gs) =
      (gateWordUnitary n gs).conjTranspose

/-- Classical primitive descriptors for fixed-precision comparison, maximum selection, and
exponential approximation. -/
inductive PaidPrim where

  | compare (bits : ℕ)

  | argmax (size bits : ℕ)

  | expApprox (bits : ℕ)

namespace PaidPrim

/-- The prescribed integer time and space costs of a classical primitive, with zero quantum
queries and gates. -/
def cost : PaidPrim → IntCost
  | compare bits => ⟨0, 0, 8 * bits + 8, 2 * bits + 8⟩
  | argmax size bits => ⟨0, 0, 16 * size * bits + 16, size * bits + 2 * bits + 16⟩
  | expApprox bits => ⟨0, 0, 64 * bits * bits + 32, 4 * bits + 16⟩

/-- Requires positive precision and, for maximum selection, a positive input size. -/
def legal : PaidPrim → Prop
  | compare bits => 0 < bits
  | argmax size bits => 0 < size ∧ 0 < bits
  | expApprox bits => 0 < bits

end PaidPrim

/-- A quantum step consisting of a finite gate word or a single query descriptor. -/
inductive QuantumStep where

  | gateWord (n : ℕ) (gs : List FiniteGateCode)

  | query (q : QueryDesc)

namespace QuantumStep

/-- Counts one query for a query step and zero for a gate word. -/
def queries : QuantumStep → ℕ
  | .gateWord _ _ => 0
  | .query _ => 1

/-- Counts the gates in a gate word and assigns zero gates to a query step. -/
def gates : QuantumStep → ℕ
  | .gateWord _ gs => gs.length
  | .query _ => 0

/-- Checks legality of a finite gate word and returns true for a query descriptor. -/
def legal : QuantumStep → Bool
  | .gateWord n gs => finiteWordLegal n gs
  | .query _ => true

end QuantumStep

/-- A resource receipt containing quantum steps, classical primitives, a register width, and an
output sampling tree. -/
structure MixedReceipt (O : Type) where

  width : ℕ

  steps : List QuantumStep

  prims : List PaidPrim

  out : SamplerTree O

namespace MixedReceipt

variable {O : Type}

/-- Aggregates query and gate counts, adds sampling depth to classical bit time, and takes the
maximum of register width and classical space costs. -/
def cost (R : MixedReceipt O) : IntCost where
  queries := (R.steps.map QuantumStep.queries).sum
  gates := (R.steps.map QuantumStep.gates).sum
  bitTime := R.out.maxDepth + (R.prims.map (fun p => p.cost.bitTime)).sum
  peakSpace := max R.width ((R.prims.map (fun p => p.cost.peakSpace)).foldl max 0)

/-- Requires every quantum step and every classical primitive in the receipt to be legal. -/
def legal (R : MixedReceipt O) : Prop :=
  (∀ s ∈ R.steps, s.legal = true) ∧ (∀ p ∈ R.prims, p.legal)

/-- The output mass function of the receipt's sampling tree. -/
noncomputable def law [DecidableEq O] (R : MixedReceipt O) : O → ℝ := R.out.law

/-- States that the receipt's sampling tree agrees pointwise with the target mass function. -/
def realizes [DecidableEq O] (R : MixedReceipt O) (target : O → ℝ) : Prop :=
  ∀ o, R.out.law o = target o

/-- The bit time component of the receipt's aggregate integer cost. -/
def worstCaseBitTime (R : MixedReceipt O) : ℕ := R.cost.bitTime

/-- Requires a legal receipt whose output masses equal the instrument's outcome probabilities on
`ρ`. -/
def realizesInstrument [Fintype O] [DecidableEq O]
    (R : MixedReceipt O) {D : ℕ} (I : Instrument O D D) (ρ : Operator D) : Prop :=
  R.legal ∧ (∀ o, R.out.law o = instrumentProb I ρ o)

end MixedReceipt

/-- The real trace mass Re tr(Λ(o) ρ) associated with a POVM outcome. -/
noncomputable def bornLaw {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) : O → ℝ :=
  fun o => (Matrix.trace ((Λ.mats o).mat * ρ)).re

/-- The matrix exponential `exp (-β • H)` divided by its complex trace. -/
noncomputable def gibbsState {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (Matrix.trace (NormedSpace.exp (-(β : ℝ) • H)))⁻¹ •
    NormedSpace.exp (-(β : ℝ) • H)

namespace SamplerTree

/-- Replaces each emitted outcome by a continuation tree, preserving failure leaves and fair-bit
branches. -/
def bind {O P : Type} : SamplerTree O → (O → SamplerTree P) → SamplerTree P
  | .emit o, k => k o
  | .fail, _ => .fail
  | .bit l r, k => .bit (bind l k) (bind r k)

end SamplerTree

/-- A rejection trial paired with its target output mass function. -/
structure RejectReceipt (O : Type) [Fintype O] [DecidableEq O] where

  trial : RejectTrial O

  target : O → ℝ

namespace RejectReceipt

variable {O : Type} [Fintype O] [DecidableEq O]

/-- States that the normalized law of the rejection trial equals its target pointwise. -/
def exactLaw (S : RejectReceipt O) : Prop := ∀ o, S.trial.law o = S.target o

/-- States that the rejection trial has strictly positive acceptance mass. -/
def aSFinite (S : RejectReceipt O) : Prop := 0 < S.trial.acceptMass

/-- The expected trial count multiplied by one plus the trial tree's maximum depth. -/
noncomputable def expectedBitTime (S : RejectReceipt O) : ℝ :=
  S.trial.expectedTrials * (S.trial.tree.maxDepth + 1)

/-- The `k`th power of the rejection probability, representing the mass of `k` consecutive
unsuccessful trials. -/
noncomputable def tailMass (S : RejectReceipt O) (k : ℕ) : ℝ :=
  S.trial.rejectProb ^ k

/-- States that the trial's rejection probability is zero. -/
def hasWorstCaseTimeBound (S : RejectReceipt O) : Prop := S.trial.rejectProb = 0

end RejectReceipt

/-- A rejection trial equipped with a finite cutoff on the number of attempts. -/
structure TruncatedReject (O : Type) [Fintype O] [DecidableEq O] where

  trial : RejectTrial O

  cutoff : ℕ

namespace TruncatedReject

variable {O : Type} [Fintype O] [DecidableEq O]

/-- The rejection probability raised to the cutoff, representing failure to accept before
truncation. -/
noncomputable def timeoutMass (S : TruncatedReject O) : ℝ :=
  S.trial.rejectProb ^ S.cutoff

/-- The accepted output mass multiplied by the geometric sum of rejection probabilities up to
the cutoff. -/
noncomputable def law (S : TruncatedReject O) : O → ℝ :=
  fun o => if S.trial.accept o then
    S.trial.tree.law o * (∑ k ∈ Finset.range S.cutoff, S.trial.rejectProb ^ k)
  else 0

/-- The cutoff multiplied by the maximum bit depth of a single trial. -/
def worstCaseBitTime (S : TruncatedReject O) : ℕ :=
  S.cutoff * S.trial.tree.maxDepth

/-- States that the truncated output mass function equals the normalized law of the underlying
rejection trial. -/
def exactLaw (S : TruncatedReject O) : Prop := ∀ o, S.law o = S.trial.law o

end TruncatedReject

/-- States that a real number is an integer divided by a nonnegative power of two. -/
def IsDyadic (x : ℝ) : Prop := ∃ (z : ℤ) (k : ℕ), x = (z : ℝ) / (2 ^ k : ℝ)

/-- States that the output mass function of a finite sampling tree equals the target pointwise. -/
def treeRealizes {O : Type} [Fintype O] [DecidableEq O] (target : O → ℝ)
    (tree : SamplerTree O) : Prop := ∀ o, tree.law o = target o

/-- An increasing sequence of event families containing the whole space and closed under
complements and binary unions. -/
structure Filtration (Ω : Type) [Fintype Ω] where

  events : ℕ → Set (Set Ω)

  mono : ∀ t s, t ≤ s → events t ⊆ events s

  univ_mem : ∀ t, Set.univ ∈ events t

  compl_mem : ∀ t (E : Set Ω), E ∈ events t → (Set.univ \ E) ∈ events t

  union_mem : ∀ t (E F : Set Ω), E ∈ events t → F ∈ events t → (E ∪ F) ∈ events t

namespace FiniteSupportSpace

variable {Ω : Type} [Fintype Ω]

/-- The probability-weighted mean of `Z` restricted to `E`, normalized by the event probability
when positive and set to zero otherwise. -/
noncomputable def condExpect (S : FiniteSupportSpace Ω) (E : Set Ω) (Z : Ω → ℝ) : ℝ :=
  letI := Classical.decPred (· ∈ E)
  if 0 < S.eventProb E then
    (S.eventProb E)⁻¹ * ∑ ω : Ω, if ω ∈ E then S.prob ω * Z ω else 0
  else 0

end FiniteSupportSpace

/-- A record of a concentration window and its failure and error allowances. -/
structure ConcentrationLedger where

  window : ℝ

  failMass : ℝ

  errorMass : ℝ

/-- A record of stopped and timed-out events together with a failure allowance. -/
structure StopTimeoutLedger (Ω : Type) [Fintype Ω] where

  stopped : Set Ω

  timedOut : Set Ω

  failMass : ℝ
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

/-- Data for a finite Step 2 search, including candidate laws, sampled indices, measurement
records, and sparsification indices. -/
structure Step2Search (m γ Nmax M L Q : ℕ) where

  law : Fin γ → Fin m → ℝ

  draws : Fin γ → Fin Nmax → Fin M → Fin m

  measA : Fin γ → Fin Nmax → Fin m → Fin L → ℝ

  measC : Fin γ → Fin Nmax → Fin L → ℝ

  idx : Fin γ → Fin Nmax → Fin Q → Fin m

namespace Step2Search

variable {m γ Nmax M L Q : ℕ}

/-- Requires each candidate law in the search to have nonnegative entries summing to one. -/
def lawsOk (S : Step2Search m γ Nmax M L Q) : Prop :=
  ∀ k : Fin γ, (∀ i, 0 ≤ S.law k i) ∧ (∑ i : Fin m, S.law k i) = 1

/-- The grid mass `κ * (N + 1)` at index `N`. -/
noncomputable def gridMass (κ : ℝ) (N : ℕ) : ℝ := κ * (N + 1)

/-- The average of the constraint measurement records for the constraint chosen by draw `j`. -/
noncomputable def estA (S : Step2Search m γ Nmax M L Q) (k : Fin γ) (N : Fin Nmax)
    (j : Fin M) : ℝ := (∑ l : Fin L, S.measA k N (S.draws k N j) l) / L

/-- The average of the payoff measurement records at the specified search indices. -/
noncomputable def estC (S : Step2Search m γ Nmax M L Q) (k : Fin γ) (N : Fin Nmax) :
    ℝ := (∑ l : Fin L, S.measC k N l) / L

/-- The pair of empirical payoff and constraint-cost inequalities defining acceptance of a Step
2 candidate. -/
noncomputable def accepts (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
    (α R κ ν : ℝ) (k : Fin γ) (N : Fin Nmax) : Prop :=
  S.estC k N / gridMass κ N - (κ + ν) ≤
      (∑ j : Fin M, S.estA k N j) / M ∧
    (∑ j : Fin M, b (S.draws k N j)) / M ≤
      α / gridMass κ N + R * (κ + ν)

/-- The candidate law multiplied by the corresponding grid mass. -/
noncomputable def roundVector (S : Step2Search m γ Nmax M L Q) (κ : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Fin m → ℝ :=
  fun i => gridMass κ N * S.law k i

/-- States that no pair of grid indices satisfies the Step 2 acceptance test. -/
def noOutput (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
    (α R κ ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax), ¬ S.accepts b α R κ ν k N

/-- Requires simultaneous accuracy of sampled costs, empirical constraint and payoff estimates,
and the sparsified payoff matrix at every grid point. -/
noncomputable def goodEvent (S : Step2Search m γ Nmax M L Q) {D : ℕ}
    (b : Fin m → ℝ) (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ) :
    Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    |(∑ i : Fin m, S.law k i * b i) -
      (∑ j : Fin M, b (S.draws k N j)) / M| ≤ R * (κ + ν) ∧
    |(∑ j : Fin M, S.estA k N j) / M -
      (∑ i : Fin m, S.law k i * (∑ l : Fin L, S.measA k N i l) / L)| ≤ κ + ν ∧
    (∀ i : Fin m, |(∑ l : Fin L, S.measA k N i l) / L -
      (Matrix.trace (A i * ρ)).re| ≤ κ + ν) ∧
    |S.estC k N - (Matrix.trace (Cv * ρ)).re| ≤ κ + ν ∧
    ‖sdpScaledSparsifiedPayoff D m Q A Cv α (gridMass κ N) (S.idx k N) -
      sourceScaledPayoff A Cv α (S.roundVector κ k N)‖ ≤ ν

end Step2Search

/-- The payoff threshold Re tr(Cv ρ) − 3αε used in the no-output separator. -/
noncomputable def eq75Threshold {D : ℕ} (Cv ρ : Operator D) (α ε : ℝ) : ℝ :=
  (Matrix.trace (Cv * ρ)).re - 3 * α * ε

/-- The cost threshold `α * (1 - 3 * R * ε)` for the corrected separator. -/
noncomputable def noCheapWidth (α R ε : ℝ) : ℝ := α * (1 - 3 * R * ε)

/-- States that every nonnegative vector reaching `eq75Threshold` has constraint cost at least
`noCheapWidth`. -/
def correctedNoCheapSeparator {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re →
    ¬ (∑ i, z i * b i < noCheapWidth α R ε)

/-- The correction mass `a` plus the average of the round masses `μ`. -/
noncomputable def dualMixtureScale {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) : ℝ :=
  a + (∑ t : Fin T, μ t) / T

/-- The corrected average of the round laws, normalized by `dualMixtureScale`, with correction
mass placed at `j₀`. -/
noncomputable def dualMixtureLaw {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ)
    (q : Fin T → Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    ((if i = j₀ then a else 0) + (∑ t : Fin T, μ t * q t i) / T) /
      dualMixtureScale a μ

/-- The average of the mass-weighted round laws plus correction mass `a` at `j₀`. -/
noncomputable def dualMixtureVector {m T : ℕ} (j₀ : Fin m) (a : ℝ)
    (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ) : Fin m → ℝ :=
  fun i => (if i = j₀ then a else 0) + (∑ t : Fin T, μ t * q t i) / T

/-- The mixture weights for the distinguished correction component and the `T` round components,
normalized by `dualMixtureScale`. -/
noncomputable def dualMixtureWeights {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) :
    Fin (T + 1) → ℝ :=
  Fin.cases (a / dualMixtureScale a μ)
    (fun t => μ t / (T * dualMixtureScale a μ))

/-- States that every entry of the finite weight vector is dyadic. -/
def weightsDyadic {n : ℕ} (w : Fin n → ℝ) : Prop := ∀ i, IsDyadic (w i)

/-- A rational matrix input accompanied by sparsity and bit precision parameters. -/
structure SparseMatrixInput (D : ℕ) where

  s : ℕ

  bits : ℕ

  entry : Fin D → Fin D → ℚ

/-- The matrix input length expression `(m + 1) * D * s * bits`. -/
def sparseInputLength (D m s bits : ℕ) : ℕ :=
  (m + 1) * D * s * bits

/-- The sparse matrix input length plus the binary sizes of the rational weights and the
rational parameter `β`. -/
def totalInputLength (D m s bits : ℕ) (wt : Fin m → ℚ) (β : ℚ) : ℕ :=
  sparseInputLength D m s bits +
    (Finset.univ.sum fun i : Fin m =>
      (wt i).num.natAbs.size + (wt i).den.size) +
    β.num.natAbs.size + β.den.size

end Qatlib.Concepts.SdpDuality.ConeSeparation
