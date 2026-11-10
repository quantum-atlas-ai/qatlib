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
set_option warningAsError false
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

noncomputable def spectralLog {n : ℕ} (A : HermitianMat (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (HermitianMat.log A).mat

noncomputable def gtHermitianGap {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp H * NormedSpace.exp K)).re -
    (Matrix.trace (NormedSpace.exp (H + K))).re

noncomputable def logInputGT {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp (spectralLog A + spectralLog B))).re

noncomputable def psdRegularizedGT {n : ℕ} (A B : HermitianMat (Fin n) ℂ) (ε : ℝ) : ℝ :=
  logInputGT (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ))
    (B + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ))

noncomputable def psdGTInfimum {n : ℕ} (A B : HermitianMat (Fin n) ℂ) : ℝ :=
  ⨅ ε ∈ Set.Ioi (0 : ℝ), psdRegularizedGT A B ε

noncomputable def psdRegularizedProductTrace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : ℝ :=
  (Matrix.trace
    ((A + ε • (1 : Matrix (Fin n) (Fin n) ℂ)) *
      (B + ε • (1 : Matrix (Fin n) (Fin n) ℂ)))).re

structure ApproxRound (D : ℕ) where

  approx : Operator D

  recorded : ℝ

  xi : ℝ

  zeta : ℝ

def ApproxRound.wellFormed {D : ℕ} (M ρ : Operator D) (r : ApproxRound D) : Prop :=
  IsDensityOperator r.approx ∧ 0 ≤ r.xi ∧ 0 ≤ r.zeta ∧
    Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance r.approx ρ ≤ r.xi ∧
    |r.recorded - (Matrix.trace (M * r.approx)).re| ≤ r.zeta

noncomputable def robustRegretBound {T : ℕ} (η : ℝ) (D : ℕ)
    (xi zeta : Fin T → ℝ) : ℝ :=
  η * T + Real.log D / η + ∑ t : Fin T, (2 * xi t + zeta t)

noncomputable def robustRegretBoundActual {T : ℕ} (η : ℝ) (D : ℕ)
    (xi : Fin T → ℝ) : ℝ :=
  η * T + Real.log D / η + ∑ t : Fin T, (2 * xi t)

noncomputable def sourceWidthBudget (α R ε : ℝ) : ℝ := α * (1 + 2 * R * ε)

noncomputable def sourcePayoffTarget (D : ℕ) (Cv : Operator D) (ρ : Operator D)
    (α ε : ℝ) : ℝ :=
  (Matrix.trace (Cv * ρ)).re - 2 * α * ε

noncomputable def sourceScaledPayoff {D m : ℕ}
    (A : Fin m → Operator D) (Cv : Operator D) (α : ℝ) (y : Fin m → ℝ) :
    Operator D :=
  ((4 * α : ℝ))⁻¹ • ((∑ i, y i • A i) - Cv + (2 * α) • (1 : Operator D))

noncomputable def exactWidthSlack (α R ε : ℝ) : ℝ := 2 * α * R * ε

structure BisectionBudget where

  calls : ℕ

  failMass : ℝ

  errorMass : ℝ

def BisectionBudget.legal (B : BisectionBudget) (totalFail totalError : ℝ) : Prop :=
  0 ≤ B.failMass ∧ 0 ≤ B.errorMass ∧ B.failMass ≤ totalFail ∧ B.errorMass ≤ totalError

structure Lemma2Rescale {D m : ℕ} (A : Fin m → Operator D) (b : Fin m → ℝ) where

  bp : Fin m → ℝ

  r : ℝ

  valueError : ℝ

def Lemma2Rescale.legal {D m : ℕ} (A : Fin m → Operator D) (b : Fin m → ℝ)
    (S : Lemma2Rescale A b) : Prop :=
  0 < S.r ∧ (∀ i, 1 ≤ S.bp i) ∧ 0 ≤ S.valueError

inductive SamplerTree (O : Type) where

  | emit (o : O)

  | fail

  | bit (left right : SamplerTree O)

namespace SamplerTree

variable {O : Type}

noncomputable def failProb : SamplerTree O → ℝ
  | .emit _ => 0
  | .fail => 1
  | .bit l r => (failProb l + failProb r) / 2

noncomputable def law [DecidableEq O] : SamplerTree O → O → ℝ
  | .emit o' => fun o => if o = o' then 1 else 0
  | .fail => fun _ => 0
  | .bit l r => fun o => (law l o + law r o) / 2

def maxDepth : SamplerTree O → ℕ
  | .emit _ => 0
  | .fail => 0
  | .bit l r => max (maxDepth l) (maxDepth r) + 1

noncomputable def expDepth : SamplerTree O → ℝ
  | .emit _ => 0
  | .fail => 0
  | .bit l r => 1 + (expDepth l + expDepth r) / 2

noncomputable def tail : SamplerTree O → ℕ → ℝ
  | .emit _, _ => 0
  | .fail, _ => 0
  | .bit _ _, 0 => 1
  | .bit l r, k + 1 => (tail l k + tail r k) / 2

end SamplerTree

structure RejectTrial (O : Type) where

  tree : SamplerTree O

  accept : O → Bool

namespace RejectTrial

variable {O : Type} [Fintype O] [DecidableEq O]

noncomputable def acceptMass (S : RejectTrial O) : ℝ :=
  ∑ o : O, if S.accept o then S.tree.law o else 0

noncomputable def rejectProb (S : RejectTrial O) : ℝ :=
  S.tree.failProb + ∑ o : O, if S.accept o then 0 else S.tree.law o

noncomputable def law (S : RejectTrial O) : O → ℝ :=
  fun o => if S.accept o ∧ 0 < S.acceptMass
    then S.tree.law o / S.acceptMass
    else 0

noncomputable def expectedTrials (S : RejectTrial O) : ℝ :=
  if 0 < S.acceptMass then S.acceptMass⁻¹ else 0

end RejectTrial

noncomputable def mixtureLaw {n m : ℕ} (w : Fin n → ℝ) (q : Fin n → Fin m → ℝ) :
    Fin m → ℝ :=
  fun j => ∑ i : Fin n, w i * q i j

def IsWeighting {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i : Fin n, w i) = 1

inductive QueryDesc where

  | entry (D m : ℕ) (A : Fin m → Operator D) (i : Fin m) (r c : Fin D)

  | sparseRow (D m : ℕ) (A : Fin m → Operator D) (i : Fin m) (r : Fin D)

  | payoffEntry (D : ℕ) (Cv : Operator D) (r c : Fin D)

  | gibbsPrepare (D : ℕ) (H : Operator D) (β : ℚ)

  | measure (D : ℕ) (M : Operator D)

structure IntCost where

  queries : ℕ

  gates : ℕ

  bitTime : ℕ

  peakSpace : ℕ

def IntCost.le (c B : IntCost) : Prop :=
  c.queries ≤ B.queries ∧ c.gates ≤ B.gates ∧
    c.bitTime ≤ B.bitTime ∧ c.peakSpace ≤ B.peakSpace

structure BackendProgram (O : Type) where

  width : ℕ

  gates : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode

  queries : List QueryDesc

  out : SamplerTree O

def BackendProgram.cost {O : Type} (P : BackendProgram O) : IntCost where
  queries := P.queries.length
  gates := P.gates.length
  bitTime := P.out.maxDepth
  peakSpace := P.width

def BackendProgram.legal {O : Type} (P : BackendProgram O) : Prop :=
  Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal P.width P.gates = true

structure FiniteSupportSpace (Ω : Type) [Fintype Ω] where

  prob : Ω → ℝ

  prob_nonneg : ∀ ω, 0 ≤ prob ω

  prob_sum : (∑ ω : Ω, prob ω) = 1

namespace FiniteSupportSpace

variable {Ω : Type} [Fintype Ω]

noncomputable def eventProb (S : FiniteSupportSpace Ω) (E : Set Ω) : ℝ :=
  letI := Classical.decPred (· ∈ E)
  ∑ ω : Ω, if ω ∈ E then S.prob ω else 0

noncomputable def failProb (S : FiniteSupportSpace Ω) (E : Set Ω) : ℝ :=
  S.eventProb (Set.univ \ E)

end FiniteSupportSpace

structure GoodEventLedger (Ω : Type) [Fintype Ω] where

  good : Set Ω

  failBound : ℝ

def GoodEventLedger.legal {Ω : Type} [Fintype Ω]
    (S : FiniteSupportSpace Ω) (L : GoodEventLedger Ω) : Prop :=
  0 ≤ L.failBound ∧ S.failProb L.good ≤ L.failBound

def sumFailBound {n : ℕ} (f : Fin n → ℝ) : ℝ := ∑ i : Fin n, f i

noncomputable def densityOf {I : Type} [Fintype I] (ψ : QState I) : Matrix I I ℂ :=
  fun i j => ψ i * starRingEnd ℂ (ψ j)

noncomputable def gateWordUnitary (n : ℕ) (gs : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ :=
  gs.foldl (fun acc g => finiteCodeMatrix n g * acc) 1

noncomputable def gateWordChannel (n : ℕ) (gs : List FiniteGateCode)
    (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  gateWordUnitary n gs * ρ * (gateWordUnitary n gs).conjTranspose

def gateWordExecutes (n : ℕ) (gs : List FiniteGateCode) : Prop :=
  finiteWordLegal n gs = true ∧
    ∀ (ψ ψ' : QState (Reg n)), finiteWordRun n gs ψ = some ψ' →
      densityOf ψ' = gateWordChannel n gs (densityOf ψ)

def gateWordAdjointExecutes (n : ℕ) (gs : List FiniteGateCode) : Prop :=
  finiteWordLegal n gs = true ∧
    gateWordUnitary n (finiteWordAdjoint gs) =
      (gateWordUnitary n gs).conjTranspose

inductive PaidPrim where

  | compare (bits : ℕ)

  | argmax (size bits : ℕ)

  | expApprox (bits : ℕ)

namespace PaidPrim

def cost : PaidPrim → IntCost
  | compare bits => ⟨0, 0, 8 * bits + 8, 2 * bits + 8⟩
  | argmax size bits => ⟨0, 0, 16 * size * bits + 16, size * bits + 2 * bits + 16⟩
  | expApprox bits => ⟨0, 0, 64 * bits * bits + 32, 4 * bits + 16⟩

def legal : PaidPrim → Prop
  | compare bits => 0 < bits
  | argmax size bits => 0 < size ∧ 0 < bits
  | expApprox bits => 0 < bits

end PaidPrim

inductive QuantumStep where

  | gateWord (n : ℕ) (gs : List FiniteGateCode)

  | query (q : QueryDesc)

namespace QuantumStep

def queries : QuantumStep → ℕ
  | .gateWord _ _ => 0
  | .query _ => 1

def gates : QuantumStep → ℕ
  | .gateWord _ gs => gs.length
  | .query _ => 0

def legal : QuantumStep → Bool
  | .gateWord n gs => finiteWordLegal n gs
  | .query _ => true

end QuantumStep

structure MixedReceipt (O : Type) where

  width : ℕ

  steps : List QuantumStep

  prims : List PaidPrim

  out : SamplerTree O

namespace MixedReceipt

variable {O : Type}

def cost (R : MixedReceipt O) : IntCost where
  queries := (R.steps.map QuantumStep.queries).sum
  gates := (R.steps.map QuantumStep.gates).sum
  bitTime := R.out.maxDepth + (R.prims.map (fun p => p.cost.bitTime)).sum
  peakSpace := max R.width ((R.prims.map (fun p => p.cost.peakSpace)).foldl max 0)

def legal (R : MixedReceipt O) : Prop :=
  (∀ s ∈ R.steps, s.legal = true) ∧ (∀ p ∈ R.prims, p.legal)

noncomputable def law [DecidableEq O] (R : MixedReceipt O) : O → ℝ := R.out.law

def realizes [DecidableEq O] (R : MixedReceipt O) (target : O → ℝ) : Prop :=
  ∀ o, R.out.law o = target o

def worstCaseBitTime (R : MixedReceipt O) : ℕ := R.cost.bitTime

def realizesInstrument [Fintype O] [DecidableEq O]
    (R : MixedReceipt O) {D : ℕ} (I : Instrument O D D) (ρ : Operator D) : Prop :=
  R.legal ∧ (∀ o, R.out.law o = instrumentProb I ρ o)

end MixedReceipt

noncomputable def bornLaw {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) : O → ℝ :=
  fun o => (Matrix.trace ((Λ.mats o).mat * ρ)).re

noncomputable def gibbsState {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (Matrix.trace (NormedSpace.exp (-(β : ℝ) • H)))⁻¹ •
    NormedSpace.exp (-(β : ℝ) • H)

namespace SamplerTree

def bind {O P : Type} : SamplerTree O → (O → SamplerTree P) → SamplerTree P
  | .emit o, k => k o
  | .fail, _ => .fail
  | .bit l r, k => .bit (bind l k) (bind r k)

end SamplerTree

structure RejectReceipt (O : Type) [Fintype O] [DecidableEq O] where

  trial : RejectTrial O

  target : O → ℝ

namespace RejectReceipt

variable {O : Type} [Fintype O] [DecidableEq O]

def exactLaw (S : RejectReceipt O) : Prop := ∀ o, S.trial.law o = S.target o

def aSFinite (S : RejectReceipt O) : Prop := 0 < S.trial.acceptMass

noncomputable def expectedBitTime (S : RejectReceipt O) : ℝ :=
  S.trial.expectedTrials * (S.trial.tree.maxDepth + 1)

noncomputable def tailMass (S : RejectReceipt O) (k : ℕ) : ℝ :=
  S.trial.rejectProb ^ k

def hasWorstCaseTimeBound (S : RejectReceipt O) : Prop := S.trial.rejectProb = 0

end RejectReceipt

structure TruncatedReject (O : Type) [Fintype O] [DecidableEq O] where

  trial : RejectTrial O

  cutoff : ℕ

namespace TruncatedReject

variable {O : Type} [Fintype O] [DecidableEq O]

noncomputable def timeoutMass (S : TruncatedReject O) : ℝ :=
  S.trial.rejectProb ^ S.cutoff

noncomputable def law (S : TruncatedReject O) : O → ℝ :=
  fun o => if S.trial.accept o then
    S.trial.tree.law o * (∑ k ∈ Finset.range S.cutoff, S.trial.rejectProb ^ k)
  else 0

def worstCaseBitTime (S : TruncatedReject O) : ℕ :=
  S.cutoff * S.trial.tree.maxDepth

def exactLaw (S : TruncatedReject O) : Prop := ∀ o, S.law o = S.trial.law o

end TruncatedReject

def IsDyadic (x : ℝ) : Prop := ∃ (z : ℤ) (k : ℕ), x = (z : ℝ) / (2 ^ k : ℝ)

def treeRealizes {O : Type} [Fintype O] [DecidableEq O] (target : O → ℝ)
    (tree : SamplerTree O) : Prop := ∀ o, tree.law o = target o

structure Filtration (Ω : Type) [Fintype Ω] where

  events : ℕ → Set (Set Ω)

  mono : ∀ t s, t ≤ s → events t ⊆ events s

  univ_mem : ∀ t, Set.univ ∈ events t

  compl_mem : ∀ t (E : Set Ω), E ∈ events t → (Set.univ \ E) ∈ events t

  union_mem : ∀ t (E F : Set Ω), E ∈ events t → F ∈ events t → (E ∪ F) ∈ events t

namespace FiniteSupportSpace

variable {Ω : Type} [Fintype Ω]

noncomputable def condExpect (S : FiniteSupportSpace Ω) (E : Set Ω) (Z : Ω → ℝ) : ℝ :=
  letI := Classical.decPred (· ∈ E)
  if 0 < S.eventProb E then
    (S.eventProb E)⁻¹ * ∑ ω : Ω, if ω ∈ E then S.prob ω * Z ω else 0
  else 0

end FiniteSupportSpace

structure ConcentrationLedger where

  window : ℝ

  failMass : ℝ

  errorMass : ℝ

structure StopTimeoutLedger (Ω : Type) [Fintype Ω] where

  stopped : Set Ω

  timedOut : Set Ω

  failMass : ℝ
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

structure Step2Search (m γ Nmax M L Q : ℕ) where

  law : Fin γ → Fin m → ℝ

  draws : Fin γ → Fin Nmax → Fin M → Fin m

  measA : Fin γ → Fin Nmax → Fin m → Fin L → ℝ

  measC : Fin γ → Fin Nmax → Fin L → ℝ

  idx : Fin γ → Fin Nmax → Fin Q → Fin m

namespace Step2Search

variable {m γ Nmax M L Q : ℕ}

def lawsOk (S : Step2Search m γ Nmax M L Q) : Prop :=
  ∀ k : Fin γ, (∀ i, 0 ≤ S.law k i) ∧ (∑ i : Fin m, S.law k i) = 1

noncomputable def gridMass (κ : ℝ) (N : ℕ) : ℝ := κ * (N + 1)

noncomputable def estA (S : Step2Search m γ Nmax M L Q) (k : Fin γ) (N : Fin Nmax)
    (j : Fin M) : ℝ := (∑ l : Fin L, S.measA k N (S.draws k N j) l) / L

noncomputable def estC (S : Step2Search m γ Nmax M L Q) (k : Fin γ) (N : Fin Nmax) :
    ℝ := (∑ l : Fin L, S.measC k N l) / L

noncomputable def accepts (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
    (α R κ ν : ℝ) (k : Fin γ) (N : Fin Nmax) : Prop :=
  S.estC k N / gridMass κ N - (κ + ν) ≤
      (∑ j : Fin M, S.estA k N j) / M ∧
    (∑ j : Fin M, b (S.draws k N j)) / M ≤
      α / gridMass κ N + R * (κ + ν)

noncomputable def roundVector (S : Step2Search m γ Nmax M L Q) (κ : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Fin m → ℝ :=
  fun i => gridMass κ N * S.law k i

def noOutput (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
    (α R κ ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax), ¬ S.accepts b α R κ ν k N

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

noncomputable def eq75Threshold {D : ℕ} (Cv ρ : Operator D) (α ε : ℝ) : ℝ :=
  (Matrix.trace (Cv * ρ)).re - 3 * α * ε

noncomputable def noCheapWidth (α R ε : ℝ) : ℝ := α * (1 - 3 * R * ε)

def correctedNoCheapSeparator {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re →
    ¬ (∑ i, z i * b i < noCheapWidth α R ε)

noncomputable def dualMixtureScale {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) : ℝ :=
  a + (∑ t : Fin T, μ t) / T

noncomputable def dualMixtureLaw {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ)
    (q : Fin T → Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    ((if i = j₀ then a else 0) + (∑ t : Fin T, μ t * q t i) / T) /
      dualMixtureScale a μ

noncomputable def dualMixtureVector {m T : ℕ} (j₀ : Fin m) (a : ℝ)
    (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ) : Fin m → ℝ :=
  fun i => (if i = j₀ then a else 0) + (∑ t : Fin T, μ t * q t i) / T

noncomputable def dualMixtureWeights {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) :
    Fin (T + 1) → ℝ :=
  Fin.cases (a / dualMixtureScale a μ)
    (fun t => μ t / (T * dualMixtureScale a μ))

def weightsDyadic {n : ℕ} (w : Fin n → ℝ) : Prop := ∀ i, IsDyadic (w i)

structure SparseMatrixInput (D : ℕ) where

  s : ℕ

  bits : ℕ

  entry : Fin D → Fin D → ℚ

def sparseInputLength (D m s bits : ℕ) : ℕ :=
  (m + 1) * D * s * bits

def totalInputLength (D m s bits : ℕ) (wt : Fin m → ℚ) (β : ℚ) : ℕ :=
  sparseInputLength D m s bits +
    (Finset.univ.sum fun i : Fin m =>
      (wt i).num.natAbs.size + (wt i).den.size) +
    β.num.natAbs.size + β.den.size

end Qatlib.Concepts.SdpDuality.ConeSeparation
