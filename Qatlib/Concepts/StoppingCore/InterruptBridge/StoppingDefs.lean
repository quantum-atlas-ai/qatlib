/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.Stopping
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
import Qatlib.Concepts.ZeroCostLimit.FirstHitMass.ZeroCostLimit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.StoppingCore.InterruptBridge.WeightedStoppingBudget
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open scoped ENNReal BigOperators Classical Matrix

inductive CutKind where
  | oracleBoundary
  | interiorCut
  deriving DecidableEq, Repr

variable {I R : Type}

def isAtomicStep : Step I → Bool
  | .query => true
  | .gate _ => false

def optAtomic : Option (Step I) → Bool
  | none => false
  | some s => isAtomicStep s

def cutKind (w : Circuit I) (k : ℕ) : CutKind :=
  if optAtomic (w.drop k).head? || optAtomic (w.take k).getLast? then
    CutKind.oracleBoundary
  else
    CutKind.interiorCut

def legalCut (w : Circuit I) (k : ℕ) : Prop := k ≤ w.length

structure InterruptConfig (I R : Type) where

  word : Circuit I

  mem : QState I

  ref : R

  log : List (Step I)

abbrev InterruptOutput (I R : Type) := QState I × R × List (Step I)

variable [Fintype I] [DecidableEq I]

noncomputable def microStep (O : Matrix I I ℂ) : InterruptConfig I R → InterruptConfig I R
  | ⟨[], ψ, r, lg⟩ => ⟨[], ψ, r, lg⟩
  | ⟨Step.gate U :: cs, ψ, r, lg⟩ => ⟨cs, ApplyGate U ψ, r, Step.gate U :: lg⟩
  | ⟨Step.query :: cs, ψ, r, lg⟩ => ⟨cs, ApplyGate O ψ, r, Step.query :: lg⟩

noncomputable def microAfter (O : Matrix I I ℂ) : ℕ → InterruptConfig I R → InterruptConfig I R
  | 0, cfg => cfg
  | k + 1, cfg => microAfter O k (microStep O cfg)

noncomputable def microNext (O : Matrix I I ℂ) :
    InterruptConfig I R → PMF (InterruptOutput I R ⊕ InterruptConfig I R)
  | ⟨[], ψ, r, lg⟩ => PMF.pure (Sum.inl (ψ, r, lg))
  | ⟨s :: cs, ψ, r, lg⟩ =>
    if cs = [] then
      PMF.pure (Sum.inl ((microStep O ⟨s :: cs, ψ, r, lg⟩).mem,
        (microStep O ⟨s :: cs, ψ, r, lg⟩).ref, (microStep O ⟨s :: cs, ψ, r, lg⟩).log))
    else
      PMF.pure (Sum.inr (microStep O ⟨s :: cs, ψ, r, lg⟩))

def microLaunch (cfg : InterruptConfig I R) : InterruptOutput I R ⊕ InterruptConfig I R :=
  if cfg.word = [] then Sum.inl (cfg.mem, cfg.ref, cfg.log) else Sum.inr cfg

noncomputable def microResult (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R) :
    InterruptOutput I R ⊕ InterruptConfig I R :=
  let a := microAfter O k cfg
  if cfg.word.length ≤ k then Sum.inl (a.mem, a.ref, a.log) else Sum.inr a

def flipFirst : Bool × Bool → Bool × Bool := fun p => (Bool.not p.1, p.2)

theorem flipFirst_involutive : Function.Involutive flipFirst := by
  intro p
  cases p with
  | mk a b => cases a <;> cases b <;> rfl

def InterruptPrefixResume : Prop :=
  ∀ (I R : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (m n : ℕ)
    (cfg : InterruptConfig I R),
    runFor (microNext O) (m + n) (microLaunch cfg) =
      CostedLaw.bind (runFor (microNext O) m (microLaunch cfg))
        (runFor (microNext O) n) ∧
    microAfter O n (microAfter O m cfg) = microAfter O (m + n) cfg ∧
    (runFor (microNext O) (m + n) (microLaunch cfg)).map Prod.fst =
      PMF.bind (runFor (microNext O) m (microLaunch cfg))
        (fun x => (runFor (microNext O) n x.1).map Prod.fst)

def InterruptPrefixState : Prop :=
  ∀ (I R : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (k : ℕ)
    (cfg : InterruptConfig I R),
    microAfter O k cfg =
      ⟨cfg.word.drop k, Run O (cfg.word.take k) cfg.mem, cfg.ref,
        (cfg.word.take k).reverse ++ cfg.log⟩ ∧
    (legalCut cfg.word k →
      runFor (microNext O) k (microLaunch cfg) =
        PMF.pure (microResult O k cfg, k))

def InterruptCutDegenerate : Prop :=
  ∀ (I R : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ)
    (cfg : InterruptConfig I R),
    microAfter O 0 cfg = cfg ∧
    (∀ n : ℕ, runFor (microNext O) n
        (Sum.inl (cfg.mem, cfg.ref, cfg.log) : InterruptOutput I R ⊕ InterruptConfig I R) =
      CostedLaw.ret (Sum.inl (cfg.mem, cfg.ref, cfg.log))) ∧
    (∀ k : ℕ, k < cfg.word.length →
      microResult O k cfg = Sum.inr (microAfter O k cfg) ∧
        (microAfter O k cfg).word = cfg.word.drop k ∧
        (microAfter O k cfg).word ≠ [])

def InterruptCutKinds : Prop :=
  (∀ (I : Type) (w : Circuit I) (k : ℕ),
      cutKind w k = CutKind.oracleBoundary ↔
        optAtomic (w.drop k).head? = true ∨ optAtomic (w.take k).getLast? = true) ∧
  (∀ (I : Type) (w : Circuit I) (k : ℕ), legalCut w k ↔ k ≤ w.length) ∧
  (∀ (I : Type) (w : Circuit I), w = [Step.query] →
      ∀ k, legalCut w k → cutKind w k = CutKind.oracleBoundary) ∧
  (∀ (U V : Matrix Bool Bool ℂ), cutKind [Step.gate U, Step.gate V] 1 = CutKind.interiorCut)

def InterruptConsumers : Prop :=
  (∀ (O : Matrix Bool Bool ℂ),
      PauliX * PauliZ ≠ PauliZ * PauliX ∧
        Run O [Step.gate PauliX, Step.gate PauliZ] (Qatlib.Foundations.PureStateMath.Ket false) ≠
          Run O [Step.gate PauliZ, Step.gate PauliX] (Qatlib.Foundations.PureStateMath.Ket false)) ∧
  (∀ (O : Matrix Bool Bool ℂ),
      microAfter O 1 ⟨[Step.gate PauliX, Step.gate PauliZ], Qatlib.Foundations.PureStateMath.Ket false, (), []⟩ =
        ⟨[Step.gate PauliZ], ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false), (), [Step.gate PauliX]⟩) ∧
  (∀ (O : Matrix Bool Bool ℂ),
      microAfter O 2 ⟨[Step.gate PauliX, Step.gate PauliZ], Qatlib.Foundations.PureStateMath.Ket false, (), []⟩ =
        ⟨[], Run O [Step.gate PauliX, Step.gate PauliZ] (Qatlib.Foundations.PureStateMath.Ket false), (),
          [Step.gate PauliZ, Step.gate PauliX]⟩) ∧
  (∀ (O : Matrix Bool Bool ℂ),
      runFor (microNext O) 2
          (microLaunch ⟨[Step.gate PauliX, Step.gate PauliZ], Qatlib.Foundations.PureStateMath.Ket false, (), []⟩) =
        CostedLaw.bind
          (runFor (microNext O) 1
            (microLaunch ⟨[Step.gate PauliX, Step.gate PauliZ], Qatlib.Foundations.PureStateMath.Ket false, (), []⟩))
          (runFor (microNext O) 1)) ∧
  (Normalized teleportBellResource ∧
    ¬ ∃ (a : QState Bool) (b : QState Bool), teleportBellResource = TensorState a b) ∧
  (∀ (Rt : Type) (r : Rt) (k : ℕ),
      (microAfter (permMatrix flipFirst) k
          ⟨[Step.gate (permMatrix flipFirst)], teleportBellResource, r, []⟩).ref = r ∧
      (microAfter (permMatrix flipFirst) k
          ⟨[Step.gate (permMatrix flipFirst)], teleportBellResource, r, []⟩).mem =
        Run (permMatrix flipFirst) ([Step.gate (permMatrix flipFirst)].take k)
          teleportBellResource)

def Clause13Claim : Prop :=
  InterruptPrefixResume ∧ InterruptPrefixState ∧ InterruptCutDegenerate ∧
    InterruptCutKinds ∧ InterruptConsumers

def nonZenoCheck {S : Type} [Fintype S] [DecidableEq S] (c : S → ℕ) : Bool :=
  decide (((Finset.univ.filter (fun s => 0 < c s) : Finset S)).card =
    (Finset.univ : Finset S).card)

def ZeroCostNeverSemantics : Prop :=
  ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S),
    (∀ o, (∑' k, haltMass next cost cfg o k) = ∑' t, haltJoint next cfg o t) ∧
      (∑' o, ∑' k, haltMass next cost cfg o k) + nonterminationMass next cfg = 1

def ZeroCostNonZenoLaws : Prop :=
  (∀ (S : Type) [Fintype S] [DecidableEq S] (c : S → ℕ),
      nonZenoCheck c = true ↔ positiveCharge c) ∧
  (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (hc : ∀ s, 1 ≤ cost s)
    (cfg : O ⊕ S) (o : O) (k fuel : ℕ), k ≤ fuel →
      weightedRunFor next cost fuel cfg (Sum.inl o, k) =
        weightedHaltJoint next cost cfg o k) ∧
  (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ),
      (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        pendingMass next cfg fuel = 1)

def ZeroCostFirstStopJoint : Prop :=
  ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cost : S → ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ),
    haltMass next cost cfg o k = ⨆ fuel : ℕ, weightedRunFor next cost fuel cfg (Sum.inl o, k) ∧
      (∀ fuel : ℕ,
        (∑' o' : O, ∑' k' : ℕ, weightedRunFor next cost fuel cfg (Sum.inl o', k')) +
          (∑ s : S, ∑' j : ℕ, weightedRunFor next cost fuel cfg (Sum.inr s, j)) = 1) ∧
      (0 < haltMass next cost cfg o k →
        Filter.Tendsto (fun fuel => weightedRunFor next cost fuel cfg (Sum.inl o, k))
          Filter.atTop (nhds (haltMass next cost cfg o k)))

def unitCharge : Bool → ℕ := fun _ => 1

def ZeroCostConsumers : Prop :=
  (haltMass zeroCountdownNext (fun _ => 0) (Sum.inr true) () 0 = 1 ∧
    (∀ k : ℕ, k ≠ 0 → haltMass zeroCountdownNext (fun _ => 0) (Sum.inr true) () k = 0) ∧
    nonterminationMass zeroCountdownNext (Sum.inr true) = 0 ∧
    weightedRunFor zeroCountdownNext (fun _ => 0) 2 (Sum.inr true) (Sum.inl (), 0) = 1) ∧
  (zenoZeroCharge zenoNext zenoCharge PUnit.unit ∧
    neverStopMass zenoNext (Sum.inr PUnit.unit) = 1) ∧
  (positiveCharge unitCharge ∧
    weightedHaltJoint zeroCountdownNext unitCharge (Sum.inr true) () 2 = 1 ∧
    (∀ B : ℕ, weightedBudgetRun zeroCountdownNext unitCharge B (Sum.inr true) =
      if 2 ≤ B then CostedLaw.charge 2 (CostedLaw.ret (Sum.inl ()))
      else if 1 ≤ B then CostedLaw.charge 1 (CostedLaw.ret (Sum.inr false))
      else CostedLaw.ret (Sum.inr true)))

def Clause14Claim : Prop :=
  ZeroCostNeverSemantics ∧ ZeroCostNonZenoLaws ∧ ZeroCostFirstStopJoint ∧ ZeroCostConsumers

noncomputable def eventBranchMap {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (Ev : X → Prop) [DecidablePred Ev] :
    Operator D →ₗ[ℂ] Operator E :=
  ∑ x ∈ Finset.univ.filter Ev, I.branch x

noncomputable def eventProb {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop) [DecidablePred Ev] : ℝ :=
  ∑ x ∈ Finset.univ.filter Ev, instrumentProb I ρ x

noncomputable def normalizedPost {X : Type} [Fintype X] [DecidableEq X]
    {D E : ℕ} (I : Instrument X D E) (ρ : Operator D) (Ev : X → Prop) [DecidablePred Ev] :
    Operator E :=
  if 0 < eventProb I ρ Ev then
    (((eventProb I ρ Ev : ℝ) : ℂ)⁻¹) • eventBranchMap I Ev ρ
  else
    0

structure StopResiduals (S O : Type) [Fintype S] [Fintype O] where

  pending : ℝ≥0∞

  never : ℝ≥0∞

  overflow : ℝ≥0∞

noncomputable def residualsOf {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel budget : ℕ) : StopResiduals S O :=
  ⟨pendingMass next cfg fuel, nonterminationMass next cfg,
    CostedLaw.overflow (runFor next fuel cfg) budget⟩

def ConditionCorrespondence : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (Ev : X → Prop) [DecidablePred Ev],
    eventBranchMap I Ev ρ = ((eventProb I ρ Ev : ℝ) : ℂ) • normalizedPost I ρ Ev ∧
      (Matrix.trace (eventBranchMap I Ev ρ)).re = eventProb I ρ Ev ∧
      (eventProb I ρ Ev = 0 → eventBranchMap I Ev ρ = 0 ∧ normalizedPost I ρ Ev = 0) ∧
      (0 < eventProb I ρ Ev → IsDensityOperator (normalizedPost I ρ Ev))

def ConditionMixture : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (Ev : X → Prop) [DecidablePred Ev],
    normalizedPost I ρ Ev =
      ∑ x ∈ Finset.univ.filter Ev,
        if h : 0 < instrumentProb I ρ x then
          ((((instrumentProb I ρ x) / eventProb I ρ Ev : ℝ) : ℂ)) •
            I.conditionalState ρ x h
        else 0

def ConditionCoarseResidual : Prop :=
  (∀ (X P : Type) [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P]
    (D E : ℕ) (I : Instrument X D E) (f : X → P) (p : P),
      eventBranchMap I (fun x => f x = p) = (I.coarsen f).branch p ∧
        ∀ (ρ : Operator D),
          eventProb I ρ (fun x => f x = p) = instrumentProb (I.coarsen f) ρ p) ∧
  (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ) (Ev : O → Prop) [DecidablePred Ev],
      (∑ o ∈ Finset.univ.filter Ev, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        (∑ o ∈ Finset.univ.filter (fun o => ¬ Ev o),
          ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
        (residualsOf next cfg fuel 0).pending = 1)

noncomputable def conjByX (A : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  PauliX * A * Matrix.conjTranspose PauliX

noncomputable def conjByZ (A : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  PauliZ * A * Matrix.conjTranspose PauliZ

def ConditionDownstream : Prop :=
  (∀ (X : Type) (Q : X → Type) [Fintype X] [∀ o, Fintype (Q o)]
    (D E F : ℕ) (I : Instrument X D E) (J : ∀ o, Instrument (Q o) E F)
    (ρ : Operator D) (o : X) (q : Q o),
      (I.feedForward J).branch ⟨o, q⟩ ρ = (J o).branch q (I.branch o ρ)) ∧
  (PauliX * PauliZ ≠ PauliZ * PauliX ∧
    ApplyGate PauliX (ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket false)) ≠
      ApplyGate PauliZ (ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false)) ∧
    conjByX (outerProduct (Qatlib.Foundations.PureStateMath.Ket false)) ≠ conjByZ (outerProduct (Qatlib.Foundations.PureStateMath.Ket false))) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
    (ψ : QState (Fin D)) (Ev : X → Prop) [DecidablePred Ev],
      eventProb I (outerProduct ψ) Ev =
        (Matrix.trace (eventBranchMap I Ev (outerProduct ψ))).re) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (D E : ℕ) (I : Instrument X D E)
    (ρ σ : Operator D) (c : ℝ) (Ev : X → Prop) [DecidablePred Ev],
      eventBranchMap I Ev (((c : ℝ) : ℂ) • ρ) = ((c : ℝ) : ℂ) • eventBranchMap I Ev ρ ∧
        eventBranchMap I Ev (ρ + σ) = eventBranchMap I Ev ρ + eventBranchMap I Ev σ)

def PaidWalkClaim : Prop :=
  ConditionCorrespondence ∧ ConditionMixture ∧ ConditionCoarseResidual ∧ ConditionDownstream

noncomputable def fairBit : PMF Bool :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

structure FinEncoding (X : Type) [Fintype X] where

  w : X → ℚ

  nonneg : ∀ x, 0 ≤ w x

  sum_one : ∑ x, w x = 1

noncomputable def bitDecodeSampler {X R : Type} [Fintype X] [Fintype R]
    (decode : (R → Bool) → X) : PMF X :=
  (PMF.ofFintype (fun _ : R → Bool => (2 ^ Fintype.card R : ℝ≥0∞)⁻¹) (by
    classical
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by norm_num))
        (ENNReal.pow_ne_top (by norm_num)))).map decode

noncomputable def samplerCharge {X : Type} (n : ℕ) (p : PMF X) : CostedLaw X :=
  p.map (fun x => (x, n))

def SamplerExactLaw : Prop :=
  ∀ (X R : Type) [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (decode : (R → Bool) → X) (x : X),
    bitDecodeSampler decode x =
      ((Finset.univ.filter (fun ω : R → Bool => decode ω = x)).card : ℝ≥0∞) /
        (2 ^ Fintype.card R) ∧
    (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).map Prod.fst =
      bitDecodeSampler decode ∧
    (∀ y ∈ (samplerCharge (Fintype.card R) (bitDecodeSampler decode)).support,
      y.2 = Fintype.card R) ∧
    CostedLaw.expectedCost (samplerCharge (Fintype.card R) (bitDecodeSampler decode)) =
      (Fintype.card R : ℝ≥0∞)

def TailTruncationContract : Prop :=
  ∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    (next : S → PMF (O ⊕ S)) (cfg : O ⊕ S) (fuel : ℕ),
    (∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k) +
      pendingMass next cfg fuel = 1 ∧
    (∀ ε : ℝ≥0∞, pendingMass next cfg fuel ≤ ε →
      1 - ε ≤ ∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k)

structure SamplerResources where

  bits : ℕ

  bitTime : ℕ

  space : ℕ

  error : ℝ≥0∞

def SamplerResourceTransport : Prop :=
  ∀ (I R : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (m n : ℕ)
    (cfg : InterruptConfig I R),
    runFor (microNext O) (m + n) (microLaunch cfg) =
      CostedLaw.bind (runFor (microNext O) m (microLaunch cfg)) (runFor (microNext O) n) ∧
    (∀ k : ℕ, (microAfter O k cfg).log = (cfg.word.take k).reverse ++ cfg.log) ∧
    (∀ k : ℕ, k ≤ cfg.word.length →
      (microAfter O k cfg).ref = cfg.ref ∧
        ∃ r : SamplerResources,
          r.bits = k ∧ r.bitTime = k ∧ r.space = cfg.word.length ∧ r.error = 0)

def Clause16Claim : Prop :=
  SamplerExactLaw ∧ TailTruncationContract ∧ SamplerResourceTransport

end Qatlib.Concepts.StoppingCore.InterruptBridge
