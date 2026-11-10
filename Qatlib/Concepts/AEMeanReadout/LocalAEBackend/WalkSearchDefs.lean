/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3
import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Th4Expander

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped BigOperators Classical

def complexLift {I : Type} (u : I → ℝ) : QState I := fun x => (u x : ℂ)

noncomputable def graphRowState {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (x : I) : QState (I × I) :=
  SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket x

noncomputable def graphSwapRowState {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (x : I) : QState (I × I) :=
  SzegedyIsometryB P *ᵥ Qatlib.Foundations.PureStateMath.Ket x

noncomputable def walkReachableSpan {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) : Submodule ℂ (QState (I × I)) :=
  Submodule.span ℂ (Set.range (graphRowState P) ∪ Set.range (graphSwapRowState P))

def WalkPreservesReachableSpan {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) : Prop :=
  (∀ ψ ∈ walkReachableSpan P, SzegedyWalk P *ᵥ ψ ∈ walkReachableSpan P) ∧
    (∀ ψ ∈ walkReachableSpan P, SwapGate *ᵥ ψ ∈ walkReachableSpan P)

def ReachableTwoPlaneLaw {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) : Prop :=
  ∀ (u : I → ℝ) (lam : ℝ),
    SzegedyDiscriminant P *ᵥ u = lam • u →
      SzegedyWalk P *ᵥ (SzegedyIsometry P *ᵥ complexLift u) =
          ((2 * lam : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u) -
            SzegedyIsometry P *ᵥ complexLift u ∧
        SzegedyWalk P *ᵥ (SzegedyIsometryB P *ᵥ complexLift u) =
          ((-(2 * lam) : ℝ) : ℂ) • (SzegedyIsometry P *ᵥ complexLift u) +
            ((4 * lam ^ 2 - 1 : ℝ) : ℂ) • (SzegedyIsometryB P *ᵥ complexLift u)

def GraphSetupAccount {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) : Prop :=
  ∀ j : I, ∃ U ∈ Matrix.unitaryGroup (I × I) ℂ,
    (∀ i : I, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) ∧
      U *ᵥ TensorState chainUniform (Qatlib.Foundations.PureStateMath.Ket j) = detectionInitial P ∧
      MeasureProb (detectionInitial P)
          (Finset.univ.filter (fun p => p.1 ∈ S)) = markedFraction S

def regPad (w a : ℕ) (r : Reg a) : Reg w :=
  fun i => if h : (i : ℕ) < a then r ⟨i, h⟩ else false

def regCat {a b : ℕ} (r : Reg a) (s : Reg b) : Reg (a + b) :=
  fun i => (finSumFinEquiv.symm i).elim r s

def FiniteWordComputes (w a : ℕ) (gs : List FiniteGateCode) (F : Reg a → Reg a) : Prop :=
  finiteWordLegal w gs = true ∧
    ∀ r : Reg a, finiteWordRun w gs (Qatlib.Foundations.PureStateMath.Ket (regPad w a r)) = some (Qatlib.Foundations.PureStateMath.Ket (regPad w a (F r)))

noncomputable def graphNeighborOf (n : ℕ) (adj : Fin n → Fin n → Bool)
    (x : Fin n) (k : ℕ) : Fin n :=
  ((Finset.univ.filter (fun j => adj x j)).toList.getD k) x

def HasGraphBitAccess (n d : ℕ) (hdn : d ≤ n) (adj : Fin n → Fin n → Bool)
    (M : Fin n → Bool) : Prop :=
  ∃ (a w gateRow gateCheck spaceBits : ℕ)
      (enc : Fin n → Reg a) (rowWord checkWord : List FiniteGateCode),
    Function.Injective enc ∧
      finiteWordLegal w rowWord = true ∧
      finiteWordLegal w checkWord = true ∧
      (∀ x : Fin n, ∀ k : ℕ, (hk : k < d) →
        finiteWordRun w rowWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a)
              (regCat (enc x) (enc ⟨k, Nat.lt_of_lt_of_le hk hdn⟩)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a)
            (regCat (enc x) (enc (graphNeighborOf n adj x k)))))) ∧
      (∀ x : Fin n,
        finiteWordRun w checkWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => M x))))) ∧
      rowWord.length ≤ gateRow ∧
      checkWord.length ≤ gateCheck ∧
      w ≤ spaceBits

def HasGraphRowGeneration (n d av w : ℕ) (adj : Fin n → Fin n → Bool)
    (enc : Fin n → Reg av) (gs : List FiniteGateCode) : Prop :=
  0 < d ∧
    finiteWordLegal w gs = true ∧
    ∀ x : Fin n,
      finiteWordRun w gs (Qatlib.Foundations.PureStateMath.Ket (regPad w av (enc x))) = some
        (∑ k : Fin d, ((Real.sqrt (d : ℝ))⁻¹ : ℂ) •
          Qatlib.Foundations.PureStateMath.Ket (regPad w (av + av)
            (regCat (enc x) (enc (graphNeighborOf n adj x k.val)))))

def ExplicitGapExpanderFamily (δ : ℝ) : Prop :=
  ∀ N : ℕ, ∃ (n d av w : ℕ) (adj : Fin n → Fin n → Bool) (enc : Fin n → Reg av)
      (genWord : List FiniteGateCode),
    N ≤ n ∧ 0 < d ∧ d < n ∧
      (∀ i j, adj i j = adj j i) ∧
      (∀ i, (Finset.univ.filter (fun j => adj i j)).card = d) ∧
      SymmetricChainGap
        (Qatlib.Concepts.WalkSearch.Th4Expander.expanderStep n d adj) δ ∧
      HasGraphRowGeneration n d av w adj enc genWord

noncomputable def walkFindSuccessProb {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (ψ : QState I) (S : Finset I) (M k t : ℕ) : ℝ :=
  MeasureProb (phaseSearchState W ψ S M k t)
    (Finset.univ.filter (fun q => q.2.2 ∈ S))

noncomputable def mnrsFindCostForm (Sc Uc Cc ε δ : ℝ) : ℝ :=
  Sc + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * Real.log (1 / Real.sqrt ε) * Uc + Cc)

noncomputable def szegedyDetectCostForm (Sc Uc Cc ε δ : ℝ) : ℝ :=
  Sc + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * Uc + Cc)

def edgeMarkedSet {I : Type} [Fintype I] [DecidableEq I] (M : Finset I) :
    Finset (I × I) :=
  Finset.univ.filter (fun p => p.1 ∈ M)

def HasWalkFind {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (M : Finset I) (Sc Uc Cc bound : ℝ) : Prop :=
  ∃ (k t Mq : ℕ), 2 ≤ Mq ∧
    1 / 24 ≤ walkFindSuccessProb (SzegedyWalk P) (detectionInitial P)
        (edgeMarkedSet M) Mq k t ∧
      Sc + ((2 * k * t * (Mq - 1) : ℕ) : ℝ) * Uc + (t : ℝ) * Cc ≤ bound

abbrev JohnsonVertex (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) :=
  {s : Finset X // s.card = k}

noncomputable def johnsonSubsetStep (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) :
    JohnsonVertex X k → JohnsonVertex X k → ℝ :=
  fun s t =>
    if (s.1 ∩ t.1).card = k - 1 then ((k * (Fintype.card X - k) : ℕ) : ℝ)⁻¹ else 0

def JohnsonRelationDetectionReduction : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (X : Type) [Fintype X] [DecidableEq X] (k : ℕ)
        (hne : Nonempty (JohnsonVertex X k)), 0 < k → 2 * k ≤ Fintype.card X →
      ∃ δ : ℝ, 0 < δ ∧ SymmetricChainGap (johnsonSubsetStep X k) δ ∧
        ∀ (Mset : Finset (JohnsonVertex X k)) (ε Sc Uc Cc : ℝ),
          0 < ε → ε ≤ 1 →
            (Mset.Nonempty →
              ε ≤ (Mset.card : ℝ) / (Fintype.card (JohnsonVertex X k) : ℝ)) →
            0 ≤ Sc → 0 ≤ Uc → 0 ≤ Cc →
            HasWalkFind (johnsonSubsetStep X k) Mset Sc Uc Cc
              (c * szegedyDetectCostForm Sc Uc Cc ε δ)

def edCollisionMarked (n : ℕ) (x : Fin n → ℕ) (r : ℕ) :
    Finset (JohnsonVertex (Fin n) r) :=
  Finset.univ.filter (fun s =>
    ∃ a b : Fin n, a ∈ s.1 ∧ b ∈ s.1 ∧ a ≠ b ∧ x a = x b)

def ElementDistinctnessWalkReduction : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 0 < n → ∀ x : Fin n → ℕ,
      (∃ a b : Fin n, a ≠ b ∧ x a = x b) →
      ∃ (r : ℕ) (hne : Nonempty (JohnsonVertex (Fin n) r)),
        0 < r ∧
          HasWalkFind (johnsonSubsetStep (Fin n) r) (edCollisionMarked n x r)
            (r : ℝ) 1 0 (c * ((n : ℝ) ^ (2 / 3 : ℝ) + 1))

def TriangleWalkReduction : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), 0 < n →
      (∃ a b w : Fin n, a ≠ b ∧ b ≠ w ∧ w ≠ a ∧ adj a b ∧ adj b w ∧ adj w a) →
      ∃ (V : Type) (iV : Fintype V) (iD : DecidableEq V) (hne : Nonempty V)
          (P : V → V → ℝ) (S : Finset V) (decode : V → Fin n × Fin n × Fin n)
          (Sc Uc Cc : ℝ),
        (∀ v ∈ S,
          (decode v).1 ≠ (decode v).2.1 ∧ (decode v).1 ≠ (decode v).2.2 ∧
            (decode v).2.1 ≠ (decode v).2.2 ∧ adj (decode v).1 (decode v).2.1 ∧
            adj (decode v).2.1 (decode v).2.2 ∧ adj (decode v).2.2 (decode v).1) ∧
        HasWalkFind P S Sc Uc Cc (c * ((n : ℝ) ^ (13 / 10 : ℝ) + 1))

def SatisfiesAbstractSearchInterface {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (x₀ : W) (ε Uc Cc δ : ℝ) : Prop :=
  ∃ (unmarkRefl : W ≃ₗᵢ[ℂ] W) (tMax : ℕ) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (c₁ c₂ : ℝ)
      (costR : ℕ → ℝ) (costMark : ℝ) (Rs : Submodule ℂ W),
    (∀ z ∈ Mr, unmarkRefl z = -z) ∧
      (∀ z ∈ Mrᗮ, unmarkRefl z = z) ∧
      ‖x₀‖ = 1 ∧
      0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧
      (markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀) ∧
      0 ≤ c₁ ∧ 0 ≤ c₂ ∧ 0 ≤ Uc ∧ 0 ≤ Cc ∧
      x₀ ∈ Rs ∧
      (∀ z ∈ Rs, markProj Mr z ∈ Rs) ∧
      (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ z ∈ Rs, R i z ∈ Rs) ∧
      (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
        R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1)) ∧
      (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ ψ ∈ Rs,
        ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
          ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
            ≤ betaAt (1 / 72) i * ‖ψ‖) ∧
      (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
        costR i ≤ c₁ * Real.log (1 / betaAt (1 / 72) i)) ∧
      costMark ≤ c₂ ∧
      3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 4) ∧
      (∀ j, j < tMax →
        3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (Real.pi / 4) (3 * Real.pi / 4)) ∧
      c₁ ≤ 2 * Uc / Real.sqrt δ ∧
      c₂ ≤ Cc

def FreshSliceApplicabilityBridge : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ),
    IsTransitionMatrix P → (∀ i j, P i j = P j i) →
      0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
      0 < ε → ε ≤ 1 → (S.Nonempty → ε ≤ markedFraction S) →
      ∃ (W : Type) (hW1 : NormedAddCommGroup W) (hW2 : InnerProductSpace ℂ W)
          (hW3 : FiniteDimensional ℂ W) (Mr : Submodule ℂ W) (x₀ : W),
        SatisfiesAbstractSearchInterface Mr x₀ ε 1 0 δ ∧
          markedMass Mr x₀ = markedFraction S ∧
          (S = ∅ → markedMass Mr x₀ = 0)

def NonreversibleSearchBridge : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
      (P : Matrix X X ℝ) (π : X → ℝ) (S : Finset X) (ε : ℝ),
    P.IsIrreducible →
      (∀ x y, 0 ≤ P x y) →
      (∀ x, ∑ y, P x y = 1) →
      (∀ x, 0 < P x x) →
      (∀ x, 0 < π x) →
      (∑ x, π x) = 1 →
      (∀ y, ∑ x, π x * P x y = π y) →
      0 < ε → ε ≤ 1 → (S.Nonempty → ε ≤ ∑ x ∈ S, π x) →
      ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ 1 ∧
        (∀ i : Fin (Fintype.card X),
          (Matrix.toEuclideanLin (mnrsDiscriminant P π)).singularValues i ≤ 1 - Δ ∨
            (Matrix.toEuclideanLin (mnrsDiscriminant P π)).singularValues i = 1) →
        ∃ (W : Type) (hW1 : NormedAddCommGroup W) (hW2 : InnerProductSpace ℂ W)
            (hW3 : FiniteDimensional ℂ W) (Mr : Submodule ℂ W) (x₀ : W),
          SatisfiesAbstractSearchInterface Mr x₀ ε 1 0 Δ ∧
            markedMass Mr x₀ = ∑ x ∈ S, π x ∧
            (S = ∅ → markedMass Mr x₀ = 0)

def WalkEigenGapAccount {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ) : Prop :=
  ∃ (n' : ℕ) (v : Fin n' → QState (I × I)) (μ : Fin n' → ℂ),
    (∀ a b, Qatlib.Foundations.PureStateMath.Inner (v a) (v b) = if a = b then 1 else 0) ∧
      (∀ j, SzegedyWalk P *ᵥ v j = μ j • v j) ∧
      (∀ ψ ∈ walkReachableSpan P, ∃ c : Fin n' → ℂ, ψ = ∑ j, c j • v j) ∧
      (∀ j, μ j ≠ 1 → 2 * Real.sqrt δ ≤ ‖μ j - 1‖) ∧
      MeasureProb (detectionInitial P)
          (Finset.univ.filter (fun p => p.1 ∈ S)) = markedFraction S

def HasLocalGateSynthesis : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (w : ℕ) (U : Matrix (Reg w) (Reg w) ℂ),
      U ∈ Matrix.unitaryGroup (Reg w) ℂ →
      ∀ ε : ℝ, 0 < ε →
        ∃ gs : List FiniteGateCode,
          finiteWordLegal w gs = true ∧
            gs.length ≤ C w * (Nat.ceil (((1 : ℝ) / ε) ^ 2) + 1) ∧
            ∀ r : Reg w, ∃ φ : QState (Reg w),
              finiteWordRun w gs (Qatlib.Foundations.PureStateMath.Ket r) = some φ ∧
                ∑ i, ‖φ i - (U *ᵥ Qatlib.Foundations.PureStateMath.Ket r) i‖ ^ 2 ≤ ε ^ 2

def HasFairBitUniformLengthSampler : Prop :=
  ∀ L : ℕ, 0 < L →
    ∃ (b : ℕ) (draw : Reg b → Option (Fin L)),
      L ≤ 2 ^ b ∧
        (∀ K K' : Fin L,
          (∑ r : Reg b, if draw r = some K then (1 : ℝ) else 0) =
            (∑ r : Reg b, if draw r = some K' then (1 : ℝ) else 0)) ∧
        (2 * (∑ K : Fin L, ∑ r : Reg b, if draw r = some K then (1 : ℝ) else 0)
            ≥ (2 ^ b : ℝ))

def threeCycleStep : Fin 3 → Fin 3 → ℝ :=
  fun x y => if (x.val + 1) % 3 = y.val then 1 else 0

def IrreducibleIdleCounterexample : Prop :=
  IsTransitionMatrix threeCycleStep ∧
    Matrix.IsIrreducible threeCycleStep ∧
    (∃ v : QState (Fin 3 × Fin 3), SzegedyWalk threeCycleStep *ᵥ v = v ∧ v ≠ 0) ∧
    (∀ v ∈ walkReachableSpan threeCycleStep,
      SzegedyWalk threeCycleStep *ᵥ v = v → v = 0)

noncomputable def plusIReflectionWord {I : Type} [DecidableEq I] (j : I) :
    List (DetectionStep I) :=
  [.rowForward, .marker, .rowBackward]

noncomputable def plusIWalkWord {I : Type} [DecidableEq I] (j : I) :
    List (DetectionStep I) :=
  [.fixed detectionControlledSwap] ++ plusIReflectionWord j ++
    [.fixed detectionControlledSwap] ++ plusIReflectionWord j

noncomputable def plusIProgram {I : Type} [DecidableEq I] (j : I) (K : ℕ) :
    List (DetectionStep I) :=
  [.marker, .fixed detectionHadamard] ++ (List.replicate K (plusIWalkWord j)).flatten ++
    [.fixed detectionHadamard, .rowInitial]

noncomputable def plusIDetectionProbability {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (j : I) (K : ℕ) : ℝ :=
  MeasureProb (detectionEvaluate U S (plusIProgram j K) *ᵥ detectionStart j)
    detectionAccept

def PerKDetectionCounterexample : Prop :=
  ∃ (I : Type) (hi : Fintype I) (hd : DecidableEq I) (hn : Nonempty I)
      (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ),
    IsTransitionMatrix P ∧ (∀ i y, P i y = P y i) ∧ 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap P δ ∧ S.Nonempty ∧ markedFraction S ≤ 1 / 32 ∧
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      (∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) ∧
      ∃ K : ℕ, detectionProbability U S j K < 1 / 32

def PlusIVariantCounterexample : Prop :=
  ∃ (I : Type) (hi : Fintype I) (hd : DecidableEq I) (hn : Nonempty I)
      (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ) (K : ℕ),
    IsTransitionMatrix P ∧ (∀ i y, P i y = P y i) ∧ 0 < δ ∧ δ ≤ 1 ∧
      SymmetricChainGap P δ ∧ S.Nonempty ∧ markedFraction S ≤ 1 / 32 ∧
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      (∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) ∧
      plusIDetectionProbability U S j K < 1 / 32

def BipartiteTauEndpointVanishes : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B →
      ∀ u : QState (I ⊕ J),
        bipartiteDiscriminant A B *ᵥ u = ((1 : ℝ) : ℂ) • u →
          ∀ s : Bool, bipartiteTauLinear A B 1 s u = 0

def SourceDualWitnessAttained : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
      (input : X → Fin n → Bool) (f : X → Bool),
    (∃ v : X → Fin n → Fin m → ℂ, ∃ W : ℝ,
        Qatlib.Concepts.QueryComplexity.Reflections.SourceDualFeasible input f v W) →
    ∃ (v : X → Fin n → Fin m → ℂ) (W : ℝ),
      Qatlib.Concepts.QueryComplexity.Reflections.SourceDualFeasible input f v W ∧
        ∀ (v' : X → Fin n → Fin m → ℂ) (W' : ℝ),
          Qatlib.Concepts.QueryComplexity.Reflections.SourceDualFeasible input f v' W' →
            W ≤ W'

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
