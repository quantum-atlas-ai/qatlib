/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstruction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.MultiBandFilter
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.HspRecovery.SieveLaw

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.HspRecovery.KitaevReadout
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

def Clause6RowAccessResidual : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (a w : ℕ) (enc : I → Reg a)
    (support : I → Finset I) (idx : ℕ → I) (nbr : I → ℕ → I)
    (setupWord updateWord checkWord : List FiniteGateCode) (C : ℕ → ℕ),
    HasPaidWalkAccess P S a w enc support idx nbr setupWord updateWord checkWord C →
      Function.Injective enc ∧
      finiteWordLegal w setupWord = true ∧
      finiteWordLegal w updateWord = true ∧
      finiteWordLegal w checkWord = true

abbrev busySpace {I : Type} [DecidableEq I] (S : Finset I) : Type := Unmarked I S

noncomputable def busyAction {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) : Matrix (busySpace S) (busySpace S) ℂ :=
  unmarkedPrincipal P S

noncomputable def hermitianEigenfamily {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : n) : n → ℂ :=
  hA.eigenvectorBasis j |>.ofLp

noncomputable def hermitianEigenvalue {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : n) : ℝ :=
  hA.eigenvalues j

def Clause6PaidAccessClauses : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (a w : ℕ) (enc : I → Reg a)
    (support : I → Finset I) (idx : ℕ → I) (nbr : I → ℕ → I)
    (setupWord updateWord checkWord : List FiniteGateCode) (C : ℕ → ℕ),
    HasPaidWalkAccess P S a w enc support idx nbr setupWord updateWord checkWord C →
    Function.Injective enc ∧
    finiteWordLegal w setupWord = true ∧
    finiteWordLegal w updateWord = true ∧
    finiteWordLegal w checkWord = true ∧
    (∀ (eps : ℝ), 0 < eps → setupWord.length ≤ C (Nat.ceil ((1 / eps) ^ 2) + 1)) ∧
    updateWord.length ≤ 2 * a + 2 ∧ checkWord.length ≤ 2 * a + 2 ∧ w ≤ 2 * a + 2

def Clause6BusySpectrumContent : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ → S.Nonempty →
    (∀ (x y : I) (hx : x ∉ S),
      unmarkedRowFrame P S (x, y) ⟨x, hx⟩ = ((Real.sqrt (P x y) : ℝ) : ℂ)) ∧
    (∀ (x y : I) (b : ℕ) (e : I → Reg b) (_hb : 0 < b) (_henc : Function.Injective e),
      rowBasisRecordState P b (b + b) e x (regPad (b + b) (b + b) (regCat (e x) (e y)))
        = ((Real.sqrt (P x y) : ℝ) : ℂ)) ∧
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (unmarkedRowFrame P S) ∧
    (unmarkedRowFrame P S)ᴴ * (SwapGate : Matrix (I × I) (I × I) ℂ) * (unmarkedRowFrame P S)
      = unmarkedPrincipal P S ∧
    ‖unmarkedPrincipal P S‖ ≤ 1 - δ * markedFraction S ∧
    (∃ (hH : (unmarkedPrincipal P S).IsHermitian)
        (fam : busySpace S → QState (busySpace S)),
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (fam i) (fam j) = if i = j then 1 else 0) ∧
      (∀ i, unmarkedPrincipal P S *ᵥ fam i = (hermitianEigenvalue hH i : ℂ) • fam i)) ∧
    (∀ u : QState (busySpace S), u ≠ 0 → unmarkedPrincipal P S *ᵥ u ≠ u) ∧
    (∀ (π : I → ℝ) (_hπ : (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1) (_hrev : IsReversible P π),
      SzegedyWalk P *ᵥ SzegedyEmbedState P π = SzegedyEmbedState P π)

def Clause6BusySpectrumTransport : Prop :=
  Clause6PaidAccessClauses ∧ Clause6BusySpectrumContent

def Clause32ScheduleResidual : Prop :=
  ∀ (M k t : ℕ) (hM : 2 ≤ M),
    phaseSearchLedger M k t = (2 * k * t * (M - 1), t, 1)

def TunableQueryClassifierResidual : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (M : ℕ) (bands : List (ℚ × ℚ))
    (phi : J → ℝ) (eta : ℝ), 2 ≤ M → 0 < eta → eta ≤ 1/16 →
    (∀ j, |phi j| ≤ 1/4) → (∀ b ∈ bands, -1/4 ≤ (b.1:ℝ) ∧ (b.2:ℝ) ≤ 1/4) →
    (∀ j b, b∈bands → ((b.1:ℝ)+2*eta ≤ phi j ∧ phi j ≤ (b.2:ℝ)-2*eta) ∨
      (phi j ≤ (b.1:ℝ)-2*eta ∨ (b.2:ℝ)+2*eta ≤ phi j)) →
    bandClassificationGap M (bandLabels M bands) phi
      (Finset.univ.filter (fun j => bandContains bands (phi j))) eta ∧
    (∀ j b, b ∈ bands → phi j = (b.1:ℝ) + 2*eta →
      ¬ (phi j ≤ (b.1:ℝ)-2*eta ∨ (b.2:ℝ)+2*eta ≤ phi j) →
      bandContains bands (phi j))

def repeatWord {H : Type*} (w : List (AdjointStep H)) : ℕ → List (AdjointStep H)
  | 0 => []
  | n + 1 => w ++ repeatWord w n

theorem adjointQueryCount_append {H : Type*} (a b : List (AdjointStep H)) :
    adjointQueryCount (a ++ b) = adjointQueryCount a + adjointQueryCount b := by
  induction a with
  | nil => simp [adjointQueryCount]
  | cons h t ih =>
    cases h with
    | gate V => simpa only [List.cons_append, adjointQueryCount] using! ih
    | forward => simp only [List.cons_append, adjointQueryCount]; omega
    | backward => simp only [List.cons_append, adjointQueryCount]; omega

theorem adjointGateCount_append {H : Type*} (a b : List (AdjointStep H)) :
    adjointGateCount (a ++ b) = adjointGateCount a + adjointGateCount b := by
  induction a with
  | nil => simp [adjointGateCount]
  | cons h t ih =>
    cases h with
    | gate V => simp only [List.cons_append, adjointGateCount]; omega
    | forward => simp only [List.cons_append, adjointGateCount]; omega
    | backward => simp only [List.cons_append, adjointGateCount]; omega

noncomputable def clause33Pass (M k : ℕ) (hM : 0 < M) (φ : ℝ) : ℂ :=
  (sinEnvelopeKernel M φ (⟨0, hM⟩ : Fin M)) ^ k

noncomputable def clause33Coeff {J : Type} (M k : ℕ) (hM : 0 < M)
    (c : J → ℂ) (φ : J → ℝ) (j : J) : ℂ :=
  c j * clause33Pass M k hM (φ j)

noncomputable def clause33TargetCoeff {J : Type} (M k : ℕ) (hM : 0 < M)
    (c : J → ℂ) (φ : J → ℝ) (T : Finset J) (j : J) : ℂ :=
  if j ∈ T then clause33Coeff M k hM c φ j else 0

noncomputable def clause33LeakCoeff {J : Type} (M k : ℕ) (hM : 0 < M)
    (c : J → ℂ) (φ : J → ℝ) (T : Finset J) (j : J) : ℂ :=
  if j ∈ T then 0 else clause33Coeff M k hM c φ j

noncomputable def clause33FilteredState {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ) : QState I :=
  ∑ j, clause33Coeff M k hM c φ j • v j

noncomputable def clause33TargetPart {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ) (T : Finset J) : QState I :=
  ∑ j, clause33TargetCoeff M k hM c φ T j • v j

noncomputable def clause33Leakage {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ) (T : Finset J) : QState I :=
  ∑ j, clause33LeakCoeff M k hM c φ T j • v j

noncomputable def clause33ReflectedState {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ) (T : Finset J) : QState I :=
  clause33TargetPart M k hM v c φ T - clause33Leakage M k hM v c φ T

noncomputable def clause33Contraction (M : ℕ) (η : ℝ) : ℝ := Real.sqrt 10 / ((M : ℝ)^2 * η^2)

noncomputable def clause33ForwardWord {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 2 ≤ M) : List (AdjointStep (Fin M × (Bool × I))) :=
  repeatWord (sinEnvelopeForwardWord (I := I) M hM) k

noncomputable def clause33InverseWord {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 2 ≤ M) : List (AdjointStep (Fin M × (Bool × I))) :=
  (clause33ForwardWord (I := I) M k hM).map swapQueries

def Clause33CoherentFilterResidual : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ),
    W ∈ Matrix.unitaryGroup I ℂ → 0 < η → 1 ≤ (M : ℝ) * η →
    (∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0) →
    (∑ j, ‖c j‖ ^ 2) = 1 →
    (∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) →
    (∀ j ∈ T, phaseDistance (φ j) 0 = 0) →
    (∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) →
    let a := ∑ j ∈ T, ‖c j‖ ^ 2
    let ρ := clause33Contraction M η

    (W *ᵥ clause33FilteredState M k (by omega) v c φ =
      ∑ j, (c j * clause33Pass M k (by omega) (φ j) *
        Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ))) • v j) ∧

    (∀ j, j ∉ T → ‖clause33Pass M k (by omega) (φ j)‖ ≤ ρ ^ k) ∧

    ‖toEuclidean_fromVec (clause33Leakage M k (by omega) v c φ T)‖ ≤ ρ ^ k * Real.sqrt (1 - a) ∧

    ‖toEuclidean_fromVec (clause33FilteredState M k (by omega) v c φ -
        clause33ReflectedState M k (by omega) v c φ T)‖ ≤ 2 * ρ ^ k * Real.sqrt (1 - a) ∧

    (∃ (s : ℂ), (∀ j ∈ T, clause33Pass M k (by omega) (φ j) = s) ∧
      clause33TargetPart M k (by omega) v c φ T = s • spectralTargetState v c T ∧
      ‖s‖ ≤ 1) ∧

    ‖toEuclidean_fromVec (clause33TargetPart M k (by omega) v c φ T -
        spectralTargetState v c T)‖ ≤ 2 * Real.sqrt a ∧

    adjointQueryCount (clause33ForwardWord (I := I) M k hM) = k * (M - 1) ∧
    adjointGateCount (clause33ForwardWord (I := I) M k hM) = k * (2 * (M - 1) + 2) ∧
    adjointQueryCount (clause33InverseWord (I := I) M k hM) = k * (M - 1) ∧
    adjointGateCount (clause33InverseWord (I := I) M k hM) = k * (2 * (M - 1) + 2)

theorem clause33_norm_smul {I : Type} [Fintype I] (a : ℂ) (x : QState I) :
    ‖toEuclidean_fromVec (a • x)‖ = ‖a‖ * ‖toEuclidean_fromVec x‖ := by
  have hs : ‖toEuclidean_fromVec (a • x)‖ ^ 2
      = (‖a‖ * ‖toEuclidean_fromVec x‖) ^ 2 := by
    have h1 : (∑ i, ‖(a • x) i‖ ^ 2) = ∑ i, (‖a‖ * ‖x i‖) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.smul_apply, norm_smul]
    have h2 : (∑ i, (‖a‖ * ‖x i‖) ^ 2) = ∑ i, ‖a‖ ^ 2 * ‖x i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow]
    have h3 : (∑ i, ‖a‖ ^ 2 * ‖x i‖ ^ 2) = ‖a‖ ^ 2 * (∑ i, ‖x i‖ ^ 2) :=
      (Finset.mul_sum Finset.univ _ _).symm
    have h4 : (∑ i, ‖x i‖ ^ 2) = ‖toEuclidean_fromVec x‖ ^ 2 :=
      (norm_toEuclidean_fromVec_sq x).symm
    rw [norm_toEuclidean_fromVec_sq, h1, h2, h3, h4]
    ring
  have h1 := Real.sqrt_le_sqrt (le_of_eq hs)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h1
  have h2 := Real.sqrt_le_sqrt (le_of_eq hs.symm)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h2
  exact le_antisymm h1 h2

theorem clause33_smul_sum {I : Type} [Fintype I] (a : ℂ) (w : I → QState I) :
    (∑ j, a • w j) = a • (∑ j, w j) :=
  (Finset.smul_sum (s := Finset.univ) (f := w)).symm

theorem clause33_ite_sum {I : Type} [Fintype I] (S : Finset I) (f : I → QState I) :
    (∑ j, if j ∈ S then f j else 0) = ∑ j ∈ S, f j := by
  rw [Finset.sum_ite_mem Finset.univ S f, Finset.univ_inter]

def coreSpectralClause6Prop : Prop :=
  WalkSpectralClause6Prop ∧ Clause6RowAccessResidual ∧ Clause6BusySpectrumTransport

def coreSpectralClause32Prop : Prop := WalkSpectralClause32Prop ∧ Clause32ScheduleResidual

def coreSpectralClause33Prop : Prop := WalkSpectralClause33Prop ∧ Clause33CoherentFilterResidual

def coreSpectralTunableQueryProp : Prop :=
    WalkSpectralTunableQueryProp ∧ TunableQueryClassifierResidual

def coreSpectralOptimizedTunableProp : Prop := WalkSpectralOptimizedTunableProp

def clause36FailureSet {O : Type} [Fintype O] [DecidableEq O] (S : Finset O) : Finset O :=
  Finset.univ \ S

def Clause36DiamondStabilityResidual : Prop :=
  ∀ (O : Type) [Fintype O] [DecidableEq O] (D E R : ℕ) (J : Instrument O D E)
    (S : Finset O) (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (p ε : ℝ),
    ρ.PosSemidef → τ.PosSemidef → (Matrix.trace ρ).re = (Matrix.trace τ).re →
    p ≤ (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re →
    0 < ε → ε < p / 2 → Matrix.traceNorm (ρ - τ) ≤ ε →
    0 < (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re ∧
    Matrix.traceNorm (normalizedPositiveBranch (tensorLeft (selectiveMap J S) ρ) -
      normalizedPositiveBranch (tensorLeft (selectiveMap J S) τ)) ≤ ε / p ∧
    Matrix.traceNorm (tensorLeft (selectiveMap J (clause36FailureSet S)) (ρ - τ))
      ≤ Matrix.traceNorm (ρ - τ) ∧
    |(Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) ρ)).re
        - (Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) τ)).re| ≤ ε / 2

def coreSpectralClause36Prop : Prop := WalkSpectralClause36Prop ∧ Clause36DiamondStabilityResidual

def Clause37OperatorFilterResidual : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (T : Finset J) (η : ℝ) (W : Matrix I I ℂ),
    W ∈ Matrix.unitaryGroup I ℂ → 0 < η →
    (∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0) →
    (∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) →
    (∀ j ∈ T, phaseDistance (φ j) 0 = 0) →
    (∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) →
    (∑ j ∈ T, ‖c j‖ ^ 2) ≤ ‖toEuclidean_fromVec
        (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j)‖ ^ 2 ∧
    ‖toEuclidean_fromVec
        (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j)‖ ^ 2
      ≤ (∑ j ∈ T, ‖c j‖ ^ 2) +
        ((1 / (2 * (M : ℝ) * η)) ^ k) ^ 2 *
          ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2)) ∧
    ‖toEuclidean_fromVec
        (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j -
          spectralTargetState v c T)‖
      ≤ (1 / (2 * (M : ℝ) * η)) ^ k *
        Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2)) ∧
    ‖toEuclidean_fromVec
        (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j -
          spectralTargetState v c T)‖
      ≤ (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖ ∧
    ‖toEuclidean_fromVec
        (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j -
          spectralTargetState v c T)‖
      ≤ 2 * (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖

def coreSpectralClause37Prop : Prop := WalkSpectralClause37Prop ∧ Clause37OperatorFilterResidual

noncomputable def clause39UniformWord {I : Type} [Fintype I] [DecidableEq I]
    (M s : ℕ) : List (AdjointStep (Fin M × (Bool × I))) :=
  repeatWord (phaseCompileCircuit (countedPhaseCircuit (I := I) M)) (2 * s)

theorem clause39_repeat_length {H : Type} (w : List (AdjointStep H)) (n : ℕ) :
    (repeatWord w n).length = n * w.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
    have hrw : repeatWord w (Nat.succ n) = w ++ repeatWord w n := by
      simp [repeatWord]
    rw [hrw, List.length_append, ih]
    ring

theorem clause39_repeat_queryCount {H : Type} (w : List (AdjointStep H)) (n : ℕ) :
    adjointQueryCount (repeatWord w n) = n * adjointQueryCount w := by
  induction n with
  | zero => simp [repeatWord, adjointQueryCount]
  | succ n ih =>
    have hrw : repeatWord w (Nat.succ n) = w ++ repeatWord w n := by
      simp [repeatWord]
    rw [hrw, adjointQueryCount_append, ih]
    ring

theorem clause39_repeat_gateCount {H : Type} (w : List (AdjointStep H)) (n : ℕ) :
    adjointGateCount (repeatWord w n) = n * adjointGateCount w := by
  induction n with
  | zero => simp [repeatWord, adjointGateCount]
  | succ n ih =>
    have hrw : repeatWord w (Nat.succ n) = w ++ repeatWord w n := by
      simp [repeatWord]
    rw [hrw, adjointGateCount_append, ih]
    ring

def Clause39UniformSequenceResidual : Prop :=
  ∀ (M s l : ℕ) (ε δ : ℝ) (I : Type) [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ),
    2 ≤ M → 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 / 2 →
    M = 2 ^ (l + 2) → δ = ((2 : ℝ) ^ (-(l + 2 : ℕ) : ℤ)) →
    36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 ≤ s →
    U *ᵥ ψ = eigenPhase φ • ψ →
    (clause39UniformWord (I := I) M s).length =
        2 * s * (phaseCompileCircuit (countedPhaseCircuit (I := I) M)).length ∧
    adjointQueryCount (clause39UniformWord (I := I) M s) = 2 * s * (M - 1) ∧
    adjointGateCount (clause39UniformWord (I := I) M s) = 2 * s * (2 * (M - 1) + 2) ∧
    (1 / (M : ℝ)) = ((2 : ℝ) ^ (-(l + 2 : ℕ) : ℤ)) ∧
    (eigenphaseSampleLaw φ s).probEvent (L := 1)
        (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ) ≤ ε

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def cfSteps : ℕ → ℕ → ℕ
  | a, 0 => 0
  | a, b + 1 => 1 + cfSteps (b + 1) (a % (b + 1))
termination_by p q => q
decreasing_by
  simp_wf
  have h : a % (b + 1) < b + 1 := Nat.mod_lt a (by omega)
  omega

def Clause39ContinuedFractionResidual : Prop :=
  ∀ (p q l : ℕ) (_h1 : 1 ≤ q) (_h2 : q ≤ 2 ^ (l + 2)),
    fib (cfSteps p q + 1) ≤ q ∧ cfSteps p q ≤ 2 * l + 5

def coreSpectralClause39Prop : Prop :=
  WalkSpectralClause39Prop ∧ Clause39UniformSequenceResidual ∧ Clause39ContinuedFractionResidual

end Qatlib.Concepts.WalkSearch.FrameSpectral
