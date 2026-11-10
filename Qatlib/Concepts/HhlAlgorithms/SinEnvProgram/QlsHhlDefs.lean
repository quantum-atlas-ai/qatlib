/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseRetry
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseConsumers
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridgesDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

def qlsBitWidth (N : ℕ) : ℕ := Nat.log2 N + 1

def qlsZeroReg (n : ℕ) : Reg n := fun _ => false

def qlsRegEmbed (M : ℕ) (i : Fin M) : Reg (qlsBitWidth M) :=
  fun b => i.val.testBit b.1

def qlsLabelEmbed (M w : ℕ) : Fin M → Reg w :=
  fun i t => if ht : t.1 < qlsBitWidth M then i.val.testBit t.1 else false

def qlsDataEmbed (D w : ℕ) : Fin D → Reg w :=
  fun i t => if ht : t.1 < qlsBitWidth D then i.val.testBit t.1 else false

def qlsControlEmbed (D w : ℕ) : Bool × Fin D → Reg w :=
  fun p t =>
    if t.1 = 0 then p.1
    else if ht : t.1 ≤ qlsBitWidth D then p.2.val.testBit (t.1 - 1) else false

noncomputable def qlsZeroExtend {M : ℕ} (ψ : QState (Fin M)) :
    QState (Reg (qlsBitWidth M)) :=
  fun x => if h : ∃ i, qlsRegEmbed M i = x then ψ h.choose else 0

noncomputable def qlsZeroExtendTo (M w : ℕ) (ψ : QState (Fin M)) :
    QState (Reg w) :=
  fun x => if hc : ∃ i, qlsLabelEmbed M w i = x then ψ hc.choose else 0

noncomputable def qlsWordMatrix (n : ℕ) (W : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ := (W.map (finiteCodeMatrix n)).reverse.prod

noncomputable def qlsWordRunState {n : ℕ} (W : List FiniteGateCode)
    (ψ : QState (Reg n)) : QState (Reg n) :=
  Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n W) ψ

noncomputable def qlsCompressMatrix {n : ℕ} {I : Type} [Fintype I] (e : I → Reg n)
    (G : Matrix (Reg n) (Reg n) ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => G (e i) (e j)

def qlsSystemRestrict {m n : ℕ} (hmn : m ≤ n) (z : Reg n) : Reg m :=
  fun i => z (Fin.castLE hmn i)

def qlsWorkZero (m : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → z i = false

def qlsResidualZero (m flag : ℕ) {n : ℕ} (z : Reg n) : Prop :=
  ∀ i : Fin n, m ≤ i.1 → i.1 ≠ flag → z i = false

def qlsSuccessEvent (n flag : ℕ) : Finset (Reg n) :=
  if h : flag < n then Finset.univ.filter fun z => z ⟨flag, h⟩ = true else ∅

noncomputable def qlsSuccessSystemVector {n : ℕ} (W : List FiniteGateCode)
    (flag m : ℕ) (hmn : m ≤ n) : QState (Reg m) :=
  fun x => ∑ z ∈ qlsSuccessEvent n flag,
    if qlsResidualZero m flag z ∧ qlsSystemRestrict hmn z = x then
      qlsWordRunState W (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n)) z else 0

noncomputable def qlsConditionalSystemOutput {n : ℕ} (W : List FiniteGateCode)
    (flag m : ℕ) (hmn : m ≤ n) : QState (Reg m) :=
  sinEnvelopeConditionalOutput (qlsSuccessSystemVector W flag m hmn)

def qlsSumEquiv (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) where
  toFun x := Sum.elim (fun i => Fin.castAdd n i) (fun i => Fin.natAdd m i) x
  invFun k :=
    if h : (k : ℕ) < m then Sum.inl ⟨k, h⟩
    else Sum.inr ⟨k - m, by omega⟩
  left_inv := by
    intro x
    cases x with
    | inl i =>
        simp only [Sum.elim_inl]
        have h : ((Fin.castAdd n i : Fin (m + n)) : ℕ) < m := by simp
        simp
    | inr i =>
        simp only [Sum.elim_inr]
        have h : ¬ ((Fin.natAdd m i : Fin (m + n)) : ℕ) < m := by
          simp [Fin.natAdd]
        simp [Fin.natAdd]
  right_inv := by
    intro k
    by_cases h : (k : ℕ) < m
    · simp only [h, dif_pos, Sum.elim_inl]
      simp
    · have hk : m ≤ (k : ℕ) := by omega
      simp only [h, dif_neg, not_false_iff, Sum.elim_inr]
      apply Fin.ext
      show (m : ℕ) + ((k : ℕ) - m) = (k : ℕ)
      omega

def HasConditionWindow {N : ℕ} (A : Operator N) (κ : ℝ) : Prop :=
  1 ≤ κ ∧ ∀ v : QState (Fin N),
    ‖toEuclidean_fromVec v‖ ≤ κ * ‖toEuclidean_fromVec (A *ᵥ v)‖

def qlsSparseHermitianBounded {N : ℕ}
    (dat : SparseOracleData (Fin N) (Fin N)) : Prop :=
  (dat.matrix).IsHermitian ∧ ‖(dat.matrix : Operator N)‖ ≤ 1

def HasFullRankWindow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (κ : ℝ) : Prop :=
  1 ≤ κ ∧ ∀ v : QState (Fin n),
    ‖toEuclidean_fromVec v‖ ≤ κ * ‖toEuclidean_fromVec (A *ᵥ v)‖

structure SparseHHLRequest where

  dim : ℕ

  sparsity : ℕ

  kappa : ℝ

  eps : ℝ

  data : SparseOracleData (Fin dim) (Fin dim)

  inputPrep : List FiniteGateCode

noncomputable def qlsPreparedInput (r : SparseHHLRequest) : QState (Fin r.dim) :=
  fun i => qlsWordRunState r.inputPrep (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (qlsBitWidth r.dim)))
    (qlsRegEmbed r.dim i)

def SparseHHLRequest.Legal (r : SparseHHLRequest) : Prop :=
  0 < r.sparsity ∧ 1 ≤ r.kappa ∧ 0 < r.eps ∧ r.eps ≤ 1 ∧
    r.data.IsSparseBounded r.sparsity 1 ∧
    qlsSparseHermitianBounded r.data ∧
    HasConditionWindow (r.data.matrix) r.kappa ∧
    finiteWordLegal (qlsBitWidth r.dim) r.inputPrep = true ∧
    Normalized (qlsPreparedInput r)

structure SparseHHLProgram where

  wires : SparseHHLRequest → ℕ

  word : SparseHHLRequest → List FiniteGateCode

  successWire : SparseHHLRequest → ℕ

  bitTime : SparseHHLRequest → ℕ

def SparseHHLProgram.LegalAt (P : SparseHHLProgram) (r : SparseHHLRequest) : Prop :=
  finiteWordLegal (P.wires r) (P.word r) = true ∧
    P.successWire r < P.wires r ∧
    qlsBitWidth r.dim < P.wires r ∧
    (P.word r).length ≤ P.bitTime r

noncomputable def SparseHHLProgram.output (P : SparseHHLProgram)
    (r : SparseHHLRequest) (h : qlsBitWidth r.dim ≤ P.wires r) :
    QState (Reg (qlsBitWidth r.dim)) :=
  qlsConditionalSystemOutput (P.word r) (P.successWire r) (qlsBitWidth r.dim) h

def SparseHHLProgram.SolvesAt (P : SparseHHLProgram) (p₀ : ℝ)
    (r : SparseHHLRequest) : Prop :=
  p₀ ≤ MeasureProb (qlsWordRunState (P.word r) (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (P.wires r))))
      (qlsSuccessEvent (P.wires r) (P.successWire r)) ∧
    ∃ φ : QState (Fin r.dim),
      leastSquaresDirection (r.data.matrix) (qlsPreparedInput r) = some φ ∧
        ∀ h : qlsBitWidth r.dim ≤ P.wires r,
          ‖toEuclidean_fromVec (P.output r h - qlsZeroExtend φ)‖ ≤ r.eps

def qlsSourceRuntimeScale (κ s logN T_B invEps : ℕ) : ℕ :=
  κ * T_B + κ * κ * s * s * logN * invEps

def qlsSourceLogParameter (κ s logN T_B invEps : ℕ) : ℕ :=
  max (max (max (max κ s) logN) T_B) (max invEps 2)

def SparseHHLProgram.SourceScaleBounded (P : SparseHHLProgram) : Prop :=
  ∃ (c e : ℕ), ∀ r : SparseHHLRequest, r.Legal →
    P.bitTime r ≤ c * qlsSourceRuntimeScale (Nat.ceil r.kappa) (r.sparsity + 1)
        (qlsBitWidth r.dim) (r.inputPrep.length + 1) (Nat.ceil (1 / r.eps) + 1) *
      (qlsSourceLogParameter (Nat.ceil r.kappa) (r.sparsity + 1) (qlsBitWidth r.dim)
        (r.inputPrep.length + 1) (Nat.ceil (1 / r.eps) + 1) + 1) ^ e ∧
      P.wires r ≤ qlsBitWidth r.dim + c *
        (qlsSourceLogParameter (Nat.ceil r.kappa) (r.sparsity + 1) (qlsBitWidth r.dim)
          (r.inputPrep.length + 1) (Nat.ceil (1 / r.eps) + 1) + 1) ^ e

structure SinEnvelopePrepFamily where

  wireCount : ℕ → ℕ → ℕ

  word : ℕ → ℕ → List FiniteGateCode

def SinEnvelopePrepFamily.PreparesAt (P : SinEnvelopePrepFamily) (M k : ℕ)
    (hM : 2 ≤ M) : Prop :=
  finiteWordLegal (P.wireCount M k) (P.word M k) = true ∧
    M ≤ 2 ^ (P.wireCount M k) ∧
    ∀ h2 : M ≤ 2 ^ (P.wireCount M k),
      ‖toEuclidean_fromVec (qlsWordRunState (P.word M k)
          (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (P.wireCount M k))) -
          qlsZeroExtendTo M (P.wireCount M k) (sinEnvelopeState M))‖
        ≤ (1 / 2 : ℝ) ^ k ∧
      ‖qlsCompressMatrix (qlsLabelEmbed M (P.wireCount M k))
          (qlsWordMatrix (P.wireCount M k) (P.word M k)) - sinEnvelopePrep M hM‖
        ≤ (1 / 2 : ℝ) ^ k

def SinEnvelopePrepFamily.PolyBounded (P : SinEnvelopePrepFamily) : Prop :=
  ∃ (c e : ℕ), ∀ (M k : ℕ), 2 ≤ M →
    (P.word M k).length ≤ c * (qlsBitWidth M + k + 1) ^ e ∧
      P.wireCount M k ≤ c * (qlsBitWidth M + k + 1) ^ e

noncomputable def qlsPhaseCircuitWith {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (Pm : Matrix (Fin M) (Fin M) ℂ) :
    Circuit (Fin M × (Bool × I)) :=
  [Step.gate (TensorGate Pm (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
    phaseThresholdLoop M (M - 1) ++
    [Step.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]

noncomputable def qlsForwardWordWith {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (Pm : Matrix (Fin M) (Fin M) ℂ) :
    List (AdjointStep (Fin M × (Bool × I))) :=
  ((qlsPhaseCircuitWith (I := I) M hM Pm).map stepToAdjoint).reverse

noncomputable def qlsSinEnvelopeWordWith {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (B : Operator D) (Pm : Matrix (Fin M) (Fin M) ℂ) :
    List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D)))) :=
  adjointCircuit (qlsForwardWordWith M hM Pm) ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopeFlagGate d))] ++
    qlsForwardWordWith M hM Pm ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopePrepMain B))]

noncomputable def qlsSinEnvelopeRunWith {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (Pm : Matrix (Fin M) (Fin M) ℂ) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  evaluate (sinEnvelopeOracleLift U) (qlsSinEnvelopeWordWith M hM d B Pm) *ᵥ
    TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))

structure SparseAccessSystem where

  dim : ℕ

  data : SparseOracleData (Fin dim) (Fin dim)

  wireCount : ℕ

  rowOracle : Matrix (Reg wireCount) (Reg wireCount) ℂ

  colOracle : Matrix (Reg wireCount) (Reg wireCount) ℂ

  valueOracle : Matrix (Reg wireCount) (Reg wireCount) ℂ

def SparseAccessSystem.Legal (S : SparseAccessSystem) (s : ℕ) : Prop :=
  0 < s ∧ 1 + qlsBitWidth S.dim ≤ S.wireCount ∧
    S.data.IsSparseBounded s 1 ∧ qlsSparseHermitianBounded S.data ∧
    S.rowOracle ∈ Matrix.unitaryGroup (Reg S.wireCount) ℂ ∧
    S.colOracle ∈ Matrix.unitaryGroup (Reg S.wireCount) ℂ ∧
    S.valueOracle ∈ Matrix.unitaryGroup (Reg S.wireCount) ℂ

structure SparseHamiltonianSynthesis (S : SparseAccessSystem) where

  forward : List (SparsePipelineStep S.wireCount)

  backward : List (SparsePipelineStep S.wireCount)

noncomputable def SparseHamiltonianSynthesis.matrix
    (S : SparseAccessSystem) (Y : SparseHamiltonianSynthesis S)
    (ps : List (SparsePipelineStep S.wireCount)) :
    Matrix (Reg S.wireCount) (Reg S.wireCount) ℂ :=
  sparsePipelineMatrix S.rowOracle S.colOracle S.valueOracle ps

def SparseHamiltonianSynthesis.ImplementsAt (S : SparseAccessSystem)
    (Y : SparseHamiltonianSynthesis S) (eig : Fin S.dim → ℝ) (V : Operator S.dim)
    (k : ℕ) : Prop :=
  continuousHHLMatrix eig V = S.data.matrix →
    ‖qlsCompressMatrix (qlsDataEmbed S.dim S.wireCount)
        (Y.matrix S Y.forward) - continuousHHLOracle eig V‖ ≤ (1 / 2 : ℝ) ^ k ∧
      ‖qlsCompressMatrix (qlsDataEmbed S.dim S.wireCount)
          (Y.matrix S Y.backward) - (continuousHHLOracle eig V)ᴴ‖ ≤ (1 / 2 : ℝ) ^ k

def SparseHamiltonianSynthesis.BudgetBounded (S : SparseAccessSystem)
    (Y : SparseHamiltonianSynthesis S) (s k : ℕ) : Prop :=
  ∃ (c e : ℕ),
    (sparsePipelineLedger S.data Y.forward).positionCalls ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.forward).valueCalls ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.forward).elementaryGates ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.forward).classicalBitOps ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.backward).positionCalls ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.backward).valueCalls ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.backward).elementaryGates ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    (sparsePipelineLedger S.data Y.backward).classicalBitOps ≤
      c * (s + 1) ^ 2 * (qlsBitWidth S.dim + k + 2) ^ e ∧
    S.wireCount ≤ qlsBitWidth S.dim + c * (qlsBitWidth S.dim + k + 2) ^ e

noncomputable def qlsSynthAccessRun {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (W : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  evaluate (sinEnvelopeOracleLift W) (sinEnvelopeHHLWord M hM d B) *ᵥ
    TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))

noncomputable def qlsSynthAccessFactor (M k : ℕ) : ℝ :=
  (1 + (1 / 2 : ℝ) ^ k) ^ (4 * (M - 1) + 6)

noncomputable def qlsScaledDilation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) ((1 / 4 : ℂ) • A)
    (((1 / 4 : ℂ) • A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)

def qlsDilationInput {m n : ℕ} (b : QState (Fin m)) : QState (Fin m ⊕ Fin n) :=
  Sum.elim b 0

def qlsDilationExtract {m n : ℕ} (ψ : QState (Fin m ⊕ Fin n)) : QState (Fin n) :=
  fun j => ψ (Sum.inr j)

noncomputable def qlsDilationWorkspaceExtract {m n M : ℕ} (hM : 0 < M)
    (v : QState (Fin M × (Bool × (Bool × Fin (m + n))))) : QState (Fin n) :=
  fun i => v (⟨0, hM⟩, (false, (true, qlsSumEquiv m n (Sum.inr i))))

structure LeastSquaresDilationInput where

  rows : ℕ

  cols : ℕ

  data : SparseOracleData (Fin rows) (Fin cols)

  kappa : ℝ

  rhs : QState (Fin rows)

  rhsPrep : List FiniteGateCode

noncomputable def qlsDilationPreparedRhs (r : LeastSquaresDilationInput) :
    QState (Fin r.rows) :=
  fun i => qlsWordRunState r.rhsPrep (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (qlsBitWidth r.rows)))
    (qlsRegEmbed r.rows i)

def LeastSquaresDilationInput.Legal (r : LeastSquaresDilationInput) (s : ℕ) : Prop :=
  0 < s ∧ 1 ≤ r.kappa ∧ r.data.IsSparseBounded s 1 ∧
    HasFullRankWindow r.data.matrix r.kappa ∧
    ‖(r.data.matrix)ᴴ * r.data.matrix‖ ≤ 1 ∧ Normalized r.rhs ∧
    finiteWordLegal (qlsBitWidth r.rows) r.rhsPrep = true ∧
    qlsDilationPreparedRhs r = r.rhs

structure QlsPrecisionCertificate where

  gapCert : ℚ

  overlapCert : ℚ

  phaseDigits : ℕ

  rotationDigits : ℕ

def QlsPrecisionCertificate.Legal (c : QlsPrecisionCertificate) : Prop :=
  0 < c.gapCert ∧ c.gapCert ≤ 1 / 4 ∧ 0 < c.overlapCert ∧ c.overlapCert ≤ 1 ∧
    0 < c.phaseDigits ∧ 0 < c.rotationDigits

structure RationalHHLBackend where

  wireCount : ℕ → ℕ → ℕ

  selectWord : (D : ℕ) → QuantizedMatrixInput (Fin D) (Fin D) → ℕ →
    List FiniteGateCode

  inverseWord : (D : ℕ) → QuantizedMatrixInput (Fin D) (Fin D) → ℕ →
    List FiniteGateCode

def sinEnvelopeJointSet (D M : ℕ) :
    Finset (Fin M × (Bool × (Fin 3 × Fin D))) :=
  Finset.univ.filter (fun p => p.2.2.1 = 1 ∨ p.2.2.1 = 2)

noncomputable def sinEnvelopeJointIdealMass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) : ℝ :=
  sinEnvelopeIdealMass M hM eig V B j d

noncomputable def sinEnvelopeActualCleanOp {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (d : ℝ) (B : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin D) ℂ :=
  Matrix.of fun p j => sinEnvelopeHHLRun M hM U d B j p

noncomputable def sinEnvelopeIdealCleanOp {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin D) ℂ :=
  Matrix.of fun p j => sinEnvelopeHHLIdeal M hM eig V d B j p

def CleanInputOperatorBound {D M : ℕ}
    (E : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin D) ℂ) (c : ℝ) : Prop :=
  ∀ v : QState (Fin D),
    ‖toEuclidean_fromVec (E *ᵥ v)‖ ≤ c * ‖toEuclidean_fromVec v‖

structure SignedSinEnvelopeFilter where

  filterF : ℝ → ℝ → ℝ

  filterG : ℝ → ℝ → ℝ

def SignedSinEnvelopeFilter.Consistent (F : SignedSinEnvelopeFilter) : Prop :=
  (∀ (d θ : ℝ), 0 < d → F.filterF d θ = -(F.filterF d (-θ))) ∧
    (∀ (d θ : ℝ), 0 < d → F.filterG d θ = F.filterG d (-θ)) ∧
    (∀ d : ℝ, 0 < d → F.filterF d 0 = 0 ∧ F.filterG d 0 = 1 / 2) ∧
    (∀ (d θ : ℝ), 0 < d → 0 ≤ θ →
      F.filterF d θ = sinEnvelopeFilterF d θ ∧
        F.filterG d θ = sinEnvelopeFilterG d θ) ∧
    (∀ (d θ : ℝ), 0 < d → F.filterF d θ ^ 2 + F.filterG d θ ^ 2 ≤ 1)

noncomputable def SignedSinEnvelopeFilter.hVector
    (F : SignedSinEnvelopeFilter) (d θ : ℝ) : QState (Fin 3) :=
  fun s =>
    if s = 0 then (Real.sqrt (1 - F.filterF d θ ^ 2 - F.filterG d θ ^ 2) : ℂ)
    else if s = 1 then (F.filterF d θ : ℂ) else (F.filterG d θ : ℂ)

structure SignedSinEnvelopeProgram where

  filter : SignedSinEnvelopeFilter

  rotation : ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℂ

noncomputable def SignedSinEnvelopeProgram.flagGate
    (P : SignedSinEnvelopeProgram) {D M : ℕ} (d : ℝ) :
    Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
    (TensorGate (BlockDiag (fun z : Fin M =>
      P.rotation d (sinEnvelopeDecode M z))) (1 : Operator D))

noncomputable def SignedSinEnvelopeProgram.word
    (P : SignedSinEnvelopeProgram) {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D)))) :=
  adjointCircuit (sinEnvelopeForwardWord M hM) ++
    [AdjointStep.gate (sinEnvelopeLiftGate (P.flagGate d))] ++
    sinEnvelopeForwardWord M hM ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopePrepMain B))]

noncomputable def SignedSinEnvelopeProgram.run
    (P : SignedSinEnvelopeProgram) {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D)
    (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  evaluate (sinEnvelopeOracleLift U) (P.word M hM d B) *ᵥ
    TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 3)) (Qatlib.Foundations.PureStateMath.Ket j)))

noncomputable def SignedSinEnvelopeProgram.ideal
    (P : SignedSinEnvelopeProgram) {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false)
    (fun p : Fin 3 × Fin D =>
      ((V * Matrix.diagonal (fun i => P.filter.hVector d (eig i) p.1) * Vᴴ) *ᵥ
        (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) p.2))

noncomputable def qlsWellBranch {D M : ℕ}
    (v : QState (Fin M × (Bool × (Fin 3 × Fin D)))) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  fun p => if p.2.2.1 = 1 then v p else 0

noncomputable def SignedSinEnvelopeProgram.wellTarget
    (P : SignedSinEnvelopeProgram) {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  qlsWellBranch (P.ideal M hM eig V d B j)

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
