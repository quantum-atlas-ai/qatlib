/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleCore
import Mathlib.Data.Matrix.Block
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! The concrete nonnormal hard input family: a common norm-two Jordan core
and one marked complex scalar, with exact alpha=2 Halmos input oracles.
Unitarity, compression, nonnormality, norm, actual controlled/adjoint modes,
workspace extension and the finite-query hybrid are derived from these matrices.

Finite coordinate equivalences depend only on dimension/workspace. They are
mathematical basis labels, not an effective basis/state-preparation compiler.
The true numerical-range maximum/support, angular visibility, finite-program
compilation and physical block-output/majority reduction remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
/-! Original OQ #132 restricted finite shared-port hard family. This is an
OQ access-boundary extension for the numerical-range normalization question,
not a claim proved by Lorist and Schwenninger. The model gives no free maximum
and no general-machine or given-maximum impossibility theorem. -/
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator

/-- Construction for halmos in the marked halmos oracle model. -/
def halmos (z : ℂ) : Matrix Bool Bool ℂ
  | false,false => z
  | false,true => (Real.sqrt (1-Complex.normSq z) : ℝ)
  | true,false => (Real.sqrt (1-Complex.normSq z) : ℝ)
  | true,true => -star z

/-- The restricted-access construction satisfies `halmos_unitary` under the complete displayed premises. -/
theorem halmos_unitary (z : ℂ) (hz : Complex.normSq z≤1) : halmos z∈Matrix.unitaryGroup Bool ℂ := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hz)
  rw [Complex.normSq_apply] at hs
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [halmos,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Complex.mul_re,Complex.mul_im,RCLike.star_def,Complex.normSq_apply] <;> nlinarith

/-- The restricted-access construction satisfies `blockDiagonal_unitary` under the complete displayed premises. -/
private theorem blockDiagonal_unitary {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (U : K → Matrix I I ℂ) (hU : ∀ k,U k∈Matrix.unitaryGroup I ℂ) :
    Matrix.blockDiagonal U∈Matrix.unitaryGroup (I × K) ℂ := by
  have hh (k : K) : U k*(U k).conjTranspose=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hU k)
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose,←Matrix.blockDiagonal_mul]
  simp_rw [hh]
  exact Matrix.blockDiagonal_one

/-- The common input block is the exact dilation of the norm-two Jordan core. -/
def core : Matrix (Bool × Bool) (Bool × Bool) ℂ := Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.oracle 1 0
/-- The restricted-access construction satisfies `core_unitary` under the complete displayed premises. -/
private theorem core_unitary : core∈Matrix.unitaryGroup (Bool × Bool) ℂ :=
  Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.oracle_unitary 1 0 (by norm_num)

/-- Construction for data Oracle in the marked halmos oracle model. -/
def dataOracle {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (Bool × Fin N) (Bool × Fin N) ℂ :=
  Matrix.blockDiagonal (fun j => if j=w then halmos z else halmos 0)

/-- The restricted-access construction satisfies `dataOracle_unitary` under the complete displayed premises. -/
theorem dataOracle_unitary {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) :
    dataOracle w z∈Matrix.unitaryGroup (Bool × Fin N) ℂ := by
  apply blockDiagonal_unitary
  intro j
  by_cases hj : j=w
  · simpa [hj] using halmos_unitary z hz
  · simpa [hj] using halmos_unitary 0 (by norm_num)


/-- Abbreviation for Basis in the marked halmos oracle model. -/
abbrev Basis (N : ℕ) := (Bool × Bool) ⊕ (Bool × Fin N)
/-- Abbreviation for System in the marked halmos oracle model. -/
abbrev System (N : ℕ) := Bool ⊕ Fin N

/-- Construction for oracle Raw in the marked halmos oracle model. -/
def oracleRaw {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (Basis N) (Basis N) ℂ :=
  Matrix.fromBlocks core 0 0 (dataOracle w z)

/-- Construction for baseline Raw in the marked halmos oracle model. -/
def baselineRaw (N : ℕ) : Matrix (Basis N) (Basis N) ℂ :=
  Matrix.fromBlocks core 0 0 (Matrix.blockDiagonal (fun _ : Fin N => halmos 0))

/-- The restricted-access construction satisfies `oracleRaw_unitary` under the complete displayed premises. -/
theorem oracleRaw_unitary {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) :
    oracleRaw w z∈Matrix.unitaryGroup (Basis N) ℂ := by
  have hc : core*core.conjTranspose=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp core_unitary
  have hd : dataOracle w z*(dataOracle w z).conjTranspose=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (dataOracle_unitary w z hz)
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,oracleRaw,
    Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  simp [hc,hd]

/-- The restricted-access construction satisfies `oracleRaw_zero` under the complete displayed premises. -/
theorem oracleRaw_zero {N : ℕ} (w : Fin N) : oracleRaw w 0=baselineRaw N := by
  simp [oracleRaw,baselineRaw,dataOracle]

/-- Construction for split Basis in the marked halmos oracle model. -/
def splitBasis (N : ℕ) : (Bool × System N) ≃ Basis N where
  toFun p := match p.2 with
    | .inl b => .inl (p.1,b)
    | .inr j => .inr (p.1,j)
  invFun p := match p with
    | .inl q => (q.1,.inl q.2)
    | .inr q => (q.1,.inr q.2)
  left_inv p := by rcases p with ⟨a,s⟩; cases s <;> rfl
  right_inv p := by cases p <;> rfl

/-- Construction for oracle in the marked halmos oracle model. -/
def oracle {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (Bool × System N) (Bool × System N) ℂ :=
  relabelGate (splitBasis N).symm (oracleRaw w z)

/-- The restricted-access construction satisfies `oracle_unitary` under the complete displayed premises. -/
theorem oracle_unitary {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) :
    oracle w z∈Matrix.unitaryGroup (Bool × System N) ℂ :=
  (relabelGate_mem_unitaryGroup (splitBasis N).symm (oracleRaw w z)).mpr (oracleRaw_unitary w z hz)

/-- Construction for address in the marked halmos oracle model. -/
def address {N : ℕ} : Basis N → Option (Fin N)
  | .inl _ => none
  | .inr q => some q.2

/-- Both rows and columns outside the mark are unchanged, so adjoint queries
can use the same data fiber as forward queries. -/
theorem oracleRaw_unmarked_entry {N : ℕ} (w : Fin N) (z : ℂ) (p q : Basis N)
    (h : address p≠some w ∨ address q≠some w) : oracleRaw w z p q=baselineRaw N p q := by
  cases p with
  | inl p => cases q <;> rfl
  | inr p =>
    cases q with
    | inl q => rfl
    | inr q =>
      change (if p.2=q.2 then (if p.2=w then halmos z else halmos 0) p.1 q.1 else 0)=
        if p.2=q.2 then halmos 0 p.1 q.1 else 0
      by_cases hpq : p.2=q.2
      · have hp : p.2≠w := by
          intro hw
          have he : q.2=w := hpq.symm.trans hw
          simp [address,hw,he] at h
        have hq : q.2≠w := fun hw => hp (hpq.trans hw)
        simp [hpq,hq]
      · simp [hpq]



/-- Construction for compressed Target in the marked halmos oracle model. -/
def compressedTarget {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (System N) (System N) ℂ :=
  Matrix.fromBlocks Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan 0 0 (Matrix.diagonal (fun j => if j=w then z else 0))

/-- The restricted-access construction satisfies `oracle_compress` under the complete displayed premises. -/
theorem oracle_compress {N : ℕ} (w : Fin N) (z : ℂ) :
    compress (encodingFiber false) (oracle w z) (encodingFiber false)=compressedTarget w z := by
  ext i j
  rw [compress_encodingFiber_eq]
  change oracleRaw w z (splitBasis N (false,i)) (splitBasis N (false,j))=compressedTarget w z i j
  cases i with
  | inl a =>
    cases j with
    | inl b => cases a <;> cases b <;> norm_num [oracleRaw,splitBasis,compressedTarget,core,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.oracle,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl b => rfl
    | inr j =>
      change (if i=j then (if i=w then halmos z else halmos 0) false false else 0)=
        if i=j then (if i=w then z else 0) else 0
      by_cases hij : i=j
      · subst j; split_ifs <;> rfl
      · simp [hij]

/-- Construction for target in the marked halmos oracle model. -/
def target {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (System N) (System N) ℂ :=
  (2 : ℝ) • compressedTarget w z

/-- Exact alpha=2 input encoding of the same nonnormal matrix, with a known
zero-ancilla frame. There is no supplied matrix-norm or encoding certificate. -/
theorem input_block_encoding {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) :
    BlockEncoding (target w z) (oracle w z) (encodingFiber false) (encodingFiber false) 2 0 := by
  refine ⟨oracle_unitary w z hz,encodingFiber_isIsometry _,encodingFiber_isIsometry _,by norm_num,by norm_num,?_⟩
  rw [oracle_compress]
  simp [target]

/-- The restricted-access construction satisfies `target_nonnormal` under the complete displayed premises. -/
theorem target_nonnormal {N : ℕ} (w : Fin N) (z : ℂ) :
    target w z*(target w z).conjTranspose≠(target w z).conjTranspose*target w z := by
  intro hh
  have he := congrArg (fun M : Matrix (System N) (System N) ℂ => M (.inl false) (.inl false)) hh
  norm_num [target,compressedTarget,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_sum_type,Fintype.sum_bool,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan] at he



/-- The restricted-access construction satisfies `target_norm` under the complete displayed premises. -/
theorem target_norm {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) : ‖target w z‖=2 := by
  have hc := Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one (encodingFiber_isIsometry (I := System N) false)
    (oracle_unitary w z hz) (encodingFiber_isIsometry (I := System N) false)
  rw [oracle_compress] at hc
  have hu : ‖target w z‖≤2 := by
    calc
      _ = 2*‖compressedTarget w z‖ := by simp [target,norm_smul]
      _ ≤ 2*1 := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = 2 := by ring
  have he : target w z (.inl false) (.inl true)=(2 : ℂ) := by
    norm_num [target,compressedTarget,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan]
  have hl := Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt.rectangular_entry_norm_le (target w z) (.inl false) (.inl true)
  rw [he] at hl
  norm_num at hl
  exact le_antisymm hu hl



/-- The restricted-access construction satisfies `baselineRaw_unitary` under the complete displayed premises. -/
theorem baselineRaw_unitary (N : ℕ) (hN : 0<N) : baselineRaw N∈Matrix.unitaryGroup (Basis N) ℂ := by
  have hh := oracleRaw_unitary (⟨0,hN⟩ : Fin N) 0 (by norm_num)
  rwa [oracleRaw_zero] at hh

/-- Construction for directed Raw in the marked halmos oracle model. -/
def directedRaw {N : ℕ} (w : Fin N) (z : ℂ) (mode : Bool) : Matrix (Basis N) (Basis N) ℂ :=
  if mode then oracleRaw w z else (oracleRaw w z).conjTranspose

/-- Construction for directed Baseline in the marked halmos oracle model. -/
def directedBaseline (N : ℕ) (mode : Bool) : Matrix (Basis N) (Basis N) ℂ :=
  if mode then baselineRaw N else (baselineRaw N).conjTranspose

/-- The restricted-access construction satisfies `directedRaw_unitary` under the complete displayed premises. -/
theorem directedRaw_unitary {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) (mode : Bool) :
    directedRaw w z mode∈Matrix.unitaryGroup (Basis N) ℂ := by
  cases mode
  · exact Qatlib.Foundations.QueryWordCore.Circuit.conjTranspose_mem_unitaryGroup (oracleRaw_unitary w z hz)
  · exact oracleRaw_unitary w z hz

/-- The restricted-access construction satisfies `directedBaseline_unitary` under the complete displayed premises. -/
theorem directedBaseline_unitary (N : ℕ) (hN : 0<N) (mode : Bool) :
    directedBaseline N mode∈Matrix.unitaryGroup (Basis N) ℂ := by
  cases mode
  · exact Qatlib.Foundations.QueryWordCore.Circuit.conjTranspose_mem_unitaryGroup (baselineRaw_unitary N hN)
  · exact baselineRaw_unitary N hN

/-- The restricted-access construction satisfies `directedRaw_unmarked_column` under the complete displayed premises. -/
theorem directedRaw_unmarked_column {N : ℕ} (w : Fin N) (z : ℂ) (mode : Bool) (p q : Basis N)
    (hq : address q≠some w) : directedRaw w z mode p q=directedBaseline N mode p q := by
  cases mode
  · exact congrArg star (oracleRaw_unmarked_entry w z q p (Or.inl hq))
  · exact oracleRaw_unmarked_entry w z p q (Or.inr hq)

/-- This specifies the GIVEN controlled primitive of the hard oracle family;
it does not synthesize control of an unprovided unknown unitary. -/
def controlledRaw {N : ℕ} (w : Fin N) (z : ℂ) (mode : Bool) :
    Matrix (Basis N × Bool) (Basis N × Bool) ℂ :=
  Matrix.blockDiagonal (fun c : Bool => if c then directedRaw w z mode else 1)

/-- Construction for controlled Baseline in the marked halmos oracle model. -/
def controlledBaseline (N : ℕ) (mode : Bool) : Matrix (Basis N × Bool) (Basis N × Bool) ℂ :=
  Matrix.blockDiagonal (fun c : Bool => if c then directedBaseline N mode else 1)

/-- The restricted-access construction satisfies `controlledRaw_unitary` under the complete displayed premises. -/
theorem controlledRaw_unitary {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) (mode : Bool) :
    controlledRaw w z mode∈Matrix.unitaryGroup (Basis N × Bool) ℂ := by
  apply blockDiagonal_unitary
  intro c
  cases c
  · exact one_mem _
  · exact directedRaw_unitary w z hz mode

/-- The restricted-access construction satisfies `controlledBaseline_unitary` under the complete displayed premises. -/
theorem controlledBaseline_unitary (N : ℕ) (hN : 0<N) (mode : Bool) :
    controlledBaseline N mode∈Matrix.unitaryGroup (Basis N × Bool) ℂ := by
  apply blockDiagonal_unitary
  intro c
  cases c
  · exact one_mem _
  · exact directedBaseline_unitary N hN mode

/-- The restricted-access construction satisfies `controlledRaw_unmarked_column` under the complete displayed premises. -/
theorem controlledRaw_unmarked_column {N : ℕ} (w : Fin N) (z : ℂ) (mode : Bool)
    (p q : Basis N × Bool) (hq : address q.1≠some w) :
    controlledRaw w z mode p q=controlledBaseline N mode p q := by
  rcases p with ⟨p,c⟩
  rcases q with ⟨q,d⟩
  cases c <;> cases d <;> simp only [controlledRaw,controlledBaseline,Matrix.blockDiagonal_apply]
  · rfl
  · rfl
  · rfl
  · exact directedRaw_unmarked_column w z mode p q hq

/-- The restricted-access construction satisfies `tensorOne_unitary` under the complete displayed premises. -/
private theorem tensorOne_unitary {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) :
    TensorGate U (1 : Matrix W W ℂ)∈Matrix.unitaryGroup (I × W) ℂ := by
  have hu : U*U.conjTranspose=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,tensorGate_conjTranspose,
    Matrix.conjTranspose_one,tensorGate_mul,hu,Matrix.one_mul,tensorGate_one]

/-- Construction for workspace Oracle in the marked halmos oracle model. -/
def workspaceOracle {W : Type} [Fintype W] [DecidableEq W] {N : ℕ} (w : Fin N) (z : ℂ) (mode : Bool) :
    Matrix ((Basis N × Bool) × W) ((Basis N × Bool) × W) ℂ :=
  TensorGate (controlledRaw w z mode) 1

/-- Construction for workspace Baseline in the marked halmos oracle model. -/
def workspaceBaseline (W : Type) [Fintype W] [DecidableEq W] (N : ℕ) (mode : Bool) :
    Matrix ((Basis N × Bool) × W) ((Basis N × Bool) × W) ℂ :=
  TensorGate (controlledBaseline N mode) 1

/-- The restricted-access construction satisfies `workspaceOracle_unitary` under the complete displayed premises. -/
theorem workspaceOracle_unitary {W : Type} [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) (mode : Bool) :
    workspaceOracle (W := W) w z mode∈Matrix.unitaryGroup ((Basis N × Bool) × W) ℂ :=
  tensorOne_unitary _ (controlledRaw_unitary w z hz mode)

/-- The restricted-access construction satisfies `workspaceBaseline_unitary` under the complete displayed premises. -/
theorem workspaceBaseline_unitary (W : Type) [Fintype W] [DecidableEq W] (N : ℕ) (hN : 0<N) (mode : Bool) :
    workspaceBaseline W N mode∈Matrix.unitaryGroup ((Basis N × Bool) × W) ℂ :=
  tensorOne_unitary _ (controlledBaseline_unitary N hN mode)

/-- The restricted-access construction satisfies `workspaceOracle_unmarked_column` under the complete displayed premises. -/
theorem workspaceOracle_unmarked_column {W : Type} [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (mode : Bool) (p q : (Basis N × Bool) × W)
    (hq : address q.1.1≠some w) : workspaceOracle w z mode p q=workspaceBaseline W N mode p q := by
  have hh := controlledRaw_unmarked_column w z mode p.1 q.1 hq
  exact congrArg (fun a : ℂ => a*(1 : Matrix W W ℂ) p.2 q.2) hh



/-- The restricted-access construction satisfies `controlledRaw_inverse_mode` under the complete displayed premises. -/
theorem controlledRaw_inverse_mode {N : ℕ} (w : Fin N) (z : ℂ) :
    controlledRaw w z false=(controlledRaw w z true).conjTranspose := by
  simp only [controlledRaw,Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext c
  cases c <;> simp [directedRaw]

/-- The restricted-access construction satisfies `workspaceOracle_inverse_mode` under the complete displayed premises. -/
theorem workspaceOracle_inverse_mode {W : Type} [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) : workspaceOracle (W := W) w z false=(workspaceOracle (W := W) w z true).conjTranspose := by
  simp only [workspaceOracle,tensorGate_conjTranspose,Matrix.conjTranspose_one,controlledRaw_inverse_mode]

/-- Abbreviation for Query Basis in the marked halmos oracle model. -/
abbrev QueryBasis (W : Type) (N : ℕ) := (Basis N × Bool) × W

/-- Construction for query Dim in the marked halmos oracle model. -/
def queryDim (W : Type) [Fintype W] (N : ℕ) : ℕ := Fintype.card (QueryBasis W N)

/-- Construction for finite Equiv in the marked halmos oracle model. -/
def finiteEquiv (W : Type) [Fintype W] (N : ℕ) : QueryBasis W N ≃ Fin (queryDim W N) :=
  Fintype.equivFin (QueryBasis W N)

/-- Construction for finite Oracle in the marked halmos oracle model. -/
def finiteOracle (W : Type) [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (mode : Bool) : Operator (queryDim W N) :=
  relabelGate (finiteEquiv W N) (workspaceOracle (W := W) w z mode)

/-- Construction for finite Baseline in the marked halmos oracle model. -/
def finiteBaseline (W : Type) [Fintype W] [DecidableEq W] (N : ℕ) (mode : Bool) : Operator (queryDim W N) :=
  relabelGate (finiteEquiv W N) (workspaceBaseline W N mode)

/-- Construction for finite Address in the marked halmos oracle model. -/
def finiteAddress (W : Type) [Fintype W] (N : ℕ) (p : Fin (queryDim W N)) : Option (Fin N) :=
  address ((finiteEquiv W N).symm p).1.1

/-- The restricted-access construction satisfies `finiteOracle_unitary` under the complete displayed premises. -/
theorem finiteOracle_unitary (W : Type) [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) (mode : Bool) :
    finiteOracle W w z mode∈Matrix.unitaryGroup (Fin (queryDim W N)) ℂ :=
  (relabelGate_mem_unitaryGroup (finiteEquiv W N) _).mpr (workspaceOracle_unitary w z hz mode)

/-- The restricted-access construction satisfies `finiteBaseline_unitary` under the complete displayed premises. -/
theorem finiteBaseline_unitary (W : Type) [Fintype W] [DecidableEq W] (N : ℕ) (hN : 0<N) (mode : Bool) :
    finiteBaseline W N mode∈Matrix.unitaryGroup (Fin (queryDim W N)) ℂ :=
  (relabelGate_mem_unitaryGroup (finiteEquiv W N) _).mpr (workspaceBaseline_unitary W N hN mode)

/-- The restricted-access construction satisfies `finiteOracle_unmarked_column` under the complete displayed premises. -/
theorem finiteOracle_unmarked_column (W : Type) [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (mode : Bool) (p q : Fin (queryDim W N))
    (hq : finiteAddress W N q≠some w) : finiteOracle W w z mode p q=finiteBaseline W N mode p q :=
  workspaceOracle_unmarked_column w z mode ((finiteEquiv W N).symm p) ((finiteEquiv W N).symm q) hq

/-- The restricted-access construction satisfies `queryDim_formula` under the complete displayed premises. -/
theorem queryDim_formula (W : Type) [Fintype W] (N : ℕ) : queryDim W N=4*(N+2)*Fintype.card W := by
  simp only [queryDim,QueryBasis,Basis,Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin]
  ring

/-- The actual Jordan/Halmos family, with controlled forward/adjoint access and
arbitrary finite workspace, now consumes the derived local quantum bound. -/
theorem actual_joint_query_error {Θ W : Type} [Fintype Θ] [Fintype W] [DecidableEq W] {N : ℕ}
    (π : FinDist Θ) (hN : 0<N) (z : Θ → ℂ) (hz : ∀ θ,Complex.normSq (z θ)≤1)
    (mode : Bool) (ρ : Operator (queryDim W N)) (hρ : ρ.PosSemidef) :
    (∑ h : Θ × Fin N,(Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior π N hN).prob h*
      (Matrix.traceNorm (finiteOracle W h.2 (z h.1) mode*ρ*(finiteOracle W h.2 (z h.1) mode).conjTranspose-
        finiteBaseline W N mode*ρ*(finiteBaseline W N mode).conjTranspose)/2))≤
      (2/Real.sqrt N)*(Matrix.trace ρ).re := by
  exact Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.joint_marked_query_error π hN (fun _ => finiteAddress W N)
    (fun θ w m => finiteOracle W w (z θ) m) (finiteBaseline W N)
    (fun θ w m => finiteOracle_unitary W w (z θ) (hz θ) m)
    (fun m => finiteBaseline_unitary W N hN m)
    (fun θ m w j hj i => finiteOracle_unmarked_column W w (z θ) m i j hj) mode ρ hρ



/-- The restricted-access construction satisfies `changeRows_isometry` under the complete displayed premises. -/
private theorem changeRows_isometry {H K I : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] (e : H ≃ K)
    (F : Matrix H I ℂ) (hF : IsIsometry F) : IsIsometry (F.submatrix e.symm id) := by
  change (F.submatrix e.symm id).conjTranspose*(F.submatrix e.symm id)=1
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  simpa [Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry] using hF

/-- The restricted-access construction satisfies `changeRows_compress` under the complete displayed premises. -/
private theorem changeRows_compress {H K I : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] (e : H ≃ K)
    (F : Matrix H I ℂ) (U : Matrix H H ℂ) :
    compress (F.submatrix e.symm id) (U.submatrix e.symm e.symm) (F.submatrix e.symm id)=compress F U F := by
  unfold compress
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

/-- Construction for raw Frame in the marked halmos oracle model. -/
def rawFrame (N : ℕ) : Matrix (Basis N) (System N) ℂ :=
  (encodingFiber false).submatrix (splitBasis N).symm id

/-- The restricted-access construction satisfies `rawFrame_isometry` under the complete displayed premises. -/
theorem rawFrame_isometry (N : ℕ) : IsIsometry (rawFrame N) :=
  changeRows_isometry (splitBasis N) (encodingFiber false) (encodingFiber_isIsometry false)

/-- The restricted-access construction satisfies `raw_compression` under the complete displayed premises. -/
theorem raw_compression {N : ℕ} (w : Fin N) (z : ℂ) :
    compress (rawFrame N) (oracleRaw w z) (rawFrame N)=compressedTarget w z := by
  have hu : (oracle w z).submatrix (splitBasis N).symm (splitBasis N).symm=oracleRaw w z := by
    ext p q
    change oracleRaw w z (splitBasis N ((splitBasis N).symm p)) (splitBasis N ((splitBasis N).symm q))=oracleRaw w z p q
    simp
  rw [←hu]
  exact (changeRows_compress (splitBasis N) (encodingFiber false) (oracle w z)).trans (oracle_compress w z)

/-- The restricted-access construction satisfies `raw_input_block_encoding` under the complete displayed premises. -/
theorem raw_input_block_encoding {N : ℕ} (w : Fin N) (z : ℂ) (hz : Complex.normSq z≤1) :
    BlockEncoding (target w z) (oracleRaw w z) (rawFrame N) (rawFrame N) 2 0 := by
  refine ⟨oracleRaw_unitary w z hz,rawFrame_isometry N,rawFrame_isometry N,by norm_num,by norm_num,?_⟩
  rw [raw_compression]
  simp [target]

/-- The restricted-access construction satisfies `finiteOracle_inverse_mode` under the complete displayed premises. -/
theorem finiteOracle_inverse_mode (W : Type) [Fintype W] [DecidableEq W] {N : ℕ} (w : Fin N) (z : ℂ) :
    finiteOracle W w z false=(finiteOracle W w z true).conjTranspose := by
  unfold finiteOracle
  rw [workspaceOracle_inverse_mode]
  rfl



/-- Same-input quantum/support hybrid for the explicit nonnormal block oracle
family. Only support-window agreement/visibility and the finite program budget
remain premises; no unitary, encoding or hybrid certificate is supplied. -/
theorem actual_joint_support_bound {Θ W : Type} [Fintype Θ] [DecidableEq Θ]
    [Fintype W] [DecidableEq W] {N R : ℕ} (π : FinDist Θ) (hN : 0<N)
    (z : Θ → ℂ) (hz : ∀ θ,Complex.normSq (z θ)≤1)
    (S : (Θ × Fin N) → ℝ → Fin R) (B : ℝ → Fin R)
    (P : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program (queryDim W N) R)
    (ρ : Operator (queryDim W N)) (hρ : ρ.PosSemidef) (htrace : (Matrix.trace ρ).re=1)
    (bad : (Θ × Fin N) → ℝ → Prop) (hS : ∀ h a,¬bad h a → S h a=B a) (s : ℕ) (v : ℝ)
    (hv : ∀ a,(∑ h∈Finset.univ.filter (fun h => bad h a),(Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior π N hN).prob h)≤v)
    (hc : ∀ p : Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Path P, (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathCharge P p).2 ≤ s) :
    (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior π N hN)
      (fun h => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw
        (fun mode => Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.oracleChannel (finiteOracle W h.2 (z h.1) mode)
          (finiteOracle_unitary W h.2 (z h.1) (hz h.1) mode)) (S h) P ρ hρ htrace)).prob hp-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior π N hN)
        (fun _ => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.pathLaw
          (fun mode => Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.oracleChannel (finiteBaseline W N mode) (finiteBaseline_unitary W N hN mode))
          B P ρ hρ htrace)).prob hp|)/2≤
      4*(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.queryDepth P : ℝ)/Real.sqrt N+(s : ℝ)*v := by
  exact Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.marked_joint_support_bound π hN (fun _ => finiteAddress W N)
    (fun θ w m => finiteOracle W w (z θ) m) (finiteBaseline W N)
    (fun θ w m => finiteOracle_unitary W w (z θ) (hz θ) m)
    (fun m => finiteBaseline_unitary W N hN m)
    (fun θ m w j hj i => finiteOracle_unmarked_column W w (z θ) m i j hj)
    S B P ρ hρ htrace bad hS s v hv hc



/-- Enabling the provided query-control flag gives the original input oracle. -/
theorem controlledRaw_forward_component {N : ℕ} (w : Fin N) (z : ℂ) (p q : Basis N) :
    controlledRaw w z true (p,true) (q,true)=oracleRaw w z p q := rfl

/-- Exact coordinate transport through the same hidden-independent equivalence. -/
theorem finiteOracle_apply_image (W : Type) [Fintype W] [DecidableEq W] {N : ℕ}
    (w : Fin N) (z : ℂ) (mode : Bool) (p q : QueryBasis W N) :
    finiteOracle W w z mode (finiteEquiv W N p) (finiteEquiv W N q)=workspaceOracle w z mode p q := by
  change workspaceOracle w z mode ((finiteEquiv W N).symm (finiteEquiv W N p))
    ((finiteEquiv W N).symm (finiteEquiv W N q))=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

end Qatlib.Papers.CrouzeixLS26.AccessLower.MarkedHalmos
