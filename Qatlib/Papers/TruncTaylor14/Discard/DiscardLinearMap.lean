/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TruncTaylor14.Discard.DiscardActualSimulationSimu
import Qatlib.Concepts.ReferenceError.DensityToRaw.FiniteReferenceDensityError
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Linear-map semantics of Taylor discard simulation

This module represents one amplified reset-and-discard step by its Kraus sum
`sourceDiscardLinearMap` and defines its iterates. It proves complete positivity and trace
preservation for unitary workspaces, identifies reset-and-discard semantics on arbitrary
operators and reference extensions, and shows that the Taylor workspace construction commutes
with adjoining an idle reference. See [BerryEtAl2015Taylor].

## Main statements

* `sourceDiscardLinearMap_channel`: Channel properties of a single discard step.
* `sourceDiscardLinearMap_semantics`: Iterated semantics with and without a reference system.
* `sourceTaylorDiscardWorkspace_reference`: Compatibility of the Taylor workspace with idle
  references.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Papers.TruncTaylor14.DiscardCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- The complex linear map obtained by summing conjugation branches of the amplified workspace
matrix from the initialized ancilla fiber. -/
def sourceDiscardLinearMap {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J) :
    Operator D →ₗ[ℂ] Operator D :=
  let A := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  ∑ j : J, conjBranch (fun i k => A (j, i) (j₀, k))

/-- Repeated composition of `sourceDiscardLinearMap`, with the identity map at iteration zero. -/
def sourceDiscardLinearIterate {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J) :
    ℕ → (Operator D →ₗ[ℂ] Operator D)
  | 0 => LinearMap.id
  | n + 1 => (sourceDiscardLinearIterate W j₀ n).comp (sourceDiscardLinearMap W j₀)

/-- The workspace matrix tensored with the identity on a reference of dimension `r`, using the
grouped ancilla-system-reference indexing. -/
def sourceDiscardWorkspaceReference {J : Type} {D : ℕ} (r : ℕ)
    (W : Matrix (J × Fin D) (J × Fin D) ℂ) :
    Matrix (J × (Fin D × Fin r)) (J × (Fin D × Fin r)) ℂ :=
  fun x y => W (x.1, x.2.1) (y.1, y.2.1) *
    (if x.2.2 = y.2.2 then 1 else 0)

/-- The Taylor LCU adjoint circuit substituted into the source discard oblivious-amplification
word. -/
def sourceTaylorDiscardWord {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) :=
  substituteAdjointCircuit (taylorLCUWord (I := I) h j₀ τ K)
    (sourceDiscardOAAWord (rangeProjector (taylorFrame (I := I) j₀ K)))

/-- The evaluated Taylor LCU workspace matrix relabeled to separate the discard ancilla from the
system. -/
def sourceTaylorDiscardWorkspace {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j₀ : J) (τ : ℝ) (K : ℕ) :
    Matrix ((TaylorWordLabel J K × (Bool × J)) × I)
      ((TaylorWordLabel J K × (Bool × J)) × I) ℂ :=
  relabelGate (taylorDiscardEquiv J I K)
    (evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K))

/-- The Taylor discard linear map iterated for the selected segment count, segment time, and
truncation cutoff. -/
def sourceTaylorDiscardChannel {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (h : J → ℝ) (U : J → Operator D) (j₀ : J) (t Λ : ℝ) (k : ℕ) :
    Operator D →ₗ[ℂ] Operator D :=
  let r := max 1 (Nat.ceil (Λ * t / Real.log 2))
  sourceDiscardLinearIterate
    (sourceTaylorDiscardWorkspace h U j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))
    (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) r

/-- The Kraus sum from an amplified workspace equals `ResetDiscardStepCorrected` on every input
matrix. -/
theorem sourceDiscard_kraus_step {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (X : Matrix I I ℂ) :
    let A := ObliviousAmplitudeAmplification (FiberProjector j₀) W
    let K : J → Matrix I I ℂ := fun a i k => A (a, i) (j₀, k)
    (∑ a : J, K a * X * (K a)ᴴ) = ResetDiscardStepCorrected W j₀ X := by
  ext i k
  simp [ResetDiscardStepCorrected, ReducedState, AncillaSystemOp, vecOuter, Qatlib.Foundations.PureStateMath.Ket,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_ite, ite_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- A unitary workspace makes `sourceDiscardLinearMap` completely positive and trace preserving.
See [BerryEtAl2015Taylor]. -/
theorem sourceDiscardLinearMap_channel :
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D : ℕ)
    (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J),
    W ∈ Matrix.unitaryGroup (J × Fin D) ℂ →
      CompletelyPositive (sourceDiscardLinearMap W j₀) ∧
      TracePreserving (sourceDiscardLinearMap W j₀) := by
  intro J _ _ D W j₀ hW
  let A := ObliviousAmplitudeAmplification (FiberProjector j₀) W
  let K : J → Operator D := fun a i k => A (a, i) (j₀, k)
  have hp := isOrthogonalProjector_fiberProjector (I := Fin D) j₀
  have hA := obliviousAmplitudeAmplification_mem_unitary _ _ ⟨hp.1, hp.2⟩ hW
  have hu : Aᴴ * A = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hA
  have hk : ∑ a, (K a)ᴴ * K a = 1 := by
    ext i k
    have he := congrFun (congrFun hu (j₀, i)) (j₀, k)
    simpa [K, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply] using! he
  exact ⟨CompletelyPositive.sum (fun a _ => completelyPositive_conjBranch (K a)),
    by
      intro X
      simpa only [sourceDiscardLinearMap, LinearMap.sum_apply] using!
        (Instrument.ofKraus K hk).total X⟩

/-- The complex algebra homomorphism adjoining the identity on a finite reference system. -/
private noncomputable def sourceReferenceAlgHom (D r : ℕ) :
    Operator D →ₐ[ℂ] Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ where
  toFun A := TensorGate A 1
  map_one' := tensorGate_one
  map_mul' A B := by rw [tensorGate_mul, Matrix.one_mul]
  map_zero' := by ext p q; simp [TensorGate]
  map_add' A B := by ext p q; simp [TensorGate, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, TensorGate, Matrix.smul_kronecker]
    change c • TensorGate (1 : Operator D) (1 : Operator r) = c • 1
    rw [tensorGate_one]

/-- Hamiltonian evolution of `H` tensored with the reference identity equals the evolution of
`H` tensored with that identity. See [BerryEtAl2015Taylor]. -/
theorem sourceTaylorReferenceEvolution :
  ∀ (D r : ℕ) (H : Operator D) (t : ℝ),
    Qatlib.Concepts.QspSimulation.Achievability.hamiltonianEvolution (TensorGate H (1 : Operator r)) t =
      TensorGate (Qatlib.Concepts.QspSimulation.Achievability.hamiltonianEvolution H t) (1 : Operator r) := by
  intro D r H t
  have he := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (sourceReferenceAlgHom D r)
    (sourceReferenceAlgHom D r).toLinearMap.continuous_of_finiteDimensional
    ((-Complex.I * (t : ℂ)) • H)
    (by simpa only [NormedSpace.expSeries_radius_eq_top] using!
      edist_lt_top ((-Complex.I * (t : ℂ)) • H) 0)
  rw [map_smul] at he
  exact he.symm

/-- The algebra homomorphism extending a workspace matrix by an idle reference while retaining
the grouped product indices. -/
private def workspaceReferenceHom (J I R : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] :
    Matrix (J × I) (J × I) ℂ →ₐ[ℂ] Matrix (J × (I × R)) (J × (I × R)) ℂ where
  toFun W x y := W (x.1, x.2.1) (y.1, y.2.1) *
    (if x.2.2 = y.2.2 then 1 else 0)
  map_one' := by
    ext ⟨a, i, r⟩ ⟨b, k, s⟩
    by_cases hrs : r = s <;> simp [Matrix.one_apply, Prod.ext_iff, hrs]
  map_mul' W V := by
    ext ⟨a, i, r⟩ ⟨b, k, s⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  map_zero' := by ext x y; simp
  map_add' W V := by
    ext x y
    by_cases h : x.2.2 = y.2.2 <;> simp [h]
  commutes' c := by
    ext ⟨a, i, r⟩ ⟨b, k, s⟩
    by_cases hrs : r = s <;>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Prod.ext_iff, hrs]

/-- The workspace reference extension commutes with conjugate transpose. -/
private theorem workspaceReference_star {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (W : Matrix (J × I) (J × I) ℂ) :
    workspaceReferenceHom J I R Wᴴ = (workspaceReferenceHom J I R W)ᴴ := by
  ext ⟨a, i, r⟩ ⟨b, k, s⟩
  by_cases hrs : r = s <;> simp [workspaceReferenceHom, Matrix.conjTranspose_apply, hrs, eq_comm]

/-- The workspace reference extension sends an initialized-fiber projector to the corresponding
extended-fiber projector. -/
private theorem workspaceReference_fiber {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] (j₀ : J) :
    workspaceReferenceHom J I R (FiberProjector (I := I) j₀) =
      FiberProjector (I := I × R) j₀ := by
  ext ⟨a, i, r⟩ ⟨b, k, s⟩
  by_cases hrs : r = s <;> simp [workspaceReferenceHom, FiberProjector, Prod.ext_iff, hrs]

/-- The workspace reference extension commutes with oblivious amplitude amplification about the
initialized fiber. -/
private theorem workspaceReference_oaa {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    workspaceReferenceHom J I R (ObliviousAmplitudeAmplification (FiberProjector j₀) W) =
      ObliviousAmplitudeAmplification (FiberProjector j₀) (workspaceReferenceHom J I R W) := by
  simp only [ObliviousAmplitudeAmplification, map_neg, map_mul, map_sub, map_one,
    map_ofNat, Matrix.star_eq_conjTranspose, workspaceReference_star, workspaceReference_fiber]

/-- Evaluating the source discard linear map on a matrix agrees with the corrected
reset-and-discard step. -/
private theorem sourceDiscardLinearMap_step {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J) (X : Operator D) :
    sourceDiscardLinearMap W j₀ X = ResetDiscardStepCorrected W j₀ X := by
  simpa only [sourceDiscardLinearMap, LinearMap.sum_apply, conjBranch_apply] using!
    sourceDiscard_kraus_step W j₀ X

/-- Extending the source discard map by a reference identity agrees with the corrected discard
step for the extended workspace. -/
private theorem sourceDiscardLinearMap_reference_step {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (sourceDiscardLinearMap W j₀) X =
      ResetDiscardStepCorrected (sourceDiscardWorkspaceReference r W) j₀ X := by
  rw [sourceDiscardLinearMap, tensorLeft_sum,
    ← sourceDiscard_kraus_step (sourceDiscardWorkspaceReference r W) j₀ X]
  apply Finset.sum_congr rfl
  intro a _
  rw [tensorLeft_conjBranch]
  have he : ObliviousAmplitudeAmplification (FiberProjector j₀)
      (sourceDiscardWorkspaceReference r W) =
      workspaceReferenceHom J (Fin D) (Fin r)
        (ObliviousAmplitudeAmplification (FiberProjector j₀) W) :=
    (workspaceReference_oaa W j₀).symm
  (try dsimp only)
  rw [he]
  have hk : TensorGate (fun i k => ObliviousAmplitudeAmplification (FiberProjector j₀) W
        (a, i) (j₀, k)) (1 : Operator r) =
      (fun i k => workspaceReferenceHom J (Fin D) (Fin r)
        (ObliviousAmplitudeAmplification (FiberProjector j₀) W) (a, i) (j₀, k)) := by
    ext i k
    rfl
  rw [hk]

/-- Source discard iterates agree with repeated corrected reset-and-discard steps on system
operators and on all finite reference extensions. See [BerryEtAl2015Taylor]. -/
theorem sourceDiscardLinearMap_semantics :
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D : ℕ)
    (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J),
    (∀ (n : ℕ) (X : Operator D),
      sourceDiscardLinearIterate W j₀ n X = (ResetDiscardStepCorrected W j₀)^[n] X) ∧
    (∀ (r n : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      tensorLeft (sourceDiscardLinearIterate W j₀ n) X =
        (ResetDiscardStepCorrected (sourceDiscardWorkspaceReference r W) j₀)^[n] X) := by
  intro J _ _ D W j₀
  constructor
  · intro n
    induction n with
    | zero => intro X; rfl
    | succ n ih =>
      intro X
      rw [sourceDiscardLinearIterate, LinearMap.comp_apply, ih,
        sourceDiscardLinearMap_step, Function.iterate_succ_apply]
  · intro r n
    induction n with
    | zero => intro X; exact tensorLeft_id X
    | succ n ih =>
      intro X
      rw [sourceDiscardLinearIterate, tensorLeft_comp, ih,
        sourceDiscardLinearMap_reference_step, Function.iterate_succ_apply]

local instance (priority := 10000) sourceProdProdFast {α β γ : Type} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] : DecidableEq ((α × β) × γ) :=
  @instDecidableEqProd (α × β) γ (@instDecidableEqProd α β _ _) _

/-- The algebra homomorphism adjoining an idle reference to a Taylor workspace through the
discard-index relabelings. -/
private def taylorReferenceHom (J I R : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I)))
      (TaylorWordLabel J K × (Bool × (J × I))) ℂ →ₐ[ℂ]
    Matrix (TaylorWordLabel J K × (Bool × (J × (I × R))))
      (TaylorWordLabel J K × (Bool × (J × (I × R)))) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (taylorDiscardEquiv J (I × R) K).symm).toAlgHom.comp
    ((workspaceReferenceHom (TaylorWordLabel J K × (Bool × J)) I R).comp
      (Matrix.reindexAlgEquiv ℂ ℂ (taylorDiscardEquiv J I K)).toAlgHom)

/-- Each entry of the Taylor reference extension is the original workspace entry times the
Kronecker delta on reference indices. -/
private theorem taylorReferenceHom_apply {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] (K : ℕ)
    (W : Matrix (TaylorWordLabel J K × (Bool × (J × I)))
      (TaylorWordLabel J K × (Bool × (J × I))) ℂ)
    (x y : TaylorWordLabel J K × (Bool × (J × (I × R)))) :
    taylorReferenceHom J I R K W x y =
      W (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1)))
        (y.1, (y.2.1, (y.2.2.1, y.2.2.2.1))) *
      (if x.2.2.2.2 = y.2.2.2.2 then 1 else 0) := rfl

/-- The Taylor reference extension sends the query matrix to the query for component unitaries
tensored with the reference identity. -/
private theorem taylorReference_query {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (U : J → Matrix I I ℂ) (K : ℕ) :
    taylorReferenceHom J I R K (taylorQuery U K) =
      taylorQuery (fun j => TensorGate (U j) (1 : Matrix R R ℂ)) K := by
  ext ⟨w, b, a, i, r⟩ ⟨v, c, d, k, s⟩
  rw [taylorReferenceHom_apply]
  by_cases hrs : r = s <;> cases b <;> cases c <;>
    simp [hrs, taylorQuery, TensorGate, controlOracle, select, Matrix.one_apply,
      Prod.ext_iff, mul_ite, ite_mul]

/-- The Taylor reference extension preserves an ancilla matrix tensored with the identity on the
remaining registers. -/
private theorem taylorReference_ancilla {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (K : ℕ) (P : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ) :
    taylorReferenceHom J I R K
      (TensorGate P (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)) =
      TensorGate P (1 : Matrix (Bool × (J × (I × R))) (Bool × (J × (I × R))) ℂ) := by
  ext ⟨w, b, a, i, r⟩ ⟨v, c, d, k, s⟩
  rw [taylorReferenceHom_apply]
  by_cases hrs : r = s <;>
    simp [hrs, TensorGate, Matrix.one_apply, Prod.ext_iff, mul_ite]

/-- The Taylor reference extension sends each route matrix to the corresponding route matrix
with the extended system. -/
private theorem taylorReference_route {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (j₀ : J) {K : ℕ} (j : Fin K) :
    taylorReferenceHom J I R K (taylorRouteMatrix (I := I) j₀ j) =
      taylorRouteMatrix (I := I × R) j₀ j := by
  ext ⟨w, b, a, i, r⟩ ⟨v, c, d, k, s⟩
  rw [taylorReferenceHom_apply]
  by_cases hrs : r = s <;> cases v <;>
    simp [hrs, taylorRouteMatrix, permMatrix, taylorRouteSwap, Prod.ext_iff]

/-- The Taylor reference extension commutes with evaluation of every block list of length at
most the truncation cutoff. -/
private theorem taylorReference_blocks {J I R : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (U : J → Matrix I I ℂ) (j₀ : J) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K),
    taylorReferenceHom J I R K (evaluate (taylorQuery U K) (taylorBlockList j₀ K n hn)) =
      evaluate (taylorQuery (fun j => TensorGate (U j) (1 : Matrix R R ℂ)) K)
        (taylorBlockList (I := I × R) j₀ K n hn) := by
  intro n
  induction n with
  | zero => intro hn; exact (taylorReferenceHom J I R K).map_one
  | succ n ih =>
    intro hn
    simp only [taylorBlockList, taylorQueryRouteStep, List.cons_append,
      List.nil_append, evaluate, instructionMatrix, map_mul,
      taylorReference_route, taylorReference_query, ih]

/-- Building the Taylor discard workspace from component operators tensored with an idle
reference equals extending the original workspace by that reference. See
[BerryEtAl2015Taylor]. -/
theorem sourceTaylorDiscardWorkspace_reference :
  ∀ (J : Type) [Fintype J] [DecidableEq J] (D r : ℕ)
    (h : J → ℝ) (U : J → Operator D) (j₀ : J) (τ : ℝ) (K : ℕ),
    sourceTaylorDiscardWorkspace h
      (fun j => TensorGate (U j) (1 : Operator r)) j₀ τ K =
        sourceDiscardWorkspaceReference r (sourceTaylorDiscardWorkspace h U j₀ τ K) := by
  intro J _ _ D r h U j₀ τ K
  have he : taylorReferenceHom J (Fin D) (Fin r) K
      (evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K)) =
      evaluate (taylorQuery (fun j => TensorGate (U j) (1 : Operator r)) K)
        (taylorLCUWord h j₀ τ K) := by
    simp only [taylorLCUWord, List.cons_append, List.nil_append, evaluate,
      instructionMatrix, evaluate_append, map_mul, taylorReference_ancilla,
      taylorReference_blocks, Matrix.mul_one]
  ext ⟨a, i, s⟩ ⟨b, k, t⟩
  have hx := congrFun (congrFun he
    ((taylorDiscardEquiv J (Fin D × Fin r) K).symm (a, (i, s))))
    ((taylorDiscardEquiv J (Fin D × Fin r) K).symm (b, (k, t)))
  rw [taylorReferenceHom_apply] at hx
  exact hx.symm

end Qatlib.Papers.TruncTaylor14.DiscardCore
