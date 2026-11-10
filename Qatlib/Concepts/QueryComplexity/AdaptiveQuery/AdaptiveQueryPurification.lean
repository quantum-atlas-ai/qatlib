/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Matrix

def observedQueryDepth {I : Type} : ObservedCircuit I → ℕ
  | .halt _ => 0
  | .step (.gate _) P => observedQueryDepth P
  | .step .query P => observedQueryDepth P + 1
  | .measure k _ next =>
      (List.ofFn (fun o : Fin k => observedQueryDepth (next o))).foldl max 0
  | .project _ P Q => max (observedQueryDepth P) (observedQueryDepth Q)

def observedTreeNodes {I : Type} : ObservedCircuit I → ℕ
  | .halt _ => 1
  | .step _ P => observedTreeNodes P + 1
  | .measure k _ next =>
      (List.ofFn (fun o : Fin k => observedTreeNodes (next o))).sum + 1
  | .project _ P Q => observedTreeNodes P + observedTreeNodes Q + 1

def emptyObservedTrace (I : Type) : BranchTrace I :=
  ⟨0, false, 0, 0, 0, []⟩

noncomputable def deferredObservedInput {n R : ℕ} {W : Type}
    (ψ : QState ((Fin n × Bool) × W)) :
    QState ((Fin n × Bool) × (W × Fin (R + 1) × Bool)) :=
  fun x => if x.2.2.1.val = 0 then ψ (x.1, x.2.1) / Real.sqrt 2 else 0

theorem deferredObservedInput_mass {n R : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (ψ : QState ((Fin n × Bool) × W)) :
    branchMass (deferredObservedInput (R := R) ψ) = branchMass ψ := by
  simp only [branchMass, MeasureProb, BornProb, deferredObservedInput]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ib _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_eq_single (0 : Fin (R + 1))]
  · simp [div_pow]
  · intro h _ hne
    have hval : h.val ≠ 0 := fun he => hne (Fin.ext he)
    simp [hval]
  · simp

theorem deferredObservedInput_normalized {n R : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] {ψ : QState ((Fin n × Bool) × W)}
    (hψ : Normalized ψ) : Normalized (deferredObservedInput (R := R) ψ) := by
  change branchMass (deferredObservedInput (R := R) ψ) = 1
  exact (deferredObservedInput_mass ψ).trans (measureProb_univ hψ)

private theorem foldl_max_le (xs : List ℕ) (a K : ℕ)
    (ha : a ≤ K) (hxs : ∀ x ∈ xs, x ≤ K) : xs.foldl max a ≤ K := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (max a x) (max_le ha (hxs x List.mem_cons_self))
      (fun y hy => hxs y (List.mem_cons_of_mem x hy))

private theorem le_foldl_max (xs : List ℕ) (a : ℕ) :
    a ≤ xs.foldl max a ∧ ∀ x ∈ xs, x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have htail := ih (max a x)
    refine ⟨le_trans (le_max_left _ _) htail.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (le_max_right _ _) htail.1
    · exact htail.2 y hy

private theorem foldl_max_ofFn (k : ℕ) (g : Fin k → ℕ) :
    (List.ofFn g).foldl max 0 = Finset.univ.sup g := by
  apply le_antisymm
  · apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hx
    exact Finset.le_sup (f := g) (Finset.mem_univ o)
  · apply Finset.sup_le
    intro o _
    exact (le_foldl_max (List.ofFn g) 0).2 (g o) (List.mem_ofFn.mpr ⟨o, rfl⟩)

theorem observedQueryDepth_eq_budget {I : Type} (P : ObservedCircuit I) :
    observedQueryDepth P = observedQueryBudget P := by
  induction P with
  | halt accepted => rfl
  | step s P ih => cases s <;> simpa [observedQueryDepth, observedQueryBudget] using ih
  | measure k label next ih =>
    simp only [observedQueryDepth, observedQueryBudget, foldl_max_ofFn]
    exact Finset.sup_congr rfl (fun o _ => ih o)
  | project A P Q ihP ihQ => simp only [observedQueryDepth, observedQueryBudget, ihP, ihQ]

theorem observed_query_depth_all_trace_bound
    (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (f : Fin n → Bool)
    (ψ : QState ((Fin n × Bool) × W)) :
    ∀ t ∈ observedTraces (workspaceBitOracle (W := W) f) P ψ,
      t.queries ≤ observedQueryDepth P := by
  intro t ht
  rw [observedQueryDepth_eq_budget]
  exact queries_le_observedQueryBudget _ P ψ ht

open scoped InnerProductSpace in

theorem adaptiveHistoryIsometry_extension {J : Type} [Fintype J] [DecidableEq J]
    (S : Submodule ℂ (EuclideanSpace ℂ J))
    (L : S →ₗᵢ[ℂ] EuclideanSpace ℂ J) :
    ∃ U : Matrix J J ℂ, U ∈ Matrix.unitaryGroup J ℂ ∧
      ∀ s : S, U.toEuclideanLin s = L s := by
  let M := L.extend
  let U : Matrix J J ℂ := Matrix.toEuclideanLin.symm M.toLinearMap
  have hact : U.toEuclideanLin = M.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    have hh := M.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    change ⟪M.toLinearMap _, M.toLinearMap _⟫_ℂ = _ at hh
    rw [← hact] at hh
    have hcol (k : J) : U.toEuclideanLin (EuclideanSpace.single k 1) =
        WithLp.toLp 2 (Uᵀ k) := by
      change WithLp.toLp 2 (U *ᵥ WithLp.ofLp (EuclideanSpace.single k 1)) = _
      congr 1
      ext x
      simp [Matrix.mulVec, dotProduct]
    rw [hcol, hcol, inner_matrix_col_col] at hh
    simpa [Matrix.one_apply, PiLp.inner_apply] using hh
  · intro s
    rw [hact]
    exact L.extend_apply s

section Padding

variable {n : ℕ} {W H : Type} [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H]

def adaptivePaddingSwap (active : H → Bool)
    (x : (Fin n × Bool) × (W × H × Bool)) :
    (Fin n × Bool) × (W × H × Bool) :=
  if active x.2.2.1 then x else
    ((x.1.1, x.2.2.2), (x.2.1, x.2.2.1, x.1.2))

omit [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H] in

theorem adaptivePaddingSwap_involutive (active : H → Bool) :
    Function.Involutive (adaptivePaddingSwap (n := n) (W := W) active) := by
  intro x
  rcases x with ⟨⟨i, b⟩, w, h, s⟩
  cases ha : active h <;> simp [adaptivePaddingSwap, ha]

noncomputable def adaptivePaddedQuery (active : H → Bool) :
    Circuit ((Fin n × Bool) × (W × H × Bool)) :=
  [.gate (permMatrix (adaptivePaddingSwap active)), .query,
    .gate (permMatrix (adaptivePaddingSwap active))]

theorem adaptivePaddedQuery_cost_and_unitary (active : H → Bool) :
    IsUnitaryCircuit (adaptivePaddedQuery (n := n) (W := W) active) ∧
      QueryCount (adaptivePaddedQuery (n := n) (W := W) active) = 1 ∧
      GateCount (adaptivePaddedQuery (n := n) (W := W) active) = 2 := by
  have hu := permMatrix_unitary (adaptivePaddingSwap_involutive (n := n) (W := W) active)
  simp [adaptivePaddedQuery, hu]

noncomputable def adaptiveSpareInput
    (v : QState ((Fin n × Bool) × (W × H))) :
    QState ((Fin n × Bool) × (W × H × Bool)) :=
  fun x => v (x.1, x.2.1, x.2.2.1) / Real.sqrt 2

theorem run_adaptivePaddedQuery (active : H → Bool) (f : Fin n → Bool)
    (v : QState ((Fin n × Bool) × (W × H)))
    (x : (Fin n × Bool) × (W × H × Bool)) :
    Run (workspaceBitOracle (W := W × H × Bool) f) (adaptivePaddedQuery active)
      (adaptiveSpareInput v) x =
      (if active x.2.2.1 then v ((x.1.1, x.1.2 ^^ f x.1.1), x.2.1, x.2.2.1)
        else v (x.1, x.2.1, x.2.2.1)) / Real.sqrt 2 := by
  simp only [adaptivePaddedQuery, run_gate, run_query, run_nil,
    applyGate_permMatrix (adaptivePaddingSwap_involutive active),
    applyGate_workspaceBitOracle]
  rcases x with ⟨⟨i, b⟩, w, h, s⟩
  cases ha : active h <;> simp [adaptivePaddingSwap, adaptiveSpareInput, ha]

end Padding

section MeasurementHistory

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

def adaptivePartitionSwap (label : I → H) (blank : H) (x : I × H) : I × H :=
  (x.1, Equiv.swap blank (label x.1) x.2)

omit [Fintype I] [DecidableEq I] [Fintype H] in

theorem adaptivePartitionSwap_involutive (label : I → H) (blank : H) :
    Function.Involutive (adaptivePartitionSwap label blank) := by
  intro x
  exact Prod.ext rfl (Equiv.swap_apply_self blank (label x.1) x.2)

noncomputable def adaptivePartitionHistoryGate (label : I → H) (blank : H) :
    Matrix (I × H) (I × H) ℂ := permMatrix (adaptivePartitionSwap label blank)

theorem adaptivePartitionHistoryGate_unitary (label : I → H) (blank : H) :
    adaptivePartitionHistoryGate label blank ∈ Matrix.unitaryGroup (I × H) ℂ :=
  permMatrix_unitary (adaptivePartitionSwap_involutive label blank)

theorem apply_adaptivePartitionHistoryGate (label : I → H) (blank : H)
    (ψ : QState I) (x : I × H) :
    ApplyGate (adaptivePartitionHistoryGate label blank) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket blank)) x =
      (if label x.1 = x.2 then ψ x.1 else 0) := by
  rw [adaptivePartitionHistoryGate,
    applyGate_permMatrix (adaptivePartitionSwap_involutive label blank)]
  simp only [adaptivePartitionSwap, TensorState, Qatlib.Foundations.PureStateMath.Ket]
  have he : Equiv.swap blank (label x.1) x.2 = blank ↔ label x.1 = x.2 := by
    constructor
    · intro h
      have := congrArg (Equiv.swap blank (label x.1)) h
      simpa using this.symm
    · intro h
      rw [← h, Equiv.swap_apply_right]
  by_cases h : label x.1 = x.2 <;> simp [he, h]

noncomputable def adaptiveProjectHistoryGate (P : Matrix I I ℂ) (a b : H) :
    Matrix (I × H) (I × H) ℂ :=
  TensorGate (1 - P) 1 + TensorGate P (permMatrix (Equiv.swap a b))

theorem adaptiveProjectHistoryGate_unitary {P : Matrix I I ℂ}
    (hP : IsOrthogonalProjector P) (a b : H) :
    adaptiveProjectHistoryGate P a b ∈ Matrix.unitaryGroup (I × H) ℂ := by
  let V : Matrix H H ℂ := permMatrix (Equiv.swap a b)
  have hV := permMatrix_unitary (fun h : H => Equiv.swap_apply_self a b h)
  change V ∈ Matrix.unitaryGroup H ℂ at hV
  have hVV : V.conjTranspose * V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hV
  have hC := isOrthogonalProjector_compl hP
  have hPP : P * P = P := hP.1
  have hCC : (1 - P) * (1 - P) = 1 - P := hC.1
  have hPstar : P.conjTranspose = P := hP.2
  have hCstar : (1 - P).conjTranspose = 1 - P := hC.2
  have hcross₁ : (1 - P) * P = 0 := hP.one_sub_mul_self
  have hcross₂ : P * (1 - P) = 0 := hP.mul_one_sub_self
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (TensorGate (1 - P) 1 + TensorGate P V).conjTranspose *
    (TensorGate (1 - P) 1 + TensorGate P V) = 1
  rw [Matrix.conjTranspose_add, tensorGate_conjTranspose, tensorGate_conjTranspose,
    hCstar, hPstar, Matrix.conjTranspose_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add]
  simp only [tensorGate_mul, Matrix.one_mul, Matrix.mul_one, hCC, hPP,
    hcross₁, hcross₂, hVV]
  simp only [TensorGate, Matrix.zero_kronecker, add_zero, zero_add,
    ← Matrix.add_kronecker, sub_add_cancel, Matrix.one_kronecker_one]

theorem apply_adaptiveProjectHistoryGate (P : Matrix I I ℂ) (a b : H)
    (hab : a ≠ b) (ψ : QState I) (x : I × H) :
    ApplyGate (adaptiveProjectHistoryGate P a b) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket a)) x =
      (if x.2 = a then ProjectiveBranch P false ψ x.1 else
       if x.2 = b then ProjectiveBranch P true ψ x.1 else 0) := by
  have hket : ApplyGate (permMatrix (Equiv.swap a b)) (Qatlib.Foundations.PureStateMath.Ket a) = Qatlib.Foundations.PureStateMath.Ket b := by
    simpa using applyGate_permMatrix_ket
      (fun h : H => Equiv.swap_apply_self a b h) a
  simp only [adaptiveProjectHistoryGate, ApplyGate, Matrix.add_mulVec]
  change (ApplyGate (TensorGate (1 - P) 1) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket a)) +
    ApplyGate (TensorGate P (permMatrix (Equiv.swap a b))) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket a))) x = _
  rw [applyGate_tensorGate, applyGate_tensorGate, applyGate_one, hket]
  simp only [Pi.add_apply, TensorState, Qatlib.Foundations.PureStateMath.Ket, ProjectiveBranch, Bool.false_eq_true,
    ↓reduceIte]
  by_cases ha : x.2 = a
  · simp [ha, hab]
  · by_cases hb : x.2 = b <;> simp [ha, hb, hab.symm]

end MeasurementHistory

section HistoryLayout

variable {A W H : Type} [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H]

def adaptiveHistoryLayoutEquiv : (((A × W) × H) × Bool) ≃ A × (W × H × Bool) where
  toFun x := (x.1.1.1, x.1.1.2, x.1.2, x.2)
  invFun x := (((x.1, x.2.1), x.2.2.1), x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def adaptiveHistoryLift
    (U : Matrix ((A × W) × H) ((A × W) × H) ℂ) :
    Matrix (A × (W × H × Bool)) (A × (W × H × Bool)) ℂ :=
  Matrix.reindex adaptiveHistoryLayoutEquiv adaptiveHistoryLayoutEquiv (TensorGate U 1)

theorem adaptiveHistoryLift_unitary
    {U : Matrix ((A × W) × H) ((A × W) × H) ℂ}
    (hU : U ∈ Matrix.unitaryGroup ((A × W) × H) ℂ) :
    adaptiveHistoryLift U ∈ Matrix.unitaryGroup (A × (W × H × Bool)) ℂ :=
  unitaryGroup_reindex adaptiveHistoryLayoutEquiv (tensorGate_unitary hU (Submonoid.one_mem _))

omit [DecidableEq A] [DecidableEq W] [DecidableEq H] in

theorem apply_adaptiveHistoryLift
    (U : Matrix ((A × W) × H) ((A × W) × H) ℂ)
    (v : QState ((A × W) × H)) (x : A × (W × H × Bool)) :
    ApplyGate (adaptiveHistoryLift U)
      (fun y => v ((y.1, y.2.1), y.2.2.1) / Real.sqrt 2) x =
      ApplyGate U v ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2 := by
  simp only [adaptiveHistoryLift, ApplyGate, Matrix.mulVec, dotProduct,
    Matrix.reindex_apply, Matrix.submatrix_apply, adaptiveHistoryLayoutEquiv,
    Equiv.coe_fn_symm_mk, TensorGate, Matrix.kronecker_apply]
  simp only [Fintype.sum_prod_type]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro h _
  ring

noncomputable def adaptiveBinaryHistory (P : Matrix (A × W) (A × W) ℂ)
    (ψ : QState (A × W)) : QState ((A × W) × Fin 2) :=
  fun x => if x.2 = 0 then ProjectiveBranch P false ψ x.1
    else ProjectiveBranch P true ψ x.1

noncomputable def adaptiveBinaryHistoryGate (P : Matrix (A × W) (A × W) ℂ) :
    Matrix (A × (W × Fin 2 × Bool)) (A × (W × Fin 2 × Bool)) ℂ :=
  adaptiveHistoryLift (adaptiveProjectHistoryGate P (0 : Fin 2) 1)

theorem adaptiveBinaryHistoryGate_unitary {P : Matrix (A × W) (A × W) ℂ}
    (hP : IsOrthogonalProjector P) :
    adaptiveBinaryHistoryGate P ∈ Matrix.unitaryGroup (A × (W × Fin 2 × Bool)) ℂ :=
  adaptiveHistoryLift_unitary (adaptiveProjectHistoryGate_unitary hP 0 1)

theorem apply_adaptiveBinaryHistoryGate (P : Matrix (A × W) (A × W) ℂ)
    (ψ : QState (A × W)) (x : A × (W × Fin 2 × Bool)) :
    ApplyGate (adaptiveBinaryHistoryGate P)
      (fun y => if y.2.2.1.val = 0 then ψ (y.1, y.2.1) / Real.sqrt 2 else 0) x =
      adaptiveBinaryHistory P ψ ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2 := by
  have hi : (fun y : A × (W × Fin 2 × Bool) =>
      if y.2.2.1.val = 0 then ψ (y.1, y.2.1) / Real.sqrt 2 else 0) =
      (fun y => TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))
        ((y.1, y.2.1), y.2.2.1) / Real.sqrt 2) := by
    funext y
    have hz : y.2.2.1.val = 0 ↔ y.2.2.1 = 0 := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
    by_cases h : y.2.2.1 = 0 <;> simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, hz, h]
  rw [adaptiveBinaryHistoryGate, hi, apply_adaptiveHistoryLift,
    apply_adaptiveProjectHistoryGate P 0 1 (by decide)]
  by_cases hz : x.2.2.1 = 0
  · simp [adaptiveBinaryHistory, hz]
  · have ho : x.2.2.1 = 1 := by omega
    simp [adaptiveBinaryHistory, ho]

end HistoryLayout

section BinaryQueryBranch

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

def observedQueryChain {I : Type} (accepted : Bool) : ℕ → ObservedCircuit I
  | 0 => .halt accepted
  | k + 1 => .step .query (observedQueryChain accepted k)

noncomputable def observedProjectQueryBranch
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (a b : Bool) (k : ℕ) : ObservedCircuit ((Fin n × Bool) × W) :=
  .project P (.halt a) (observedQueryChain b k)

noncomputable def adaptiveProjectQueryBranchCircuit
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ) (k : ℕ) :
    Circuit ((Fin n × Bool) × (W × Fin 2 × Bool)) :=
  [.gate (adaptiveBinaryHistoryGate P)] ++
    RepeatCircuit (adaptivePaddedQuery (fun h : Fin 2 => decide (h ≠ 0))) k

theorem observedQueryChain_traces {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (accepted : Bool) (k : ℕ) (ψ : QState I) :
    observedTraces O (observedQueryChain accepted k) ψ =
      [⟨(ApplyGate O)^[k] ψ, accepted, k, 0, 0, []⟩] := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih =>
    simp [observedQueryChain, observedTraces, ih, Function.iterate_succ_apply]

noncomputable def adaptiveTwoHistory (ψ₀ ψ₁ : QState ((Fin n × Bool) × W)) :
    QState ((Fin n × Bool) × (W × Fin 2)) :=
  fun x => if x.2.2 = 0 then ψ₀ (x.1, x.2.1) else ψ₁ (x.1, x.2.1)

private theorem paddedQuery_twoHistory (f : Fin n → Bool)
    (ψ₀ ψ₁ : QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle (W := W × Fin 2 × Bool) f)
      (adaptivePaddedQuery (fun h : Fin 2 => decide (h ≠ 0)))
      (adaptiveSpareInput (adaptiveTwoHistory ψ₀ ψ₁)) =
      adaptiveSpareInput (adaptiveTwoHistory ψ₀
        (ApplyGate (workspaceBitOracle (W := W) f) ψ₁)) := by
  funext x
  rw [run_adaptivePaddedQuery]
  by_cases hz : x.2.2.1 = 0
  · simp [adaptiveSpareInput, adaptiveTwoHistory, hz]
  · simp [adaptiveSpareInput, adaptiveTwoHistory, hz, applyGate_workspaceBitOracle]

theorem run_adaptiveTwoHistory_padding (f : Fin n → Bool) (k : ℕ)
    (ψ₀ ψ₁ : QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle (W := W × Fin 2 × Bool) f)
      (RepeatCircuit (adaptivePaddedQuery (fun h : Fin 2 => decide (h ≠ 0))) k)
      (adaptiveSpareInput (adaptiveTwoHistory ψ₀ ψ₁)) =
      adaptiveSpareInput (adaptiveTwoHistory ψ₀
        ((ApplyGate (workspaceBitOracle (W := W) f))^[k] ψ₁)) := by
  induction k generalizing ψ₁ with
  | zero => rfl
  | succ k ih =>
    rw [RepeatCircuit, run_append, paddedQuery_twoHistory, ih,
      Function.iterate_succ_apply]

theorem adaptiveProjectQueryBranchCircuit_cost_and_unitary
    {P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ}
    (hP : IsOrthogonalProjector P) (k : ℕ) :
    IsUnitaryCircuit (adaptiveProjectQueryBranchCircuit P k) ∧
      QueryCount (adaptiveProjectQueryBranchCircuit P k) = k ∧
      GateCount (adaptiveProjectQueryBranchCircuit P k) = 1 + 2*k := by
  have hpad := adaptivePaddedQuery_cost_and_unitary
    (n := n) (W := W) (fun h : Fin 2 => decide (h ≠ 0))
  refine ⟨?_, ?_, ?_⟩
  · exact (isUnitaryCircuit_append _ _).mpr
      ⟨by simpa using adaptiveBinaryHistoryGate_unitary hP, hpad.1.repeatCircuit k⟩
  · simp only [adaptiveProjectQueryBranchCircuit, queryCount_append,
      queryCount_repeatCircuit, queryCount_gate, queryCount_nil, hpad.2.1,
      zero_add, mul_one]
  · simp only [adaptiveProjectQueryBranchCircuit, gateCount_append,
      gateCount_repeatCircuit, gateCount_gate, gateCount_nil, hpad.2.2]
    omega

theorem run_adaptiveProjectQueryBranchCircuit
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (k : ℕ) (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle (W := W × Fin 2 × Bool) f)
      (adaptiveProjectQueryBranchCircuit P k) (deferredObservedInput (R := 1) ψ) =
      adaptiveSpareInput (adaptiveTwoHistory (ProjectiveBranch P false ψ)
        ((ApplyGate (workspaceBitOracle (W := W) f))^[k] (ProjectiveBranch P true ψ))) := by
  have hm : ApplyGate (adaptiveBinaryHistoryGate P) (deferredObservedInput (R := 1) ψ) =
      adaptiveSpareInput (adaptiveTwoHistory
        (ProjectiveBranch P false ψ) (ProjectiveBranch P true ψ)) := by
    funext y
    simpa only [deferredObservedInput, adaptiveSpareInput, adaptiveTwoHistory,
      adaptiveBinaryHistory] using! apply_adaptiveBinaryHistoryGate P ψ y
  simp only [adaptiveProjectQueryBranchCircuit, run_append, run_gate, run_nil, hm,
    run_adaptiveTwoHistory_padding]

theorem observed_project_query_branch_purification
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (a b : Bool) (k : ℕ) (f : Fin n → Bool)
    (ψ : QState ((Fin n × Bool) × W))
    (x : (Fin n × Bool) × (W × Fin 2 × Bool)) :
    Run (workspaceBitOracle (W := W × Fin 2 × Bool) f)
      (adaptiveProjectQueryBranchCircuit P k) (deferredObservedInput (R := 1) ψ) x =
      ((observedTraces (workspaceBitOracle (W := W) f)
        (observedProjectQueryBranch P a b k) ψ).getD
          x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2 := by
  rw [run_adaptiveProjectQueryBranchCircuit]
  simp only [observedProjectQueryBranch, observedTraces, observedQueryChain_traces,
    List.map_cons, List.map_nil, List.singleton_append]
  by_cases hz : x.2.2.1 = 0
  · simp [adaptiveSpareInput, adaptiveTwoHistory, hz]
  · have ho : x.2.2.1 = 1 := by omega
    simp [adaptiveSpareInput, adaptiveTwoHistory, ho]

omit [Fintype W] [DecidableEq W] in

theorem observedProjectQueryBranch_depth
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (a b : Bool) (k : ℕ) : observedQueryDepth (observedProjectQueryBranch P a b k) = k := by
  have hc : ∀ j, observedQueryDepth (observedQueryChain (I := (Fin n × Bool) × W) b j) = j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp [observedQueryChain, observedQueryDepth, ih]
  simp [observedProjectQueryBranch, observedQueryDepth, hc]

theorem observed_project_query_branch_same_cost
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (hP : IsOrthogonalProjector P) (a b : Bool) (k : ℕ) :
    ∃ C : Circuit ((Fin n × Bool) × (W × Fin 2 × Bool)),
      IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth (observedProjectQueryBranch P a b k) ∧
      GateCount C ≤ 10 * observedTreeNodes (observedProjectQueryBranch P a b k) *
        (observedQueryDepth (observedProjectQueryBranch P a b k) + 1) ∧
      ∀ (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)),
      let ts :=
          observedTraces (workspaceBitOracle (W := W) f) (observedProjectQueryBranch P a b k) ψ
      ts.length ≤ 2 ∧
      ∀ x : (Fin n × Bool) × (W × Fin 2 × Bool),
        Run (workspaceBitOracle (W := W × Fin 2 × Bool) f) C (deferredObservedInput (R := 1) ψ) x =
          (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2 := by
  have hcost := adaptiveProjectQueryBranchCircuit_cost_and_unitary hP k
  refine ⟨adaptiveProjectQueryBranchCircuit P k, hcost.1, ?_, ?_, ?_⟩
  · rw [observedProjectQueryBranch_depth]
    exact hcost.2.1
  · have hc : ∀ j, observedTreeNodes (observedQueryChain (I := (Fin n × Bool) × W) b j) = j + 1 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => simp [observedQueryChain, observedTreeNodes, ih]
    rw [hcost.2.2, observedProjectQueryBranch_depth]
    simp only [observedProjectQueryBranch, observedTreeNodes, hc]
    nlinarith
  · intro f ψ
    refine ⟨?_, observed_project_query_branch_purification P a b k f ψ⟩
    simp [observedProjectQueryBranch, observedTraces, observedQueryChain_traces]

def adaptiveBinaryHistoryEvent (a b : Bool) :
    Finset ((Fin n × Bool) × (W × Fin 2 × Bool)) :=
  Finset.univ.filter (fun x => if x.2.2.1 = 0 then a else b)

omit [DecidableEq W] in

theorem adaptiveTwoHistory_readout (a b : Bool)
    (ψ₀ ψ₁ : QState ((Fin n × Bool) × W)) :
    MeasureProb (adaptiveSpareInput (adaptiveTwoHistory ψ₀ ψ₁)) (adaptiveBinaryHistoryEvent a b) =
      (if a then branchMass ψ₀ else 0) + (if b then branchMass ψ₁ else 0) := by
  cases a <;> cases b <;>
    simp [adaptiveBinaryHistoryEvent, MeasureProb, BornProb, branchMass,
      adaptiveSpareInput, adaptiveTwoHistory, Finset.sum_filter,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      div_pow, Finset.sum_add_distrib]

theorem observed_project_query_branch_acceptance_transport
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (a b : Bool) (k : ℕ) (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)) :
    MeasureProb (Run (workspaceBitOracle (W := W × Fin 2 × Bool) f)
      (adaptiveProjectQueryBranchCircuit P k) (deferredObservedInput (R := 1) ψ))
      (adaptiveBinaryHistoryEvent a b) =
      observedAcceptance (workspaceBitOracle (W := W) f) (observedProjectQueryBranch P a b k) ψ := by
  rw [run_adaptiveProjectQueryBranchCircuit, adaptiveTwoHistory_readout, observedAcceptance_eq_sum]
  cases a <;> cases b <;>
    simp [observedProjectQueryBranch, observedTraces, observedQueryChain_traces]

theorem observed_project_query_branch_multilinear_polynomial
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (hP : IsOrthogonalProjector P) (a b : Bool) (k : ℕ)
    (ψ : QState ((Fin n × Bool) × W)) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ 2 * observedQueryDepth (observedProjectQueryBranch P a b k) ∧
      (∀ d : Fin n →₀ ℕ, p.coeff d ≠ 0 → ∀ i, d i ≤ 1) ∧
      ∀ f : Fin n → Bool, MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p =
        observedAcceptance (workspaceBitOracle (W := W) f) (observedProjectQueryBranch P a b k) ψ := by
  have hc := adaptiveProjectQueryBranchCircuit_cost_and_unitary hP k
  obtain ⟨hd, hm, he⟩ := acceptance_boolean_multilinearization_preserves_run
    (adaptiveProjectQueryBranchCircuit P k) (deferredObservedInput (R := 1) ψ)
    (adaptiveBinaryHistoryEvent a b)
  refine ⟨_, ?_, hm, ?_⟩
  · simpa only [hc.2.1, observedProjectQueryBranch_depth] using hd
  · intro f
    exact (he f).trans (observed_project_query_branch_acceptance_transport P a b k f ψ)

end BinaryQueryBranch

section BranchPolynomials

noncomputable def observedBranchWords {I : Type} [Fintype I] [DecidableEq I] :
    ObservedCircuit I → List (Bool × Circuit I)
  | .halt a => [(a, [])]
  | .step s P => (observedBranchWords P).map (fun b => (b.1, s :: b.2))
  | .measure k label next =>
      (List.ofFn (fun o : Fin k => (observedBranchWords (next o)).map
        (fun b => (b.1, .gate (Projector (Finset.univ.filter (fun i => label i = o))) :: b.2)))).flatten
  | .project A P Q =>
      (observedBranchWords P).map (fun b => (b.1, .gate (1 - A) :: b.2)) ++
      (observedBranchWords Q).map (fun b => (b.1, .gate A :: b.2))

theorem observedBranchWords_traces {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    (observedTraces O P ψ).map (fun t => (t.state, t.accepted, t.queries)) =
      (observedBranchWords P).map (fun b => (Run O b.2 ψ, b.1, QueryCount b.2)) := by
  induction P generalizing ψ with
  | halt a => simp [observedTraces, observedBranchWords]
  | step s P ih =>
    cases s with
    | gate U =>
      simpa [observedTraces, observedBranchWords, List.map_map, Function.comp_def] using
        ih (ApplyGate U ψ)
    | query =>
      simpa [observedTraces, observedBranchWords, List.map_map, Function.comp_def] using
        congrArg (List.map (fun t : QState I × Bool × ℕ =>
          (t.1, t.2.1, t.2.2 + 1))) (ih (ApplyGate O ψ))
  | measure k label next ih =>
    simp only [observedTraces, observedBranchWords, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def]
    congr 2
    funext o
    simpa [Collapse, List.map_map, Function.comp_def] using
      ih o (Collapse ψ (Finset.univ.filter (fun i => label i = o)))
  | project A P Q ihP ihQ =>
    simpa [observedTraces, observedBranchWords, List.map_append,
      List.map_map, Function.comp_def, ProjectiveBranch] using
      congrArg₂ List.append (ihP (ProjectiveBranch A false ψ))
        (ihQ (ProjectiveBranch A true ψ))

theorem observedBranchWords_queryCount_le (n : ℕ) (W : Type)
    [Fintype W] [DecidableEq W]
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (b : Bool × Circuit ((Fin n × Bool) × W)) (hb : b ∈ observedBranchWords P) :
    QueryCount b.2 ≤ observedQueryDepth P := by
  let O := workspaceBitOracle (W := W) (fun _ : Fin n => false)
  have hm : (Run O b.2 0, b.1, QueryCount b.2) ∈
      (observedTraces O P 0).map (fun t => (t.state, t.accepted, t.queries)) := by
    rw [observedBranchWords_traces]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
  have hq := congrArg (fun x : QState ((Fin n × Bool) × W) × Bool × ℕ => x.2.2) he
  change t.queries = QueryCount b.2 at hq
  rw [← hq]
  exact observed_query_depth_all_trace_bound n W P (fun _ => false) 0 t ht

theorem observedAcceptance_eq_branchWords {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    observedAcceptance O P ψ =
      ((observedBranchWords P).map
        (fun b => if b.1 then branchMass (Run O b.2 ψ) else 0)).sum := by
  rw [← observedEventMass_accepted]
  have h := congrArg (fun xs : List (QState I × Bool × ℕ) =>
    (xs.map (fun t => if t.2.1 then branchMass t.1 else 0)).sum)
    (observedBranchWords_traces O P ψ)
  simpa only [observedEventMass, List.map_map, Function.comp_def] using h

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

noncomputable def observedRawAcceptancePolynomial
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)) :
    MvPolynomial (Fin n) ℝ :=
  ((observedBranchWords P).map (fun b =>
    if b.1 then rawAcceptancePolynomial b.2 ψ Finset.univ else 0)).sum

private theorem adaptivePolynomial_list_degree {α : Type}
    (xs : List α) (g : α → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : ∀ x ∈ xs, (g x).totalDegree ≤ d) : (xs.map g).sum.totalDegree ≤ d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hd x List.mem_cons_self)
        (ih (fun y hy => hd y (List.mem_cons_of_mem x hy))))

theorem observedRawAcceptancePolynomial_degree
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)) :
    (observedRawAcceptancePolynomial P ψ).totalDegree ≤ 2 * observedQueryDepth P := by
  apply adaptivePolynomial_list_degree
  intro b hb
  cases b.1
  · simp
  · simp only [↓reduceIte]
    exact (acceptance_polynomial_actual_born_and_degree b.2 ψ Finset.univ
      (fun _ => false)).2.trans
        (Nat.mul_le_mul_left 2 (observedBranchWords_queryCount_le n W P b hb))

theorem observedRawAcceptancePolynomial_eval
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (f : Fin n → Bool) :
    MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0)
      (observedRawAcceptancePolynomial P ψ) =
      observedAcceptance (workspaceBitOracle (W := W) f) P ψ := by
  rw [observedAcceptance_eq_branchWords, observedRawAcceptancePolynomial, map_list_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b.1
  · simp
  · simp only [↓reduceIte]
    exact (acceptance_polynomial_actual_born_and_degree b.2 ψ Finset.univ f).1

theorem observed_actual_multilinear_acceptance_polynomial
    (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (_hn : 0 < n) (_hP : observedWellFormed P) (_hψ : Normalized ψ) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 2 * observedQueryDepth P ∧
      (∀ d : Fin n →₀ ℕ, p.coeff d ≠ 0 → ∀ i, d i ≤ 1) ∧
      ∀ f : Fin n → Bool, MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p =
        observedAcceptance (workspaceBitOracle (W := W) f) P ψ := by
  refine ⟨multilinearize (observedRawAcceptancePolynomial P ψ),
    (multilinearize_totalDegree_le _).trans (observedRawAcceptancePolynomial_degree P ψ),
    multilinearize_coeff_multilinear _, ?_⟩
  intro f
  rw [multilinearize_eval _ _ (fun i => by cases f i <;> simp)]
  exact observedRawAcceptancePolynomial_eval P ψ f

end BranchPolynomials

section QueryFreeHistory

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def adaptiveBranchMatrix (O : Matrix I I ℂ) : Circuit I → Matrix I I ℂ
  | [] => 1
  | .gate U :: C => adaptiveBranchMatrix O C * U
  | .query :: C => adaptiveBranchMatrix O C * O

theorem adaptiveBranchMatrix_apply (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    ApplyGate (adaptiveBranchMatrix O C) ψ = Run O C ψ := by
  induction C generalizing ψ with
  | nil => simp [adaptiveBranchMatrix]
  | cons s C ih => cases s <;> simp [adaptiveBranchMatrix, applyGate_mul, ih]

theorem observedBranchWords_states (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    (observedTraces O P ψ).map BranchTrace.state =
      (observedBranchWords P).map (fun b => Run O b.2 ψ) := by
  have h := congrArg (List.map (fun x : QState I × Bool × ℕ => x.1))
    (observedBranchWords_traces O P ψ)
  simpa only [List.map_map, Function.comp_def] using h

omit [DecidableEq I] in

theorem adaptiveListHistory_mass (vs : List (QState I)) (K : ℕ) (hK : vs.length ≤ K) :
    branchMass (fun x : I × Fin K => (vs.getD x.2.val 0) x.1) =
      (vs.map branchMass).sum := by
  induction K generalizing vs with
  | zero =>
    have hv : vs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hK)
    simp [hv, branchMass, MeasureProb]
  | succ K ih =>
    cases vs with
    | nil => simp [branchMass, MeasureProb, BornProb]
    | cons v vs =>
      have hm : branchMass (fun x : I × Fin (K + 1) => ((v :: vs).getD x.2.val 0) x.1) =
          branchMass v + branchMass (fun x : I × Fin K => (vs.getD x.2.val 0) x.1) := by
        simp [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type,
          Fin.sum_univ_succ, Finset.sum_add_distrib]
      rw [hm, ih vs (by simpa using hK)]
      simp

omit [DecidableEq I] in

theorem adaptiveHistoryIsometries_transport {J : Type} [Fintype J] [DecidableEq J]
    (E F : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J) :
    ∃ U : Matrix J J ℂ, U ∈ Matrix.unitaryGroup J ℂ ∧
      ∀ ψ : EuclideanSpace ℂ I, U.toEuclideanLin (E ψ) = F ψ := by
  let L := F.comp E.equivRange.symm.toLinearIsometry
  obtain ⟨U, hU, hact⟩ := adaptiveHistoryIsometry_extension E.toLinearMap.range L
  refine ⟨U, hU, ?_⟩
  intro ψ
  have h := hact (E.equivRange ψ)
  simpa [L] using h

noncomputable def adaptiveLeafHistoryMatrix (P : ObservedCircuit I) :
    Matrix (I × Fin ((observedBranchWords P).length + 1)) I ℂ :=
  fun x i => if h : x.2.val < (observedBranchWords P).length then
    adaptiveBranchMatrix 1 ((observedBranchWords P).get ⟨x.2.val, h⟩).2 x.1 i else 0

theorem adaptiveLeafHistoryMatrix_apply (P : ObservedCircuit I) (ψ : QState I)
    (x : I × Fin ((observedBranchWords P).length + 1)) :
    (adaptiveLeafHistoryMatrix P *ᵥ ψ) x =
      (((observedBranchWords P).map (fun b => Run 1 b.2 ψ)).getD x.2.val 0) x.1 := by
  by_cases h : x.2.val < (observedBranchWords P).length
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_map]
    have hr := congrFun (adaptiveBranchMatrix_apply 1
      ((observedBranchWords P).get ⟨x.2.val, h⟩).2 ψ) x.1
    simpa only [ApplyGate, Matrix.mulVec, dotProduct, adaptiveLeafHistoryMatrix,
      dif_pos h] using! hr
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
    simp [adaptiveLeafHistoryMatrix, h, Matrix.mulVec, dotProduct]

theorem adaptiveLeafHistoryMatrix_mass (P : ObservedCircuit I) (hP : observedWellFormed P)
    (ψ : QState I) : branchMass (adaptiveLeafHistoryMatrix P *ᵥ ψ) = branchMass ψ := by
  have h := adaptiveListHistory_mass ((observedBranchWords P).map (fun b => Run 1 b.2 ψ))
    ((observedBranchWords P).length + 1) (by simp)
  have hv : adaptiveLeafHistoryMatrix P *ᵥ ψ =
      (fun x => (((observedBranchWords P).map (fun b => Run 1 b.2 ψ)).getD x.2.val 0) x.1) :=
    funext (adaptiveLeafHistoryMatrix_apply P ψ)
  rw [← hv, ← observedBranchWords_states 1 P ψ, List.map_map, Function.comp_def] at h
  exact h.trans (observedTraces_mass 1 (Submonoid.one_mem _) P hP ψ)

noncomputable def adaptiveLeafHistoryIsometry (P : ObservedCircuit I)
    (hP : observedWellFormed P) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I × Fin ((observedBranchWords P).length + 1)) where
  toLinearMap := (adaptiveLeafHistoryMatrix P).toEuclideanLin
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toEuclidean_fromVec (adaptiveLeafHistoryMatrix P *ᵥ WithLp.ofLp ψ)‖ ^ 2 =
      ‖toEuclidean_fromVec (WithLp.ofLp ψ)‖ ^ 2
    simp only [norm_toEuclidean_fromVec_sq]
    exact adaptiveLeafHistoryMatrix_mass P hP (WithLp.ofLp ψ)

noncomputable def adaptiveBlankHistoryMatrix (R : ℕ) : Matrix (I × Fin (R + 1)) I ℂ :=
  fun x i => if x.2 = 0 then (1 : Matrix I I ℂ) x.1 i else 0

theorem adaptiveBlankHistoryMatrix_apply (R : ℕ) (ψ : QState I) (x : I × Fin (R + 1)) :
    (adaptiveBlankHistoryMatrix R *ᵥ ψ) x = if x.2 = 0 then ψ x.1 else 0 := by
  by_cases h : x.2 = 0
  · simpa only [Matrix.mulVec, dotProduct, adaptiveBlankHistoryMatrix, h, ↓reduceIte] using
      congrFun (Matrix.one_mulVec ψ) x.1
  · simp [adaptiveBlankHistoryMatrix, h, Matrix.mulVec, dotProduct]

noncomputable def adaptiveBlankHistoryIsometry (R : ℕ) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I × Fin (R + 1)) where
  toLinearMap := (adaptiveBlankHistoryMatrix R).toEuclideanLin
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toEuclidean_fromVec (adaptiveBlankHistoryMatrix R *ᵥ WithLp.ofLp ψ)‖ ^ 2 =
      ‖toEuclidean_fromVec (WithLp.ofLp ψ)‖ ^ 2
    simp [norm_toEuclidean_fromVec_sq, adaptiveBlankHistoryMatrix_apply,
      Fintype.sum_prod_type, apply_ite]

end QueryFreeHistory

section QueryFreeCompilation

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

theorem observed_zero_query_full_branch_purification
    (P : ObservedCircuit ((Fin n × Bool) × W)) (hP : observedWellFormed P)
    (hd : observedQueryDepth P = 0) :
    ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
      IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth P ∧
      GateCount C ≤ 10 * observedTreeNodes P * (observedQueryDepth P + 1) ∧
      ∀ (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)),
      let ts := observedTraces (workspaceBitOracle (W := W) f) P ψ
      ts.length ≤ R + 1 ∧
      ∀ x : (Fin n × Bool) × (W × Fin (R + 1) × Bool),
        Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) f) C
          (deferredObservedInput (R := R) ψ) x =
          (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2 := by
  let R := (observedBranchWords P).length
  obtain ⟨U, hU, hact⟩ := adaptiveHistoryIsometries_transport
    (adaptiveBlankHistoryIsometry (I := (Fin n × Bool) × W) R)
    (adaptiveLeafHistoryIsometry P hP)
  refine ⟨R, [.gate (adaptiveHistoryLift U)], ?_, ?_, ?_, ?_⟩
  · simpa using adaptiveHistoryLift_unitary hU
  · simp [hd]
  · have hn : 0 < observedTreeNodes P := by cases P <;> simp only [observedTreeNodes] <;> omega
    simp only [gateCount_gate, gateCount_nil, hd, zero_add, mul_one]
    omega
  · intro f ψ
    have hs := observedBranchWords_states (workspaceBitOracle (W := W) f) P ψ
    have hlen := congrArg List.length hs
    simp only [List.length_map] at hlen
    refine ⟨by dsimp [R]; omega, ?_⟩
    intro x
    have hwords : (observedBranchWords P).map (fun b => Run 1 b.2 ψ) =
        (observedTraces (workspaceBitOracle (W := W) f) P ψ).map BranchTrace.state := by
      rw [hs]
      apply List.map_congr_left
      intro b hb
      have hq : QueryCount b.2 = 0 :=
        Nat.eq_zero_of_le_zero (hd ▸ observedBranchWords_queryCount_le n W P b hb)
      exact run_eq_of_queryCount_eq_zero 1 (workspaceBitOracle (W := W) f) b.2 hq ψ
    have hm : ApplyGate U (adaptiveBlankHistoryMatrix R *ᵥ ψ) =
        adaptiveLeafHistoryMatrix P *ᵥ ψ := by
      have hh := hact (toEuclidean_fromVec ψ)
      exact congrArg WithLp.ofLp hh
    have hi : deferredObservedInput (R := R) ψ =
        (fun y => (adaptiveBlankHistoryMatrix R *ᵥ ψ)
          ((y.1, y.2.1), y.2.2.1) / Real.sqrt 2) := by
      funext y
      rw [adaptiveBlankHistoryMatrix_apply]
      have hz : y.2.2.1.val = 0 ↔ y.2.2.1 = 0 := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
      by_cases h : y.2.2.1 = 0 <;> simp [deferredObservedInput, hz, h]
    rw [run_gate, run_nil, hi, apply_adaptiveHistoryLift, hm, adaptiveLeafHistoryMatrix_apply,
      hwords]
    exact congrArg (fun v : QState ((Fin n × Bool) × W) => v (x.1, x.2.1) / Real.sqrt 2)
      (List.getD_map (observedTraces (workspaceBitOracle (W := W) f) P ψ)
        (emptyObservedTrace _) BranchTrace.state (n := x.2.2.1.val))

end QueryFreeCompilation

section QueryFrontiers

@[reducible] def adaptiveFrontierType {I : Type} : ObservedCircuit I → ℕ → Type
  | .halt _, _ => Unit
  | .step (.gate _) P, j => adaptiveFrontierType P j
  | .step .query _, 0 => Unit
  | .step .query P, j + 1 => adaptiveFrontierType P j
  | .measure k _ next, j => (o : Fin k) × adaptiveFrontierType (next o) j
  | .project _ P Q, j => adaptiveFrontierType P j ⊕ adaptiveFrontierType Q j

@[reducible] private noncomputable def adaptiveFrontierFintype {I : Type} :
    (P : ObservedCircuit I) → (j : ℕ) → Fintype (adaptiveFrontierType P j)
  | .halt _, _ => inferInstance
  | .step (.gate _) P, j => adaptiveFrontierFintype P j
  | .step .query _, 0 => inferInstance
  | .step .query P, j + 1 => adaptiveFrontierFintype P j
  | .measure k _ next, j => by
      letI (o : Fin k) := adaptiveFrontierFintype (next o) j
      exact inferInstance
  | .project _ P Q, j => by
      letI := adaptiveFrontierFintype P j
      letI := adaptiveFrontierFintype Q j
      exact inferInstance

noncomputable instance {I : Type} (P : ObservedCircuit I) (j : ℕ) :
    Fintype (adaptiveFrontierType P j) := adaptiveFrontierFintype P j

noncomputable instance {I : Type} (P : ObservedCircuit I) (j : ℕ) :
    DecidableEq (adaptiveFrontierType P j) := Classical.decEq _

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def adaptiveFrontierRun (O : Matrix I I ℂ) :
    (P : ObservedCircuit I) → (j : ℕ) → QState I → QState (I × adaptiveFrontierType P j)
  | .halt _, _, ψ => fun x => ψ x.1
  | .step (.gate U) P, j, ψ => adaptiveFrontierRun O P j (ApplyGate U ψ)
  | .step .query _, 0, ψ => fun x => ψ x.1
  | .step .query P, j + 1, ψ => adaptiveFrontierRun O P j (ApplyGate O ψ)
  | .measure _ label next, j, ψ => fun x =>
      adaptiveFrontierRun O (next x.2.1) j
        (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1))) (x.1, x.2.2)
  | .project A P Q, j, ψ => fun x => match x.2 with
      | .inl h => adaptiveFrontierRun O P j (ProjectiveBranch A false ψ) (x.1, h)
      | .inr h => adaptiveFrontierRun O Q j (ProjectiveBranch A true ψ) (x.1, h)

omit [DecidableEq I] in

private theorem adaptiveSigma_mass {K : Type} [Fintype K]
    {H : K → Type} [∀ k, Fintype (H k)]
    (v : ∀ k, QState (I × H k)) :
    branchMass (fun x : I × Sigma H => v x.2.1 (x.1, x.2.2)) =
      ∑ k, branchMass (v k) := by
  simp only [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type, Fintype.sum_sigma]
  rw [Finset.sum_comm]

omit [DecidableEq I] in

private theorem adaptiveSum_mass {H K : Type} [Fintype H] [Fintype K]
    (v : QState (I × H)) (w : QState (I × K)) :
    branchMass (fun x : I × (H ⊕ K) => Sum.elim
      (fun h => v (x.1, h)) (fun k => w (x.1, k)) x.2) =
      branchMass v + branchMass w := by
  simp [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem adaptiveFrontierRun_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (j : ℕ) (ψ : QState I) :
    branchMass (adaptiveFrontierRun O P j ψ) = branchMass ψ := by
  induction P generalizing j ψ with
  | halt a => simp [adaptiveFrontierRun, branchMass, MeasureProb, BornProb,
      Fintype.sum_prod_type]
  | step s P ih =>
    cases s with
    | gate U =>
      rw [adaptiveFrontierRun, ih hP.2]
      exact measureProb_applyGate_univ hP.1 ψ
    | query =>
      cases j with
      | zero => simp [adaptiveFrontierRun, branchMass, MeasureProb, BornProb,
          Fintype.sum_prod_type]
      | succ j =>
        rw [adaptiveFrontierRun, ih hP]
        exact measureProb_applyGate_univ hO ψ
  | measure k label next ih =>
    change branchMass (fun x : I × Sigma (fun o => adaptiveFrontierType (next o) j) =>
      adaptiveFrontierRun O (next x.2.1) j
        (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1)))
        (x.1, x.2.2)) = _
    rw [adaptiveSigma_mass (fun o => adaptiveFrontierRun O (next o) j
      (Collapse ψ (Finset.univ.filter (fun i => label i = o))))]
    simp only [ih _ (hP _)]
    exact sum_measureProb_collapse_partition ψ label
  | project A P Q ihP ihQ =>
    have he : adaptiveFrontierRun O (.project A P Q) j ψ =
      (fun x : I × (adaptiveFrontierType P j ⊕ adaptiveFrontierType Q j) =>
      Sum.elim (fun h => adaptiveFrontierRun O P j (ProjectiveBranch A false ψ) (x.1, h))
        (fun h => adaptiveFrontierRun O Q j (ProjectiveBranch A true ψ) (x.1, h)) x.2) := by
      funext x
      rcases x with ⟨i, h⟩
      cases h <;> rfl
    rw [he, adaptiveSum_mass, ihP hP.2.1, ihQ hP.2.2]
    exact projectiveBranchMass_add hP.1 ψ

def adaptiveFrontierActive : (P : ObservedCircuit I) → (j : ℕ) →
    adaptiveFrontierType P j → Bool
  | .halt _, _, _ => false
  | .step (.gate _) P, j, h => adaptiveFrontierActive P j h
  | .step .query _, 0, _ => true
  | .step .query P, j + 1, h => adaptiveFrontierActive P j h
  | .measure _ _ next, j, h => adaptiveFrontierActive (next h.1) j h.2
  | .project _ P _, j, .inl h => adaptiveFrontierActive P j h
  | .project _ _ Q, j, .inr h => adaptiveFrontierActive Q j h

noncomputable def adaptiveFrontierAdvance : (P : ObservedCircuit I) → (j : ℕ) →
    QState (I × adaptiveFrontierType P j) → QState (I × adaptiveFrontierType P (j + 1))
  | .halt _, _, v => v
  | .step (.gate _) P, j, v => adaptiveFrontierAdvance P j v
  | .step .query P, 0, v => adaptiveFrontierRun 1 P 0 (fun i => v (i, ()))
  | .step .query P, j + 1, v => adaptiveFrontierAdvance P j v
  | .measure _ _ next, j, v => fun x =>
      adaptiveFrontierAdvance (next x.2.1) j (fun y => v (y.1, ⟨x.2.1, y.2⟩))
        (x.1, x.2.2)
  | .project _ P Q, j, v => fun x => match x.2 with
      | .inl h => adaptiveFrontierAdvance P j (fun y => v (y.1, .inl y.2)) (x.1, h)
      | .inr h => adaptiveFrontierAdvance Q j (fun y => v (y.1, .inr y.2)) (x.1, h)

theorem adaptiveFrontierAdvance_mass (P : ObservedCircuit I)
    (hP : observedWellFormed P) (j : ℕ)
    (v : QState (I × adaptiveFrontierType P j)) :
    branchMass (adaptiveFrontierAdvance P j v) = branchMass v := by
  induction P generalizing j with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U => exact ih hP.2 j v
    | query =>
      cases j with
      | zero =>
        rw [adaptiveFrontierAdvance, adaptiveFrontierRun_mass 1 (Submonoid.one_mem _) P hP]
        simp [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type]
      | succ j => exact ih hP j v
  | measure k label next ih =>
    change branchMass (fun x : I × Sigma (fun o => adaptiveFrontierType (next o) (j + 1)) =>
      adaptiveFrontierAdvance (next x.2.1) j (fun y => v (y.1, ⟨x.2.1, y.2⟩))
        (x.1, x.2.2)) = _
    rw [adaptiveSigma_mass (fun o => adaptiveFrontierAdvance (next o) j
      (fun y => v (y.1, ⟨o, y.2⟩)))]
    simp only [ih _ (hP _)]
    exact (adaptiveSigma_mass (fun o y => v (y.1, ⟨o, y.2⟩))).symm
  | project A P Q ihP ihQ =>
    have he : adaptiveFrontierAdvance (.project A P Q) j v =
      (fun x : I × (adaptiveFrontierType P (j + 1) ⊕
        adaptiveFrontierType Q (j + 1)) => Sum.elim
      (fun h => adaptiveFrontierAdvance P j (fun y => v (y.1, .inl y.2)) (x.1, h))
      (fun h => adaptiveFrontierAdvance Q j (fun y => v (y.1, .inr y.2)) (x.1, h)) x.2) := by
      funext x
      rcases x with ⟨i, h⟩
      cases h <;> rfl
    rw [he, adaptiveSum_mass, ihP hP.2.1, ihQ hP.2.2]
    convert (adaptiveSum_mass (fun y => v (y.1, .inl y.2))
      (fun y => v (y.1, .inr y.2))).symm using 1
    congr 1
    funext ⟨i, h⟩
    cases h <;> rfl

theorem adaptiveFrontierRun_zero_eq (O O' : Matrix I I ℂ) (P : ObservedCircuit I)
    (ψ : QState I) : adaptiveFrontierRun O P 0 ψ = adaptiveFrontierRun O' P 0 ψ := by
  induction P generalizing ψ with
  | halt a => rfl
  | step s P ih => cases s with
    | gate U => exact ih (ApplyGate U ψ)
    | query => rfl
  | measure k label next ih =>
    funext x
    exact congrFun (ih x.2.1 (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1))))
      (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext x
    rcases x with ⟨i, h⟩
    cases h with
    | inl h => exact congrFun (ihP (ProjectiveBranch A false ψ)) (i, h)
    | inr h => exact congrFun (ihQ (ProjectiveBranch A true ψ)) (i, h)

noncomputable def adaptiveFrontierQuery (O : Matrix I I ℂ) (P : ObservedCircuit I) (j : ℕ)
    (v : QState (I × adaptiveFrontierType P j)) : QState (I × adaptiveFrontierType P j) :=
  fun x => if adaptiveFrontierActive P j x.2 then
    ApplyGate O (fun i => v (i, x.2)) x.1 else v x

theorem adaptiveFrontierAdvance_query (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (j : ℕ) (ψ : QState I) :
    adaptiveFrontierAdvance P j (adaptiveFrontierQuery O P j (adaptiveFrontierRun O P j ψ)) =
      adaptiveFrontierRun O P (j + 1) ψ := by
  induction P generalizing j ψ with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U => exact ih j (ApplyGate U ψ)
    | query =>
      cases j with
      | zero => exact adaptiveFrontierRun_zero_eq 1 O P (ApplyGate O ψ)
      | succ j => exact ih j (ApplyGate O ψ)
  | measure k label next ih =>
    funext x
    exact congrFun (ih x.2.1 j
      (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1)))) (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext x
    rcases x with ⟨i, h⟩
    cases h with
    | inl h => exact congrFun (ihP j (ProjectiveBranch A false ψ)) (i, h)
    | inr h => exact congrFun (ihQ j (ProjectiveBranch A true ψ)) (i, h)

theorem adaptiveFrontierRun_add (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (j : ℕ) (ψ φ : QState I) :
    adaptiveFrontierRun O P j (ψ + φ) =
      adaptiveFrontierRun O P j ψ + adaptiveFrontierRun O P j φ := by
  induction P generalizing j ψ φ with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U =>
      simpa only [adaptiveFrontierRun, ApplyGate, Matrix.mulVec_add] using
        (ih j (ApplyGate U ψ) (ApplyGate U φ))
    | query => cases j with
      | zero => rfl
      | succ j =>
        simpa only [adaptiveFrontierRun, ApplyGate, Matrix.mulVec_add] using
          (ih j (ApplyGate O ψ) (ApplyGate O φ))
  | measure k label next ih =>
    funext x
    simpa only [adaptiveFrontierRun, Collapse, ApplyGate, Matrix.mulVec_add, Pi.add_apply] using
      congrFun (ih x.2.1 j (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1)))
        (Collapse φ (Finset.univ.filter (fun i => label i = x.2.1)))) (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext ⟨i, h⟩
    cases h with
    | inl h => simpa only [adaptiveFrontierRun, ProjectiveBranch, ApplyGate,
        Matrix.mulVec_add, Pi.add_apply] using
        congrFun (ihP j (ProjectiveBranch A false ψ) (ProjectiveBranch A false φ)) (i, h)
    | inr h => simpa only [adaptiveFrontierRun, ProjectiveBranch, ApplyGate,
        Matrix.mulVec_add, Pi.add_apply] using
        congrFun (ihQ j (ProjectiveBranch A true ψ) (ProjectiveBranch A true φ)) (i, h)

theorem adaptiveFrontierRun_smul (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (j : ℕ) (c : ℂ) (ψ : QState I) :
    adaptiveFrontierRun O P j (c • ψ) = c • adaptiveFrontierRun O P j ψ := by
  induction P generalizing j ψ with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U =>
      simpa only [adaptiveFrontierRun, ApplyGate, Matrix.mulVec_smul] using
        (ih j (ApplyGate U ψ))
    | query => cases j with
      | zero => rfl
      | succ j =>
        simpa only [adaptiveFrontierRun, ApplyGate, Matrix.mulVec_smul] using
          (ih j (ApplyGate O ψ))
  | measure k label next ih =>
    funext x
    simpa only [adaptiveFrontierRun, Collapse, ApplyGate, Matrix.mulVec_smul, Pi.smul_apply] using
      congrFun (ih x.2.1 j (Collapse ψ (Finset.univ.filter (fun i => label i = x.2.1))))
        (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext ⟨i, h⟩
    cases h with
    | inl h => simpa only [adaptiveFrontierRun, ProjectiveBranch, ApplyGate,
        Matrix.mulVec_smul, Pi.smul_apply] using
        congrFun (ihP j (ProjectiveBranch A false ψ)) (i, h)
    | inr h => simpa only [adaptiveFrontierRun, ProjectiveBranch, ApplyGate,
        Matrix.mulVec_smul, Pi.smul_apply] using
        congrFun (ihQ j (ProjectiveBranch A true ψ)) (i, h)

noncomputable def adaptiveFrontierIsometry (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (j : ℕ) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I × adaptiveFrontierType P j) where
  toLinearMap := LinearMap.withLpMap 2
    { toFun := adaptiveFrontierRun O P j
      map_add' := adaptiveFrontierRun_add O P j
      map_smul' := adaptiveFrontierRun_smul O P j }
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toEuclidean_fromVec (adaptiveFrontierRun O P j (WithLp.ofLp ψ))‖ ^ 2 =
      ‖toEuclidean_fromVec (WithLp.ofLp ψ)‖ ^ 2
    simp only [norm_toEuclidean_fromVec_sq]
    exact adaptiveFrontierRun_mass O hO P hP j (WithLp.ofLp ψ)

theorem adaptiveFrontierAdvance_add (P : ObservedCircuit I) (j : ℕ)
    (v w : QState (I × adaptiveFrontierType P j)) :
    adaptiveFrontierAdvance P j (v + w) =
      adaptiveFrontierAdvance P j v + adaptiveFrontierAdvance P j w := by
  induction P generalizing j with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U => exact ih j v w
    | query => cases j with
      | zero => exact adaptiveFrontierRun_add 1 P 0 (fun i => v (i, ())) (fun i => w (i, ()))
      | succ j => exact ih j v w
  | measure k label next ih =>
    funext x
    exact congrFun (ih x.2.1 j (fun y => v (y.1, ⟨x.2.1, y.2⟩))
      (fun y => w (y.1, ⟨x.2.1, y.2⟩))) (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext ⟨i, h⟩
    cases h with
    | inl h => exact congrFun (ihP j (fun y => v (y.1, .inl y.2))
        (fun y => w (y.1, .inl y.2))) (i, h)
    | inr h => exact congrFun (ihQ j (fun y => v (y.1, .inr y.2))
        (fun y => w (y.1, .inr y.2))) (i, h)

theorem adaptiveFrontierAdvance_smul (P : ObservedCircuit I) (j : ℕ) (c : ℂ)
    (v : QState (I × adaptiveFrontierType P j)) :
    adaptiveFrontierAdvance P j (c • v) = c • adaptiveFrontierAdvance P j v := by
  induction P generalizing j with
  | halt a => rfl
  | step s P ih =>
    cases s with
    | gate U => exact ih j v
    | query => cases j with
      | zero => exact adaptiveFrontierRun_smul 1 P 0 c (fun i => v (i, ()))
      | succ j => exact ih j v
  | measure k label next ih =>
    funext x
    exact congrFun (ih x.2.1 j (fun y => v (y.1, ⟨x.2.1, y.2⟩))) (x.1, x.2.2)
  | project A P Q ihP ihQ =>
    funext ⟨i, h⟩
    cases h with
    | inl h => exact congrFun (ihP j (fun y => v (y.1, .inl y.2))) (i, h)
    | inr h => exact congrFun (ihQ j (fun y => v (y.1, .inr y.2))) (i, h)

noncomputable def adaptiveFrontierAdvanceIsometry (P : ObservedCircuit I)
    (hP : observedWellFormed P) (j : ℕ) :
    EuclideanSpace ℂ (I × adaptiveFrontierType P j) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (I × adaptiveFrontierType P (j + 1)) where
  toLinearMap := LinearMap.withLpMap 2
    { toFun := adaptiveFrontierAdvance P j
      map_add' := adaptiveFrontierAdvance_add P j
      map_smul' := adaptiveFrontierAdvance_smul P j }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toEuclidean_fromVec (adaptiveFrontierAdvance P j (WithLp.ofLp v))‖ ^ 2 =
      ‖toEuclidean_fromVec (WithLp.ofLp v)‖ ^ 2
    simp only [norm_toEuclidean_fromVec_sq]
    exact adaptiveFrontierAdvance_mass P hP j (WithLp.ofLp v)

end QueryFrontiers

section AdaptiveCoordinates

variable {K H : Type} [Fintype K] [Fintype H] [DecidableEq K] [DecidableEq H]

noncomputable def adaptiveCoordinateMatrix (e : K ↪ H) : Matrix H K ℂ :=
  fun h k => if e k = h then 1 else 0

omit [Fintype K] in

theorem adaptiveCoordinateMatrix_gram (e : K ↪ H) :
    (adaptiveCoordinateMatrix e)ᴴ * adaptiveCoordinateMatrix e = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, adaptiveCoordinateMatrix,
    apply_ite, star_one, star_zero]
  rw [Finset.sum_eq_single (e a)]
  · simp [e.injective.eq_iff, Matrix.one_apply, eq_comm]
  · intro h _ hne
    simp [Ne.symm hne]
  · simp

noncomputable def adaptiveCoordinateIsometry (e : K ↪ H) :
    EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ H :=
  (Matrix.toEuclideanLin (adaptiveCoordinateMatrix e)).isometryOfInner (by
    intro v w
    change inner ℂ (toEuclidean_fromVec (adaptiveCoordinateMatrix e *ᵥ v.ofLp))
      (toEuclidean_fromVec (adaptiveCoordinateMatrix e *ᵥ w.ofLp)) =
        inner ℂ (toEuclidean_fromVec v.ofLp) (toEuclidean_fromVec w.ofLp)
    rw [inner_euclidean_fromVec, inner_euclidean_fromVec]
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, adaptiveCoordinateMatrix_gram, Matrix.vecMul_one])

omit [Fintype H] in

theorem adaptiveCoordinateMatrix_apply_image (e : K ↪ H) (v : QState K) (k : K) :
    (adaptiveCoordinateMatrix e *ᵥ v) (e k) = v k := by
  simp [adaptiveCoordinateMatrix, Matrix.mulVec, dotProduct, e.injective.eq_iff]

omit [Fintype H] [DecidableEq K] in

theorem adaptiveCoordinateMatrix_apply_outside (e : K ↪ H) (v : QState K) (h : H)
    (hh : ∀ k, e k ≠ h) : (adaptiveCoordinateMatrix e *ᵥ v) h = 0 := by
  simp [adaptiveCoordinateMatrix, Matrix.mulVec, dotProduct, hh]

end AdaptiveCoordinates

section AdaptiveFrontierEnumeration

def adaptiveFrontierEnumeration {I : Type} : (P : ObservedCircuit I) → (j : ℕ) →
    List (adaptiveFrontierType P j)
  | .halt _, _ => [()]
  | .step (.gate _) P, j => adaptiveFrontierEnumeration P j
  | .step .query _, 0 => [()]
  | .step .query P, j + 1 => adaptiveFrontierEnumeration P j
  | .measure k _ next, j =>
      (List.ofFn (fun o : Fin k => (adaptiveFrontierEnumeration (next o) j).map
        (fun h => Sigma.mk o h))).flatten
  | .project _ P Q, j =>
      (adaptiveFrontierEnumeration P j).map Sum.inl ++
        (adaptiveFrontierEnumeration Q j).map Sum.inr

theorem adaptiveFrontierEnumeration_mem {I : Type} (P : ObservedCircuit I) (j : ℕ)
    (h : adaptiveFrontierType P j) : h ∈ adaptiveFrontierEnumeration P j := by
  induction P generalizing j with
  | halt a => cases h; simp [adaptiveFrontierEnumeration]
  | step s P ih => cases s with
    | gate U => exact ih j h
    | query => cases j with
      | zero => cases h; simp [adaptiveFrontierEnumeration]
      | succ j => exact ih j h
  | measure k label next ih =>
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨h.1, rfl⟩,
      List.mem_map.mpr ⟨h.2, ih h.1 j h.2, rfl⟩⟩
  | project A P Q ihP ihQ =>
    cases h with
    | inl h => exact List.mem_append_left _ (List.mem_map.mpr ⟨h, ihP j h, rfl⟩)
    | inr h => exact List.mem_append_right _ (List.mem_map.mpr ⟨h, ihQ j h, rfl⟩)

theorem adaptiveFrontierEnumeration_nodup {I : Type} (P : ObservedCircuit I) (j : ℕ) :
    (adaptiveFrontierEnumeration P j).Nodup := by
  induction P generalizing j with
  | halt a => simp [adaptiveFrontierEnumeration]
  | step s P ih => cases s with
    | gate U => exact ih j
    | query => cases j with
      | zero => simp [adaptiveFrontierEnumeration]
      | succ j => exact ih j
  | measure k label next ih =>
    apply List.nodup_flatten.mpr
    constructor
    · intro xs hx
      obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hx
      exact (ih o j).map (fun a b he => by cases he; rfl)
    · apply List.pairwise_ofFn.mpr
      intro a b hab
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨u, _, hu⟩ := List.mem_map.mp hx
      obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
      have he : a = b := congrArg Sigma.fst (hu.trans hv.symm)
      exact (ne_of_lt hab) he
  | project A P Q ihP ihQ =>
    apply List.nodup_append'.mpr
    refine ⟨(ihP j).map Sum.inl_injective, (ihQ j).map Sum.inr_injective, ?_⟩
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hx
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
    cases hu.trans hv.symm

noncomputable def adaptiveFrontierEnumerationEquiv {I : Type} (P : ObservedCircuit I) (j : ℕ) :
    Fin (adaptiveFrontierEnumeration P j).length ≃ adaptiveFrontierType P j :=
  List.Nodup.getEquivOfForallMemList _ (adaptiveFrontierEnumeration_nodup P j)
    (adaptiveFrontierEnumeration_mem P j)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem adaptiveFrontierEnumeration_final (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (j : ℕ) (hd : observedQueryDepth P ≤ j) (ψ : QState I) :
    (adaptiveFrontierEnumeration P j).map (fun h => fun i => adaptiveFrontierRun O P j ψ (i, h)) =
      (observedTraces O P ψ).map BranchTrace.state := by
  induction P generalizing j ψ with
  | halt a => simp [adaptiveFrontierEnumeration, adaptiveFrontierRun, observedTraces]
  | step s P ih => cases s with
    | gate U =>
      simpa only [adaptiveFrontierEnumeration, adaptiveFrontierRun, observedTraces,
        List.map_map, Function.comp_def] using (ih j hd (ApplyGate U ψ))
    | query =>
      cases j with
      | zero => simp [observedQueryDepth] at hd
      | succ j =>
        have hj : observedQueryDepth P ≤ j := by simpa [observedQueryDepth] using hd
        simpa only [adaptiveFrontierEnumeration, adaptiveFrontierRun, observedTraces,
          List.map_map, Function.comp_def] using (ih j hj (ApplyGate O ψ))
  | measure k label next ih =>
    have hj (o : Fin k) : observedQueryDepth (next o) ≤ j := by
      have hle : observedQueryDepth (next o) ≤ observedQueryDepth (.measure k label next) := by
        rw [observedQueryDepth_eq_budget, observedQueryDepth_eq_budget]
        exact Finset.le_sup (f := fun o => observedQueryBudget (next o)) (Finset.mem_univ o)
      exact hle.trans hd
    simp only [adaptiveFrontierEnumeration, adaptiveFrontierRun, observedTraces,
      List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]
    congr 2
    funext o
    exact ih o j (hj o) (Collapse ψ (Finset.univ.filter (fun i => label i = o)))
  | project A P Q ihP ihQ =>
    have hdp : observedQueryDepth P ≤ j := (le_max_left _ _).trans hd
    have hdq : observedQueryDepth Q ≤ j := (le_max_right _ _).trans hd
    simpa only [adaptiveFrontierEnumeration, adaptiveFrontierRun, observedTraces,
      List.map_append, List.map_map, Function.comp_def] using!
      congrArg₂ List.append (ihP j hdp (ProjectiveBranch A false ψ))
        (ihQ j hdq (ProjectiveBranch A true ψ))

end AdaptiveFrontierEnumeration

section FrontierHistoryPacking
variable {K H : Type} [Fintype K] [Fintype H] [DecidableEq K] [DecidableEq H]

section HistoryCoordinate
variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def adaptiveHistoryCoordinateMatrix (e : K ↪ H) : Matrix (I × H) (I × K) ℂ :=
  adaptiveCoordinateMatrix ((Function.Embedding.refl I).prodMap e)

theorem adaptiveFrontierLayer_transport (P : ObservedCircuit I) (hP : observedWellFormed P)
    (j : ℕ) (e : adaptiveFrontierType P j ↪ H)
    (e' : adaptiveFrontierType P (j + 1) ↪ H) :
    ∃ U : Matrix (I × H) (I × H) ℂ, U ∈ Matrix.unitaryGroup (I × H) ℂ ∧
      ∀ v : QState (I × adaptiveFrontierType P j),
        ApplyGate U (adaptiveHistoryCoordinateMatrix e *ᵥ v) =
          adaptiveHistoryCoordinateMatrix e' *ᵥ adaptiveFrontierAdvance P j v := by
  obtain ⟨U, hU, hact⟩ := adaptiveHistoryIsometries_transport
    (adaptiveCoordinateIsometry ((Function.Embedding.refl I).prodMap e))
    ((adaptiveCoordinateIsometry ((Function.Embedding.refl I).prodMap e')).comp
      (adaptiveFrontierAdvanceIsometry P hP j))
  refine ⟨U, hU, ?_⟩
  intro v
  exact congrArg WithLp.ofLp (hact (toEuclidean_fromVec v))

theorem adaptiveFrontierInitial_transport (P : ObservedCircuit I) (hP : observedWellFormed P)
    (blank : H) (e : adaptiveFrontierType P 0 ↪ H) :
    ∃ U : Matrix (I × H) (I × H) ℂ, U ∈ Matrix.unitaryGroup (I × H) ℂ ∧
      ∀ ψ : QState I,
        ApplyGate U (fun x => if x.2 = blank then ψ x.1 else 0) =
          adaptiveHistoryCoordinateMatrix e *ᵥ adaptiveFrontierRun 1 P 0 ψ := by
  let b : I ↪ I × H := ⟨fun i => (i, blank), fun i j h => congrArg Prod.fst h⟩
  obtain ⟨U, hU, hact⟩ := adaptiveHistoryIsometries_transport
    (adaptiveCoordinateIsometry b)
    ((adaptiveCoordinateIsometry ((Function.Embedding.refl I).prodMap e)).comp
      (adaptiveFrontierIsometry 1 (Submonoid.one_mem _) P hP 0))
  refine ⟨U, hU, ?_⟩
  intro ψ
  have hb : adaptiveCoordinateMatrix b *ᵥ ψ =
      (fun x => if x.2 = blank then ψ x.1 else 0) := by
    funext ⟨i,h⟩
    by_cases hh : h = blank
    · subst h
      simpa only [↓reduceIte] using! adaptiveCoordinateMatrix_apply_image b ψ i
    · exact (adaptiveCoordinateMatrix_apply_outside b ψ (i,h)
        (fun k he => hh (congrArg Prod.snd he).symm)).trans (by simp [hh])
  have he := congrArg WithLp.ofLp (hact (toEuclidean_fromVec ψ))
  change ApplyGate U (adaptiveCoordinateMatrix b *ᵥ ψ) = _ at he
  rwa [hb] at he

omit [Fintype H] in

theorem adaptiveHistoryCoordinateMatrix_apply_image (e : K ↪ H)
    (v : QState (I × K)) (i : I) (k : K) :
    (adaptiveHistoryCoordinateMatrix e *ᵥ v) (i, e k) = v (i, k) :=
  adaptiveCoordinateMatrix_apply_image ((Function.Embedding.refl I).prodMap e) v (i, k)

omit [Fintype H] [DecidableEq K] in

theorem adaptiveHistoryCoordinateMatrix_apply_outside (e : K ↪ H)
    (v : QState (I × K)) (i : I) (h : H) (hh : ∀ k, e k ≠ h) :
    (adaptiveHistoryCoordinateMatrix e *ᵥ v) (i, h) = 0 :=
  adaptiveCoordinateMatrix_apply_outside ((Function.Embedding.refl I).prodMap e) v (i, h)
    (fun k he => hh k.2 (congrArg Prod.snd he))

end HistoryCoordinate

noncomputable def adaptiveEmbeddedActive (e : K ↪ H) (active : K → Bool) : H → Bool :=
  fun h => decide (∃ k, e k = h ∧ active k = true)

omit [Fintype H] [DecidableEq K] in

theorem adaptiveEmbeddedActive_image (e : K ↪ H) (active : K → Bool) (k : K) :
    adaptiveEmbeddedActive e active (e k) = active k := by
  simp [adaptiveEmbeddedActive, e.injective.eq_iff]

section EmbeddedPadding
variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

theorem run_adaptivePaddedQuery_embedded (e : K ↪ H) (active : K → Bool)
    (f : Fin n → Bool) (v : QState (((Fin n × Bool) × W) × K)) :
    Run (workspaceBitOracle (W := W × H × Bool) f)
      (adaptivePaddedQuery (adaptiveEmbeddedActive e active))
      (fun x => (adaptiveHistoryCoordinateMatrix e *ᵥ v)
        ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) =
    (fun x => (adaptiveHistoryCoordinateMatrix e *ᵥ
      (fun y => if active y.2 then
        v (((y.1.1.1, y.1.1.2 ^^ f y.1.1.1), y.1.2), y.2) else v y))
      ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) := by
  funext x
  change Run _ _ (adaptiveSpareInput (fun y =>
    (adaptiveHistoryCoordinateMatrix e *ᵥ v) ((y.1, y.2.1), y.2.2))) x = _
  rw [run_adaptivePaddedQuery]
  rcases x with ⟨ib, w, h, s⟩
  by_cases hh : ∃ k, e k = h
  · obtain ⟨k, rfl⟩ := hh
    simp only [adaptiveEmbeddedActive_image, adaptiveHistoryCoordinateMatrix_apply_image]
  · have hzero (u : QState (((Fin n × Bool) × W) × K)) (i : (Fin n × Bool) × W) :
        (adaptiveHistoryCoordinateMatrix e *ᵥ u) (i, h) = 0 :=
      adaptiveHistoryCoordinateMatrix_apply_outside e u i h (fun k he => hh ⟨k, he⟩)
    simp only [hzero, ite_self, zero_div]

end EmbeddedPadding

end FrontierHistoryPacking

section FrontierSize
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

theorem adaptiveFrontier_card_le_nodes (P : ObservedCircuit I) (j : ℕ) :
    Fintype.card (adaptiveFrontierType P j) ≤ observedTreeNodes P := by
  induction P generalizing j with
  | halt a => simp [adaptiveFrontierType, observedTreeNodes]
  | step s P ih =>
    cases s with
    | gate U => exact (ih j).trans (Nat.le_add_right _ _)
    | query => cases j with
      | zero => simp [adaptiveFrontierType, observedTreeNodes]
      | succ j => exact (ih j).trans (Nat.le_add_right _ _)
  | measure k label next ih =>
    change Fintype.card (Sigma (fun o : Fin k => adaptiveFrontierType (next o) j)) ≤ _
    rw [Fintype.card_sigma]
    simp only [observedTreeNodes, List.sum_ofFn]
    exact (Finset.sum_le_sum (fun o _ => ih o j)).trans (Nat.le_add_right _ _)
  | project A P Q ihP ihQ =>
    change Fintype.card (adaptiveFrontierType P j ⊕ adaptiveFrontierType Q j) ≤ _
    rw [Fintype.card_sum]
    exact (Nat.add_le_add (ihP j) (ihQ j)).trans (Nat.le_add_right _ _)

omit [Fintype I] [DecidableEq I] in

theorem adaptiveFrontierEnumeration_length (P : ObservedCircuit I) (j : ℕ) :
    (adaptiveFrontierEnumeration P j).length = Fintype.card (adaptiveFrontierType P j) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (adaptiveFrontierEnumerationEquiv P j)

noncomputable def adaptiveHistorySlots (P : ObservedCircuit I) (j : ℕ) :
    adaptiveFrontierType P j ↪ Fin (observedTreeNodes P + 1) :=
  (adaptiveFrontierEnumerationEquiv P j).symm.toEmbedding.trans
    (Fin.castLEEmb ((adaptiveFrontierEnumeration_length P j ▸
      adaptiveFrontier_card_le_nodes P j).trans (Nat.le_add_right _ _)))

end FrontierSize

section LayerWord
variable {n : ℕ} {W H : Type} [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H]

noncomputable def adaptiveFrontierLayerWord
    (U0 : Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (active : ℕ → H → Bool) : ℕ → Circuit ((Fin n × Bool) × (W × H × Bool))
  | 0 => [.gate (adaptiveHistoryLift U0)]
  | k + 1 => adaptiveFrontierLayerWord U0 Us active k ++
      (adaptivePaddedQuery (active k) ++ [.gate (adaptiveHistoryLift (Us k))])

theorem adaptiveFrontierLayerWord_cost
    (U0 : Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (active : ℕ → H → Bool)
    (hU0 : U0 ∈ Matrix.unitaryGroup (((Fin n × Bool) × W) × H) ℂ)
    (hUs : ∀ j, Us j ∈ Matrix.unitaryGroup (((Fin n × Bool) × W) × H) ℂ) (k : ℕ) :
    IsUnitaryCircuit (adaptiveFrontierLayerWord U0 Us active k) ∧
      QueryCount (adaptiveFrontierLayerWord U0 Us active k) = k ∧
      GateCount (adaptiveFrontierLayerWord U0 Us active k) = 1 + 3*k := by
  induction k with
  | zero => simp [adaptiveFrontierLayerWord, adaptiveHistoryLift_unitary hU0]
  | succ k ih =>
    have hp := adaptivePaddedQuery_cost_and_unitary (n := n) (W := W) (active k)
    refine ⟨?_, ?_, ?_⟩
    · apply (isUnitaryCircuit_append _ _).mpr
      refine ⟨ih.1, (isUnitaryCircuit_append _ _).mpr ⟨hp.1, ?_⟩⟩
      simpa using adaptiveHistoryLift_unitary (hUs k)
    · simp only [adaptiveFrontierLayerWord, queryCount_append, ih.2.1, hp.2.1,
        queryCount_gate, queryCount_nil, add_zero]
    · simp only [adaptiveFrontierLayerWord, gateCount_append, ih.2.2, hp.2.2,
        gateCount_gate, gateCount_nil]
      omega

theorem run_adaptiveFrontierLayerWord
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (e : ∀ j, adaptiveFrontierType P j ↪ H) (blank : H)
    (U0 : Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Bool) × W) × H) (((Fin n × Bool) × W) × H) ℂ)
    (hinit : ∀ ψ : QState ((Fin n × Bool) × W),
      ApplyGate U0 (fun x => if x.2 = blank then ψ x.1 else 0) =
        adaptiveHistoryCoordinateMatrix (e 0) *ᵥ adaptiveFrontierRun 1 P 0 ψ)
    (hstep : ∀ j (v : QState (((Fin n × Bool) × W) × adaptiveFrontierType P j)),
      ApplyGate (Us j) (adaptiveHistoryCoordinateMatrix (e j) *ᵥ v) =
        adaptiveHistoryCoordinateMatrix (e (j+1)) *ᵥ adaptiveFrontierAdvance P j v)
    (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)) (k : ℕ) :
    Run (workspaceBitOracle (W := W × H × Bool) f)
      (adaptiveFrontierLayerWord U0 Us
        (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) k)
      (fun x => if x.2.2.1 = blank then ψ (x.1, x.2.1) / Real.sqrt 2 else 0) =
      (fun x => (adaptiveHistoryCoordinateMatrix (e k) *ᵥ
        adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ)
        ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) := by
  induction k with
  | zero =>
    have hi : (fun x : (Fin n × Bool) × (W × H × Bool) =>
      if x.2.2.1 = blank then ψ (x.1, x.2.1) / Real.sqrt 2 else 0) =
      (fun x => (if x.2.2.1 = blank then ψ (x.1, x.2.1) else 0) / Real.sqrt 2) := by
      funext x
      split_ifs <;> simp
    rw [adaptiveFrontierLayerWord, run_gate, run_nil, hi]
    funext x
    rw [apply_adaptiveHistoryLift U0 (fun y => if y.2 = blank then ψ y.1 else 0), hinit,
      adaptiveFrontierRun_zero_eq 1 (workspaceBitOracle (W := W) f)]
  | succ k ih =>
    rw [adaptiveFrontierLayerWord, run_append, ih, run_append]
    have hp := run_adaptivePaddedQuery_embedded (e k) (adaptiveFrontierActive P k) f
      (adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ)
    have hp' : Run (workspaceBitOracle (W := W × H × Bool) f)
        (adaptivePaddedQuery (adaptiveEmbeddedActive (e k) (adaptiveFrontierActive P k)))
        (fun x => (adaptiveHistoryCoordinateMatrix (e k) *ᵥ
          adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ)
          ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) =
        (fun x => (adaptiveHistoryCoordinateMatrix (e k) *ᵥ
          adaptiveFrontierQuery (workspaceBitOracle (W := W) f) P k
            (adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ))
          ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) := by
      have hq : adaptiveFrontierQuery (workspaceBitOracle (W := W) f) P k
          (adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ) =
          (fun y => if adaptiveFrontierActive P k y.2 then
            adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ
              (((y.1.1.1, y.1.1.2 ^^ f y.1.1.1), y.1.2), y.2) else
            adaptiveFrontierRun (workspaceBitOracle (W := W) f) P k ψ y) := by
        funext ⟨⟨⟨i, b⟩, w⟩, h⟩
        simp only [adaptiveFrontierQuery, applyGate_workspaceBitOracle]
      rw [hq]
      exact hp
    rw [hp', run_gate, run_nil]
    funext x
    rw [apply_adaptiveHistoryLift, hstep, adaptiveFrontierAdvance_query]

end LayerWord
section FinalCoordinates
variable {I : Type} [Fintype I] [DecidableEq I]

theorem adaptiveFrontier_final_coordinate (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (ψ : QState I) (x : I × Fin (observedTreeNodes P + 1)) :
    (adaptiveHistoryCoordinateMatrix (adaptiveHistorySlots P (observedQueryDepth P)) *ᵥ
      adaptiveFrontierRun O P (observedQueryDepth P) ψ) x =
      ((observedTraces O P ψ).getD x.2.val (emptyObservedTrace I)).state x.1 := by
  let d := observedQueryDepth P
  let ls := adaptiveFrontierEnumeration P d
  let ts := observedTraces O P ψ
  have he := adaptiveFrontierEnumeration_final O P d le_rfl ψ
  have hlen : ts.length = ls.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map] using hh.symm
  by_cases hx : x.2.val < ls.length
  · let k : Fin ls.length := ⟨x.2.val, hx⟩
    let q := adaptiveFrontierEnumerationEquiv P d k
    have hq : adaptiveHistorySlots P d q = x.2 := by
      apply Fin.ext
      simp [adaptiveHistorySlots, q, k]
    have hp := adaptiveHistoryCoordinateMatrix_apply_image (adaptiveHistorySlots P d)
      (adaptiveFrontierRun O P d ψ) x.1 q
    change (adaptiveHistoryCoordinateMatrix (adaptiveHistorySlots P d) *ᵥ
      adaptiveFrontierRun O P d ψ) x = _
    rw [hq] at hp
    rw [hp]
    have hh : ((ls.map (fun h => fun i => adaptiveFrontierRun O P d ψ (i, h))).getD
        x.2.val 0) x.1 = (ts.getD x.2.val (emptyObservedTrace I)).state x.1 := by
      rw [he]
      exact congrArg (fun v : QState I => v x.1)
        (List.getD_map ts (emptyObservedTrace I) BranchTrace.state (n := x.2.val))
    rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map] at hh
    exact hh
  · have hout (q : adaptiveFrontierType P d) : adaptiveHistorySlots P d q ≠ x.2 := by
      intro hq
      have hlt : (adaptiveHistorySlots P d q).val < ls.length :=
        ((adaptiveFrontierEnumerationEquiv P d).symm q).isLt
      have hv := congrArg Fin.val hq
      omega
    rw [adaptiveHistoryCoordinateMatrix_apply_outside (adaptiveHistorySlots P d)
      (adaptiveFrontierRun O P d ψ) x.1 x.2 hout]
    rw [List.getD_eq_default _ _ (by change ts.length ≤ x.2.val; omega)]
    rfl

end FinalCoordinates

theorem observed_query_same_cost_full_branch_purification
    (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (_hn : 0 < n) (hP : observedWellFormed P) :
    ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
      IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth P ∧
      GateCount C ≤ 10 * observedTreeNodes P * (observedQueryDepth P + 1) ∧
      ∀ (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)),
      let ts := observedTraces (workspaceBitOracle (W := W) f) P ψ
      ts.length ≤ R + 1 ∧
      ∀ x : (Fin n × Bool) × (W × Fin (R + 1) × Bool),
        Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) f) C
          (deferredObservedInput (R := R) ψ) x =
          (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2 := by
  let R := observedTreeNodes P
  let e := adaptiveHistorySlots P
  obtain ⟨U0, hU0, hinit⟩ := adaptiveFrontierInitial_transport P hP (0 : Fin (R + 1)) (e 0)
  have htrans (j : ℕ) := adaptiveFrontierLayer_transport P hP j (e j) (e (j + 1))
  choose Us hUs hstep using htrans
  let C := adaptiveFrontierLayerWord U0 Us
    (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) (observedQueryDepth P)
  have hc := adaptiveFrontierLayerWord_cost U0 Us
    (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) hU0 hUs (observedQueryDepth P)
  refine ⟨R, C, hc.1, hc.2.1, ?_, ?_⟩
  · rw [hc.2.2]
    have hn : 0 < observedTreeNodes P := by cases P <;> simp only [observedTreeNodes] <;> omega
    nlinarith
  · intro f ψ
    have he := adaptiveFrontierEnumeration_final (workspaceBitOracle (W := W) f)
      P (observedQueryDepth P) le_rfl ψ
    have hlen := congrArg List.length he
    simp only [List.length_map] at hlen
    refine ⟨?_, ?_⟩
    · rw [← hlen, adaptiveFrontierEnumeration_length]
      exact (adaptiveFrontier_card_le_nodes P _).trans (Nat.le_add_right _ _)
    · intro x
      have hr := run_adaptiveFrontierLayerWord P e (0 : Fin (R + 1)) U0 Us hinit hstep
        f ψ (observedQueryDepth P)
      have hi : deferredObservedInput (R := R) ψ =
          (fun x => if x.2.2.1 = (0 : Fin (R + 1)) then
            ψ (x.1, x.2.1) / Real.sqrt 2 else 0) := by
        funext y
        have hz : y.2.2.1.val = 0 ↔ y.2.2.1 = 0 := ⟨fun h => Fin.ext h, congrArg Fin.val⟩
        simp [deferredObservedInput, hz]
      rw [← hi] at hr
      rw [hr]
      exact congrArg (fun z : ℂ => z / Real.sqrt 2)
        (adaptiveFrontier_final_coordinate (workspaceBitOracle (W := W) f) P ψ
          ((x.1, x.2.1), x.2.2.1))

section FullHistoryReadout
variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in

theorem adaptiveSpareHistory_mass {H : Type} [Fintype H]
    (v : QState (((Fin n × Bool) × W) × H)) :
    branchMass (fun x : (Fin n × Bool) × (W × H × Bool) =>
      v ((x.1, x.2.1), x.2.2.1) / Real.sqrt 2) = branchMass v := by
  have ht (r : ℝ) : 2 * (r / 2) = r := by ring
  simp [branchMass, MeasureProb, BornProb, Fintype.sum_prod_type,
    div_pow, ht]

theorem adaptivePackedTraceHistory_readout (ts : List (BranchTrace ((Fin n × Bool) × W)))
    (K : ℕ) (hK : ts.length ≤ K) :
    MeasureProb (fun x : (Fin n × Bool) × (W × Fin K × Bool) =>
      (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2)
      (Finset.univ.filter (fun x => (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted)) =
      (ts.map (fun t => if t.accepted then branchMass t.state else 0)).sum := by
  let vs := ts.map (fun t => if t.accepted then t.state else 0)
  let v : QState ((Fin n × Bool) × (W × Fin K × Bool)) := fun x =>
    (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2
  let E : Finset ((Fin n × Bool) × (W × Fin K × Bool)) :=
    Finset.univ.filter (fun x => (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted)
  have hc : Collapse v E = (fun x => (vs.getD x.2.2.1.val 0) (x.1, x.2.1) / Real.sqrt 2) := by
    funext x
    rw [collapse_apply]
    have hv := List.getD_map ts (emptyObservedTrace _) (fun t => if t.accepted then t.state else 0)
      (n := x.2.2.1.val)
    change vs.getD x.2.2.1.val 0 = _ at hv
    rw [hv]
    simp only [E, v, Finset.mem_filter, Finset.mem_univ, true_and]
    cases (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted <;> simp
  change MeasureProb v E = _
  calc
    MeasureProb v E = branchMass (Collapse v E) := by
      rw [branchMass, measureProb_collapse, Finset.inter_univ]
    _ = branchMass (fun x : (Fin n × Bool) × (W × Fin K × Bool) =>
      (vs.getD x.2.2.1.val 0) (x.1, x.2.1) / Real.sqrt 2) := congrArg branchMass hc
    _ = branchMass (fun x : ((Fin n × Bool) × W) × Fin K => (vs.getD x.2.val 0) x.1) :=
      adaptiveSpareHistory_mass (n := n) (W := W) (H := Fin K)
        (fun x : ((Fin n × Bool) × W) × Fin K => (vs.getD x.2.val 0) x.1)
    _ = (vs.map branchMass).sum := adaptiveListHistory_mass (I := (Fin n × Bool) × W)
      vs K (by simpa only [vs, List.length_map] using hK)
    _ = _ := by
      simp only [vs, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro t _
      cases t.accepted <;> simp [branchMass, MeasureProb, BornProb]

theorem observedBranchWords_accepted {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) :
    (observedTraces O P ψ).map BranchTrace.accepted = (observedBranchWords P).map Prod.fst := by
  have h := congrArg (List.map (fun x : QState I × Bool × ℕ => x.2.1))
    (observedBranchWords_traces O P ψ)
  simpa only [List.map_map, Function.comp_def] using h

noncomputable def adaptiveObservedHistoryEvent (P : ObservedCircuit ((Fin n × Bool) × W)) (R : ℕ) :
    Finset ((Fin n × Bool) × (W × Fin (R + 1) × Bool)) :=
  Finset.univ.filter (fun x => ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false)

theorem observed_full_history_acceptance_transport
    (P : ObservedCircuit ((Fin n × Bool) × W)) (R : ℕ)
    (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool)))
    (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W))
    (hlen : (observedTraces (workspaceBitOracle (W := W) f) P ψ).length ≤ R + 1)
    (hstate : ∀ x,
      Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) f) C
        (deferredObservedInput (R := R) ψ) x =
      ((observedTraces (workspaceBitOracle (W := W) f) P ψ).getD
        x.2.2.1.val (emptyObservedTrace _)).state (x.1, x.2.1) / Real.sqrt 2) :
    MeasureProb (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) f) C
      (deferredObservedInput (R := R) ψ)) (adaptiveObservedHistoryEvent P R) =
      observedAcceptance (workspaceBitOracle (W := W) f) P ψ := by
  let ts := observedTraces (workspaceBitOracle (W := W) f) P ψ
  have he : adaptiveObservedHistoryEvent P R =
      Finset.univ.filter (fun x => (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted) := by
    ext x
    simp only [adaptiveObservedHistoryEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := List.getD_map ts (emptyObservedTrace _) BranchTrace.accepted (n := x.2.2.1.val)
    rw [observedBranchWords_accepted] at hh
    change ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false = _ at hh
    rw [hh]
  rw [funext hstate, he, adaptivePackedTraceHistory_readout ts (R + 1) hlen]
  exact observedEventMass_accepted _ P ψ

end FullHistoryReadout

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
