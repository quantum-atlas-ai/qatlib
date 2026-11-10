/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

set_option linter.unusedSectionVars false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

def networkCzLo {n : ℕ} (i j : Fin n) : Fin n := ⟨min (i : ℕ) (j : ℕ), by omega⟩

def networkCzHi {n : ℕ} (i j : Fin n) : Fin n := ⟨max (i : ℕ) (j : ℕ), by omega⟩

theorem networkCzLo_lt_hi {n : ℕ} (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ)) :
    (networkCzLo i j : ℕ) < (networkCzHi i j : ℕ) := by
  show min (i : ℕ) (j : ℕ) < max (i : ℕ) (j : ℕ)
  omega

noncomputable def networkPhysicalStepProgram {n : ℕ} :
    ClusterNetworkGate n → ObservedCircuit (Fin (2 ^ (n + 2)))
  | .inl (i, ζ) => networkStepLift (eWireFin n i) (clusterWireProgram ζ)
  | .inr (i, j) =>
      if h : (i : ℕ) ≠ (j : ℕ) then
        networkStepLift
          (eCzFin n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h))
          clusterCZProgram
      else .halt true

def networkBranchValid {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) : Prop :=
  ∀ k : Fin gs.length, match gs.get k with
    | .inl _ => (hist k).2 = false
    | .inr _ => True

noncomputable def networkWireStepLeaf (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) :
    Operator (2 ^ (n + 2)) :=
  (networkStepLiftLeaf (eWireFin n i)
    (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ a))).operator

noncomputable def networkCzStepLeaf (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) : Operator (2 ^ (n + 2)) :=
  (networkStepLiftLeaf (eCzFin n lo hi h1)
    (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d))).operator

noncomputable def networkActualStepCore {n : ℕ} :
    ClusterNetworkGate n → Bool × Bool → Operator (2 ^ n) → Operator (2 ^ n)
  | .inl (i, ζ), o, ρ =>
      if o.2 then 0 else
      Matrix.traceLeft (relabelGate (eWireOutFin n i).symm
        (networkWireStepLeaf n i ζ o.1 * (networkFrame n * ρ * (networkFrame n).conjTranspose)
          * (networkWireStepLeaf n i ζ o.1).conjTranspose))
  | .inr (i, j), o, ρ =>
      if h : (i : ℕ) ≠ (j : ℕ) then
        Matrix.traceLeft (relabelGate (eCzOutFin n (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h)).symm
          (networkCzStepLeaf n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h)
              o.1 o.2
            * (networkFrame n * ρ * (networkFrame n).conjTranspose)
            * (networkCzStepLeaf n (networkCzLo i j) (networkCzHi i j)
                (networkCzLo_lt_hi i j h) o.1 o.2).conjTranspose))
      else 0

noncomputable def networkActualStepBranch {n : ℕ} (g : ClusterNetworkGate n) (o : Bool × Bool) :
    Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) where
  toFun := networkActualStepCore g o
  map_add' := by
    intro ρ σ
    cases g with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      by_cases ho : o.2
      · simp [networkActualStepCore, ho]
      · simp only [networkActualStepCore, if_neg ho, Matrix.mul_add, Matrix.add_mul,
          relabelGate_add', traceLeft_add]
    | inr p =>
      obtain ⟨i, j⟩ := p
      by_cases hv : (i : ℕ) ≠ (j : ℕ)
      · simp only [networkActualStepCore, dif_pos hv, Matrix.mul_add, Matrix.add_mul,
          relabelGate_add', traceLeft_add]
      · simp [networkActualStepCore, hv]
  map_smul' := by
    intro r ρ
    cases g with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      by_cases ho : o.2
      · simp [networkActualStepCore, ho]
      · simp only [networkActualStepCore, if_neg ho, Matrix.mul_smul, Matrix.smul_mul,
          relabelGate_smul', traceLeft_smul, RingHom.id_apply]
    | inr p =>
      obtain ⟨i, j⟩ := p
      by_cases hv : (i : ℕ) ≠ (j : ℕ)
      · simp only [networkActualStepCore, dif_pos hv, Matrix.mul_smul, Matrix.smul_mul,
          relabelGate_smul', traceLeft_smul, RingHom.id_apply]
      · simp [networkActualStepCore, hv]

theorem networkLogicalMatrix_cons {n : ℕ} (g : ClusterNetworkGate n) :
    networkLogicalMatrix [g] = networkGateMatrix g := by
  simp [networkLogicalMatrix]

theorem networkRelabelState_ket {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (i : I) : relabelState e (Ket i) = Ket (e i) := by
  funext x
  show (Ket i) (e.symm x) = Ket (e i) x
  simp only [Qatlib.Foundations.PureStateMath.Ket]
  by_cases h : e.symm x = i
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq e).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((Equiv.symm_apply_eq e).mpr h'))]

theorem networkRelabelGate_trans {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype K] [DecidableEq K] (e : I ≃ J) (f : J ≃ K)
    (U : Matrix I I ℂ) :
    relabelGate f (relabelGate e U) = relabelGate (e.trans f) U := by
  ext i k
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply]

theorem networkRelabelGate_symm {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (U : Matrix J J ℂ) :
    relabelGate e (relabelGate e.symm U) = U := by
  have h := relabelGate_relabelGate e.symm U
  rw [Equiv.symm_symm] at h
  exact h

theorem networkWireRouteFromF_outToF (n : ℕ) (i : Fin n) (p : (Bool × Bool) × Reg n) :
    networkWireRouteFromF n i (networkWireOutToF n i p)
      = ((p.1.1, p.2 i), fun k => if k = i then p.1.2 else p.2 k) := by
  have hss : eRegSplit n (networkWireOutToF n i p)
      = ((fun k : Fin n => if k = i then p.1.1 else p.2 k), ![p.2 i, p.1.2]) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkWireRouteFromF
  rw [hss]
  have h1 : (if (i : Fin n) = i then p.1.1 else p.2 i) = p.1.1 := by
    rw [if_pos rfl]
  have h2 : (![p.2 i, p.1.2] : Fin 2 → Bool) 0 = p.2 i := rfl
  have h3 : ∀ k : Fin n, (if k = i then (![p.2 i, p.1.2] : Fin 2 → Bool) 1
      else (if k = i then p.1.1 else p.2 k)) = if k = i then p.1.2 else p.2 k := by
    intro k
    by_cases hk : k = i
    · rw [if_pos hk, if_pos hk]
      rfl
    · rw [if_neg hk, if_neg hk, if_neg hk]
  exact Prod.ext (Prod.ext h1 h2) (funext fun k => h3 k)

theorem networkWireRoute_symm_frameVec (n : ℕ) (i : Fin n) (w : Reg n) :
    (networkWireRoute n i).symm (networkFrameVec n w)
      = ((w i, false), fun k => if k = i then false else w k) := by
  show networkWireRouteFromF n i (networkFrameVec n w) = _
  have hss : eRegSplit n (networkFrameVec n w) = (w, fun _ => false) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkWireRouteFromF
  rw [hss]

noncomputable def networkWireSmallLeafOp (ζ : ℂ) (a : Bool) : Operator 4 :=
  (observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ a)).operator

theorem networkWireSmallLeaf_column (ζ : ℂ) (a bb : Bool) :
    (relabelGate teleportOutcomeEquiv.symm (networkWireSmallLeafOp ζ a)) *ᵥ (Ket (bb, false))
      = (fun q : Bool × Bool =>
          if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 q.2)
            (boolEquivFin2 bb) else 0) := by
  have hm : boolEquivFin2.symm (boolEquivFin2 bb) = bb := Equiv.symm_apply_apply _ _
  have hkey := clusterWireLeafColumn ζ a (boolEquivFin2 bb)
  rw [hm, networkRelabelState_ket] at hkey
  unfold networkWireSmallLeafOp
  show ApplyGate (relabelGate teleportOutcomeEquiv.symm
      ((observedLeaf 1 (clusterWireProgram ζ) (clusterWireLeaf ζ a)).operator))
      (Ket (bb, false)) = _
  rw [applyGate_relabelGate',
    show teleportOutcomeEquiv.symm.symm = teleportOutcomeEquiv from Equiv.symm_symm _,
    networkRelabelState_ket, hkey, relabelState_relabelState]

theorem networkWireSmallLeaf_apply (ζ : ℂ) (a bb : Bool) :
    ApplyGate (relabelGate teleportOutcomeEquiv.symm (networkWireSmallLeafOp ζ a))
        (Ket (bb, false))
      = (fun q : Bool × Bool =>
          if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 q.2)
            (boolEquivFin2 bb) else 0) :=
  networkWireSmallLeaf_column ζ a bb

theorem networkWireGateB_apply (n : ℕ) (i : Fin n) (ζ : ℂ) (w v : Reg n) :
    networkWireGateB i ζ w v
      = clusterJ ζ (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
        * ∏ j ∈ Finset.univ.erase i, (if w j = v j then (1 : ℂ) else 0) := by
  have hne : ∀ j ∈ Finset.univ.erase i,
      (if j = i then clusterJ ζ else (1 : Operator 2)) (boolEquivFin2 (w j))
          (boolEquivFin2 (v j))
        = if w j = v j then (1 : ℂ) else 0 := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [if_neg hji, Matrix.one_apply]
    by_cases hw : w j = v j
    · rw [if_pos (congrArg boolEquivFin2 hw), if_pos hw]
    · rw [if_neg (fun h => hw (boolEquivFin2.injective h)), if_neg hw]
  have h1 : (if (i : Fin n) = i then clusterJ ζ else (1 : Operator 2))
        (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
      = clusterJ ζ (boolEquivFin2 (w i)) (boolEquivFin2 (v i)) := by
    rw [if_pos rfl]
  show (∏ j : Fin n, (if j = i then clusterJ ζ else (1 : Operator 2)) (boolEquivFin2 (w j))
        (boolEquivFin2 (v j))) = _
  exact ((Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun j => (if j = i then clusterJ ζ else (1 : Operator 2)) (boolEquivFin2 (w j))
        (boolEquivFin2 (v j))) (Finset.mem_univ i)).symm).trans
    (congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun j hj => hne j hj))

theorem networkIndicator_prod_erase (n : ℕ) (i : Fin n) (w v : Reg n) :
    ∏ j ∈ Finset.univ.erase i, (if w j = v j then (1 : ℂ) else 0)
      = if (fun k => if k = i then false else w k)
            = (fun k => if k = i then false else v k) then (1 : ℂ) else 0 := by
  by_cases hall : ∀ j ∈ Finset.univ.erase i, w j = v j
  · have hf : (fun k => if k = i then false else w k)
        = (fun k => if k = i then false else v k) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp
      · rw [if_neg hk, if_neg hk]
        exact hall k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    rw [if_pos hf]
    exact Finset.prod_eq_one fun j hj => if_pos (hall j hj)
  · have hdif : ¬((fun k => if k = i then false else w k)
        = (fun k => if k = i then false else v k)) := by
      intro hfun
      apply hall
      intro j hj
      have hd := congrFun hfun j
      rw [if_neg (Finset.mem_erase.mp hj).1, if_neg (Finset.mem_erase.mp hj).1] at hd
      exact hd
    obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.univ.erase i, w j ≠ v j := by
      by_contra hcon
      exact hall (fun j hj => by
        by_contra hjw
        exact hcon ⟨j, hj, hjw⟩)
    rw [if_neg hdif, Finset.prod_eq_zero hjmem (if_neg hjne)]

theorem networkWireGateB_mulVec_ket (n : ℕ) (i : Fin n) (ζ : ℂ) (w v : Reg n) :
    (networkWireGateB i ζ *ᵥ Ket v) w
      = clusterJ ζ (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
        * (if (fun k => if k = i then false else w k)
            = (fun k => if k = i then false else v k) then (1 : ℂ) else 0) := by
  simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Fintype.sum_eq_single v (fun u hu => by rw [if_neg hu, mul_zero]),
    if_pos rfl, mul_one, networkWireGateB_apply, networkIndicator_prod_erase]

theorem networkWireStepLeaf_column (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) (x : Fin (2 ^ n)) :
    (networkWireStepLeaf n i ζ a) *ᵥ (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (relabelState (networkWireRoute n i)
          (TensorState
            (fun q : Bool × Bool =>
              if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 q.2)
                (boolEquivFin2 (((bitVecEquiv n).symm x) i)) else 0)
            (Ket (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k)))) := by
  have hL : networkWireStepLeaf n i ζ a
      = relabelGate (bitVecEquiv (n + 2)) (relabelGate (networkWireRoute n i)
          (TensorGate (relabelGate teleportOutcomeEquiv.symm (networkWireSmallLeafOp ζ a))
            (1 : Matrix (Reg n) (Reg n) ℂ))) := by
    simp only [networkWireStepLeaf, networkStepLiftLeaf, networkStepLiftGate, eWireFin,
      networkWireSmallLeafOp]
    rw [← networkRelabelGate_trans, ← networkRelabelGate_trans,
      relabelGate_prodCongr_tensorGate_one]
  show ApplyGate (networkWireStepLeaf n i ζ a) (fun r => networkFrame n r x) = _
  rw [hL, networkFrame_column, applyGate_relabelGate, applyGate_relabelGate',
    networkRelabelState_ket, networkWireRoute_symm_frameVec, ← tensorState_ket_ket,
    applyGate_tensorGate, applyGate_one, networkWireSmallLeaf_apply]

theorem networkWireStepLeaf_firstFactor (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (x : Fin (2 ^ n)) :
    relabelState (eWireOutFin n i).symm
        ((networkWireStepLeaf n i ζ a) *ᵥ (fun r => networkFrame n r x))
      = (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹)
            * (relabelState (bitVecEquiv n) ((networkWireGateB i ζ)
                *ᵥ (Ket ((bitVecEquiv n).symm x)))) q.2
          else 0) := by
  rw [networkWireStepLeaf_column, relabelState_trans]
  funext q
  have hrr : ∀ v : Reg (n + 2),
      (networkWireRoute n i).symm v = networkWireRouteFromF n i v := fun _ => rfl
  have heq : ((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q
      = networkWireOutToF n i (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2) := by
    have h1 : ((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q
        = (bitVecEquiv (n + 2)).symm (eWireOutFin n i q) := rfl
    have h2 : eWireOutFin n i q
        = (bitVecEquiv (n + 2)) (networkWireOutToF n i
            (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2)) := rfl
    rw [h1, h2, Equiv.symm_apply_apply]
  show TensorState
      (fun q : Bool × Bool =>
          if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ (boolEquivFin2 q.2)
            (boolEquivFin2 (((bitVecEquiv n).symm x) i)) else 0)
      (Ket (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k))
      ((networkWireRoute n i).symm
        (((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q))
      = _
  rw [heq, hrr, networkWireRouteFromF_outToF]
  show (if (teleportOutcomeEquiv.symm q.1).1 = a
        then ((Real.sqrt 2 : ℂ)⁻¹) * clusterJ ζ
            (boolEquivFin2 (((bitVecEquiv n).symm q.2) i))
            (boolEquivFin2 (((bitVecEquiv n).symm x) i))
        else 0)
      * (if (fun k : Fin n => if k = i then (teleportOutcomeEquiv.symm q.1).2
              else ((bitVecEquiv n).symm q.2) k)
            = (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k)
          then (1 : ℂ) else 0)
      = (if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹)
              * ((networkWireGateB i ζ *ᵥ Ket ((bitVecEquiv n).symm x))
                  ((bitVecEquiv n).symm q.2))
          else 0)
  by_cases hq : q.1 = teleportOutcomeEquiv (a, false)
  · rw [if_pos hq]
    have hsym : teleportOutcomeEquiv.symm q.1 = (a, false) := by
      rw [hq, Equiv.symm_apply_apply]
    rw [hsym, networkWireGateB_mulVec_ket, if_pos rfl]
    exact mul_assoc _ _ _
  · rw [if_neg hq]
    by_cases h1 : (teleportOutcomeEquiv.symm q.1).1 = a
    · have h2 : (fun k : Fin n => if k = i then (teleportOutcomeEquiv.symm q.1).2
              else ((bitVecEquiv n).symm q.2) k)
            ≠ (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k) := by
        intro hf
        have hi := congrFun hf i
        simp only [] at hi
        simp only [if_true] at hi
        exact hq ((Equiv.symm_apply_eq teleportOutcomeEquiv).mp (Prod.ext h1 hi))
      rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem relabelGate_matOuter_back {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (u w : QState I) :
    matOuter (relabelState e u) (relabelState e w) = relabelGate e (matOuter u w) := by
  rw [← relabelGate_matOuter e u w]
  exact (relabelGate_relabelGate e.symm
    (matOuter (relabelState e u) (relabelState e w))).symm

theorem networkWireStepBranch_matUnit (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (x y : Fin (2 ^ n)) :
    networkActualStepCore (.inl (i, ζ)) (a, false) (networkMatUnit x y)
      = ((2 : ℂ)⁻¹) • (networkWireGate i ζ * networkMatUnit x y
          * (networkWireGate i ζ).conjTranspose) := by
  have hreal : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    have h := Complex.conj_ofReal ((Real.sqrt 2 : ℝ)⁻¹)
    rw [Complex.ofReal_inv] at h
    exact h
  have hsmulpw : ∀ (V : QState (Fin (2 ^ n))) (q : Fin 4 × Fin (2 ^ n)),
      (if q.1 = teleportOutcomeEquiv (a, false)
        then ((Real.sqrt 2 : ℂ)⁻¹) * V q.2 else 0)
        = ((Real.sqrt 2 : ℂ)⁻¹)
          • (if q.1 = teleportOutcomeEquiv (a, false) then V q.2 else 0) := by
    intro V q
    by_cases hq : q.1 = teleportOutcomeEquiv (a, false)
    · rw [if_pos hq, if_pos hq, smul_eq_mul]
    · rw [if_neg hq, if_neg hq, smul_eq_mul, mul_zero]
  have hsmul : ∀ V : QState (Fin (2 ^ n)),
      (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹) * V q.2 else 0)
        = ((Real.sqrt 2 : ℂ)⁻¹) • (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false) then V q.2 else 0) := by
    intro V
    funext q
    exact hsmulpw V q
  have htlsmul : ∀ (c : ℂ) (M : Matrix (Fin 4 × Fin (2 ^ n)) (Fin 4 × Fin (2 ^ n)) ℂ),
      Matrix.traceLeft (c • M) = c • Matrix.traceLeft M := by
    intro c M
    ext u u'
    simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum,
      smul_eq_mul]
  have hAx : ∀ v : Fin (2 ^ n),
      ApplyGate (networkWireStepLeaf n i ζ a) (fun r => networkFrame n r v)
        = (networkWireStepLeaf n i ζ a) *ᵥ (fun r => networkFrame n r v) := fun _ => rfl
  have hB : ∀ v : Fin (2 ^ n), (networkWireGateB i ζ *ᵥ Ket ((bitVecEquiv n).symm v))
      = relabelState (bitVecEquiv n).symm (networkWireGate i ζ *ᵥ Ket v) := by
    intro v
    have hBB : networkWireGateB i ζ
        = relabelGate (bitVecEquiv n).symm (networkWireGate i ζ) := networkWireGateB_eq i ζ
    have hket : Ket ((bitVecEquiv n).symm v)
        = relabelState (bitVecEquiv n).symm (Ket v) := (networkRelabelState_ket _ _).symm
    rw [hBB, hket]
    show ApplyGate (relabelGate (bitVecEquiv n).symm (networkWireGate i ζ))
        (relabelState (bitVecEquiv n).symm (Ket v))
      = relabelState (bitVecEquiv n).symm (networkWireGate i ζ *ᵥ Ket v)
    rw [applyGate_relabelGate]
    rfl
  simp only [networkActualStepCore]
  rw [if_neg (by simp)]
  rw [networkFrame_matUnit, matOuter_sandwich, relabelGate_matOuter_fwd,
    hAx x, hAx y,
    networkWireStepLeaf_firstFactor, networkWireStepLeaf_firstFactor,
    hsmul _, hsmul _, matOuter_smul_smul, hreal, sqrt2_inv_sq, one_div, htlsmul,
    traceLeft_matOuter_supported, relabelGate_matOuter_back, hB x, hB y,
    relabelGate_matOuter_back, networkRelabelGate_symm,
    networkMatUnit_eq_matOuter_ket x y,
    show (networkWireGate i ζ *ᵥ Ket x) = ApplyGate (networkWireGate i ζ) (Ket x) from rfl,
    show (networkWireGate i ζ *ᵥ Ket y) = ApplyGate (networkWireGate i ζ) (Ket y) from rfl,
    ← matOuter_sandwich]

theorem networkWireStepBranch_apply (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (ρ : Operator (2 ^ n)) :
    networkActualStepBranch (.inl (i, ζ)) (a, false) ρ
      = (if networkBranchValid [.inl (i, ζ)] (fun _ => (a, false))
        then ((2 : ℂ)⁻¹) ^ ((networkCounts [.inl (i, ζ)]).1 + 2 * (networkCounts [.inl (i, ζ)]).2)
            • conjBranch (networkLogicalMatrix [.inl (i, ζ)]) ρ else 0) := by
  have hvalid : networkBranchValid [.inl (i, ζ)] (fun _ => (a, false)) := by
    intro k
    fin_cases k
    rfl
  have hcount : (networkCounts [.inl (i, ζ)]).1 + 2 * (networkCounts [.inl (i, ζ)]).2 = 1 := by
    simp [networkCounts]
  rw [if_pos hvalid, hcount, pow_one]
  have hsmul : ∀ p : Fin (2 ^ n) × Fin (2 ^ n),
      networkActualStepBranch (.inl (i, ζ)) (a, false) (ρ p.1 p.2 • networkMatUnit p.1 p.2)
        = (((2 : ℂ)⁻¹) * ρ p.1 p.2)
          • (networkWireGate i ζ * networkMatUnit p.1 p.2
              * (networkWireGate i ζ).conjTranspose) := by
    intro p
    have h1 : networkActualStepBranch (.inl (i, ζ)) (a, false)
        (ρ p.1 p.2 • networkMatUnit p.1 p.2)
        = ρ p.1 p.2 • networkActualStepCore (.inl (i, ζ)) (a, false)
            (networkMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, networkWireStepBranch_matUnit, smul_smul,
      mul_comm (ρ p.1 p.2) ((2 : ℂ)⁻¹)]
  have hsumdistr : networkActualStepBranch (.inl (i, ζ)) (a, false)
      (∑ p : Fin (2 ^ n) × Fin (2 ^ n), ρ p.1 p.2 • networkMatUnit p.1 p.2)
      = ∑ p : Fin (2 ^ n) × Fin (2 ^ n), (((2 : ℂ)⁻¹) * ρ p.1 p.2)
          • (networkWireGate i ζ * networkMatUnit p.1 p.2
              * (networkWireGate i ζ).conjTranspose) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => hsmul p
  rw [networkMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch (networkLogicalMatrix [.inl (i, ζ)]))
      (fun p : Fin (2 ^ n) × Fin (2 ^ n) => ρ p.1 p.2 • networkMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, networkLogicalMatrix_cons]
  simp only [networkGateMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

theorem networkCzRouteFromF_outToF (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (p : (Bool × Bool) × Reg n) :
    networkCzRouteFromF n lo hi h1 (networkCzOutToF n lo hi p)
      = (((p.1.1, p.1.2), (p.2 lo, p.2 hi)),
          fun k : Fin (n - 2) =>
            p.2 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩) := by
  have hss : eRegSplit n (networkCzOutToF n lo hi p)
      = ((fun m : Fin n => if m = lo then p.1.1 else if m = hi then p.1.2 else p.2 m),
          ![p.2 lo, p.2 hi]) :=
    (eRegSplit n).apply_symm_apply _
  have hnehl : ¬((hi : Fin n) = lo) := by
    intro hc
    have hv : (hi : ℕ) = (lo : ℕ) := congrArg Fin.val hc
    omega
  unfold networkCzRouteFromF
  rw [hss]
  have hA : (if (lo : Fin n) = lo then p.1.1
      else if (lo : Fin n) = hi then p.1.2 else p.2 lo) = p.1.1 := by
    rw [if_pos rfl]
  have hB : (if (hi : Fin n) = lo then p.1.1
      else if (hi : Fin n) = hi then p.1.2 else p.2 hi) = p.1.2 := by
    rw [if_neg hnehl, if_pos rfl]
  have hS : ∀ k : Fin (n - 2),
      (if (⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩ : Fin n) = lo
        then p.1.1
        else if (⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩ : Fin n) = hi
          then p.1.2
          else p.2 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
      = p.2 ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
          networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩ := by
    intro k
    have hne := networkCzSpec_ne (lo : ℕ) (hi : ℕ) (k : ℕ) h1
    rw [if_neg (fun hc => hne.1 (congrArg Fin.val hc)),
      if_neg (fun hc => hne.2 (congrArg Fin.val hc))]
  exact Prod.ext (Prod.ext (Prod.ext hA hB) (Prod.ext rfl rfl)) (funext fun k => hS k)

theorem networkCzRoute_symm_frameVec (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (w : Reg n) :
    (networkCzRoute n lo hi h1).symm (networkFrameVec n w)
      = (((w lo, w hi), (false, false)),
          fun k : Fin (n - 2) =>
            w ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩) := by
  show networkCzRouteFromF n lo hi h1 (networkFrameVec n w) = _
  have hss : eRegSplit n (networkFrameVec n w) = (w, fun _ => false) :=
    (eRegSplit n).apply_symm_apply _
  unfold networkCzRouteFromF
  rw [hss]

noncomputable def networkCzSmallLeafOp (a d : Bool) : Operator 16 :=
  (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator

theorem networkCzSmallLeaf_column (a d xx yy : Bool) :
    (relabelGate clusterCZRegisterEquiv.symm (networkCzSmallLeafOp a d)) *ᵥ
        (Ket ((xx, yy), (false, false)))
      = (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2)
            * clusterCZ (teleportOutcomeEquiv q.2) (teleportOutcomeEquiv (xx, yy)) else 0) := by
  have hkey := clusterCZLeafColumn a d xx yy
  rw [networkRelabelState_ket] at hkey
  unfold networkCzSmallLeafOp
  show ApplyGate (relabelGate clusterCZRegisterEquiv.symm
      ((observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).operator))
      (Ket ((xx, yy), (false, false))) = _
  rw [applyGate_relabelGate',
    show clusterCZRegisterEquiv.symm.symm = clusterCZRegisterEquiv from Equiv.symm_symm _,
    networkRelabelState_ket, hkey, relabelState_relabelState]

theorem networkCzSmallLeaf_apply (a d xx yy : Bool) :
    ApplyGate (relabelGate clusterCZRegisterEquiv.symm (networkCzSmallLeafOp a d))
        (Ket ((xx, yy), (false, false)))
      = (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2)
            * clusterCZ (teleportOutcomeEquiv q.2) (teleportOutcomeEquiv (xx, yy)) else 0) :=
  networkCzSmallLeaf_column a d xx yy

theorem networkCzGateB_mulVec_ket (n : ℕ) (lo hi : Fin n) (w v : Reg n) :
    (networkCzGateB lo hi *ᵥ Ket v) w
      = (if w = v then (if w lo && w hi then (-1 : ℂ) else 1) else 0) := by
  simp only [networkCzGateB, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Qatlib.Foundations.PureStateMath.Ket]
  rw [Fintype.sum_eq_single w (fun u hu => by rw [if_neg (fun hc => hu hc.symm), zero_mul]),
    if_pos rfl]
  by_cases hw : w = v
  · subst hw
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg hw, if_neg hw, mul_zero]

theorem networkCzSupport_split (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (w v : Reg n) :
    (w = v) ↔ (((w lo, w hi) = (v lo, v hi)) ∧
      (fun k : Fin (n - 2) =>
        w ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
          networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
        = (fun k : Fin (n - 2) =>
          v ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)) := by
  constructor
  · intro h
    exact ⟨by rw [h], by rw [h]⟩
  · rintro ⟨hlohi, hspec⟩
    funext m
    by_cases hm : m = lo
    · subst hm
      exact congrArg Prod.fst hlohi
    · by_cases hm2 : m = hi
      · subst hm2
        exact congrArg Prod.snd hlohi
      · have hm1' : (m : ℕ) ≠ (lo : ℕ) := fun hc => hm (Fin.ext hc)
        have hm2' : (m : ℕ) ≠ (hi : ℕ) := fun hc => hm2 (Fin.ext hc)
        have hk' : networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ) < n - 2 :=
          networkCzSlot_lt n (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hi.isLt m.isLt hm1' hm2'
        have hspecm : w ⟨networkCzSpec (lo : ℕ) (hi : ℕ)
                (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ)
                (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)) h1 hi.isLt hk'⟩
            = v ⟨networkCzSpec (lo : ℕ) (hi : ℕ)
                (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ)
                (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)) h1 hi.isLt hk'⟩ :=
          congrFun hspec ⟨networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ), hk'⟩
        rw [show (⟨networkCzSpec (lo : ℕ) (hi : ℕ) (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ)
                (networkCzSlot (lo : ℕ) (hi : ℕ) (m : ℕ)) h1 hi.isLt hk'⟩ : Fin n) = m from
            Fin.ext (networkCzSlot_spec (lo : ℕ) (hi : ℕ) (m : ℕ) h1 hm1' hm2')] at hspecm
        exact hspecm

theorem networkCzStepLeaf_column (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (x : Fin (2 ^ n)) :
    (networkCzStepLeaf n lo hi h1 a d) *ᵥ (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (relabelState (networkCzRoute n lo hi h1)
          (TensorState
            (fun q : (Bool × Bool) × (Bool × Bool) =>
              if q.1 = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2)
                * clusterCZ (teleportOutcomeEquiv q.2)
                  (teleportOutcomeEquiv (((bitVecEquiv n).symm x) lo,
                    ((bitVecEquiv n).symm x) hi)) else 0)
            (Ket (fun k : Fin (n - 2) =>
              ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
                networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)))) := by
  have hL : networkCzStepLeaf n lo hi h1 a d
      = relabelGate (bitVecEquiv (n + 2)) (relabelGate (networkCzRoute n lo hi h1)
          (TensorGate (relabelGate clusterCZRegisterEquiv.symm (networkCzSmallLeafOp a d))
            (1 : Matrix (Reg (n - 2)) (Reg (n - 2)) ℂ))) := by
    simp only [networkCzStepLeaf, networkStepLiftLeaf, networkStepLiftGate, eCzFin,
      networkCzSmallLeafOp]
    rw [← networkRelabelGate_trans, ← networkRelabelGate_trans,
      relabelGate_prodCongr_tensorGate_one]
  show ApplyGate (networkCzStepLeaf n lo hi h1 a d) (fun r => networkFrame n r x) = _
  rw [hL, networkFrame_column, applyGate_relabelGate, applyGate_relabelGate',
    networkRelabelState_ket, networkCzRoute_symm_frameVec, ← tensorState_ket_ket,
    applyGate_tensorGate, applyGate_one, networkCzSmallLeaf_apply]

theorem networkCzStepLeaf_firstFactor (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (x : Fin (2 ^ n)) :
    relabelState (eCzOutFin n lo hi h1).symm
        ((networkCzStepLeaf n lo hi h1 a d) *ᵥ (fun r => networkFrame n r x))
      = (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d)
          then ((if a && d then (-1 : ℂ) else 1) / 2)
            * (relabelState (bitVecEquiv n) ((networkCzGateB lo hi)
                *ᵥ (Ket ((bitVecEquiv n).symm x)))) q.2
          else 0) := by
  rw [networkCzStepLeaf_column, relabelState_trans]
  funext q
  have hrr : ∀ v : Reg (n + 2),
      (networkCzRoute n lo hi h1).symm v = networkCzRouteFromF n lo hi h1 v := fun _ => rfl
  have heq : ((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q
      = networkCzOutToF n lo hi (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2) := by
    have h1' : ((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q
        = (bitVecEquiv (n + 2)).symm (eCzOutFin n lo hi h1 q) := rfl
    have h2' : eCzOutFin n lo hi h1 q
        = (bitVecEquiv (n + 2)) (networkCzOutToF n lo hi
            (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2)) := rfl
    rw [h1', h2', Equiv.symm_apply_apply]
  show TensorState
      (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a, d) then ((if a && d then (-1 : ℂ) else 1) / 2)
            * clusterCZ (teleportOutcomeEquiv q.2)
              (teleportOutcomeEquiv (((bitVecEquiv n).symm x) lo,
                ((bitVecEquiv n).symm x) hi)) else 0)
      (Ket (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩))
      ((networkCzRoute n lo hi h1).symm
        (((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q))
      = _
  rw [heq, hrr, networkCzRouteFromF_outToF]
  show (if ((teleportOutcomeEquiv.symm q.1).1, (teleportOutcomeEquiv.symm q.1).2) = (a, d)
        then ((if a && d then (-1 : ℂ) else 1) / 2)
          * clusterCZ (teleportOutcomeEquiv
              (((bitVecEquiv n).symm q.2) lo, ((bitVecEquiv n).symm q.2) hi))
            (teleportOutcomeEquiv
              (((bitVecEquiv n).symm x) lo, ((bitVecEquiv n).symm x) hi))
        else 0)
      * (if (fun k : Fin (n - 2) =>
            ((bitVecEquiv n).symm q.2) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
            = (fun k : Fin (n - 2) =>
              ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
                networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
          then (1 : ℂ) else 0)
      = (if q.1 = teleportOutcomeEquiv (a, d)
          then ((if a && d then (-1 : ℂ) else 1) / 2)
            * ((networkCzGateB lo hi *ᵥ Ket ((bitVecEquiv n).symm x))
                ((bitVecEquiv n).symm q.2))
          else 0)
  by_cases hq : q.1 = teleportOutcomeEquiv (a, d)
  · rw [if_pos hq]
    have hsym : teleportOutcomeEquiv.symm q.1 = (a, d) := by
      rw [hq, Equiv.symm_apply_apply]
    rw [hsym, if_pos rfl, clusterCZ_tele_entry, networkCzGateB_mulVec_ket]
    by_cases hc1 : (((bitVecEquiv n).symm q.2) lo, ((bitVecEquiv n).symm q.2) hi)
        = (((bitVecEquiv n).symm x) lo, ((bitVecEquiv n).symm x) hi)
    · by_cases hc2 : (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm q.2) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
        = (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
      · rw [if_pos hc1, if_pos hc2, mul_one]
        rw [if_pos ((networkCzSupport_split n lo hi h1 _ _).mpr ⟨hc1, hc2⟩)]
      · rw [if_pos hc1, if_neg hc2, mul_zero]
        rw [if_neg (fun hw => hc2 ((networkCzSupport_split n lo hi h1 _ _).mp hw).2), mul_zero]
    · rw [if_neg hc1, mul_zero, zero_mul,
        if_neg (fun hw => hc1 ((networkCzSupport_split n lo hi h1 _ _).mp hw).1), mul_zero]
  · have hpairne : ¬(((teleportOutcomeEquiv.symm q.1).1, (teleportOutcomeEquiv.symm q.1).2)
        = (a, d)) := by
      intro hp
      exact hq ((Equiv.symm_apply_eq teleportOutcomeEquiv).mp
        (Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)))
    rw [if_neg hpairne, zero_mul, if_neg hq]

theorem networkCzGateB_lo_hi {n : ℕ} (i j : Fin n) :
    networkCzGateB (networkCzLo i j) (networkCzHi i j) = networkCzGateB i j := by
  ext w w'
  by_cases hww : w = w'
  · subst hww
    have hphase : (if w (networkCzLo i j) && w (networkCzHi i j) then (-1 : ℂ) else 1)
        = (if w i && w j then (-1 : ℂ) else 1) := by
      by_cases hij : (i : ℕ) < (j : ℕ)
      · have hlo : (networkCzLo i j : Fin n) = i :=
          Fin.ext (show min (i : ℕ) (j : ℕ) = (i : ℕ) by omega)
        have hhi : (networkCzHi i j : Fin n) = j :=
          Fin.ext (show max (i : ℕ) (j : ℕ) = (j : ℕ) by omega)
        rw [hlo, hhi]
      · have hlo : (networkCzLo i j : Fin n) = j :=
          Fin.ext (show min (i : ℕ) (j : ℕ) = (j : ℕ) by omega)
        have hhi : (networkCzHi i j : Fin n) = i :=
          Fin.ext (show max (i : ℕ) (j : ℕ) = (i : ℕ) by omega)
        rw [hlo, hhi, Bool.and_comm]
    simp only [networkCzGateB, Matrix.diagonal_apply, if_true]
    exact hphase
  · simp only [networkCzGateB, Matrix.diagonal_apply]
    rw [if_neg hww, if_neg hww]

theorem networkCzGate_lo_hi {n : ℕ} (i j : Fin n) :
    networkCzGate (networkCzLo i j) (networkCzHi i j) = networkCzGate i j := by
  show relabelGate (bitVecEquiv n) (networkCzGateB (networkCzLo i j) (networkCzHi i j))
      = relabelGate (bitVecEquiv n) (networkCzGateB i j)
  rw [networkCzGateB_lo_hi]

theorem networkCzStepBranch_matUnit (n : ℕ) (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (a d : Bool) (x y : Fin (2 ^ n)) :
    networkActualStepCore (.inr (i, j)) (a, d) (networkMatUnit x y)
      = ((2 : ℂ)⁻¹) ^ 2 • (networkCzGate i j * networkMatUnit x y
          * (networkCzGate i j).conjTranspose) := by
  have hlohi : (networkCzLo i j : ℕ) < (networkCzHi i j : ℕ) := networkCzLo_lt_hi i j h
  have hεreal : (starRingEnd ℂ) ((if a && d then (-1 : ℂ) else 1) / 2)
      = (if a && d then (-1 : ℂ) else 1) / 2 := by
    cases a <;> cases d <;> simp [Complex.conj_ofNat]
  have hεsq : ((if a && d then (-1 : ℂ) else 1) / 2) * ((if a && d then (-1 : ℂ) else 1) / 2)
      = 1 / 4 := by
    cases a <;> cases d <;> norm_num
  have hq4 : (1 / 4 : ℂ) = ((2 : ℂ)⁻¹) ^ 2 := by norm_num
  have hsmulpw : ∀ (V : QState (Fin (2 ^ n))) (q : Fin 4 × Fin (2 ^ n)),
      (if q.1 = teleportOutcomeEquiv (a, d)
        then ((if a && d then (-1 : ℂ) else 1) / 2) * V q.2 else 0)
        = ((if a && d then (-1 : ℂ) else 1) / 2)
          • (if q.1 = teleportOutcomeEquiv (a, d) then V q.2 else 0) := by
    intro V q
    by_cases hq : q.1 = teleportOutcomeEquiv (a, d)
    · rw [if_pos hq, if_pos hq, smul_eq_mul]
    · rw [if_neg hq, if_neg hq, smul_eq_mul, mul_zero]
  have hsmul : ∀ V : QState (Fin (2 ^ n)),
      (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d)
          then ((if a && d then (-1 : ℂ) else 1) / 2) * V q.2 else 0)
        = ((if a && d then (-1 : ℂ) else 1) / 2) • (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d) then V q.2 else 0) := by
    intro V
    funext q
    exact hsmulpw V q
  have htlsmul : ∀ (c : ℂ) (M : Matrix (Fin 4 × Fin (2 ^ n)) (Fin 4 × Fin (2 ^ n)) ℂ),
      Matrix.traceLeft (c • M) = c • Matrix.traceLeft M := by
    intro c M
    ext u u'
    simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum,
      smul_eq_mul]
  have hAx : ∀ v : Fin (2 ^ n),
      ApplyGate (networkCzStepLeaf n (networkCzLo i j) (networkCzHi i j)
          (networkCzLo_lt_hi i j h) a d) (fun r => networkFrame n r v)
        = (networkCzStepLeaf n (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h) a d) *ᵥ (fun r => networkFrame n r v) := fun _ => rfl
  have hBB : networkCzGateB (networkCzLo i j) (networkCzHi i j)
      = relabelGate (bitVecEquiv n).symm
          (networkCzGate (networkCzLo i j) (networkCzHi i j)) := by
    show networkCzGateB (networkCzLo i j) (networkCzHi i j)
        = relabelGate (bitVecEquiv n).symm
            (relabelGate (bitVecEquiv n) (networkCzGateB (networkCzLo i j) (networkCzHi i j)))
    exact (networkRelabelGate_symm _ _).symm
  have hB : ∀ v : Fin (2 ^ n),
      (networkCzGateB (networkCzLo i j) (networkCzHi i j) *ᵥ Ket ((bitVecEquiv n).symm v))
        = relabelState (bitVecEquiv n).symm
            (networkCzGate (networkCzLo i j) (networkCzHi i j) *ᵥ Ket v) := by
    intro v
    have hket : Ket ((bitVecEquiv n).symm v)
        = relabelState (bitVecEquiv n).symm (Ket v) := (networkRelabelState_ket _ _).symm
    rw [hBB, hket]
    show ApplyGate (relabelGate (bitVecEquiv n).symm
          (networkCzGate (networkCzLo i j) (networkCzHi i j)))
        (relabelState (bitVecEquiv n).symm (Ket v))
      = relabelState (bitVecEquiv n).symm
          (networkCzGate (networkCzLo i j) (networkCzHi i j) *ᵥ Ket v)
    rw [applyGate_relabelGate]
    rfl
  simp only [networkActualStepCore]
  rw [dif_pos h]
  rw [networkFrame_matUnit, matOuter_sandwich, relabelGate_matOuter_fwd,
    hAx x, hAx y,
    networkCzStepLeaf_firstFactor, networkCzStepLeaf_firstFactor,
    hsmul _, hsmul _, matOuter_smul_smul, hεreal, hεsq, hq4, htlsmul,
    traceLeft_matOuter_supported, relabelGate_matOuter_back, hB x, hB y,
    relabelGate_matOuter_back, networkRelabelGate_symm, networkCzGate_lo_hi,
    networkMatUnit_eq_matOuter_ket x y,
    show (networkCzGate i j *ᵥ Ket x) = ApplyGate (networkCzGate i j) (Ket x) from rfl,
    show (networkCzGate i j *ᵥ Ket y) = ApplyGate (networkCzGate i j) (Ket y) from rfl,
    ← matOuter_sandwich]

theorem networkCzStepBranch_apply (n : ℕ) (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (a d : Bool) (ρ : Operator (2 ^ n)) :
    networkActualStepBranch (.inr (i, j)) (a, d) ρ
      = ((2 : ℂ)⁻¹) ^ ((networkCounts [.inr (i, j)]).1 + 2 * (networkCounts [.inr (i, j)]).2)
          • conjBranch (networkLogicalMatrix [.inr (i, j)]) ρ := by
  have hcount : (networkCounts [.inr (i, j)]).1 + 2 * (networkCounts [.inr (i, j)]).2 = 2 := by
    simp [networkCounts]
  rw [hcount]
  have hsmul : ∀ p : Fin (2 ^ n) × Fin (2 ^ n),
      networkActualStepBranch (.inr (i, j)) (a, d) (ρ p.1 p.2 • networkMatUnit p.1 p.2)
        = (((2 : ℂ)⁻¹) ^ 2 * ρ p.1 p.2)
          • (networkCzGate i j * networkMatUnit p.1 p.2
              * (networkCzGate i j).conjTranspose) := by
    intro p
    have h1 : networkActualStepBranch (.inr (i, j)) (a, d) (ρ p.1 p.2 • networkMatUnit p.1 p.2)
        = ρ p.1 p.2 • networkActualStepCore (.inr (i, j)) (a, d)
            (networkMatUnit p.1 p.2) :=
      map_smul _ _ _
    rw [h1, networkCzStepBranch_matUnit n i j h a d p.1 p.2, smul_smul,
      mul_comm (ρ p.1 p.2) (((2 : ℂ)⁻¹) ^ 2)]
  have hsumdistr : networkActualStepBranch (.inr (i, j)) (a, d)
      (∑ p : Fin (2 ^ n) × Fin (2 ^ n), ρ p.1 p.2 • networkMatUnit p.1 p.2)
      = ∑ p : Fin (2 ^ n) × Fin (2 ^ n), (((2 : ℂ)⁻¹) ^ 2 * ρ p.1 p.2)
          • (networkCzGate i j * networkMatUnit p.1 p.2
              * (networkCzGate i j).conjTranspose) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => hsmul p
  rw [networkMatUnit_decomp ρ, hsumdistr,
    map_sum (conjBranch (networkLogicalMatrix [.inr (i, j)]))
      (fun p : Fin (2 ^ n) × Fin (2 ^ n) => ρ p.1 p.2 • networkMatUnit p.1 p.2) Finset.univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjBranch_apply, networkLogicalMatrix_cons]
  simp only [networkGateMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

theorem cluster_network_actual_local_step_branches :
    ∀ (n : ℕ) (g : ClusterNetworkGate n), networkLegal [g] →
      observedWellFormed (networkPhysicalStepProgram g) ∧
      ∀ (o : Bool × Bool) (ρ : Operator (2 ^ n)),
        networkActualStepBranch g o ρ
          = (if networkBranchValid [g] (fun _ => o)
            then (((2 : ℂ)⁻¹) ^ ((networkCounts [g]).1 + 2 * (networkCounts [g]).2)
                • conjBranch (networkLogicalMatrix [g]) ρ)
            else 0) := by
  intro n g hlegal
  cases g with
  | inl p =>
    obtain ⟨i, ζ⟩ := p
    have hζ : ‖ζ‖ = 1 := hlegal _ List.mem_cons_self
    refine ⟨networkStepLift_wellFormed (eWireFin n i) (clusterWireProgram ζ)
      ((cluster_wire_actual_counts ζ hζ).1), ?_⟩
    intro o ρ
    obtain ⟨oa, ob⟩ := o
    by_cases hob : ob = false
    · subst hob
      exact networkWireStepBranch_apply n i ζ oa ρ
    · have hob' : ob = true := by
        cases ob with
        | false => exact absurd rfl hob
        | true => rfl
      subst hob'
      have hinvalid : ¬ networkBranchValid [.inl (i, ζ)] (fun _ => (oa, true)) := by
        intro hv
        have h0 : true = false := hv 0
        exact Bool.noConfusion h0
      rw [if_neg hinvalid]
      show networkActualStepCore (.inl (i, ζ)) (oa, true) ρ = 0
      simp only [networkActualStepCore, if_true]
  | inr p =>
    obtain ⟨i, j⟩ := p
    have hij : (i : Fin n) ≠ j := hlegal _ List.mem_cons_self
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
    refine ⟨?_, ?_⟩
    · show observedWellFormed (networkPhysicalStepProgram (.inr (i, j)))
      simp only [networkPhysicalStepProgram]
      rw [dif_pos hne]
      exact networkStepLift_wellFormed _ _ cluster_cz_actual_program_and_feedback_cost.1
    · intro o ρ
      have hvalid : networkBranchValid [.inr (i, j)] (fun _ => o) := by
        intro k
        fin_cases k
        trivial
      rw [if_pos hvalid]
      exact networkCzStepBranch_apply n i j hne o.1 o.2 ρ
end Qatlib.Concepts.MbqcFlow.FlowDecision
