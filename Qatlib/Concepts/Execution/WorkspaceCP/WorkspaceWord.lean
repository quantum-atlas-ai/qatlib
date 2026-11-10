/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceEmbedding
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.Execution.WorkspaceCP
open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

def workspaceWord {d k K : ℕ} (h : k ≤ K) : Circuit (Fin (d*k)) → Circuit (Fin (d*K))
  | [] => []
  | Step.gate G :: C => Step.gate (workspaceGate h G) :: workspaceWord h C
  | Step.query :: C => Step.query :: workspaceWord h C

theorem workspaceWord_gate_state {d k K : ℕ} (h : k ≤ K)
    (G : Operator (d*k)) (psi : QState (Fin (d*k))) :
    ApplyGate (workspaceGate h G) (workspaceEmbedding h *ᵥ psi) =
      workspaceEmbedding h *ᵥ ApplyGate G psi := by
  change (workspaceGate h G) *ᵥ ((workspaceEmbedding h) *ᵥ psi) =
    (workspaceEmbedding h) *ᵥ (G *ᵥ psi)
  rw [Matrix.mulVec_mulVec,workspaceGate_intertwine,Matrix.mulVec_mulVec]

theorem workspaceWord_query_state {d k K : ℕ} (h : k ≤ K)
    (U : Operator d) (psi : QState (Fin (d*k))) :
    ApplyGate (forwardWorkspaceOracle K U) (workspaceEmbedding h *ᵥ psi) =
      workspaceEmbedding h *ᵥ ApplyGate (forwardWorkspaceOracle k U) psi := by
  change (forwardWorkspaceOracle K U) *ᵥ ((workspaceEmbedding h) *ᵥ psi) =
    (workspaceEmbedding h) *ᵥ ((forwardWorkspaceOracle k U) *ᵥ psi)
  rw [Matrix.mulVec_mulVec,workspaceEmbedding_intertwine,Matrix.mulVec_mulVec]

theorem workspaceWord_run {d k K : ℕ} (h : k ≤ K) (U : Operator d)
    (C : Circuit (Fin (d*k))) (psi : QState (Fin (d*k))) :
    Run (forwardWorkspaceOracle K U) (workspaceWord h C) (workspaceEmbedding h *ᵥ psi) =
      workspaceEmbedding h *ᵥ Run (forwardWorkspaceOracle k U) C psi := by
  induction C generalizing psi with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate G =>
      change Run _ (workspaceWord h C)
          (ApplyGate (workspaceGate h G) (workspaceEmbedding h *ᵥ psi)) = _
      rw [workspaceWord_gate_state]
      exact ih (ApplyGate G psi)
    | query =>
      change Run _ (workspaceWord h C)
          (ApplyGate (forwardWorkspaceOracle K U) (workspaceEmbedding h *ᵥ psi)) = _
      rw [workspaceWord_query_state]
      exact ih (ApplyGate (forwardWorkspaceOracle k U) psi)

theorem workspaceWord_queries {d k K : ℕ} (h : k ≤ K) (C : Circuit (Fin (d*k))) :
    QueryCount (workspaceWord h C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workspaceWord,QueryCount,ih]

theorem workspaceWord_gates {d k K : ℕ} (h : k ≤ K) (C : Circuit (Fin (d*k))) :
    GateCount (workspaceWord h C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workspaceWord,GateCount,ih]

theorem workspaceWord_unitary {d k K : ℕ} (h : k ≤ K) (C : Circuit (Fin (d*k)))
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (workspaceWord h C) := by
  induction C with
  | nil => simp [workspaceWord]
  | cons s C ih =>
    cases s with
    | gate G =>
      have h := (isUnitaryCircuit_gate G C).mp hC
      exact (isUnitaryCircuit_gate _ _).mpr ⟨workspaceGate_unitary _ _ h.1,ih h.2⟩
    | query =>
      exact (isUnitaryCircuit_query _).mpr (ih ((isUnitaryCircuit_query C).mp hC))

def workspaceBasis {d k K : ℕ} (h : k ≤ K) : Fin (d*k) ↪ Fin (d*K) where
  toFun b := finProdFinEquiv ((finProdFinEquiv.symm b).1,Fin.castLE h (finProdFinEquiv.symm b).2)
  inj' := by
    intro a b hab
    have hab' := congrArg finProdFinEquiv.symm hab
    simp only [Equiv.symm_apply_apply,Prod.mk.injEq] at hab'
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hab'.1 ((Fin.castLE_injective h) hab'.2)

theorem workspaceEmbedding_delta {d k K : ℕ} (h : k ≤ K)
    (a : Fin (d*K)) (b : Fin (d*k)) :
    workspaceEmbedding h a b = if a = workspaceBasis h b then 1 else 0 := by
  have he : a = workspaceBasis h b ↔
      (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1 ∧
      (finProdFinEquiv.symm a).2 = Fin.castLE h (finProdFinEquiv.symm b).2 := by
    constructor
    · intro ha
      subst a
      simp only [workspaceBasis,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply]
      exact ⟨True.intro,True.intro⟩
    · intro ha
      apply finProdFinEquiv.symm.injective
      simpa only [workspaceBasis,Function.Embedding.coeFn_mk,Equiv.symm_apply_apply] using
          Prod.ext ha.1 ha.2
  rw [workspaceEmbedding_apply]
  simp only [Matrix.one_apply]
  by_cases hd : (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1
  · simp only [hd,if_true,one_mul,he,true_and]
  · simp only [hd,if_false,zero_mul,he,false_and]

theorem workspaceEmbedding_amplitude {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (b : Fin (d*k)) :
    (workspaceEmbedding h *ᵥ psi) (workspaceBasis h b) = psi b := by
  simp [Matrix.mulVec,dotProduct,workspaceEmbedding_delta,(workspaceBasis h).injective.eq_iff]

theorem workspaceEmbedding_illegal {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (a : Fin (d*K))
    (ha : ∀ b, a ≠ workspaceBasis h b) : (workspaceEmbedding h *ᵥ psi) a = 0 := by
  simp [Matrix.mulVec,dotProduct,workspaceEmbedding_delta,ha]

theorem workspaceEmbedding_event {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (S : Finset (Fin (d*k))) :
    MeasureProb (workspaceEmbedding h *ᵥ psi) (S.map (workspaceBasis h)) = MeasureProb psi S := by
  unfold MeasureProb BornProb
  rw [Finset.sum_map]
  simp only [workspaceEmbedding_amplitude]

theorem workspaceWord_readout {d k K : ℕ} (h : k ≤ K) (U : Operator d)
    (C : Circuit (Fin (d*k))) (psi : QState (Fin (d*k))) (S : Finset (Fin (d*k))) :
    MeasureProb (Run (forwardWorkspaceOracle K U) (workspaceWord h C) (workspaceEmbedding h *ᵥ psi))
        (S.map (workspaceBasis h)) = MeasureProb (Run (forwardWorkspaceOracle k U) C psi) S := by
  rw [workspaceWord_run,workspaceEmbedding_event]

theorem workspaceEmbedding_total {d k K : ℕ} (h : k ≤ K) (psi : QState (Fin (d*k))) :
    MeasureProb (workspaceEmbedding h *ᵥ psi) Finset.univ = MeasureProb psi Finset.univ := by
  calc
    _ = MeasureProb (workspaceEmbedding h *ᵥ psi) (Finset.univ.map (workspaceBasis h)) := by
      symm
      unfold MeasureProb
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      unfold BornProb
      rw [workspaceEmbedding_illegal h psi a]
      · simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
      · intro b hab
        apply ha
        exact Finset.mem_map.mpr ⟨b,Finset.mem_univ b,hab.symm⟩
    _ = _ := workspaceEmbedding_event h psi Finset.univ

theorem workspaceEmbedding_normalized {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (hpsi : Normalized psi) :
    Normalized (workspaceEmbedding h *ᵥ psi) := by
  change MeasureProb (workspaceEmbedding h *ᵥ psi) Finset.univ = 1
  rw [workspaceEmbedding_total]
  exact hpsi

end Qatlib.Concepts.Execution.WorkspaceCP
