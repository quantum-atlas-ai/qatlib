/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceEmbedding
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Workspace padding for circuit words

`workspaceWord` lifts a gate-and-query circuit to a larger auxiliary workspace using
`workspaceGate` for known gates and the same query constructor for oracle calls. The lifted run
agrees with embedding the original run, and both query and gate counts are preserved.

The basis inclusion `workspaceBasis` identifies valid ambient basis states. The module proves
amplitude, normalization, and measurement-event preservation under this inclusion, within the
finite-register circuit formalism of [NielsenChuang2010].

## Main statements

* `workspaceWord_run`: running the lifted word commutes with workspace embedding.
* `workspaceWord_queries`: the lifted word has the same query count.
* `workspaceWord_readout`: corresponding output measurement events have equal probabilities.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.Execution.WorkspaceCP
open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

/-- Lift a circuit word to a larger auxiliary workspace by completing each known gate and
preserving each query step. -/
def workspaceWord {d k K : ℕ} (h : k ≤ K) : Circuit (Fin (d*k)) → Circuit (Fin (d*K))
  | [] => []
  | Step.gate G :: C => Step.gate (workspaceGate h G) :: workspaceWord h C
  | Step.query :: C => Step.query :: workspaceWord h C

/-- Applying a completed gate to an embedded state equals embedding the original gate's output. -/
theorem workspaceWord_gate_state {d k K : ℕ} (h : k ≤ K)
    (G : Operator (d*k)) (psi : QState (Fin (d*k))) :
    ApplyGate (workspaceGate h G) (workspaceEmbedding h *ᵥ psi) =
      workspaceEmbedding h *ᵥ ApplyGate G psi := by
  change (workspaceGate h G) *ᵥ ((workspaceEmbedding h) *ᵥ psi) =
    (workspaceEmbedding h) *ᵥ (G *ᵥ psi)
  rw [Matrix.mulVec_mulVec,workspaceGate_intertwine,Matrix.mulVec_mulVec]

/-- Applying the enlarged workspace oracle to an embedded state equals embedding the original
oracle's output. -/
theorem workspaceWord_query_state {d k K : ℕ} (h : k ≤ K)
    (U : Operator d) (psi : QState (Fin (d*k))) :
    ApplyGate (forwardWorkspaceOracle K U) (workspaceEmbedding h *ᵥ psi) =
      workspaceEmbedding h *ᵥ ApplyGate (forwardWorkspaceOracle k U) psi := by
  change (forwardWorkspaceOracle K U) *ᵥ ((workspaceEmbedding h) *ᵥ psi) =
    (workspaceEmbedding h) *ᵥ ((forwardWorkspaceOracle k U) *ᵥ psi)
  rw [Matrix.mulVec_mulVec,workspaceEmbedding_intertwine,Matrix.mulVec_mulVec]

/-- Running a lifted circuit on an embedded state equals embedding the result of the original
circuit. -/
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

/-- Lifting a circuit word preserves its number of oracle queries. -/
theorem workspaceWord_queries {d k K : ℕ} (h : k ≤ K) (C : Circuit (Fin (d*k))) :
    QueryCount (workspaceWord h C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workspaceWord,QueryCount,ih]

/-- Lifting a circuit word preserves its number of known gates. -/
theorem workspaceWord_gates {d k K : ℕ} (h : k ≤ K) (C : Circuit (Fin (d*k))) :
    GateCount (workspaceWord h C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workspaceWord,GateCount,ih]

/-- Lifting a unitary circuit word yields a unitary circuit word. -/
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

/-- The injective basis map that preserves the oracle coordinate and includes the auxiliary
coordinate into the larger workspace. -/
def workspaceBasis {d k K : ℕ} (h : k ≤ K) : Fin (d*k) ↪ Fin (d*K) where
  toFun b := finProdFinEquiv ((finProdFinEquiv.symm b).1,Fin.castLE h (finProdFinEquiv.symm b).2)
  inj' := by
    intro a b hab
    have hab' := congrArg finProdFinEquiv.symm hab
    simp only [Equiv.symm_apply_apply,Prod.mk.injEq] at hab'
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hab'.1 ((Fin.castLE_injective h) hab'.2)

/-- Workspace embedding entries are Kronecker indicators for the basis inclusion
`workspaceBasis`. -/
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

/-- The amplitude at an included basis state equals its original amplitude before workspace
embedding. -/
theorem workspaceEmbedding_amplitude {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (b : Fin (d*k)) :
    (workspaceEmbedding h *ᵥ psi) (workspaceBasis h b) = psi b := by
  simp [Matrix.mulVec,dotProduct,workspaceEmbedding_delta,(workspaceBasis h).injective.eq_iff]

/-- An embedded state has zero amplitude at every basis state outside the image of
`workspaceBasis`. -/
theorem workspaceEmbedding_illegal {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (a : Fin (d*K))
    (ha : ∀ b, a ≠ workspaceBasis h b) : (workspaceEmbedding h *ᵥ psi) a = 0 := by
  simp [Matrix.mulVec,dotProduct,workspaceEmbedding_delta,ha]

/-- Workspace embedding preserves the probability of a finite measurement event mapped along
`workspaceBasis`. -/
theorem workspaceEmbedding_event {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (S : Finset (Fin (d*k))) :
    MeasureProb (workspaceEmbedding h *ᵥ psi) (S.map (workspaceBasis h)) = MeasureProb psi S := by
  unfold MeasureProb BornProb
  rw [Finset.sum_map]
  simp only [workspaceEmbedding_amplitude]

/-- The original and lifted circuit runs have equal probabilities for corresponding basis
measurement events. -/
theorem workspaceWord_readout {d k K : ℕ} (h : k ≤ K) (U : Operator d)
    (C : Circuit (Fin (d*k))) (psi : QState (Fin (d*k))) (S : Finset (Fin (d*k))) :
    MeasureProb (Run (forwardWorkspaceOracle K U) (workspaceWord h C) (workspaceEmbedding h *ᵥ psi))
        (S.map (workspaceBasis h)) = MeasureProb (Run (forwardWorkspaceOracle k U) C psi) S := by
  rw [workspaceWord_run,workspaceEmbedding_event]

/-- Workspace embedding preserves the total basis measurement probability. -/
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

/-- Workspace embedding preserves normalization of pure states. -/
theorem workspaceEmbedding_normalized {d k K : ℕ} (h : k ≤ K)
    (psi : QState (Fin (d*k))) (hpsi : Normalized psi) :
    Normalized (workspaceEmbedding h *ᵥ psi) := by
  change MeasureProb (workspaceEmbedding h *ᵥ psi) Finset.univ = 1
  rw [workspaceEmbedding_total]
  exact hpsi

end Qatlib.Concepts.Execution.WorkspaceCP
