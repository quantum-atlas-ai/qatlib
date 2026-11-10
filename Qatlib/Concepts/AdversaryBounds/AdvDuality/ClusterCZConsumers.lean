/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ClusterPatterns.ChainFeedback.ClusterWireConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ClusterPatterns.ChainFeedback
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable def clusterCZPlusInput : QState (Fin 4) :=
  relabelState teleportOutcomeEquiv (TensorState Plus Plus)

theorem clusterCZPlusInput_normalized : Normalized clusterCZPlusInput :=
  normalized_relabelState _ (normalized_tensorState normalized_plus normalized_plus)

theorem clusterCZPlusInput_apply (r : Fin 4) : clusterCZPlusInput r = (1 / 2 : ℂ) := by
  obtain ⟨⟨u, v⟩, rfl⟩ : ∃ q : Bool × Bool, r = teleportOutcomeEquiv q :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  simp [clusterCZPlusInput, relabelState, Function.comp_apply, TensorState, Plus,
    hadamard_apply_false, sqrt2_inv_sq]

theorem clusterCZPlusInput_hsum :
    (∑ o : Bool × Bool, clusterCZActualBranchMap o.1 o.2 (outerProduct clusterCZPlusInput))
      = outerProduct (ApplyGate clusterCZ clusterCZPlusInput) := by
  rw [Finset.sum_congr rfl (fun o _ => clusterCZActualBranchMap_apply o.1 o.2 _),
    sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul,
    conjBranch_outerProduct]
  rfl

theorem cluster_cz_plus_actual_entangling_consumer :
    Normalized clusterCZPlusInput ∧
      (∑ o : Bool × Bool, clusterCZActualBranchMap o.1 o.2 (outerProduct clusterCZPlusInput))
        = outerProduct (ApplyGate clusterCZ clusterCZPlusInput) ∧
      (∑ o : Bool × Bool, clusterCZActualBranchMap o.1 o.2 (outerProduct clusterCZPlusInput))
        = (1 / 4 : ℂ) • !![1, 1, 1, -1; 1, 1, 1, -1; 1, 1, 1, -1; -1, -1, -1, 1] ∧
      ¬ (∃ ψ φ : QState Bool, ApplyGate clusterCZ clusterCZPlusInput =
        relabelState teleportOutcomeEquiv (TensorState ψ φ)) := by
  refine ⟨clusterCZPlusInput_normalized, clusterCZPlusInput_hsum, ?_, ?_⟩
  · rw [clusterCZPlusInput_hsum]
    ext r r'
    obtain ⟨⟨u, v⟩, rfl⟩ : ∃ q : Bool × Bool, r = teleportOutcomeEquiv q :=
      ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
    obtain ⟨⟨u', v'⟩, rfl⟩ : ∃ q : Bool × Bool, r' = teleportOutcomeEquiv q :=
      ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
    rw [outerProduct_apply, clusterCZ_apply]
    simp only [Equiv.symm_apply_apply, clusterCZPlusInput_apply]
    cases u <;> cases v <;> cases u' <;> cases v' <;>
      simp [teleportOutcomeEquiv, Equiv.prodCongr, finProdFinEquiv, boolEquivFin2,
        Matrix.smul_apply, smul_eq_mul, Complex.conj_ofNat] <;> norm_num
  · intro ⟨ψ, φ, h⟩
    have hff := congrFun h (teleportOutcomeEquiv (false, false))
    have htt := congrFun h (teleportOutcomeEquiv (true, true))
    have hft := congrFun h (teleportOutcomeEquiv (false, true))
    have htf := congrFun h (teleportOutcomeEquiv (true, false))
    simp [clusterCZ_apply, clusterCZPlusInput_apply, relabelState, TensorState]
      at hff htt hft htf
    have key : (ψ false * φ false) * (ψ true * φ true)
        = (ψ false * φ true) * (ψ true * φ false) := by ring
    rw [← hff, ← htt, ← hft, ← htf] at key
    norm_num at key

noncomputable def clusterCZBellReferenceInput : QState (Fin 4 × Fin 4) :=
  fun p => if p.1 = p.2 then (1 / 2 : ℂ) else 0

theorem clusterCZBellReferenceInput_normalized : Normalized clusterCZBellReferenceInput := by
  show ∑ p : Fin 4 × Fin 4, ‖clusterCZBellReferenceInput p‖ ^ 2 = 1
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_four, clusterCZBellReferenceInput]
  norm_num

theorem clusterCZBellReference_hsum :
    (∑ o : Bool × Bool, tensorLeft (clusterCZActualBranchMap o.1 o.2)
        (outerProduct clusterCZBellReferenceInput))
      = outerProduct (ApplyGate (TensorGate clusterCZ (1 : Operator 4))
          clusterCZBellReferenceInput) := by
  rw [(cluster_cz_actual_reference_channel 4 (outerProduct clusterCZBellReferenceInput)
    false false).2, tensorGate_outerProduct_conj]

theorem cluster_cz_actual_bell_reference_changed_consumer :
    Normalized clusterCZBellReferenceInput ∧
      (∑ o : Bool × Bool, tensorLeft (clusterCZActualBranchMap o.1 o.2)
          (outerProduct clusterCZBellReferenceInput))
        = outerProduct (ApplyGate (TensorGate clusterCZ (1 : Operator 4))
            clusterCZBellReferenceInput) ∧
      (∑ o : Bool × Bool, tensorLeft (clusterCZActualBranchMap o.1 o.2)
          (outerProduct clusterCZBellReferenceInput))
        ≠ outerProduct clusterCZBellReferenceInput := by
  refine ⟨clusterCZBellReferenceInput_normalized, clusterCZBellReference_hsum, ?_⟩
  intro hcontra
  rw [clusterCZBellReference_hsum] at hcontra
  have hval : ∀ i r : Fin 4,
      ApplyGate (TensorGate clusterCZ (1 : Operator 4)) clusterCZBellReferenceInput (i, r)
        = (if (teleportOutcomeEquiv.symm i).1 && (teleportOutcomeEquiv.symm i).2
            then (-1 : ℂ) else 1) * clusterCZBellReferenceInput (i, r) := by
    intro i r
    have hstep := congrFun (clusterCZ_apply
      (fun i' => clusterCZBellReferenceInput (i', r))) i
    rw [applyGate_firstFactor]
    exact hstep
  have e := congrFun (congrFun hcontra
    (teleportOutcomeEquiv (false, false), teleportOutcomeEquiv (false, false)))
    (teleportOutcomeEquiv (true, true), teleportOutcomeEquiv (true, true))
  rw [outerProduct_apply, outerProduct_apply, hval, hval] at e
  norm_num [clusterCZBellReferenceInput, Complex.conj_ofNat] at e

theorem cluster_cz_true_mixed_and_double_pattern_identity_consumer :
    IsDensityOperator ((1 / 4 : ℂ) • (1 : Operator 4)) ∧
      ¬ IsPureDensityOperator ((1 / 4 : ℂ) • (1 : Operator 4)) ∧
      (∑ o : Bool × Bool, clusterCZActualBranchMap o.1 o.2 ((1 / 4 : ℂ) • (1 : Operator 4)))
        = (1 / 4 : ℂ) • (1 : Operator 4) ∧
      (∀ (r : ℕ) (ρ : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) ℂ),
        (∑ o : Bool × Bool, ∑ p : Bool × Bool,
          tensorLeft ((clusterCZActualBranchMap p.1 p.2).comp (clusterCZActualBranchMap o.1 o.2))
            ρ) = ρ) ∧
      (∀ a d b e : Bool,
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).gates +
          (observedLeaf 1 clusterCZProgram (clusterCZLeaf b e)).gates = 26 ∧
        (observedLeaf 1 clusterCZProgram (clusterCZLeaf a d)).measurements +
          (observedLeaf 1 clusterCZProgram (clusterCZLeaf b e)).measurements = 4) := by
  have hCZ : clusterCZ * clusterCZᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp clusterCZ_unitary
    rwa [Matrix.star_eq_conjTranspose] at h
  have hCZ2 : ∀ σ : Operator 4, conjBranch clusterCZ (conjBranch clusterCZ σ) = σ := by
    intro σ
    have h := conjBranch_comp clusterCZ clusterCZ
    rw [clusterCZ_mul_self] at h
    have h2 := LinearMap.congr_fun h σ
    rw [LinearMap.comp_apply] at h2
    rw [h2, conjBranch_apply, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨Matrix.PosSemidef.smul Matrix.PosSemidef.one (by simp), ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num
  · intro ⟨⟨_, _⟩, hmul⟩
    have h00 := congrArg (fun M : Operator 4 => M 0 0) hmul
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.sum_univ_four] at h00
    simp at h00
  · rw [Finset.sum_congr rfl (fun o _ => clusterCZActualBranchMap_apply o.1 o.2 _),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4)) = 1 from by norm_num, one_smul,
      conjBranch_apply, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hCZ]
  · intro r ρ
    have hpair : ∀ o p : Bool × Bool,
        tensorLeft ((clusterCZActualBranchMap p.1 p.2).comp (clusterCZActualBranchMap o.1 o.2)) ρ
          = (1 / 16 : ℂ) • ρ := by
      intro o p
      ext ⟨x1, x2⟩ ⟨y1, y2⟩
      simp only [tensorLeft, LinearMap.comp_apply, clusterCZActualBranchMap_apply, map_smul,
        smul_smul]
      rw [hCZ2]
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun p _ => hpair o p,
      sum_univ_boolPair_smul, sum_univ_boolPair_smul,
      show ((4 : ℂ) * (4 * (1 / 16))) = 1 from by norm_num, one_smul]
  · intro a d b e
    have h1 := cluster_cz_actual_program_and_feedback_cost.2.2.2.1 a d
    have h2 := cluster_cz_actual_program_and_feedback_cost.2.2.2.1 b e
    exact ⟨by rw [h1.2.2.1, h2.2.2.1], by rw [h1.2.2.2.1, h2.2.2.2.1]⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
