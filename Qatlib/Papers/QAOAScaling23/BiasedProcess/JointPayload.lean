/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.Native
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Payload
variable {I : Type} [Fintype I]

def representative (cost : I → ℝ) (j : Fin (costLevels cost).card) : I :=
  Classical.choose (costRank_surjective cost j)

theorem representative_rank (cost : I → ℝ) (j : Fin (costLevels cost).card) :
    costRank cost (representative cost j) = j := Classical.choose_spec (costRank_surjective cost j)

def output {K : ℕ} (cost : I → ℝ) (r : ℕ) (receipt : Fin K → CappedSearchTrace I) (a : Fin K) : Option (Fin (r+1)) :=
  (receipt a).result.bind (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank cost (r+1))

def row {K : ℕ} (cost : I → ℝ) (r : ℕ) (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I)
    (fee : Fin K → ℕ) (target : PMF (Fin (r+1))) : Row r :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row p (output cost r receipt) fee target

def origin {K : ℕ} (cost : I → ℝ) (r : ℕ) (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I)
    (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (a : Fin (row cost r p receipt fee target).outcomes) : Fin K :=
  (Tree.indexedLeafValue (Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.completion p (output cost r receipt) target) a).1

def candidate {K : ℕ} (cost : I → ℝ) (r : ℕ) (hk : r+1 ≤ (costLevels cost).card)
    (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (a : Fin (row cost r p receipt fee target).outcomes) : I :=
  match (receipt (origin cost r p receipt fee target a)).result with
  | some i => i
  | none => representative cost ⟨(row cost r p receipt fee target).next a,lt_of_lt_of_le ((row cost r p receipt fee target).next a).isLt hk⟩

theorem good_label {K : ℕ} (cost : I → ℝ) (r : ℕ) (hk : r+1 ≤ (costLevels cost).card)
    (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (a : Fin (row cost r p receipt fee target).outcomes) (hgood : (row cost r p receipt fee target).bad a = false) :
    (receipt (origin cost r p receipt fee target a)).result = some (candidate cost r hk p receipt fee target a) ∧
      (costRank cost (candidate cost r hk p receipt fee target a)).val = ((row cost r p receipt fee target).next a).val := by
  have h :=
      Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row_good_output p
      (output cost r receipt) fee target a hgood
  change (receipt (origin cost r p receipt fee target a)).result.bind
      (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank cost (r+1)) = some
      ((row cost r p receipt fee target).next a) at h
  cases he : (receipt (origin cost r p receipt fee target a)).result with
  | none => simp [he] at h
  | some i =>
    have hc : candidate cost r hk p receipt fee target a = i := by simp [candidate,he]
    rw [he,Option.bind_some] at h
    exact ⟨by rw [hc],by rw [hc];exact (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank_some cost _ i _).mp h⟩

theorem bad_eq_none {K : ℕ} (cost : I → ℝ) (r : ℕ) (p : PMF (Fin K))
    (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (hsound : ∀a i,(receipt a).result = some i → (costRank cost i).val < r+1)
    (a : Fin (row cost r p receipt fee target).outcomes) :
    (row cost r p receipt fee target).bad a = (receipt (origin cost r p receipt fee target a)).result.isNone := by
  change ((receipt (origin cost r p receipt fee target a)).result.bind (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank cost (r+1))).isNone = _
  cases he : (receipt (origin cost r p receipt fee target a)).result with
  | none => simp
  | some i => simp only [Option.bind_some,Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank,dif_pos (hsound _ i he),Option.isNone_some]

theorem optional_candidate {K : ℕ} (cost : I → ℝ) (r : ℕ) (hk : r+1 ≤ (costLevels cost).card)
    (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (hsound : ∀a i,(receipt a).result = some i → (costRank cost i).val < r+1)
    (a : Fin (row cost r p receipt fee target).outcomes) :
    (if (row cost r p receipt fee target).bad a then none else some (candidate cost r hk p receipt fee target a)) =
      (receipt (origin cost r p receipt fee target a)).result := by
  rw [bad_eq_none cost r p receipt fee target hsound a]
  cases he : (receipt (origin cost r p receipt fee target a)).result with
  | none => simp
  | some i => simp [candidate,he]

theorem original_marginal {K : ℕ} (cost : I → ℝ) (r : ℕ) (p : PMF (Fin K))
    (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1))) :
    (row cost r p receipt fee target).law.map (origin cost r p receipt fee target) = p :=
  Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row_original_marginal p (output cost r receipt) fee target

theorem candidate_fee_joint {K : ℕ} (cost : I → ℝ) (r : ℕ) (hk : r+1 ≤ (costLevels cost).card)
    (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (hsound : ∀a i,(receipt a).result = some i → (costRank cost i).val < r+1) :
    (row cost r p receipt fee target).law.map (fun a =>
      (if (row cost r p receipt fee target).bad a then none else some (candidate cost r hk p receipt fee target a),
        (row cost r p receipt fee target).charge a)) = p.map (fun a => ((receipt a).result,fee a)) := by
  have he : (fun a => (if (row cost r p receipt fee target).bad a then none else some (candidate cost r hk p receipt fee target a),
      (row cost r p receipt fee target).charge a)) =
      (fun a => ((receipt (origin cost r p receipt fee target a)).result,fee (origin cost r p receipt fee target a))) := by
    funext a
    rw [optional_candidate cost r hk p receipt fee target hsound a]
    rfl
  rw [he]
  change (row cost r p receipt fee target).law.map
    ((fun x => ((receipt x).result,fee x)) ∘ origin cost r p receipt fee target) = _
  rw [← PMF.map_comp,original_marginal]

theorem candidate_rank {K : ℕ} (cost : I → ℝ) (r : ℕ) (hk : r+1 ≤ (costLevels cost).card)
    (p : PMF (Fin K)) (receipt : Fin K → CappedSearchTrace I) (fee : Fin K → ℕ) (target : PMF (Fin (r+1)))
    (hsound : ∀a i,(receipt a).result = some i → (costRank cost i).val < r+1)
    (a : Fin (row cost r p receipt fee target).outcomes) :
    (costRank cost (candidate cost r hk p receipt fee target a)).val = ((row cost r p receipt fee target).next a).val := by
  cases hb : (row cost r p receipt fee target).bad a with
  | false => exact (good_label cost r hk p receipt fee target a hb).2
  | true =>
    have hn : (receipt (origin cost r p receipt fee target a)).result = none := by
      have h := bad_eq_none cost r p receipt fee target hsound a
      rw [hb] at h
      cases he : (receipt (origin cost r p receipt fee target a)).result with
      | none => rfl
      | some i => rw [he] at h; contradiction
    simp only [candidate,hn,representative_rank]
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Payload
