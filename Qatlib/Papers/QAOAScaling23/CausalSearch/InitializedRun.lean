/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.Risk
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.FiniteDraw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open BiasedProcess
variable {I : Type} [Fintype I]

def initializedRun (cost : I → ℝ) (p : PMF I) (oracle : I → Code I (Option I))
    (fuel B initialFee : ℕ) (fallback : I) :
    Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I) :=
  if initialFee≤B then
    (Tree.sampleF p (fun current => run cost current (B-initialFee)
      (minimumCode oracle fuel current))).map (charge initialFee)
  else .pure ⟨none,B,fallback⟩

theorem initializedRun_cap (cost : I → ℝ) (p : PMF I) (oracle : I → Code I (Option I))
    (fuel B initialFee : ℕ) (fallback : I) :
    (initializedRun cost p oracle fuel B initialFee fallback).All (fun out => out.paid≤B) := by
  rw [initializedRun]
  split_ifs with hi
  · rw [Tree.all_map,Tree.all_sampleF]
    intro current
    apply Tree.all_mono _ (run_paid_le cost _ current (B-initialFee))
    intro out hout
    change initialFee+out.paid≤B
    omega
  · exact Nat.le_refl B

theorem initializedRun_failure_le_risk {L : ℕ} (cost : I → ℝ) (rank : I → Fin L)
    (hzero : ∀ i,(rank i).val=0 ↔ ∀ j,cost i≤cost j)
    (horder : ∀ i j,(rank i).val<(rank j).val ↔ cost i<cost j)
    (p : PMF I) (oracle : I → Code I (Option I)) (hno : ∀ i,NoSave (oracle i))
    (rows : (r : ℕ) → Row r)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I)
    (hnext : ∀ r a,(rank (candidate r a)).val=((rows r).next a).val)
    (hjoint : ∀ current r,(rank current).val=r+1 →
      (paidTree cost current (oracle current)).law=
        ((rows r).law.map (rowPayload rows candidate r)))
    (fuel B initialFee : ℕ) (fallback : I) (hfuel : ∀ i,(rank i).val≤fuel)
    (hinit : initialFee≤B) :
    (initializedRun cost p oracle fuel B initialFee fallback).mean
        (physicalFailure (fun i => (rank i).val))≤
      initializedRisk (p.map rank) rows B initialFee := by
  let rt:=Tree.sampleF p (fun i => descend rows (rank i).val)
  have hlaw : rt.law=(initialized (p.map rank) rows).law := by
    simp only [rt,Tree.law_sampleF,initialized,Tree.law,PMF.bind_map,Function.comp_def]
  have hraw : (initializedRun cost p oracle fuel B initialFee fallback).mean
      (physicalFailure (fun i => (rank i).val))≤
      rt.probability (fun tr => tr.oracleBad=true ∨ B < initialFee+paid tr) := by
    rw [initializedRun,if_pos hinit,Tree.mean_map]
    change (Tree.sampleF p (fun current => run cost current (B-initialFee)
      (minimumCode oracle fuel current))).mean (physicalFailure (fun i => (rank i).val))≤_
    rw [Tree.mean_sampleF]
    change _≤(Tree.sampleF p (fun i => descend rows (rank i).val)).mean _
    rw [Tree.mean_sampleF]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    have hbound:=physical_failure_le_prehitRisk cost (fun i => (rank i).val)
      hzero horder oracle hno rows candidate hnext hjoint i fuel (B-initialFee) (hfuel i)
    apply hbound.trans_eq
    unfold prehitRisk Tree.probability
    apply Tree.mean_congr
    apply Tree.all_of_forall
    intro tr
    congr 1
    apply propext
    exact or_congr Iff.rfl (Nat.sub_lt_iff_lt_add' hinit)
  unfold initializedRisk
  rw [← Tree.probability_eq_of_law_eq rt _ hlaw]
  exact hraw
end Qatlib.Papers.QAOAScaling23.CausalSearch
