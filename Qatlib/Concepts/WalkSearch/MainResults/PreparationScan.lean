/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationSoundness
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationLedger
import Qatlib.Concepts.WalkSearch.Primitives.VertexSamplingQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n k : ℕ}

structure PreparationRun (n : ℕ) where
  triangle : Option (Fin n×Fin n×Fin n)
  queries : ℕ

def preparationScan (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed) :
    List (Fin n)→PreparationRun n
  | []=>⟨none,0⟩
  | v::vs=>
    let marked:=neighborhoodMarked G v
    let q:=n+operationalSgsFindCost sgs marked 2 (n*n) (stape v)
    match operationalSgsFind sgs marked 2 (n*n) (stape v) with
    | some (w,w')=>⟨some (v,w,w'),q⟩
    | none=>
      let r:=preparationScan G sgs stape vs
      ⟨r.triangle,q+r.queries⟩

def preparationCallsGood (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) : Prop :=
  ∀ v∈vs,(∃ p,neighborhoodMarked G v p=true)→ operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v)≠none

theorem preparationScan_cost (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (hn : 0<n) :
    (preparationScan G sgs stape vs).queries≤vs.length*(n+neighborhoodFee n sgs) := by
  induction vs with
  | nil => simp [preparationScan]
  | cons v vs ih =>
    rw [preparationScan]
    have hf:=neighborhoodSearch_charge G sgs v (stape v) hn
    cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
    | some p => rcases p with ⟨w,w'⟩;(try dsimp only);rw [List.length_cons];nlinarith
    | none => (try dsimp only);rw [List.length_cons];nlinarith

theorem preparationScan_sound (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) :
    ∀ a b cc,(preparationScan G sgs stape vs).triangle=some (a,b,cc)→
      tri3 G.edges a b cc ∧ (a,b)∈G.edges ∧ (a,cc)∈G.edges ∧ (b,cc)∈G.edges := by
  induction vs with
  | nil => simp [preparationScan]
  | cons v vs ih =>
    rw [preparationScan]
    cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
    | none => exact ih
    | some p =>
      rcases p with ⟨w,w'⟩
      intro a b cc hout
      have hp:=Prod.mk.inj (Option.some.inj hout)
      have hp2:=Prod.mk.inj hp.2
      rw [← hp.1,← hp2.1,← hp2.2]
      exact neighborhoodSearch_sound G sgs v (stape v) w w' hrun

theorem preparationScan_none_empty_marked (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (hgood : preparationCallsGood G sgs stape vs)
    (hnone : (preparationScan G sgs stape vs).triangle=none) :
    ∀ v∈vs,∀ p,neighborhoodMarked G v p=false := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [preparationScan] at hnone
    cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
    | some p => rw [hrun] at hnone;rcases p with ⟨w,w'⟩;cases hnone
    | none =>
      rw [hrun] at hnone
      intro x hx p
      rcases List.mem_cons.mp hx with rfl | hx
      · apply Bool.eq_false_iff.mpr
        intro hm
        exact hgood x List.mem_cons_self ⟨p,hm⟩ hrun
      · exact ih (fun y hy=>hgood y (List.mem_cons_of_mem v hy)) hnone x hx p

theorem sampledSurvivors_symmetric (G : UGraph n) (s : Fin k→Fin n) : pairSetSymmetric (sampledSurvivors G s) := by
  intro a b h
  rw [mem_sampledSurvivors_iff] at h ⊢
  simpa only [Finset.inter_comm] using h

theorem preparationScan_survivors_contain_graph (G : UGraph n) (sgs : SGSExecution) (stape : Fin n→sgs.seed)
    (s : Fin k→Fin n)
    (hgood : preparationCallsGood G sgs stape (Finset.univ.image s).toList)
    (hnone : (preparationScan G sgs stape (Finset.univ.image s).toList).triangle=none) :
    G.edges⊆sampledSurvivors G s := by
  rintro ⟨a,b⟩ hab
  rw [mem_sampledSurvivors_iff]
  intro i hi
  have hn:=preparationScan_none_empty_marked G sgs stape _ hgood hnone (s i)
    (Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) (a,b)
  have hm : neighborhoodMarked G (s i) (a,b)=true := by
    apply decide_eq_true
    have ha:=(Finset.mem_inter.mp hi).1
    have hb:=(Finset.mem_inter.mp hi).2
    exact ⟨(mem_graph_nbr_iff G (s i) a).mpr (G.symm a (s i) ((mem_graph_nbr_iff G a (s i)).mp ha)),
      (mem_graph_nbr_iff G (s i) b).mpr (G.symm b (s i) ((mem_graph_nbr_iff G b (s i)).mp hb)),hab⟩
  rw [hn] at hm
  cases hm
end Qatlib.Concepts.WalkSearch.MainResults
