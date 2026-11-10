/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.LeafReify
import Qatlib.Papers.QAOAScaling23.BiasedProcess.WeightedVisits
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion

def completion {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (target : PMF (Fin (r+1))) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Fin K×Fin (r+1)) :=
  .sample K p (fun a=> match output a with
    | some j=>.pure (a,j)
    | none=>.sample (r+1) target (fun j=>.pure (a,j)))

def row {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1))) : Row r where
  outcomes := Fintype.card (Tree.Leaves (completion p output target))
  law := Tree.indexedLeafLaw (completion p output target)
  next a := (Tree.indexedLeafValue (completion p output target) a).2
  charge a := fee (Tree.indexedLeafValue (completion p output target) a).1
  bad a := (output (Tree.indexedLeafValue (completion p output target) a).1).isNone

theorem completion_fst {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (target : PMF (Fin (r+1))) : (completion p output target).law.map Prod.fst=p := by
  rw [completion,Tree.law,PMF.map_bind]
  have h (a : Fin K) : ((match output a with
      | some j => Tree.pure (a,j)
      | none => Tree.sample (r+1) target (fun j=>Tree.pure (a,j))).law).map Prod.fst=PMF.pure a := by
    cases output a <;> simp [Tree.law,PMF.map_bind,PMF.pure_map,PMF.bind_const]
  simp_rw [h]
  exact PMF.bind_pure p

theorem masses_sum {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1))) :
    (∑a,if (output a).isSome then p a else 0)+(∑a,if (output a).isNone then p a else 0)=1 := by
  rw [← Finset.sum_add_distrib]
  have h (a : Fin K) : (if (output a).isSome then p a else 0)+(if (output a).isNone then p a else 0)=p a := by
    cases output a <;> simp
  simp_rw [h]
  simpa only [tsum_fintype] using p.tsum_coe

theorem completion_snd_point {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (target : PMF (Fin (r+1))) (j : Fin (r+1)) :
    ((completion p output target).law.map Prod.snd) j=
      (∑a,if output a=some j then p a else 0)+(∑a,if (output a).isNone then p a else 0)*target j := by
  rw [completion,Tree.law,PMF.map_bind,PMF.bind_apply,tsum_fintype,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases h : output a with
  | none => simp [Tree.law,PMF.map_bind,PMF.pure_map,PMF.bind_pure]
  | some k =>
    by_cases hk : k=j
    · subst k; simp [Tree.law,PMF.pure_map]
    · simp [Tree.law,PMF.pure_map,PMF.pure_apply,hk,Ne.symm hk]

theorem completion_snd {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (target : PMF (Fin (r+1)))
    (hlocal : ∀j,(∑a,if output a=some j then p a else 0)=
      (∑a,if (output a).isSome then p a else 0)*target j) :
    (completion p output target).law.map Prod.snd=target := by
  ext j
  rw [completion_snd_point,hlocal,← add_mul,masses_sum,one_mul]

theorem finite_real_marginal {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (p : PMF A) (q : PMF B)
    (f : A→B) (h : p.map f=q) (b : B) :
    (∑a,if f a=b then (p a).toReal else 0)=(q b).toReal := by
  have hp : (p.map f) b=∑a,if f a=b then p a else 0 := by
    simp only [PMF.map_apply,tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a=b
    · simp [ha]
    · simp [ha,Ne.symm ha]
  rw [h] at hp
  rw [hp,ENNReal.toReal_sum (fun a _=>by split_ifs <;> simp [PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem finite_mean_marginal {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (p : PMF A) (q : PMF B)
    (f : A→B) (h : p.map f=q) (g : B→ℝ) :
    (∑a,(p a).toReal*g (f a))=∑b,(q b).toReal*g b := by
  have he (a : A) : (p a).toReal*g (f a)=∑b, (if f a=b then (p a).toReal else 0)*g b := by
    simp [eq_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul,finite_real_marginal p q f h b]

theorem row_next_marginal {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1)))
    (hlocal : ∀j,(∑a,if output a=some j then p a else 0)=
      (∑a,if (output a).isSome then p a else 0)*target j) :
    (row p output fee target).law.map (row p output fee target).next=target := by
  change (Tree.indexedLeafLaw (completion p output target)).map
    (Prod.snd ∘Tree.indexedLeafValue (completion p output target))=target
  rw [← PMF.map_comp,Tree.indexedLeafLaw_value,completion_snd p output target hlocal]

theorem row_next_real {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1)))
    (hlocal : ∀j,(∑a,if output a=some j then p a else 0)=
      (∑a,if (output a).isSome then p a else 0)*target j) (j : Fin (r+1)) :
    (∑a,if (row p output fee target).next a=j then ((row p output fee target).law a).toReal else 0)=
      (target j).toReal :=
  finite_real_marginal _ _ _ (row_next_marginal p output fee target hlocal) j

theorem row_original_marginal {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1))) :
    (row p output fee target).law.map
      (fun a=>(Tree.indexedLeafValue (completion p output target) a).1)=p := by
  change (Tree.indexedLeafLaw (completion p output target)).map
    (Prod.fst ∘Tree.indexedLeafValue (completion p output target))=p
  rw [← PMF.map_comp,Tree.indexedLeafLaw_value,completion_fst]

theorem row_charge_mean {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1))) :
    (∑a,((row p output fee target).law a).toReal*((row p output fee target).charge a:ℝ))=
      ∑a,(p a).toReal*(fee a:ℝ) :=
  finite_mean_marginal _ _ _ (row_original_marginal p output fee target) (fun a=>(fee a:ℝ))

theorem row_bad_mean {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1))) :
    (∑a,((row p output fee target).law a).toReal*(if (row p output fee target).bad a then 1 else 0))=
      ∑a,(p a).toReal*(if (output a).isNone then 1 else 0) :=
  finite_mean_marginal _ _ _ (row_original_marginal p output fee target)
    (fun a=>if (output a).isNone then 1 else 0)

theorem leafValue_all {A : Type} (t : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree A)
    (P : A→Prop) (h : t.All P) (l : Tree.Leaves t) : P (Tree.leafValue t l) := by
  induction t with
  | pure a => exact h
  | sample m p c ih => exact ih l.1 (h l.1) l.2

theorem row_good_output {r K : ℕ} (p : PMF (Fin K)) (output : Fin K→Option (Fin (r+1)))
    (fee : Fin K→ℕ) (target : PMF (Fin (r+1)))
    (a : Fin (row p output fee target).outcomes) (hgood : (row p output fee target).bad a=false) :
    output (Tree.indexedLeafValue (completion p output target) a).1=some ((row p output fee target).next a) := by
  have ht : (completion p output target).All (fun z=>output z.1=some z.2 ∨output z.1=none) := by
    change ∀a, _
    intro a
    cases ho : output a with
    | none => simp [Tree.All,ho]
    | some j => simp [Tree.All,ho]
  have hv :=
      leafValue_all _ _ ht ((Fintype.equivFin (Tree.Leaves (completion p output target))).symm a)
  change output (Tree.indexedLeafValue (completion p output target) a).1=
      some (Tree.indexedLeafValue (completion p output target) a).2 ∨
    output (Tree.indexedLeafValue (completion p output target) a).1=none at hv
  rcases hv with hv|hv
  · exact hv
  · change (output (Tree.indexedLeafValue (completion p output target) a).1).isNone=false at hgood
    rw [hv] at hgood
    contradiction

end Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion
