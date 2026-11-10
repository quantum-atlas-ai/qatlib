/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch
open scoped ENNReal Classical

inductive Tree (α : Type) where
  | pure : α → Tree α
  | sample (m : ℕ) (p : PMF (Fin m)) : (Fin m → Tree α) → Tree α

namespace Tree
variable {α β : Type}

def law : Tree α → PMF α
  | .pure a => PMF.pure a
  | .sample _ p children => p.bind (fun i => law (children i))

def mean : Tree α → (α → ℝ) → ℝ
  | .pure a, f => f a
  | .sample _ p children, f => ∑ i, (p i).toReal * mean (children i) f

def All (P : α → Prop) : Tree α → Prop
  | .pure a => P a
  | .sample _ _ children => ∀ i, All P (children i)

def map (f : α → β) : Tree α → Tree β
  | .pure a => .pure (f a)
  | .sample m p children => .sample m p (fun i => map f (children i))

theorem all_map (t : Tree α) (g : α → β) (P : β → Prop) :
    (t.map g).All P ↔ t.All (fun a => P (g a)) := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [map,All,ih]

theorem all_of_forall (t : Tree α) {P : α → Prop} (h : ∀ a, P a) : t.All P := by
  induction t with
  | pure a => exact h a
  | sample m p c ih => exact ih

theorem all_and (t : Tree α) (P Q : α → Prop) :
    t.All (fun a => P a∧Q a) ↔ t.All P∧t.All Q := by
  induction t with
  | pure a => rfl
  | sample m p c ih => simp only [All,ih,forall_and]

theorem all_mono (t : Tree α) {P Q : α → Prop} (h : t.All P)
    (hpq : ∀ a, P a → Q a) : t.All Q := by
  induction t with
  | pure a => exact hpq a h
  | sample m p c ih => exact fun i => ih i (h i)

theorem mean_congr (t : Tree α) {f g : α → ℝ} (h : t.All (fun a => f a=g a)) :
    t.mean f=t.mean g := by
  induction t with
  | pure a => exact h
  | sample m p c ih =>
    unfold mean
    apply Finset.sum_congr rfl
    intro i _
    rw [ih i (h i)]

theorem weights_sum {m : ℕ} (p : PMF (Fin m)) : ∑ i, (p i).toReal=1 := by
  rw [← ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top p i)]
  simpa only [tsum_fintype,ENNReal.toReal_one] using congrArg ENNReal.toReal p.tsum_coe

theorem law_map (t : Tree α) (g : α → β) : (t.map g).law=t.law.map g := by
  induction t with
  | pure a => simp only [map,law,PMF.pure_map]
  | sample m p children ih => simp only [map,law,ih,PMF.map_bind]

theorem mean_map (t : Tree α) (g : α → β) (f : β → ℝ) :
    (t.map g).mean f=t.mean (fun a => f (g a)) := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [map,mean,ih]

theorem mean_const (t : Tree α) (c : ℝ) : t.mean (fun _ => c)=c := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [mean,ih,← Finset.sum_mul,weights_sum,one_mul]

theorem mean_add (t : Tree α) (f g : α → ℝ) :
    t.mean (fun a => f a+g a)=t.mean f+t.mean g := by
  induction t with
  | pure a => rfl
  | sample m p children ih => simp only [mean,ih,mul_add,Finset.sum_add_distrib]

theorem mean_mul (t : Tree α) (c : ℝ) (f : α → ℝ) :
    t.mean (fun a => c*f a)=c*t.mean f := by
  induction t with
  | pure a => rfl
  | sample m p children ih =>
    simp only [mean,ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem mean_mono (t : Tree α) {f g : α → ℝ} (h : t.All (fun a => f a≤g a)) :
    t.mean f≤t.mean g := by
  induction t with
  | pure a => exact h
  | sample m p children ih =>
    exact Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (ih i (h i)) ENNReal.toReal_nonneg)

theorem mean_nonneg (t : Tree α) {f : α → ℝ} (h : t.All (fun a => 0≤f a)) : 0≤t.mean f := by
  have h' := mean_mono t h
  rwa [mean_const] at h'

def pmfMean (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a*f a

theorem pmfMean_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    pmfMean (p.bind q) f=pmfMean p (fun a => pmfMean (q a) f) := by
  simp only [pmfMean,PMF.bind_apply,← ENNReal.tsum_mul_right,← ENNReal.tsum_mul_left,mul_assoc]
  exact ENNReal.tsum_comm

theorem mean_law (t : Tree α) (f : α → ℝ) (hf : ∀ a, 0≤f a) :
    ENNReal.ofReal (t.mean f)=pmfMean t.law (fun a => ENNReal.ofReal (f a)) := by
  induction t with
  | pure a => simp [mean,law,pmfMean,PMF.pure_apply]
  | sample m p children ih =>
    rw [mean,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg
      (mean_nonneg _ (all_of_forall _ hf)))]
    simp only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ih,ENNReal.ofReal_toReal (PMF.apply_ne_top p _)]
    rw [law,pmfMean_bind,pmfMean,tsum_fintype]

def probability (t : Tree α) (P : α → Prop) : ℝ := t.mean (fun a => if P a then 1 else 0)

theorem probability_law (t : Tree α) (P : α → Prop) :
    ENNReal.ofReal (t.probability P)=pmfMean t.law (fun a => if P a then 1 else 0) := by
  have h :=
      mean_law t (fun a => if P a then 1 else 0) (fun a => by (try dsimp); split_ifs <;> norm_num)
  simpa only [probability,apply_ite ENNReal.ofReal,ENNReal.ofReal_one,ENNReal.ofReal_zero] using h
end Tree
end Qatlib.Foundations.ProbabilityCore.FiniteBranch
