/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
open scoped Classical
variable {α : Type}

theorem mean_eq_of_law_eq (s t : Tree α) (h : s.law=t.law) (f : α → ℝ)
    (hf : ∀ a,0≤f a) : s.mean f=t.mean f := by
  have he : ENNReal.ofReal (s.mean f)=ENNReal.ofReal (t.mean f) := by
    rw [mean_law s f hf,mean_law t f hf,h]
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (mean_nonneg s (all_of_forall _ hf)),
    ENNReal.toReal_ofReal (mean_nonneg t (all_of_forall _ hf))] using ht

theorem probability_eq_of_law_eq (s t : Tree α) (h : s.law=t.law) (P : α → Prop) :
    s.probability P=t.probability P := by
  apply mean_eq_of_law_eq s t h
  intro a
  split_ifs <;> norm_num

theorem probability_le_one (t : Tree α) (P : α → Prop) : t.probability P≤1 := by
  calc
    t.probability P≤t.mean (fun _ => 1) := by
      apply mean_mono t
      apply all_of_forall
      intro a
      split_ifs <;> norm_num
    _=1 := mean_const t 1

theorem law_map_congr {β : Type} (t : Tree α) (f g : α → β)
    (h : t.All (fun a => f a=g a)) : t.law.map f=t.law.map g := by
  induction t with
  | pure a =>
    change f a=g a at h
    simp only [law,PMF.pure_map,h]
  | sample m p c ih =>
    simp only [law,PMF.map_bind]
    apply congrArg (PMF.bind p)
    funext i
    exact ih i (h i)

end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
