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
variable {I α : Type} [Fintype I]

def sampleF (p : PMF I) (child : I → Tree α) : Tree α :=
  .sample (Fintype.card I) (p.map (Fintype.equivFin I))
    (fun a => child ((Fintype.equivFin I).symm a))

theorem law_sampleF (p : PMF I) (child : I → Tree α) :
    (sampleF p child).law=p.bind (fun i => (child i).law) := by
  simp only [sampleF,law,PMF.bind_map,Function.comp_def,Equiv.symm_apply_apply]

theorem all_sampleF (p : PMF I) (child : I → Tree α) (P : α → Prop) :
    (sampleF p child).All P ↔ ∀ i,(child i).All P := by
  constructor
  · intro h i
    simpa only [sampleF,All,Equiv.symm_apply_apply] using h (Fintype.equivFin I i)
  · intro h a
    exact h ((Fintype.equivFin I).symm a)

theorem mean_sampleF (p : PMF I) (child : I → Tree α) (f : α → ℝ) :
    (sampleF p child).mean f=∑ i,(p i).toReal*(child i).mean f := by
  rw [sampleF,mean]
  rw [← (Fintype.equivFin I).sum_comp]
  simp [PMF.map_apply]
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
