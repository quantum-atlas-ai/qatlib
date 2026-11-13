/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Composition

/-!
# Sampling from arbitrary finite types

The constructor `sampleF` packages a PMF draw on any finite type as a finite-branch tree. Its
distribution, mean, and branchwise predicate rules make the finite indexing representation
transparent to probability arguments for randomized algorithms [AticiServedio2007].

## Main statements

* `law_sampleF`: Sampling has the expected PMF bind law.
* `all_sampleF`: Branchwise assertions quantify over every draw outcome.
* `mean_sampleF`: The mean is the finite weighted sum of continuation means.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
open scoped Classical
variable {I α : Type} [Fintype I]

/-- A finite sampling tree drawing from a PMF on an arbitrary finite type, represented through a
finite index equivalence. -/
def sampleF (p : PMF I) (child : I → Tree α) : Tree α :=
  .sample (Fintype.card I) (p.map (Fintype.equivFin I))
    (fun a => child ((Fintype.equivFin I).symm a))

/-- The law of `sampleF` is the bind of the sampling PMF with the child-tree laws. -/
theorem law_sampleF (p : PMF I) (child : I → Tree α) :
    (sampleF p child).law=p.bind (fun i => (child i).law) := by
  simp only [sampleF,law,PMF.bind_map,Function.comp_def,Equiv.symm_apply_apply]

/-- A predicate holds on every branch of `sampleF` exactly when it holds on every branch of each
child. -/
theorem all_sampleF (p : PMF I) (child : I → Tree α) (P : α → Prop) :
    (sampleF p child).All P ↔ ∀ i,(child i).All P := by
  constructor
  · intro h i
    simpa only [sampleF,All,Equiv.symm_apply_apply] using h (Fintype.equivFin I i)
  · intro h a
    exact h ((Fintype.equivFin I).symm a)

/-- The mean of `sampleF` is the sum of each child's mean weighted by its draw probability. -/
theorem mean_sampleF (p : PMF I) (child : I → Tree α) (f : α → ℝ) :
    (sampleF p child).mean f=∑ i,(p i).toReal*(child i).mean f := by
  rw [sampleF,mean]
  rw [← (Fintype.equivFin I).sum_comp]
  simp [PMF.map_apply]
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
