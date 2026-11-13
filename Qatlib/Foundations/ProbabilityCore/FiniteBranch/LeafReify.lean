/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree

/-!
# Reifying finite-tree laws by indexed leaves

This module gives each `Tree` a finite dependent type of syntactic leaves and a PMF on those
leaves. Evaluating a leaf recovers the original law, and reindexing the leaves by `Fin` yields a
single finite draw with the same output law, a useful representation for finite randomized
algorithms [AticiServedio2007].

## Main statements

* `leafLaw_value`: Evaluating the leaf distribution gives the tree law.
* `indexedLeafLaw_value`: The finite-index leaf representation has the original output law.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
variable {α : Type}

/-- The dependent type of syntactic leaves of a finite sampling tree, retaining the branch
choices along each path. -/
def Leaves : Tree α→Type
  | .pure _=>PUnit
  | .sample _ _ children=>Sigma (fun i=>Leaves (children i))

/-- A finite-type structure on the leaves of a finite sampling tree. -/
@[implicit_reducible]
noncomputable def leavesFintype (t : Tree α) : Fintype (Leaves t) := by
  induction t with
  | pure a => exact inferInstanceAs (Fintype PUnit)
  | sample m p children ih =>
    letI (i : Fin m) : Fintype (Leaves (children i)) := ih i
    exact inferInstanceAs (Fintype (Sigma (fun i=>Leaves (children i))))

attribute [instance] leavesFintype

/-- The output value stored at a specified syntactic leaf of a tree. -/
def leafValue : (t : Tree α)→Leaves t→α
  | .pure a,_=>a
  | .sample _ _ children,⟨i,l⟩=>leafValue (children i) l

/-- The PMF on syntactic leaves obtained by following the tree's sampling distributions. -/
def leafLaw : (t : Tree α)→PMF (Leaves t)
  | .pure _=>PMF.pure PUnit.unit
  | .sample _ p children=>p.bind (fun i=>(leafLaw (children i)).map (Sigma.mk i))

/-- Mapping the leaf distribution through leaf evaluation gives the original tree law. -/
theorem leafLaw_value (t : Tree α) : (leafLaw t).map (leafValue t)=t.law := by
  induction t with
  | pure a => simp [leafLaw,leafValue,law,PMF.pure_map]
  | sample m p children ih =>
    simp only [leafLaw,law,PMF.map_bind,PMF.map_comp]
    apply congrArg (PMF.bind p)
    funext i
    exact ih i

/-- The leaf distribution reindexed by `Fin (Fintype.card (Leaves t))`. -/
def indexedLeafLaw (t : Tree α) : PMF (Fin (Fintype.card (Leaves t))) :=
  (leafLaw t).map (Fintype.equivFin (Leaves t))

/-- The output value of the leaf represented by a finite index. -/
def indexedLeafValue (t : Tree α) (i : Fin (Fintype.card (Leaves t))) : α :=
  leafValue t ((Fintype.equivFin (Leaves t)).symm i)

/-- Mapping the indexed leaf law through indexed leaf evaluation recovers the original tree law. -/
theorem indexedLeafLaw_value (t : Tree α) :
    (indexedLeafLaw t).map (indexedLeafValue t)=t.law := by
  rw [indexedLeafLaw,PMF.map_comp]
  have he : indexedLeafValue t ∘Fintype.equivFin (Leaves t)=leafValue t := by
    funext l
    simp [indexedLeafValue]
  rw [he,leafLaw_value]
end Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
