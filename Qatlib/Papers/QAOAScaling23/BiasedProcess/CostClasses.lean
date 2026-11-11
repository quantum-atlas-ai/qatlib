/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
import Mathlib.Data.Finset.Sort

/-!
# Ordered cost classes and their probability laws

This module ranks the distinct values of a finite real cost function, identifying tied costs
with a single class. It transports a candidate law to `costClassLaw` and characterizes rank zero
as global optimality, providing the treatment of cost ties used for [ShaydulinEtAl2024].

## Main statements

* `costRank_lt_iff`: One candidate has smaller cost rank than another exactly when it has
  smaller cost.
* `costRank_zero_iff`: A candidate has rank zero exactly when its cost is no greater than every
  candidate's cost. This identifies the optimal class used in [ShaydulinEtAl2024].
* `costClassLaw_fiber`: The mass of a cost class is the sum of the candidate masses in its rank
  fiber.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess
open scoped Classical ENNReal
variable {I : Type} [Fintype I]

/-- The finite set of distinct values of the cost function. -/
def costLevels (cost : I → ℝ) : Finset ℝ := Finset.univ.image cost

/-- The increasing rank of a candidate's cost among the distinct cost levels. -/
def costRank (cost : I → ℝ) (i : I) : Fin (costLevels cost).card :=
  ((costLevels cost).orderIsoOfFin rfl).symm ⟨cost i,by simp [costLevels]⟩

/-- One candidate has smaller cost rank than another exactly when it has smaller cost. -/
theorem costRank_lt_iff (cost : I → ℝ) (i j : I) :
    costRank cost i<costRank cost j ↔ cost i<cost j := by
  simp only [costRank,OrderIso.lt_iff_lt,Subtype.mk_lt_mk]

/-- Two candidates have the same cost rank exactly when their costs are equal. -/
theorem costRank_eq_iff (cost : I → ℝ) (i j : I) :
    costRank cost i=costRank cost j ↔ cost i=cost j := by
  simp only [costRank,EmbeddingLike.apply_eq_iff_eq,Subtype.mk.injEq]

/-- Every cost-class rank is realized by a candidate. -/
theorem costRank_surjective (cost : I → ℝ) : Function.Surjective (costRank cost) := by
  intro j
  have hm := ((costLevels cost).orderIsoOfFin rfl j).property
  obtain ⟨i,_,hi⟩ := Finset.mem_image.1 hm
  refine ⟨i, ?_⟩
  unfold costRank
  apply ((costLevels cost).orderIsoOfFin rfl).injective
  simp only [OrderIso.apply_symm_apply]
  exact Subtype.ext hi

/-- A candidate has rank zero exactly when its cost is no greater than every candidate's cost.
This identifies the optimal class used in [ShaydulinEtAl2024]. -/
theorem costRank_zero_iff (cost : I → ℝ) (i : I) :
    (costRank cost i).val=0 ↔ ∀ j,cost i≤cost j := by
  constructor
  · intro h j
    apply le_of_not_gt
    intro hc
    have hr := (costRank_lt_iff cost j i).2 hc
    change (costRank cost j).val<(costRank cost i).val at hr
    omega
  · intro h
    have hp : 0<(costLevels cost).card :=
      Finset.card_pos.2 ⟨cost i,by simp [costLevels]⟩
    obtain ⟨j,hj⟩ := costRank_surjective cost ⟨0,hp⟩
    have hr : ¬costRank cost j<costRank cost i := by
      rw [costRank_lt_iff]
      exact not_lt_of_ge (h j)
    rw [hj] at hr
    change ¬0<(costRank cost i).val at hr
    omega

/-- The probability law on cost ranks obtained by mapping the candidate distribution through
`costRank`. -/
def costClassLaw (cost : I → ℝ) (p : PMF I) : PMF (Fin (costLevels cost).card) :=
  p.map (costRank cost)

/-- The mass of a cost class is the sum of the candidate masses in its rank fiber. -/
theorem costClassLaw_fiber (cost : I → ℝ) (p : PMF I) (j : Fin (costLevels cost).card) :
    costClassLaw cost p j=∑ i, if costRank cost i=j then p i else 0 := by
  simp only [costClassLaw,PMF.map_apply,tsum_fintype]
  congr 1
  funext i
  by_cases h : costRank cost i=j
  · rw [if_pos h,if_pos h.symm]
  · rw [if_neg h,if_neg (Ne.symm h)]

/-- The real mass of a cost class is the sum of the real candidate masses in its rank fiber. -/
theorem costClassLaw_real_fiber (cost : I → ℝ) (p : PMF I) (j : Fin (costLevels cost).card) :
    (costClassLaw cost p j).toReal=∑ i, if costRank cost i=j then (p i).toReal else 0 := by
  rw [costClassLaw_fiber,ENNReal.toReal_sum (fun i _ => by
    split_ifs <;> simp [PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
end Qatlib.Papers.QAOAScaling23.BiasedProcess
