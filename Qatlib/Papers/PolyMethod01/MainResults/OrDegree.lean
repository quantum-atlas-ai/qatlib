/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrExactDegreeSubgoalBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open scoped Classical BigOperators

def orRepresentingPoly (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  1 - ∏ i : Fin n, (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))

theorem orRepresentingPoly_represents (n : ℕ) (g : Fin n → Bool) :
    boolEval (orRepresentingPoly n) g = if orValue g then (1 : ℝ) else 0 := by
  classical
  have hfac : ∀ i : Fin n,
      (1 - (if g i then (1 : ℝ) else 0)) = if g i then (0 : ℝ) else 1 := by
    intro i
    by_cases hi : g i <;> simp [hi]
  have hprod : (∏ i : Fin n, (if g i then (0 : ℝ) else 1))
      = if (∃ i, g i = true) then (0 : ℝ) else 1 := by
    by_cases h : ∃ i, g i = true
    · rw [if_pos h]
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    · rw [if_neg h]
      refine Finset.prod_eq_one fun i _ => ?_
      have hni : ¬ (g i = true) := fun hi => h ⟨i, hi⟩
      simp [hni]
  rw [boolEval, orRepresentingPoly]
  simp only [map_sub, map_one, map_prod, MvPolynomial.eval_X, hfac, hprod]
  unfold orValue
  by_cases h : ∃ i, g i = true <;> simp [h]

theorem orRepresentingPoly_totalDegree_le (n : ℕ) :
    (orRepresentingPoly n).totalDegree ≤ n := by
  classical
  have hprod : (∏ i : Fin n, (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).totalDegree
      ≤ ∑ i : Fin n, (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree :=
    MvPolynomial.totalDegree_finsetProd _ _
  have hsingle : ∀ i : Fin n,
      (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 := by
    intro i
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
    simp
  have hsum : ∑ i : Fin n, (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ n := by
    calc ∑ i : Fin n, (1 - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree
        ≤ ∑ _i : Fin n, (1 : ℕ) := Finset.sum_le_sum fun i _ => hsingle i
      _ = n := by simp
  unfold orRepresentingPoly
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_one]
  exact max_le (Nat.zero_le n) (hprod.trans hsum)

theorem or_representing_nonempty (n : ℕ) :
    {p : MvPolynomial (Fin n) ℝ | ∀ g, boolEval p g = if orValue g then (1 : ℝ) else 0}.Nonempty :=
  ⟨orRepresentingPoly n, orRepresentingPoly_represents n⟩

theorem or_exactDegree (n : ℕ) : exactDegree (@orValue n) = n := by
  classical
  refine Nat.le_antisymm ?_ ?_
  · have hmem : (orRepresentingPoly n).totalDegree
        ∈ (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
          {p | ∀ g, boolEval p g = if orValue g then (1 : ℝ) else 0} :=
      ⟨orRepresentingPoly n, orRepresentingPoly_represents n, rfl⟩
    exact (Nat.sInf_le hmem).trans (orRepresentingPoly_totalDegree_le n)
  · by_cases hn : n = 0
    · subst hn
      exact Nat.zero_le _
    · have hpos : 0 < Fintype.card (Fin n) := by simpa using! Nat.pos_of_ne_zero hn
      have hlower : ∀ d ∈ (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
          {p | ∀ g, boolEval p g = if orValue g then (1 : ℝ) else 0}, n ≤ d := by
        intro d hd
        obtain ⟨p, hp, rfl⟩ := hd
        have hrep : ∀ g : Fin n → Bool,
            (MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0)) p
              = @ite ℝ (∃ i, g i = true) Fintype.decidableExistsFintype (1 : ℝ) 0 := by
          intro g
          have hg := hp g
          rw [boolEval] at hg
          rw [hg]
          by_cases h : ∃ i, g i = true <;> simp [orValue, h]
        have hrep' := orExactDegreeSubgoal (Fin n) p hpos hrep
        simpa using! hrep'
      exact le_csInf ⟨_, ⟨orRepresentingPoly n, orRepresentingPoly_represents n, rfl⟩⟩ hlower

theorem or_exactMinimum_eq (n : ℕ) : exactMinimum (@orValue n) = n :=
  or_exactMinimum n

end Qatlib.Papers.PolyMethod01.MainResults
