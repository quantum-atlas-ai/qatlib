/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QActiveLearn14.NativeReflect
public import Qatlib.Papers.QActiveLearn14.TailedBounds

@[expose] public section

/-!
# Conditioning a perturbed reflecting-agent output

[PaparoEtAl2014], Theorem 5, compares the terminal Euclidean states and then conditions on
obtaining a flag. The conditional comparison needs a success bound. A projected-amplitude
estimate supplies positivity for the perturbed state and yields a total-variation bound with
the ideal flagged amplitude as the denominator. The first-register marginal specializes this
estimate to the paper's coherent transition-pair input.
-/

namespace Qatlib.Papers.QActiveLearn14.ApproxBudget

open Qatlib.Foundations.MatrixGeometry.FlagProjection
open Qatlib.Papers.QActiveLearn14.TailedBounds

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The flag projection has norm at most one in the physical Euclidean norm. -/
private theorem flag_project_norm_le (S : Finset X) (v : EuclideanSpace ℂ X) :
    ‖project S v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [project_norm_sq, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun _ _ _ => sq_nonneg _

/-- The norm of a flag projection is the square root of the accepted Born mass. -/
private theorem flag_project_norm (S : Finset X) (v : EuclideanSpace ℂ X) :
    ‖project S v‖ = Real.sqrt (mass S v) := by
  rw [← project_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

omit [DecidableEq X] in
/-- Computational-basis measurement of unit Euclidean vectors is Lipschitz from Euclidean
distance to the total variation of the Born laws. -/
private theorem basis_born_tv_le (a b : EuclideanSpace ℂ X) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    tvDist (fun i => ‖a.ofLp i‖ ^ 2) (fun i => ‖b.ofLp i‖ ^ 2) ≤ ‖a - b‖ := by
  have hterm (i : X) : |‖a.ofLp i‖ ^ 2 - ‖b.ofLp i‖ ^ 2| ≤
      ‖(a - b).ofLp i‖ * (‖a.ofLp i‖ + ‖b.ofLp i‖) := by
    have hnonneg := add_nonneg (norm_nonneg (a.ofLp i)) (norm_nonneg (b.ofLp i))
    rw [sq_sub_sq, abs_mul, abs_of_nonneg hnonneg, mul_comm (‖a.ofLp i‖ + ‖b.ofLp i‖)]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le (a.ofLp i) (b.ofLp i)) hnonneg
  have hcs (z : EuclideanSpace ℂ X) (hz : ‖z‖ = 1) :
      ∑ i, ‖(a - b).ofLp i‖ * ‖z.ofLp i‖ ≤ ‖a - b‖ := by
    calc
      _ ≤ Real.sqrt (∑ i, ‖(a - b).ofLp i‖ ^ 2) * Real.sqrt (∑ i, ‖z.ofLp i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by
        rw [← EuclideanSpace.norm_sq_eq (a - b), ← EuclideanSpace.norm_sq_eq z, hz]
        simp [Real.sqrt_sq (norm_nonneg (a - b))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp_rw [mul_add, Finset.sum_add_distrib] at hsum
  unfold tvDist
  linarith [hcs a ha, hcs b hb]

/-- The normalized tails of nearby states give nearby conditional Born laws. A uniform
Euclidean error smaller than the ideal flagged amplitude guarantees that the perturbed
acceptance probability is positive. -/
theorem conditional_born_tv_le (S : Finset X) (ideal actual : EuclideanSpace ℂ X)
    (ε : ℝ) (hclose : ‖actual - ideal‖ ≤ ε) (hgap : ε < Real.sqrt (mass S ideal)) :
    0 < mass S actual ∧
    tvDist (conditionalBorn S actual) (conditionalBorn S ideal) ≤
      2 * ε / Real.sqrt (mass S ideal) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hclose
  have hproject : ‖project S actual - project S ideal‖ ≤ ε := by
    have hsub : project S (actual - ideal) = project S actual - project S ideal := by
      rw [sub_eq_add_neg, project_add, ← neg_one_smul ℂ ideal, project_smul, neg_one_smul, ← sub_eq_add_neg]
    rw [← hsub]
    exact (flag_project_norm_le S _).trans hclose
  have hnorm : |Real.sqrt (mass S actual) - Real.sqrt (mass S ideal)| ≤ ε := by
    simpa only [flag_project_norm] using
      (abs_norm_sub_norm_le (project S actual) (project S ideal)).trans hproject
  have ha : 0 < Real.sqrt (mass S ideal) := hε.trans_lt hgap
  have hb : 0 < Real.sqrt (mass S actual) := by linarith [(abs_le.mp hnorm).1]
  have hi := Real.sqrt_pos.mp ha
  have hj := Real.sqrt_pos.mp hb
  refine ⟨hj, ?_⟩
  have ht (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) : ‖tail S v‖ = 1 := by
    have h := tail_norm_sq S v hp
    nlinarith [norm_nonneg (tail S v)]
  have hscale :
      (Real.sqrt (mass S ideal) : ℂ) • (tail S actual - tail S ideal) =
        (project S actual - project S ideal) +
          ((Real.sqrt (mass S ideal) - Real.sqrt (mass S actual) : ℝ) : ℂ) • tail S actual := by
    rw [project_source S actual hj, project_source S ideal hi, Complex.ofReal_sub]
    module
  have htail : ‖tail S actual - tail S ideal‖ ≤ 2 * ε / Real.sqrt (mass S ideal) := by
    apply (le_div_iff₀ ha).mpr
    rw [mul_comm, ← abs_of_pos ha, ← Real.norm_eq_abs, ← Complex.norm_real, ← norm_smul, hscale]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ht actual hj, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    linarith
  have hborn := basis_born_tv_le (tail S actual) (tail S ideal) (ht actual hj) (ht ideal hi)
  simp_rw [tail_born S actual hj, tail_born S ideal hi] at hborn
  exact hborn.trans htail

/-- Measuring just the first register after joint flag conditioning cannot increase the
total-variation error. For the ideal reflecting word on a coherent probability input, this
gives the tailed input law, which is the tailed stationary law in [PaparoEtAl2014], Equation (25). -/
theorem coherent_word_conditional_output (π : X → ℝ) (P : X → X → ℝ)
    (hπ : IsProbability π) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (hflag : 0 < flaggedMass π S) (n : ℕ)
    (actual : EuclideanSpace ℂ (X × X)) (ε : ℝ)
    (hclose : ‖actual - runFig (pairFlags S) (pairCoherent π P) n‖ ≤ ε)
    (hgap : ε < Real.sqrt (mass (pairFlags S) (runFig (pairFlags S) (pairCoherent π P) n))) :
    0 < mass (pairFlags S) actual ∧
    tvDist (fun i => ∑ j, conditionalBorn (pairFlags S) actual (i, j)) (tailed π S) ≤
      2 * ε / Real.sqrt (mass (pairFlags S) (runFig (pairFlags S) (pairCoherent π P) n)) := by
  let ideal := runFig (pairFlags S) (pairCoherent π P) n
  have h := conditional_born_tv_le (pairFlags S) ideal actual ε hclose hgap
  have hi : 0 < mass (pairFlags S) ideal :=
    Real.sqrt_pos.mp (((norm_nonneg _).trans hclose).trans_lt hgap)
  have htarget : (fun i => ∑ j, conditionalBorn (pairFlags S) ideal (i, j)) = tailed π S := by
    funext i
    exact Qatlib.Papers.QActiveLearn14.NativeReflect.ideal_output_tail
      π P hπ.1 hπ.2 hP hsP S hflag n hi i
  refine ⟨h.1, ?_⟩
  rw [← htarget]
  refine le_trans ?_ h.2
  unfold tvDist
  rw [Fintype.sum_prod_type]
  gcongr with i
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

end Qatlib.Papers.QActiveLearn14.ApproxBudget
