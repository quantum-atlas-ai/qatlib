/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.EmpiricalL1Concentration
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1Accuracy
open scoped BigOperators Classical
open EmpiricalL1Concentration
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def law (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin n → X) :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw (fun _ => p)

private theorem indicator_mean (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (x : X) :
    p.expect (fun y => if y=x then (1 : ℝ) else 0) = p.prob x := by
  simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_ite]

private theorem indicator_variance (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (x : X) :
    p.variance (fun y => if y=x then (1 : ℝ) else 0) = p.prob x*(1-p.prob x) := by
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance, indicator_mean]
  have he (y : X) : p.prob y*((if y=x then (1 : ℝ) else 0)-p.prob x)^2 =
      (p.prob y*(if y=x then (1 : ℝ) else 0))*(1-2*p.prob x)+p.prob y*(p.prob x)^2 := by
    split_ifs <;> ring
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, he,
      Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [show (∑ y, p.prob y*(if y=x then (1 : ℝ) else 0)) = p.prob x from indicator_mean p x,
    p.sum_one]
  ring

private theorem coordinate_mse (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) (x : X) :
    (law p n).expect (fun w => (histogram w x-p.prob x)^2) =
      p.prob x*(1-p.prob x)/(n : ℝ) := by
  have h := p.expect_avg_sub_sq (L := n) (fun y => if y=x then (1 : ℝ) else 0) hn
  rw [indicator_mean, indicator_variance] at h
  exact h

theorem total_mse (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) :
    (law p n).expect (fun w => ∑ x, (histogram w x-p.prob x)^2) =
      (1-∑ x, (p.prob x)^2)/(n : ℝ) := by
  calc
    _ = ∑ x, (law p n).expect (fun w => (histogram w x-p.prob x)^2) := by
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ x, p.prob x*(1-p.prob x)/(n : ℝ) := by
      exact Finset.sum_congr rfl fun x _ => coordinate_mse p n hn x
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      simp_rw [show ∀ x, p.prob x*(1-p.prob x) = p.prob x-(p.prob x)^2 from fun x => by ring]
      rw [Finset.sum_sub_distrib, p.sum_one]

private theorem expect_sq_ge_sq_expect {Y : Type} [Fintype Y] [DecidableEq Y]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Y) (f : Y → ℝ) : (p.expect f)^2 ≤ p.expect (fun y => (f y)^2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun y => p.prob y*f y) (f := p.prob) (g := fun y => p.prob y*(f y)^2)
    (fun y _ => p.nonneg y) (fun y _ => mul_nonneg (p.nonneg y) (sq_nonneg _))
    (fun y _ => le_of_eq (by ring))
  simpa only [p.sum_one, one_mul,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] using h

theorem mean_sq_bound (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) :
    ((law p n).expect (deviation p.prob))^2 ≤
      ((Fintype.card X : ℝ)-1)/(n : ℝ) := by
  let C : ℝ := Fintype.card X
  have hpoint (w : Fin n → X) : (deviation p.prob w)^2 ≤
      C * ∑ x, (histogram w x-p.prob x)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => |histogram w x-p.prob x|) (fun _ => (1 : ℝ))
    simpa [deviation, C, mul_comm] using h
  have hE : (law p n).expect (fun w => (deviation p.prob w)^2) ≤
      C * (law p n).expect (fun w => ∑ x, (histogram w x-p.prob x)^2) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => by
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hpoint w) ((law p n).nonneg w)
  rw [total_mse p n hn] at hE
  have hmean := (expect_sq_ge_sq_expect (law p n) (deviation p.prob)).trans hE
  have hmass := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p.prob (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, p.sum_one, one_pow] at hmass
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmean' : ((law p n).expect (deviation p.prob))^2*(n : ℝ) ≤
      C*(1-∑ x, (p.prob x)^2) := by
    apply (le_div_iff₀ hnR).mp
    simpa only [mul_div_assoc] using hmean
  apply (le_div_iff₀ hnR).mpr
  dsimp [C] at hmean'
  nlinarith

theorem mean_bound (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) :
    (law p n).expect (deviation p.prob) ≤
      Real.sqrt (((Fintype.card X : ℝ)-1)/(n : ℝ)) := by
  have h := mean_sq_bound p n hn
  have harg := (sq_nonneg ((law p n).expect (deviation p.prob))).trans h
  have hs := Real.sq_sqrt harg
  have hn0 := Real.sqrt_nonneg (((Fintype.card X : ℝ)-1)/(n : ℝ))
  nlinarith

theorem accuracy_tail (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    p.probEvent (fun w : Fin n → X =>
      Real.sqrt (((Fintype.card X : ℝ)-1)/(n : ℝ))+u ≤ deviation p.prob w) ≤
      Real.exp (-u^2*(n : ℝ)/2) := by
  have ht := (EmpiricalL1Concentration.tail n hn (fun _ => p) p.prob u hu).1
  have hm := mean_bound p n hn
  apply le_trans ?_ ht
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he := (Finset.mem_filter.mp hw).2
    change (law p n).expect (deviation p.prob)+u ≤ deviation p.prob w
    linarith only [hm, he]
  · intro w _ _
    exact (law p n).nonneg w

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.EmpiricalL1Accuracy
