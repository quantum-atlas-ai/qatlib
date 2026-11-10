/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

noncomputable section
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical BigOperators

theorem growing_running_mass_complement {C : Type} [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hl : GrowingVtLegal stages history) (j₀ : VtSpace C)
    (hs : GrowingVtSupported stages history j₀) (k : ℕ) (hk : k ≤ stages.length) :
    MeasureProb (vtState stages k (Ket j₀)) (runningSet C) =
      1-reachedStoppedMass stages history (Ket j₀) k := by
  have hn : Normalized (vtState stages k (Ket j₀)) :=
    normalized_applyGate (growing_prefix_unitary stages history hl k) (normalized_ket j₀)
  have hd : Disjoint (stoppedSet C) (runningSet C) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : stoppedSet C ∪ runningSet C = Finset.univ := by
    ext p
    simp only [Finset.mem_union, stoppedSet, runningSet, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    exact Classical.em _ |>.symm
  have he := measureProb_union (vtState stages k (Ket j₀)) hd
  rw [hu, measureProb_univ hn] at he
  rw [growing_supported_stopping_mass stages history j₀ hs k hk]
  exact eq_sub_of_add_eq (by simpa only [stoppedMass, add_comm] using he.symm)

theorem finite_stop_tail_telescopes (f : ℕ → ℝ) (m i : ℕ) (hi : i ≤ m) :
    (∑ j ∈ Finset.range m, if i ≤ j then f (j+1)-f j else 0) = f m-f i := by
  induction m generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    simp
  | succ m ih =>
    by_cases him : i ≤ m
    · rw [Finset.sum_range_succ, ih i him, if_pos him]
      ring
    · have hi' : i = m+1 := by omega
      subst i
      rw [sub_self]
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (by have := Finset.mem_range.mp hj; omega)

theorem dyadic_geometric_square_bound (n : ℕ) :
    (∑ i ∈ Finset.range n, ((2 : ℝ)^i)^2) ≤ ((2 : ℝ)^n)^2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ (2 : ℝ) n, mul_pow]
    norm_num only [sq] at *
    nlinarith [sq_nonneg ((2 : ℝ)^n)]

theorem stopping_tail_weighted_sum (p : ℕ → ℝ) (m : ℕ)
    (hp : ∀ j, j < m → 0 ≤ p j) :
    (∑ i ∈ Finset.range m, ((2 : ℝ)^i)^2 *
      (∑ j ∈ Finset.range m, if i ≤ j then p j else 0)) ≤
        ∑ j ∈ Finset.range m, p j*((2 : ℝ)^(j+1))^2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hpj := hp j (Finset.mem_range.mp hj)
  have he : (∑ i ∈ Finset.range m, ((2 : ℝ)^i)^2 * (if i ≤ j then p j else 0)) =
      p j*(∑ i ∈ Finset.range (j+1), ((2 : ℝ)^i)^2) := by
    calc
      _ = ∑ i ∈ Finset.range (j+1), ((2 : ℝ)^i)^2 * (if i ≤ j then p j else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by have := Finset.mem_range.mp hj; omega))
        intro i _ hi
        rw [if_neg (by
          have hnot : ¬ i < j+1 := fun h => hi (Finset.mem_range.mpr h)
          omega), mul_zero]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos (by have := Finset.mem_range.mp hi; omega)]
        ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (dyadic_geometric_square_bound (j+1)) hpj

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
