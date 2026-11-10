/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorAux
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix

noncomputable def taylorPoly (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), z ^ j / (Nat.factorial j : ℂ)

noncomputable def taylorSrcPoly (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, z ^ j / (Nat.factorial (j + 1) : ℂ)

theorem complex_exp_eq_tsum (z : ℂ) :
    Complex.exp z = ∑' j : ℕ, z ^ j / (Nat.factorial j : ℂ) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

set_option maxHeartbeats 600000 in

theorem taylorPoly_defect (k : ℕ) (z : ℂ) (hk : 5 ≤ k) (hz1 : ‖z‖ ≤ 1) :
    ‖Complex.exp z - taylorPoly k z‖ ≤
      (7 / 6 : ℝ) * ‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
  classical
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hfac : ∀ i : ℕ, (Nat.factorial (k + 1) : ℕ) * (k + 2) ^ i ≤ Nat.factorial (k + 1 + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep : Nat.factorial (k + 1 + i + 1) = Nat.factorial (k + 1 + i) * (k + 1 + i + 1) := by
        rw [Nat.factorial_succ]
        ring
      have hle : (Nat.factorial (k + 1 + i) : ℕ) * (k + 2) ≤
          Nat.factorial (k + 1 + i) * (k + 1 + i + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      calc (Nat.factorial (k + 1) : ℕ) * (k + 2) ^ (i + 1)
          = (Nat.factorial (k + 1) : ℕ) * (k + 2) ^ i * (k + 2) := by ring
        _ ≤ Nat.factorial (k + 1 + i) * (k + 2) := Nat.mul_le_mul ih (Nat.le_refl _)
        _ ≤ Nat.factorial (k + 1 + i) * (k + 1 + i + 1) := hle
        _ = Nat.factorial (k + 1 + i + 1) := hstep.symm
  have hnormeq : ∀ j : ℕ, ‖z ^ j / ((Nat.factorial j : ℕ) : ℂ)‖ =
      ‖z‖ ^ j / ((Nat.factorial j : ℕ) : ℝ) := by
    intro j
    rw [norm_div, norm_pow]
    simp
  have hsumf : Summable (fun j : ℕ => z ^ j / ((Nat.factorial j : ℕ) : ℂ)) :=
    Summable.of_norm (by
      rw [show (fun j : ℕ => ‖z ^ j / ((Nat.factorial j : ℕ) : ℂ)‖) =
        (fun j : ℕ => ‖z‖ ^ j / ((Nat.factorial j : ℕ) : ℝ)) from funext hnormeq]
      exact Real.summable_pow_div_factorial ‖z‖)
  have hsplit : ∑ j ∈ Finset.range (k + 1), z ^ j / ((Nat.factorial j : ℕ) : ℂ) +
      ∑' i : ℕ, z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ) =
      ∑' j : ℕ, z ^ j / ((Nat.factorial j : ℕ) : ℂ) :=
    Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff (k + 1)).mpr hsumf)
  have hsub : Complex.exp z - taylorPoly k z =
      ∑' i : ℕ, z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ) := by
    rw [complex_exp_eq_tsum, taylorPoly, ← hsplit, add_sub_cancel_left]
  have hq0 : 0 ≤ ‖z‖ / ((k + 2 : ℕ) : ℝ) := div_nonneg hz0 (by positivity)
  have hk2 : (1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hq1 : ‖z‖ / ((k + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast (by omega) : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))]
    linarith
  have hk7 : (7 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hq : ‖z‖ / ((k + 2 : ℕ) : ℝ) ≤ (1 : ℝ) / 7 := by
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega) : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))
      (by norm_num : (0 : ℝ) < (7 : ℝ))]
    linarith
  have hnum : (1 : ℝ) / 7 + (6 : ℝ) / 7 = 1 := by norm_num
  have hterm : ∀ i : ℕ, ‖z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ)‖ ≤
      (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * (‖z‖ / ((k + 2 : ℕ) : ℝ)) ^ i := by
    intro i
    rw [hnormeq]
    have hfc : (Nat.factorial (k + 1) : ℕ) * (k + 2) ^ i ≤ Nat.factorial (i + (k + 1)) := by
      have h0 := hfac i
      rwa [show Nat.factorial (k + 1 + i) = Nat.factorial (i + (k + 1)) from by
        congr 1
        omega] at h0
    have hpow : ‖z‖ ^ (i + (k + 1)) = ‖z‖ ^ (k + 1) * ‖z‖ ^ i := by
      rw [pow_add]
      ring
    have hn : (0 : ℝ) ≤ ‖z‖ ^ (k + 1) * ‖z‖ ^ i := by positivity
    have hge : (((Nat.factorial (k + 1) : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) ^ i)) ≤
        ((Nat.factorial (i + (k + 1)) : ℕ) : ℝ) := by exact_mod_cast hfc
    have hrhs : (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) *
            (‖z‖ / ((k + 2 : ℕ) : ℝ)) ^ i =
        ‖z‖ ^ (k + 1) * ‖z‖ ^ i /
          (((Nat.factorial (k + 1) : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) ^ i)) := by
      rw [div_pow, div_mul_eq_mul_div, ← mul_div_assoc, div_div,
        mul_comm (((k + 2 : ℕ) : ℝ) ^ i) ((Nat.factorial (k + 1) : ℕ) : ℝ)]
    have hd1 : (0 : ℝ) < ((Nat.factorial (i + (k + 1)) : ℕ) : ℝ) :=
      by exact_mod_cast (Nat.factorial_pos (i + (k + 1)))
    have hd2 : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) *
        (((k + 2 : ℕ) : ℝ) ^ i) :=
      mul_pos (by exact_mod_cast (Nat.factorial_pos (k + 1)))
        (pow_pos (by exact_mod_cast (by omega) : (0 : ℝ) < ((k + 2 : ℕ) : ℝ)) i)
    rw [hpow, hrhs, div_le_div_iff₀ hd1 hd2]
    exact mul_le_mul_of_nonneg_left hge hn
  have hshiftsum : Summable (fun i : ℕ => z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ)) :=
    (summable_nat_add_iff (k + 1)).mpr hsumf
  have hnormsum : Summable (fun i : ℕ =>
      ‖z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ)‖) := hshiftsum.norm
  have hgeomsum : Summable (fun i : ℕ =>
      (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * (‖z‖ / ((k + 2 : ℕ) : ℝ)) ^ i) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hinv : (1 - ‖z‖ / ((k + 2 : ℕ) : ℝ))⁻¹ ≤ (7 : ℝ) / 6 := by
    have h1q : (0 : ℝ) < 1 - ‖z‖ / ((k + 2 : ℕ) : ℝ) := by linarith
    have key : (1 - ‖z‖ / ((k + 2 : ℕ) : ℝ))⁻¹ ≤ ((6 : ℝ) / 7)⁻¹ :=
      (inv_le_inv₀ h1q (by norm_num : (0 : ℝ) < (6 : ℝ) / 7)).mpr
        (by
          have hsum : (6 : ℝ) / 7 + ‖z‖ / ((k + 2 : ℕ) : ℝ) ≤ (6 : ℝ) / 7 + (1 : ℝ) / 7 :=
            add_le_add_right hq _
          linarith)
    rwa [inv_div] at key
  rw [hsub]
  calc ‖∑' i : ℕ, z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ)‖
      ≤ ∑' i : ℕ, ‖z ^ (i + (k + 1)) / ((Nat.factorial (i + (k + 1)) : ℕ) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' i : ℕ, (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) *
          (‖z‖ / ((k + 2 : ℕ) : ℝ)) ^ i := hnormsum.tsum_le_tsum hterm hgeomsum
    _ = (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) *
          ∑' i : ℕ, (‖z‖ / ((k + 2 : ℕ) : ℝ)) ^ i := tsum_mul_left
    _ = (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) *
          (1 - ‖z‖ / ((k + 2 : ℕ) : ℝ))⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) * ((7 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (7 / 6 : ℝ) * ‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by ring

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
