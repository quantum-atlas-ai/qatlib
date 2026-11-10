/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.GroupCommutator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.CStarRing

section

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.CSD.SolovayKitaev

variable {E : Type*}

theorem norm_mul_sub_mul_le' [NormedRing E] (A B A' B' : E) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have key : A * B - A' * B' = (A - A') * B + A' * (B - B') := by noncomm_ring
  rw [key]
  exact le_trans (norm_add_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

section CStar

variable [NormedRing E] [StarRing E] [CStarRing E]

omit [StarRing E] [CStarRing E] in

theorem norm_mul_sub_mul_comm_sub_le {V W V' W' : E} {a δ : ℝ}
    (haW : ‖W - 1‖ ≤ a) (haV' : ‖V' - 1‖ ≤ a) (haV : ‖V - 1‖ ≤ a) (haW' : ‖W' - 1‖ ≤ a)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖(V * W - W * V) - (V' * W' - W' * V')‖ ≤ 4 * a * δ := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV
  have hid : (V * W - W * V) - (V' * W' - W' * V')
      = ((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1)) := by noncomm_ring
  have h1 : ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le' (V - 1) (W - 1) (V' - 1) (W' - 1)) ?_
    have e1 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    have e2 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    rw [e1, e2]
    have := mul_le_mul hδV haW (norm_nonneg _) hδ0
    have := mul_le_mul haV' hδW (norm_nonneg _) ha0
    nlinarith [mul_le_mul hδV haW (norm_nonneg _) hδ0,
      mul_le_mul haV' hδW (norm_nonneg _) ha0]
  have h2 : ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le' (W - 1) (V - 1) (W' - 1) (V' - 1)) ?_
    have e1 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    have e2 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    rw [e1, e2]
    nlinarith [mul_le_mul hδW haV (norm_nonneg _) hδ0,
      mul_le_mul haW' hδV (norm_nonneg _) ha0]
  rw [hid]
  calc ‖((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1))‖
      ≤ ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖
        + ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * a * δ + 2 * a * δ := add_le_add h1 h2
    _ = 4 * a * δ := by ring

theorem norm_groupCommutator_sub_le {V W V' W' : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {a δ : ℝ}
    (haV : ‖V - 1‖ ≤ a) (haW : ‖W - 1‖ ≤ a) (haV' : ‖V' - 1‖ ≤ a) (haW' : ‖W' - 1‖ ≤ a)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ ≤ 4 * a * δ * (1 + a) := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV

  have hKQ := CStarRing.groupCommutator_sub_one_eq hV hW
  have hKQ' := CStarRing.groupCommutator_sub_one_eq hV' hW'
  have hsplit : V * W * star V * star W - V' * W' * star V' * star W'
      = ((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)
        + (V' * W' - W' * V') * (star V * star W - star V' * star W') := by
    have h1 : V * W * star V * star W = 1 + (V * W - W * V) * (star V * star W) := by
      rw [← hKQ]; abel
    have h2 : V' * W' * star V' * star W' = 1 + (V' * W' - W' * V') * (star V' * star W') := by
      rw [← hKQ']; abel
    rw [h1, h2]
    noncomm_ring

  have hQu : (star V * star W) ∈ unitary E :=
    mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW)
  have hP : ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)‖ ≤ 4 * a * δ := by
    rw [CStarRing.norm_mul_mem_unitary _ hQu]
    exact norm_mul_sub_mul_comm_sub_le haW haV' haV haW' hδV hδW

  have hP' : ‖V' * W' - W' * V'‖ ≤ 2 * a * a := by
    refine le_trans (norm_mul_sub_mul_comm_le V' W') ?_
    nlinarith [mul_le_mul haV' haW' (norm_nonneg _) ha0]
  have hQ : ‖star V * star W - star V' * star W'‖ ≤ 2 * δ := by
    refine le_trans (CStarRing.norm_mul_sub_mul_le (Unitary.star_mem hW)
      (Unitary.star_mem hV')) ?_
    have e1 : ‖star V - star V'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδV
    have e2 : ‖star W - star W'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδW
    linarith
  calc ‖V * W * star V * star W - V' * W' * star V' * star W'‖
      ≤ ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)‖
        + ‖(V' * W' - W' * V') * (star V * star W - star V' * star W')‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ 4 * a * δ + (2 * a * a) * (2 * δ) := by
        refine add_le_add hP ?_
        refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul hP' hQ (norm_nonneg _) (by positivity)
    _ = 4 * a * δ * (1 + a) := by ring

theorem norm_groupCommutator_sub_le_sqrt {V W V' W' : E} (hV : V ∈ unitary E) (hW : W ∈ unitary E)
    (hV' : V' ∈ unitary E) (hW' : W' ∈ unitary E) {ε δ : ℝ}
    (haV : ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε) (haW : ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (haV' : ‖V' - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (haW' : ‖W' - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖
      ≤ 4 * (Real.sqrt 2 * Real.sqrt ε) * δ * (1 + Real.sqrt 2 * Real.sqrt ε) :=
  norm_groupCommutator_sub_le hV hW hV' hW' haV haW haV' haW' hδV hδW

end CStar

theorem skError_le_rpow {C : ℝ} (hC : 0 < C) {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hrec : ∀ n, ε (n + 1) ≤ C * ε n ^ ((3 : ℝ) / 2)) (n : ℕ) :
    C ^ 2 * ε n ≤ (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n := by
  have hC2 : ((C ^ 2 : ℝ)) ^ ((3 : ℝ) / 2) = C ^ 3 := by
    rw [show (C ^ 2 : ℝ) = C ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast C 2).symm,
      ← Real.rpow_mul hC.le,
      show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  have hzero : (0 : ℝ) ≤ C ^ 2 * ε 0 := mul_nonneg (sq_nonneg C) (hε 0)
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : (0 : ℝ) ≤ C ^ 2 * ε n := mul_nonneg (sq_nonneg C) (hε n)
      set X := ε n ^ ((3 : ℝ) / 2) with hX
      have h1 : C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := by
        calc C ^ 2 * ε (n + 1) ≤ C ^ 2 * (C * X) :=
              mul_le_mul_of_nonneg_left (hrec n) (sq_nonneg C)
          _ = C ^ 3 * X := by ring
      have h2 : (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) = C ^ 3 * X := by
        rw [Real.mul_rpow (sq_nonneg C) (hε n), hC2, hX]
      calc C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := h1
        _ = (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) := h2.symm
        _ ≤ ((C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hbase ih (by norm_num)
        _ = (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ (n + 1) := by
            rw [← Real.rpow_mul hzero]
            congr 1

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.CSD.SolovayKitaev

end
