/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffectiveDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.ClassShadows20.MainTheorem

open Qatlib
open Qatlib.Papers.ClassShadows20.MainTheorem

set_option linter.unusedSectionVars false

def generalSampler (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) : MemberSampler where
  size := m
  fairBits := b
  size_pos := hm
  size_le := hb

noncomputable def basisPackingFamily (d : ℕ) : PackingFamily d where
  size := d
  points := fun i => Qatlib.Foundations.PureStateMath.Ket i
  sep := Real.sqrt 2

theorem basis_distance_sq (d : ℕ) (i j : Fin d) (h : i ≠ j) :
    (‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ : ℝ) ^ 2 = 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [toEuclidean_fromVec_apply]
  have hcoord : ∀ k : Fin d,
      ‖(Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j) k‖ ^ 2 =
        ((if k = i then (1 : ℝ) else 0) + if k = j then (1 : ℝ) else 0) := by
    intro k
    by_cases hki : k = i
    · by_cases hkj : k = j
      · exact absurd (hki.symm.trans hkj) h
      · simp [Qatlib.Foundations.PureStateMath.Ket, hki, hkj, h, Complex.normSq, Complex.norm_real,
          Real.norm_eq_abs]
    · by_cases hkj : k = j
      · simp [Qatlib.Foundations.PureStateMath.Ket, hki, hkj, h, Ne.symm h, Complex.normSq,
          Complex.norm_real, Real.norm_eq_abs]
      · simp [Qatlib.Foundations.PureStateMath.Ket, hki, hkj, h, Ne.symm h, Complex.normSq,
          Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl (fun k _ => hcoord k)]
  have hone : (∑ k : Fin d, (if k = i then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp [Ne.symm h])]
    simp
  have htwo : (∑ k : Fin d, (if k = j then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp [Ne.symm h])]
    simp
  rw [Finset.sum_add_distrib, hone, htwo]
  norm_num

theorem basis_distance (d : ℕ) (i j : Fin d) (h : i ≠ j) :
    ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ = Real.sqrt 2 := by
  have hsq := basis_distance_sq d i j h
  have hnn : 0 ≤ ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ :=
    norm_nonneg _
  have hle : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖
      ≤ Real.sqrt 2 := by
    have hsq' : (‖toEuclidean_fromVec
        (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ : ℝ) ^ 2 ≤ 2 := by
      rw [hsq]
    exact (Real.le_sqrt (x := ‖toEuclidean_fromVec
      (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖) (y := 2) hnn (by norm_num)).2 hsq'
  have hge : Real.sqrt 2
      ≤ ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ := by
    have hsq' : (Real.sqrt 2 : ℝ) ^ 2 ≤ ‖toEuclidean_fromVec
        (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ ^ 2 := by
      rw [hsq]
      norm_num
    have h1 : Real.sqrt 2 ≤ Real.sqrt (‖toEuclidean_fromVec
        (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ ^ 2) :=
      (Real.le_sqrt (x := Real.sqrt 2)
        (y := ‖toEuclidean_fromVec
          (Qatlib.Foundations.PureStateMath.Ket i - Qatlib.Foundations.PureStateMath.Ket j)‖ ^ 2)
        (by positivity) (by positivity)).2 hsq'
    rw [Real.sqrt_sq hnn] at h1
    exact h1
  exact hle.antisymm hge

end Qatlib.Papers.ClassShadows20.MainTheorem
