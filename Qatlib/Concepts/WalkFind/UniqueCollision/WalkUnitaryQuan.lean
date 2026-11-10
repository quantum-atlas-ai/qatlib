/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.WalkUnitaryStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.BlockUnitary
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
set_option warningAsError false
open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.WalkFind.UniqueCollision

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

private theorem d2_real (ε : ℝ) (a b : Bool) : (jwD2 ε a b).im = 0 := by
  unfold jwD2
  split_ifs <;> simp

theorem jwStep1_real (k N r : ℕ) (i j : Fin (2 * k + 1)) : (jwStep1 k N r i j).im = 0 := by
  unfold jwStep1
  dsimp only [Matrix.of_apply]
  split_ifs <;> simp [d2_real]

theorem jwStep2_real (k r : ℕ) (i j : Fin (2 * k + 1)) : (jwStep2 k r i j).im = 0 := by
  unfold jwStep2
  dsimp only [Matrix.of_apply]
  split_ifs <;> simp [d2_real]

theorem jwWalk_real (k N r : ℕ) (i j : Fin (2 * k + 1)) : (jwWalk k N r i j).im = 0 := by
  simp [jwWalk, Matrix.mul_apply, Complex.im_sum, Complex.mul_im,
    jwStep1_real, jwStep2_real]

theorem jwStep2_unrestricted_gram :
    (star (jwStep2 2 0) * jwStep2 2 0) (4 : Fin 5) 4 = 9 := by
  norm_num [Matrix.mul_apply, Matrix.star_apply, jwStep2, jwPsiCoord, jwPhiCoord,
    jwD2, Fin.sum_univ_succ, map_ofNat]

theorem not_walkUnitary : ¬ (∀ (k N r : ℕ),
    star (jwStep1 k N r) * jwStep1 k N r = 1 ∧
    star (jwStep2 k r) * jwStep2 k r = 1 ∧
    star (jwWalk k N r) * jwWalk k N r = 1 ∧
    (∀ i j, (jwWalk k N r i j).im = 0)) := by
  intro h
  have he := (h 2 0 0).2.1
  have hentry := congrFun (congrFun he (4 : Fin 5)) 4
  rw [jwStep2_unrestricted_gram] at hentry
  norm_num [Matrix.one_apply] at hentry

theorem walkUnitary_zero_collision (N r : ℕ) :
    star (jwStep1 0 N r) * jwStep1 0 N r = 1 ∧
    star (jwStep2 0 r) * jwStep2 0 r = 1 ∧
    star (jwWalk 0 N r) * jwWalk 0 N r = 1 := by
  have h1 : jwStep1 0 N r = 1 := by
    ext i j
    have hi : i = 0 := by apply Fin.ext; omega
    have hj : j = 0 := by apply Fin.ext; omega
    subst i
    subst j
    simp [jwStep1, jwPsiCoord, jwPhiCoord, jwD2]
  have h2 : jwStep2 0 r = 1 := by
    ext i j
    have hi : i = 0 := by apply Fin.ext; omega
    have hj : j = 0 := by apply Fin.ext; omega
    subst i
    subst j
    simp [jwStep2, jwPsiCoord, jwPhiCoord, jwD2]
  simp [jwWalk, h1, h2]

theorem walkUnitary : WalkUnitary := by
  intro k N r h1 h2
  have hu1 := jwStep1_unitary k N r h1
  have hu2 := jwStep2_unitary k r h2
  refine ⟨hu1, hu2, ?_, jwWalk_real k N r⟩
  simp only [jwWalk, star_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (jwStep2 k r)), hu2, Matrix.one_mul, hu1]

end Qatlib.Concepts.WalkFind.UniqueCollision
