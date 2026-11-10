/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HidShiftQuad09.MainResults.Defs
import Qatlib.Papers.HidShiftQuad09.MainResults.FindCloseQuadratic
import Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.LinearQueryIdentification

open scoped BigOperators RealInnerProductSpace
open Qatlib.Papers.HidShiftQuad09.MainResults.Defs
open Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3

def classicalBasisQueryCount (n : ℕ) : ℝ :=
  1 + (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2

theorem classicalBasisQueryCount_ge (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ 2 / 4 ≤ classicalBasisQueryCount n := by
  unfold classicalBasisQueryCount
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem quadraticFormCount (n : ℕ) :
    Fintype.card (Fin (n * (n - 1) / 2) → ZMod 2) *
      Fintype.card (Fin n → ZMod 2) = 2 ^ (n * (n + 1) / 2) := by
  have hexp : n * (n - 1) / 2 + n = n * (n + 1) / 2 := by

    calc n * (n - 1) / 2 + n
        = n.choose 2 + n.choose 1 := by
          rw [Nat.choose_two_right, Nat.choose_one_right]
      _ = (n + 1).choose 2 := by
          have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := by
            simpa using (Nat.choose_succ_succ n 1)
          omega
      _ = n * (n + 1) / 2 := by
          rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Fintype.card_fin, ← pow_add, hexp]

theorem hiddenShift_fourier_ratio {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n)
    (hb : bent f) (hshift : HiddenShift f g s) (w : Cube n) :
    fourierCoeff g w / fourierCoeff f w = chi w s := by
  have hg : g = fun x => f (x + s) := funext hshift
  rw [hg, fourierCoeff_shift]
  have hne : fourierCoeff f w ≠ 0 := bent_fourierCoeff_ne_zero f hb w
  field_simp [hne]

theorem hiddenShift_recovery_peak {n : ℕ} (f g : Cube n → ZMod 2) (s : Cube n)
    (hb : bent f) (hshift : HiddenShift f g s) (x : Cube n) :
    (∑ w : Cube n, (fourierCoeff g w / fourierCoeff f w) * chi w x)
      = if x = s then (2 : ℝ) ^ n else 0 := by
  have hr : ∀ w : Cube n, fourierCoeff g w / fourierCoeff f w = chi w s :=
    fun w => hiddenShift_fourier_ratio f g s hb hshift w
  simp only [hr]
  have hmul : ∀ w : Cube n, chi w s * chi w x = chi w (s + x) := by
    intro w; rw [chi_add]
  simp only [hmul]
  exact chi_sum_eq_delta n s x

theorem source_mainResult_linearQueries (n : ℕ) (hn : 0 < n) :
    (∀ (f g : Cube n → ZMod 2) (s : Cube n), bent f → HiddenShift f g s →
        ∀ x : Cube n,
          (∑ w : Cube n, (fourierCoeff g w / fourierCoeff f w) * chi w x)
            = if x = s then (2 : ℝ) ^ n else 0) ∧
    ((n : ℝ) ^ 2 / 4 ≤ classicalBasisQueryCount n) ∧
    (Fintype.card (Fin (n * (n - 1) / 2) → ZMod 2) *
      Fintype.card (Fin n → ZMod 2) = 2 ^ (n * (n + 1) / 2)) := by
  refine ⟨?_, classicalBasisQueryCount_ge n hn, quadraticFormCount n⟩
  intro f g s hb hshift x
  exact hiddenShift_recovery_peak f g s hb hshift x

end Qatlib.Papers.HidShiftQuad09.MainResults.LinearQueryIdentification
