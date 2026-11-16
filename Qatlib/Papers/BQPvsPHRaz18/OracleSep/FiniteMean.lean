/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.BQPvsPHRaz18.OracleSep.Section6
open Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel

/-- Flipping a Boolean sign negates its real sign value. -/
theorem signFlip (b : Bool) : signVal (!b) = -signVal b := by
  cases b <;> norm_num [signVal]

/-- Negating the first sign table negates the normalized forrelation score. -/
theorem negTableScore {n : ℕ} (x y : Idx n → Bool) :
    scoreSigns (fun i => !(x i)) y = -scoreSigns x y := by
  unfold scoreSigns
  simp only [signFlip, neg_mul, Finset.sum_neg_distrib, neg_div]

/-- The sum of the sign score over a uniform first sign table is zero. -/
theorem sumSignScore {n : ℕ} (y : Idx n → Bool) :
    (∑ x : Idx n → Bool, scoreSigns x y) = 0 := by
  let e : Equiv.Perm (Idx n → Bool) :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  have hp := Fintype.sum_equiv e (fun x => scoreSigns (e x) y)
    (fun x => scoreSigns x y) (fun _ => rfl)
  have hn : (∑ x : Idx n → Bool, scoreSigns (e x) y) =
      -(∑ x : Idx n → Bool, scoreSigns x y) := by
    change (∑ x : Idx n → Bool, scoreSigns (fun i => !(x i)) y) = _
    simp only [negTableScore, Finset.sum_neg_distrib]
  linarith

/-- The finite uniform mean is the average of the paper score over both sign tables. -/
def finiteScoreMean (n : ℕ) : ℝ :=
  (∑ y : Idx n → Bool, ∑ x : Idx n → Bool, scoreSigns x y) /
    (Fintype.card (Idx n → Bool) : ℝ) ^ 2

/-- Claim 6.1 holds for the explicit finite uniform average of the source score. -/
theorem finiteMeanZero (n : ℕ) : finiteScoreMean n = 0 := by
  simp [finiteScoreMean, sumSignScore]

end Qatlib.Papers.BQPvsPHRaz18.OracleSep.Section6
