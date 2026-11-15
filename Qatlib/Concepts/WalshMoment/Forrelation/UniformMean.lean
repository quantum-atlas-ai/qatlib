/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.WalshMoment.Forrelation.Score
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped BigOperators

/-- Negating a Boolean negates its real sign. -/
theorem realSign_not (b : Bool) : realSign (Bool.not b) = -realSign b := by
  cases b <;> simp [realSign]

/-- Flipping every Boolean value of the left input negates the forrelation score. -/
theorem score_flip_left {I : Type} [Fintype I] (H : I → I → ℝ)
    (f g : I → Bool) :
    score H (fun i => Bool.not (f i)) g = -score H f g := by
  classical
  simp only [score, realSign_not, neg_mul, Finset.sum_neg_distrib, neg_div]

/-- The uniform mean of the forrelation score is zero for any real matrix `H`. -/
theorem uniformScoreMean_eq_zero {I : Type} [Fintype I] (H : I → I → ℝ) :
    uniformScoreMean H = 0 := by
  classical
  let flip : (I → Bool) ≃ (I → Bool) :=
    { toFun := fun f i => Bool.not (f i)
      invFun := fun f i => Bool.not (f i)
      left_inv := by
        intro f
        funext i
        simp
      right_inv := by
        intro f
        funext i
        simp }
  have hsum : (∑ f : I → Bool, ∑ g : I → Bool, score H f g) =
      -(∑ f : I → Bool, ∑ g : I → Bool, score H f g) := by
    calc
      (∑ f : I → Bool, ∑ g : I → Bool, score H f g) =
          ∑ f : I → Bool, ∑ g : I → Bool, score H (flip f) g :=
        (flip.sum_comp (fun f : I → Bool => ∑ g : I → Bool, score H f g)).symm
      _ = -(∑ f : I → Bool, ∑ g : I → Bool, score H f g) := by
        change (∑ f : I → Bool, ∑ g : I → Bool,
          score H (fun i => Bool.not (f i)) g) = _
        simp only [score_flip_left, Finset.sum_neg_distrib]
  have hzero : (∑ f : I → Bool, ∑ g : I → Bool, score H f g) = 0 := by
    linarith
  simp only [uniformScoreMean, hzero, zero_div]

end Qatlib.Concepts.WalshMoment.Forrelation
