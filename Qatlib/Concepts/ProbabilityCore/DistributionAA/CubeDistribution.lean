/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

/-!
# Boolean cube distributions and influence predicates

The module defines weighted expectation, variance, coordinate flip influence, product Bernoulli
weights, and uniform Hamming slice weights. It proves their normalization and elementary moment
identities, including the variance bound of one quarter for functions valued in `[0, 1]`.

`CubeDegreeLE` describes multilinear representations on Boolean inputs, while `AAWith` and
`AAHolds` formulate large influence properties and transfer bounds. These definitions provide
probability and degree infrastructure for the query polynomial setting of [BealsEtAl2001].

## Main statements

* `muWeight_cubeWeight`, `sliceWeight_cubeWeight`, and `nuWeight_cubeWeight`: normalization of
  cube weights.
* `CubeDegreeLE`, `AAWith`, and `AAHolds`: degree and large influence predicates.
* `cubeVar_le_one_quarter`: the variance bound for functions valued in `[0, 1]`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- The weighted sum of a real function over all Boolean inputs of length `n`. -/
def cubeExpect (n : ℕ) (w : (Fin n → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, w x * g x

/-- The condition that a Boolean cube weight is nonnegative at every input and sums to one. -/
def CubeWeight (n : ℕ) (w : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x : Fin n → Bool, 0 ≤ w x) ∧ ∑ x : Fin n → Bool, w x = 1

/-- The product Bernoulli weight with factor `p` for each true coordinate and `1 - p` for each
false coordinate. -/
def muWeight (p : ℝ) (n : ℕ) : (Fin n → Bool) → ℝ :=
  fun x => ∏ i : Fin n, (if x i then p else 1 - p)

/-- The number of true coordinates of a Boolean input. -/
def cubeHamming {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- The reciprocal slice cardinality on inputs of Hamming weight `k`, and zero elsewhere. -/
noncomputable def sliceWeight (n k : ℕ) : (Fin n → Bool) → ℝ :=
  fun x =>
    if cubeHamming x = k then
      ((Finset.univ.filter (fun y : Fin n → Bool => cubeHamming y = k)).card : ℝ)⁻¹
    else 0

/-- The uniform slice weight at Hamming level `Nat.floor (p * n)`. -/
noncomputable def nuWeight (p : ℝ) (n : ℕ) : (Fin n → Bool) → ℝ :=
  sliceWeight n (Nat.floor (p * n))

/-- Flip one specified Boolean input coordinate and leave the others fixed. -/
def cubeFlip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !x j else x j

/-- Exchange the values at two specified Boolean input coordinates. -/
def cubeSwap {n : ℕ} (x : Fin n → Bool) (i j : Fin n) : Fin n → Bool :=
  fun k => if k = i then x j else if k = j then x i else x k

/-- The weighted expectation of the squared deviation from the weighted mean. -/
def cubeVar (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  cubeExpect n w (fun x => (f x - cubeExpect n w f) ^ 2)

/-- The weighted mean squared change of a function when coordinate `i` is flipped. -/
def cubeInf (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  cubeExpect n w (fun x => (f x - f (cubeFlip x i)) ^ 2)

/-- The sum of the squared flip influences over all coordinates. -/
def cubeTotalInf (n : ℕ) (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i : Fin n, cubeInf n w f i

/-- The existence of a real multilinear monomial representation with zero coefficients for
coordinate sets larger than `d`. -/
def CubeDegreeLE {n : ℕ} (d : ℕ) (f : (Fin n → Bool) → ℝ) : Prop :=
  ∃ c : Finset (Fin n) → ℝ,
    (∀ S : Finset (Fin n), d < S.card → c S = 0) ∧
    ∀ x : Fin n → Bool,
      f x = ∑ S : Finset (Fin n), c S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)

/-- A choice of real Boolean cube weight for each input length. -/
def CubeFamily : Type := (n : ℕ) → ((Fin n → Bool) → ℝ)

/-- The family of product Bernoulli cube weights at fixed bias `p`. -/
def muFamily (p : ℝ) : CubeFamily :=
  fun n => muWeight p n

/-- The family of uniform slice weights at levels `Nat.floor (p * n)`. -/
noncomputable def nuFamily (p : ℝ) : CubeFamily :=
  fun n => nuWeight p n

/-- The property that each function valued in `[0, 1]` with cube degree at most `d` and variance
at least `v`, for `0 < v ≤ 1/4`, has a coordinate of influence at least `S v d`. -/
def AAWith (Λ : CubeFamily) (S : ℝ → ℕ → ℝ) : Prop :=
  ∀ n d : ℕ, ∀ v : ℝ, 0 < v → v ≤ 1 / 4 →
    ∀ f : (Fin n → Bool) → ℝ, (∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) → CubeDegreeLE d f →
      v ≤ cubeVar n (Λ n) f → ∃ i : Fin n, S v d ≤ cubeInf n (Λ n) f i

/-- The existence of a positive constant and a natural exponent giving an `AAWith` lower bound
of the form `c * (v / d) ^ C`. -/
def AAHolds (Λ : CubeFamily) : Prop :=
  ∃ c : ℝ, ∃ C : ℕ, 0 < c ∧ AAWith Λ (fun v d => c * (v / (d : ℝ)) ^ C)

/-- The natural ceiling of `(4 * D / a) * logb 2 (d / v)`, used as a bias gadget size. -/
noncomputable def biasGadgetSize (a : ℝ) (D : ℕ) (v : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil ((4 * (D : ℝ) / a) * Real.logb 2 ((d : ℝ) / v))

/-- The influence threshold `S (v / 2) (d * biasGadgetSize a D v d) - (v / d) ^ D` used for bias
transfer. -/
noncomputable def biasTransferS (S : ℝ → ℕ → ℝ) (a : ℝ) (D : ℕ) : ℝ → ℕ → ℝ :=
  fun v d => S (v / 2) (d * biasGadgetSize a D v d) - (v / (d : ℝ)) ^ D

/-- The slice transfer threshold `min (v ^ 5) (v * S (v / 2) d ^ 4) / (10 ^ 9 * d ^ 8)`. -/
noncomputable def sliceTransferS (S : ℝ → ℕ → ℝ) : ℝ → ℕ → ℝ :=
  fun v d => min (v ^ 5) (v * S (v / 2) d ^ 4) / (10 ^ 9 * (d : ℝ) ^ 8)

open scoped Classical BigOperators

/-- Product Bernoulli weights are nonnegative and normalized for `0 ≤ p ≤ 1`. -/
theorem muWeight_cubeWeight {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) :
    CubeWeight n (muWeight p n) := by
  constructor
  · intro x
    apply Finset.prod_nonneg
    intro i _
    split_ifs <;> linarith
  · unfold muWeight
    calc
      _ = ∏ i : Fin n, ∑ b : Bool, (if b then p else 1-p) :=
        (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then p else 1-p)).symm
      _ = 1 := by simp

/-- The uniform weight on the Hamming `k` slice is nonnegative and normalized when `k ≤ n`. -/
theorem sliceWeight_cubeWeight (n k : ℕ) (hk : k ≤ n) : CubeWeight n (sliceWeight n k) := by
  let S := Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x = k)
  let x : Fin n → Bool := fun i => decide ((i : ℕ) < k)
  have hx : cubeHamming x = k := by
    simp only [cubeHamming, x, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]
  have hS : 0 < S.card := Finset.card_pos.2 ⟨x, by simp [S, hx]⟩
  constructor
  · intro y
    unfold sliceWeight
    split_ifs <;> positivity
  · change (∑ y, if cubeHamming y = k then (S.card : ℝ)⁻¹ else 0) = 1
    rw [← Finset.sum_filter]
    change (∑ _y ∈ S, (S.card : ℝ)⁻¹) = 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hS.ne')

/-- The slice weight at level `Nat.floor (p * n)` is nonnegative and normalized for `0 < p < 1`. -/
theorem nuWeight_cubeWeight {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (n : ℕ) :
    CubeWeight n (nuWeight p n) := by
  apply sliceWeight_cubeWeight
  have hf := Nat.floor_le (show 0 ≤ p*(n : ℝ) by positivity)
  have hp := mul_le_mul_of_nonneg_right h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [one_mul] at hp
  exact_mod_cast hf.trans hp

/-- Each squared flip influence is nonnegative under a cube probability weight. -/
theorem cubeInf_nonneg (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (i : Fin n) : 0 ≤ cubeInf n w f i := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (sq_nonneg _)

/-- Weighted cube variance is nonnegative under a cube probability weight. -/
theorem cubeVar_nonneg (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) : 0 ≤ cubeVar n w f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (sq_nonneg _)

/-- Cube variance equals the second moment minus the square of the mean under a cube probability
weight. -/
theorem cube_var_eq_second_moment_sub_sq (n : ℕ) {w : (Fin n → Bool) → ℝ}
    (hw : CubeWeight n w) (f : (Fin n → Bool) → ℝ) :
    cubeVar n w f = cubeExpect n w (fun x => f x ^ 2)-(cubeExpect n w f)^2 := by
  let m := cubeExpect n w f
  have he (x : Fin n → Bool) : w x*(f x-m)^2 = w x*f x^2-2*m*(w x*f x)+m^2*w x := by ring
  change (∑ x, w x*(f x-m)^2) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw.2]
  change cubeExpect n w (fun x => f x^2)-2*m*m+m^2*1 = _
  dsimp [m]
  ring

/-- A function valued in `[0, 1]` has variance at most one quarter under any cube probability
weight. -/
theorem cubeVar_le_one_quarter (n : ℕ) {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    {f : (Fin n → Bool) → ℝ} (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) :
    cubeVar n w f ≤ 1/4 := by
  have hm : cubeExpect n w (fun x => f x^2) ≤ cubeExpect n w f := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hw.1 x)
    nlinarith [(hb x).1, (hb x).2]
  rw [cube_var_eq_second_moment_sub_sq n hw f]
  nlinarith only [hm, sq_nonneg (cubeExpect n w f-1/2)]

end Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
noncomputable section

/-- Weighted cube expectation preserves addition. -/
theorem cube_expect_add (n : ℕ) (w : (Fin n → Bool) → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => f x+g x) = cubeExpect n w f+cubeExpect n w g := by
  simp [cubeExpect, mul_add, Finset.sum_add_distrib]
end
noncomputable section

/-- A real constant factors out of weighted cube expectation. -/
theorem cube_expect_const_mul (n : ℕ) (w : (Fin n → Bool) → ℝ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => c*f x) = c*cubeExpect n w f := by
  unfold cubeExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
end
noncomputable section

/-- Weighted cube expectation preserves subtraction. -/
theorem cube_expect_sub (n : ℕ) (w : (Fin n → Bool) → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => f x-g x) = cubeExpect n w f-cubeExpect n w g := by
  simp [cubeExpect, mul_sub, Finset.sum_sub_distrib]
end
noncomputable section

/-- A pointwise absolute bound on a function also bounds the absolute value of its expectation
under a cube probability weight. -/
theorem cube_expect_abs_le {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : |cubeExpect n w f| ≤ C := by
  unfold cubeExpect
  calc
    _ ≤ ∑ x, |w x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x*|f x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hw.1 x)]
    _ ≤ ∑ x, w x*C := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (hw.1 x)
    _ = C := by rw [← Finset.sum_mul, hw.2, one_mul]
end
noncomputable section

/-- Weighted cube expectation commutes with a finite sum. -/
theorem cube_expect_sum {ι : Type} [Fintype ι] (n : ℕ) (w : (Fin n → Bool) → ℝ)
    (f : ι → (Fin n → Bool) → ℝ) :
    cubeExpect n w (fun x => ∑ i, f i x) = ∑ i, cubeExpect n w (f i) := by
  unfold cubeExpect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
end
end Qatlib.Concepts.ProbabilityCore.DistributionAA
