/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
# Moments and sign symmetry on the Boolean cube

The module defines uniform means, variances, and covariances on the finite Boolean cube. For
coefficients taking values `1/4` and `9/4`, it computes the mean and variance of
`secondOrderGap`, proves the sign symmetry of its centered sum `Tsum`, and obtains counting
bounds supporting the random-path analysis of [FarhiEtAl2011].

## Main statements

* `cubeMean_second_order` and `cubeVar_second_order`: the mean and variance of the weighted gap
  sum.
* `card_ge_half_of_mean`: at least half of the cube lies at or above the mean.
* `cubeCov_Tsum`: covariance equals the coordinate dot product of the weights.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators

namespace Qatlib.Papers.AdiabGaps09.MainResults

/-- The equivalence separating the first bit of an `(n + 1)`-bit string from its remaining `n`
bits. -/
def succEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun z := (z 0, fun i => z i.succ)
  invFun p := fun i => Fin.cases p.1 p.2 i
  left_inv z := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl
  right_inv p := by
    obtain ⟨b, z⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨rfl, rfl⟩

/-- The sum over all Boolean strings of a coordinatewise product equals the product of the sums
over each bit. -/
theorem sum_cube_prod (n : ℕ) (h : Fin n → Bool → ℝ) :
    ∑ z : Fin n → Bool, ∏ i, h i (z i) = ∏ i, (h i false + h i true) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← Equiv.sum_comp (succEquiv n).symm]
      rw [Fintype.sum_prod_type]
      have hsplit : ∀ p : Bool × (Fin n → Bool),
          ∏ i : Fin (n + 1), h i ((succEquiv n).symm p i)
            = h 0 p.1 * ∏ i : Fin n, h i.succ (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        congr 1
      simp_rw [hsplit]
      calc
        ∑ x : Bool, ∑ x_1 : Fin n → Bool, h 0 x * ∏ x, h x.succ (x_1 x)
            = ∑ x : Bool, h 0 x * (∑ x_1 : Fin n → Bool, ∏ x, h x.succ (x_1 x)) := by
                refine Finset.sum_congr rfl ?_
                intro x _
                rw [Finset.mul_sum]
          _ = (∑ x : Bool, h 0 x) * (∑ x_1 : Fin n → Bool, ∏ x, h x.succ (x_1 x)) := by
                rw [Finset.sum_mul]
          _ = (h 0 false + h 0 true) * (∏ i : Fin n, (h i.succ false + h i.succ true)) := by
                rw [ih, Fintype.sum_bool]
                ring
          _ = ∏ i : Fin (n + 1), (h i false + h i true) := by
                rw [Fin.prod_univ_succ]

/-- The uniform mean of a real-valued function on the `n`-dimensional Boolean cube. -/
def cubeMean {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ z, f z) / (2 : ℝ) ^ n

/-- The uniform second moment minus the square of the uniform mean on the Boolean cube. -/
def cubeVar {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  cubeMean (fun z => (f z) ^ 2) - (cubeMean f) ^ 2

/-- The real number `2 ^ n` is strictly positive for every natural `n`. -/
theorem two_pow_pos (n : ℕ) : (0 : ℝ) < 2 ^ n := by positivity

/-- The uniform cube mean of a constant function is that constant. -/
theorem cubeMean_const {n : ℕ} (c : ℝ) : cubeMean (fun _ : Fin n → Bool => c) = c := by
  unfold cubeMean
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm, mul_div_cancel_right₀ c (two_pow_pos n).ne']

/-- The uniform cube mean preserves addition. -/
theorem cubeMean_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    cubeMean (fun z => f z + g z) = cubeMean f + cubeMean g := by
  unfold cubeMean
  rw [Finset.sum_add_distrib, add_div]

/-- Multiplying a function by a real scalar multiplies its uniform cube mean by that scalar. -/
theorem cubeMean_smul {n : ℕ} (a : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeMean (fun z => a * f z) = a * cubeMean f := by
  unfold cubeMean
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The uniform cube mean commutes with a finite sum of functions. -/
theorem cubeMean_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → Bool) → ℝ) :
    cubeMean (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, cubeMean (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cubeMean_const]
  | insert a s ha ih =>
      have hfun : (fun z => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, cubeMean_add, ih, Finset.sum_insert ha]

/-- The uniform cube mean of a product of single-coordinate functions is the product of their
two-point means. -/
theorem cubeMean_prod {n : ℕ} (h : Fin n → Bool → ℝ) :
    cubeMean (fun z => ∏ i, h i (z i)) = ∏ i, ((h i false + h i true) / 2) := by
  unfold cubeMean
  rw [sum_cube_prod]
  rw [Finset.prod_div_distrib (s := Finset.univ)
      (f := fun i => h i false + h i true) (g := fun _ => (2 : ℝ))]
  simp

/-- The coefficient equal to `1/4` for false and `9/4` for true. -/
def cSq (b : Bool) : ℝ := if b then (9 / 4 : ℝ) else (1 / 4 : ℝ)

/-- The coefficient `cSq` has value `1/4` at false. -/
theorem cSq_false : cSq false = 1 / 4 := by norm_num [cSq]

/-- The coefficient `cSq` has value `9/4` at true. -/
theorem cSq_true : cSq true = 9 / 4 := by norm_num [cSq]

/-- The centered coefficient `cSq b - 5/4`. -/
def X (b : Bool) : ℝ := cSq b - 5 / 4

/-- The centered coefficient `X` has value `-1` at false. -/
theorem X_false : X false = -1 := by norm_num [X, cSq]

/-- The centered coefficient `X` has value one at true. -/
theorem X_true : X true = 1 := by norm_num [X, cSq]

/-- The equally weighted mean of the two values of `cSq` is `5/4`. -/
theorem cSq_mean : (1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true = 5 / 4 := by
  norm_num [cSq]

/-- The equally weighted second moment of `cSq` is `41/16`. -/
theorem cSq_second :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2 = 41 / 16 := by
  norm_num [cSq]

/-- The variance of the equally weighted two-point coefficient `cSq` is one. -/
theorem cSq_variance :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2
      - ((1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true) ^ 2 = 1 := by
  norm_num [cSq]

/-- The sum of the two values of `cSq` is `5/2`. -/
theorem cSq_mean_pair : cSq false + cSq true = 5 / 2 := by norm_num [cSq]

/-- The sum of the two values of the centered coefficient `X` is zero. -/
theorem X_mean_pair : X false + X true = 0 := by norm_num [X_true, X_false]

/-- The sum of the squares of the two values of `X` is two. -/
theorem Xsq_mean_pair : X false * X false + X true * X true = 2 := by
  norm_num [X_true, X_false]

/-- The uniform cube mean of `cSq` at any one coordinate is `5/4`. -/
theorem cubeMean_cSq {n : ℕ} (i : Fin n) :
    cubeMean (fun z : Fin n → Bool => cSq (z i)) = 5 / 4 := by
  let h : Fin n → Bool → ℝ := fun j b => if j = i then cSq b else 1
  have hfun : (fun z : Fin n → Bool => cSq (z i)) = fun z => ∏ j, h j (z j) := by
    funext z
    show cSq (z i) = ∏ j, h j (z j)
    dsimp [h]
    rw [Finset.prod_ite_eq_of_mem' _ i _ (Finset.mem_univ i)]
  rw [hfun, cubeMean_prod]
  rw [Finset.prod_eq_single i]
  · dsimp [h]
    norm_num [cSq]
  · intro j _ hj
    dsimp [h]
    simp [hj]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

/-- The uniform cube mean of `X` at any one coordinate is zero. -/
theorem cubeMean_X {n : ℕ} (i : Fin n) :
    cubeMean (fun z : Fin n → Bool => X (z i)) = 0 := by
  let h : Fin n → Bool → ℝ := fun j b => if j = i then X b else 1
  have hfun : (fun z : Fin n → Bool => X (z i)) = fun z => ∏ j, h j (z j) := by
    funext z
    show X (z i) = ∏ j, h j (z j)
    dsimp [h]
    rw [Finset.prod_ite_eq_of_mem' _ i _ (Finset.mem_univ i)]
  rw [hfun, cubeMean_prod]
  rw [Finset.prod_eq_single i]
  · dsimp [h]
    norm_num [X, cSq]
  · intro j _ hj
    dsimp [h]
    simp [hj]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

/-- The uniform cube mean of the square of `X` at any one coordinate is one. -/
theorem cubeMean_Xsq {n : ℕ} (i : Fin n) :
    cubeMean (fun z : Fin n → Bool => X (z i) * X (z i)) = 1 := by
  let h : Fin n → Bool → ℝ := fun j b => if j = i then X b * X b else 1
  have hfun : (fun z : Fin n → Bool => X (z i) * X (z i)) = fun z => ∏ j, h j (z j) := by
    funext z
    show X (z i) * X (z i) = ∏ j, h j (z j)
    dsimp [h]
    rw [Finset.prod_ite_eq_of_mem' _ i _ (Finset.mem_univ i)]
  rw [hfun, cubeMean_prod]
  rw [Finset.prod_eq_single i]
  · dsimp [h]
    norm_num [X, cSq]
  · intro j _ hj
    dsimp [h]
    simp [hj]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

/-- For distinct coordinates, the uniform cube mean of the product of their `X` values is zero. -/
theorem cubeMean_Xmul {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    cubeMean (fun z : Fin n → Bool => X (z i) * X (z j)) = 0 := by
  let h : Fin n → Bool → ℝ := fun l b =>
    (if l = i then X b else 1) * (if l = j then X b else 1)
  have hfun : (fun z : Fin n → Bool => X (z i) * X (z j)) = fun z => ∏ l, h l (z l) := by
    funext z
    show X (z i) * X (z j) = ∏ l, h l (z l)
    dsimp [h]
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq_of_mem' _ i _ (Finset.mem_univ i),
      Finset.prod_ite_eq_of_mem' _ j _ (Finset.mem_univ j)]
  rw [hfun, cubeMean_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  dsimp [h]
  simp [hij, X_mean_pair]

/-- The weighted sum `∑ i, cSq (z i) * d i` associated with a Boolean configuration. -/
def secondOrderGap {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, cSq (z i) * d i

/-- The centered weighted sum `∑ i, d i * X (z i)`. -/
def Tsum {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, d i * X (z i)

/-- The coefficient `cSq b` is the sum of its mean `5/4` and centered value `X b`. -/
theorem cSq_eq_mean_add_X (b : Bool) : cSq b = 5 / 4 + X b := by
  cases b <;> norm_num [X, cSq]

/-- The gap sum is `(5/4) * ∑ i, d i` plus the centered sum `Tsum d z`. -/
theorem secondOrderGap_eq (n : ℕ) (d : Fin n → ℝ) (z : Fin n → Bool) :
    secondOrderGap d z = (5 / 4) * (∑ i, d i) + Tsum d z := by
  unfold secondOrderGap Tsum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [cSq_eq_mean_add_X]
  ring

/-- The uniform mean of `secondOrderGap d` is `(5/4) * ∑ i, d i`. See [FarhiEtAl2011]. -/
theorem cubeMean_second_order {n : ℕ} (d : Fin n → ℝ) :
    cubeMean (fun z => secondOrderGap d z) = (5 / 4) * ∑ i, d i := by
  unfold secondOrderGap
  rw [cubeMean_sum]
  have hterm : ∀ i, cubeMean (fun z : Fin n → Bool => cSq (z i) * d i) = d i * (5 / 4) := by
    intro i
    rw [show (fun z : Fin n → Bool => cSq (z i) * d i)
          = fun z => d i * cSq (z i) from by funext z; ring]
    rw [cubeMean_smul, cubeMean_cSq]
  simp_rw [hterm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The uniform cube mean of the centered sum `Tsum d` is zero. -/
theorem cubeMean_Tsum {n : ℕ} (d : Fin n → ℝ) : cubeMean (Tsum d) = 0 := by
  unfold Tsum
  rw [cubeMean_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [cubeMean_smul, cubeMean_X, mul_zero]

/-- The uniform second moment of `Tsum d` is `∑ i, (d i)²`. -/
theorem cubeMean_Tsum_sq {n : ℕ} (d : Fin n → ℝ) :
    cubeMean (fun z => (Tsum d z) ^ 2) = ∑ i, (d i) ^ 2 := by
  have hexp : (fun z : Fin n → Bool => (Tsum d z) ^ 2)
      = fun z => ∑ i, ∑ j, d i * d j * (X (z i) * X (z j)) := by
    funext z
    unfold Tsum
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexp, cubeMean_sum]
  simp_rw [cubeMean_sum]
  have hterm : ∀ i j : Fin n,
      cubeMean (fun z : Fin n → Bool => d i * d j * (X (z i) * X (z j)))
        = if i = j then (d i) ^ 2 else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      rw [show (fun z : Fin n → Bool => d i * d i * (X (z i) * X (z i)))
            = fun z => (d i * d i) * (X (z i) * X (z i)) from by funext z; ring]
      rw [cubeMean_smul, cubeMean_Xsq]
      ring
    · rw [if_neg h]
      rw [show (fun z : Fin n → Bool => d i * d j * (X (z i) * X (z j)))
            = fun z => (d i * d j) * (X (z i) * X (z j)) from by funext z; ring]
      rw [cubeMean_smul, cubeMean_Xmul h, mul_zero]
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [if_neg (fun h : i = j => hji h.symm)]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The uniform cube variance of `secondOrderGap d` is `∑ i, (d i)²`. See [FarhiEtAl2011]. -/
theorem cubeVar_second_order {n : ℕ} (d : Fin n → ℝ) :
    cubeVar (fun z => secondOrderGap d z) = ∑ i, (d i) ^ 2 := by
  have hmean := cubeMean_second_order d
  have hsum := cubeMean_Tsum d
  have hsum2 := cubeMean_Tsum_sq d
  have hsq : cubeMean (fun z => (secondOrderGap d z) ^ 2)
      = ((5 / 4) * ∑ i, d i) ^ 2 + (∑ i, (d i) ^ 2) := by
    have hexp : (fun z : Fin n → Bool => (secondOrderGap d z) ^ 2)
        = fun z => ((5 / 4) * ∑ i, d i) ^ 2
            + (2 * ((5 / 4) * ∑ i, d i)) * Tsum d z + (Tsum d z) ^ 2 := by
      funext z
      rw [secondOrderGap_eq]
      ring
    rw [hexp]
    have e1 : cubeMean (fun z : Fin n → Bool =>
        ((5 / 4) * ∑ i, d i) ^ 2 + (2 * ((5 / 4) * ∑ i, d i)) * Tsum d z
          + (Tsum d z) ^ 2)
        = cubeMean (fun z : Fin n → Bool =>
              ((5 / 4) * ∑ i, d i) ^ 2 + (2 * ((5 / 4) * ∑ i, d i)) * Tsum d z)
          + cubeMean (fun z : Fin n → Bool => (Tsum d z) ^ 2) := cubeMean_add _ _
    rw [e1]
    have e2 : cubeMean (fun z : Fin n → Bool =>
          ((5 / 4) * ∑ i, d i) ^ 2 + (2 * ((5 / 4) * ∑ i, d i)) * Tsum d z)
        = cubeMean (fun _ : Fin n → Bool => ((5 / 4) * ∑ i, d i) ^ 2)
          + cubeMean (fun z : Fin n → Bool =>
              (2 * ((5 / 4) * ∑ i, d i)) * Tsum d z) := cubeMean_add _ _
    rw [e2, cubeMean_const, cubeMean_smul, hsum, hsum2]
    ring
  unfold cubeVar
  rw [hsq, hmean]
  ring

/-- The Boolean string obtained by complementing every bit. -/
def negBit {n : ℕ} (z : Fin n → Bool) : Fin n → Bool := fun i => !(z i)

/-- Complementing every bit twice recovers the original string. -/
theorem negBit_involutive {n : ℕ} : Function.Involutive (@negBit n) := by
  intro z
  funext i
  simp [negBit]

/-- The equivalence of the Boolean cube given by complementing every bit. -/
def negEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  ⟨negBit, negBit, negBit_involutive, negBit_involutive⟩

/-- Complementing a bit negates its centered coefficient `X`. -/
theorem X_negBit {n : ℕ} (z : Fin n → Bool) (i : Fin n) :
    X ((negBit z) i) = - X (z i) := by
  unfold negBit
  cases h : z i
  · simp only [Bool.not_false]
    norm_num [X, cSq]
  · simp only [Bool.not_true]
    norm_num [X, cSq]

/-- Complementing all bits negates the centered sum `Tsum d`. -/
theorem Tsum_negBit {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) :
    Tsum d (negBit z) = - Tsum d z := by
  unfold Tsum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [X_negBit]
  ring

/-- The numbers of cube points where `Tsum d` is negative and where it is positive are equal. -/
theorem card_filter_Tsum_neg {n : ℕ} (d : Fin n → ℝ) :
    (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card
      = (Finset.univ.filter (fun z : Fin n → Bool => 0 < Tsum d z)).card := by
  classical
  have himg : (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0))
      = (Finset.univ.filter (fun z : Fin n → Bool => 0 < Tsum d z)).image (negEquiv n) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      refine ⟨negEquiv n z, ?_, ?_⟩
      · change 0 < Tsum d (negBit z)
        rw [Tsum_negBit]
        linarith
      · exact negBit_involutive z
    · rintro ⟨w, hw, rfl⟩
      change Tsum d (negBit w) < 0
      rw [Tsum_negBit]
      linarith
  rw [himg, Finset.card_image_of_injective _ (negEquiv n).injective]

/-- At least `2 ^ n / 2` Boolean configurations have gap sum at least `(5/4) * ∑ i, d i`. See
[FarhiEtAl2011]. -/
theorem card_ge_half_of_mean {n : ℕ} (d : Fin n → ℝ) :
    (2 : ℝ) ^ n / 2 ≤ ((Finset.univ.filter
      (fun z : Fin n → Bool => (5 / 4) * ∑ i, d i ≤ secondOrderGap d z)).card : ℝ) := by
  classical
  have hset : (Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d i ≤ secondOrderGap d z))
      = Finset.univ.filter (fun z : Fin n → Bool => 0 ≤ Tsum d z) := by
    apply Finset.filter_congr
    intro z _
    rw [secondOrderGap_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hcomp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun z => Tsum d z < 0)
  have hnot : (Finset.univ.filter (fun z : Fin n → Bool => ¬ Tsum d z < 0))
      = Finset.univ.filter (fun z : Fin n → Bool => 0 ≤ Tsum d z) := by
    apply Finset.filter_congr
    intro z _
    exact not_lt
  have hsum_nat : (Finset.univ.filter (fun z : Fin n → Bool => 0 ≤ Tsum d z)).card
      + (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card = 2 ^ n := by
    have h := hcomp
    rw [hnot] at h
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    omega
  have hcard : ((Finset.univ.filter (fun z : Fin n → Bool => 0 ≤ Tsum d z)).card : ℝ)
      = (2 : ℝ) ^ n
        - ((Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card : ℝ) := by
    have hcast : ((Finset.univ.filter (fun z : Fin n → Bool => 0 ≤ Tsum d z)).card : ℝ)
        + ((Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card : ℝ)
        = (2 : ℝ) ^ n := by
      exact_mod_cast hsum_nat
    linarith
  have hneg_eq := card_filter_Tsum_neg d
  have hle : (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card
      + (Finset.univ.filter (fun z : Fin n → Bool => 0 < Tsum d z)).card ≤ 2 ^ n := by
    have hdisj : Disjoint (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0))
        (Finset.univ.filter (fun z : Fin n → Bool => 0 < Tsum d z)) := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact (lt_asymm h1 h2).elim
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)
          ∪ Finset.univ.filter (fun z : Fin n → Bool => 0 < Tsum d z)).card
        ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ n := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2c : 2 * ((Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card : ℝ)
      ≤ (2 : ℝ) ^ n := by
    have h2c_nat : 2 * (Finset.univ.filter (fun z : Fin n → Bool => Tsum d z < 0)).card
        ≤ 2 ^ n := by omega
    exact_mod_cast h2c_nat
  rw [hcard]
  nlinarith [h2c]

/-- If the mean gap sum eventually strictly exceeds `a * sc n`, then some positive fraction of
all Boolean configurations eventually has gap sum strictly exceeding that threshold. See
[FarhiEtAl2011]. -/
theorem probability_exceeds_scale {d : (n : ℕ) → Fin n → ℝ} {sc : ℕ → ℝ} {a : ℝ}
    (h : ∀ᶠ n in Filter.atTop, a * sc n < (5 / 4) * ∑ i, d n i) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in Filter.atTop,
      p * (2 : ℝ) ^ n ≤ ((Finset.univ.filter
        (fun z : Fin n → Bool => a * sc n < secondOrderGap (d n) z)).card : ℝ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [h] with n hn
  have hbase := card_ge_half_of_mean (d n)
  have hsub : (Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d n i ≤ secondOrderGap (d n) z))
      ⊆ (Finset.univ.filter (fun z : Fin n → Bool =>
        a * sc n < secondOrderGap (d n) z)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    linarith
  have hcast : ((Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d n i ≤ secondOrderGap (d n) z)).card : ℝ)
      ≤ ((Finset.univ.filter (fun z : Fin n → Bool =>
        a * sc n < secondOrderGap (d n) z)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc (1 / 2) * (2 : ℝ) ^ n = (2 : ℝ) ^ n / 2 := by ring
    _ ≤ _ := hbase
    _ ≤ _ := hcast

/-- The uniform cube covariance, defined as the mean of the product minus the product of the
means. -/
def cubeCov {n : ℕ} (f g : (Fin n → Bool) → ℝ) : ℝ :=
  cubeMean (fun z => f z * g z) - cubeMean f * cubeMean g

/-- The uniform mean of the product of two centered weighted sums equals `∑ i, dq i * dr i`. -/
theorem cubeMean_Tsum_mul {n : ℕ} (dq dr : Fin n → ℝ) :
    cubeMean (fun z => Tsum dq z * Tsum dr z) = ∑ i, dq i * dr i := by
  have hexp : (fun z : Fin n → Bool => Tsum dq z * Tsum dr z)
      = fun z => ∑ i, ∑ j, dq i * dr j * (X (z i) * X (z j)) := by
    funext z
    unfold Tsum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexp, cubeMean_sum]
  simp_rw [cubeMean_sum]
  have hterm : ∀ i j : Fin n,
      cubeMean (fun z : Fin n → Bool => dq i * dr j * (X (z i) * X (z j)))
        = if i = j then dq i * dr i else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      rw [show (fun z : Fin n → Bool => dq i * dr i * (X (z i) * X (z i)))
            = fun z => (dq i * dr i) * (X (z i) * X (z i)) from by funext z; ring]
      rw [cubeMean_smul, cubeMean_Xsq, mul_one]
    · rw [if_neg h]
      rw [show (fun z : Fin n → Bool => dq i * dr j * (X (z i) * X (z j)))
            = fun z => (dq i * dr j) * (X (z i) * X (z j)) from by funext z; ring]
      rw [cubeMean_smul, cubeMean_Xmul h, mul_zero]
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [if_neg (fun h : i = j => hji h.symm)]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The covariance of two centered weighted sums equals the dot product of their coefficient
vectors. -/
theorem cubeCov_Tsum {n : ℕ} (dq dr : Fin n → ℝ) :
    cubeCov (Tsum dq) (Tsum dr) = ∑ i, dq i * dr i := by
  unfold cubeCov
  rw [cubeMean_Tsum_mul, cubeMean_Tsum, cubeMean_Tsum, mul_zero, sub_zero]

end Qatlib.Papers.AdiabGaps09.MainResults
