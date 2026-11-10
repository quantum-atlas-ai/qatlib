/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.Bias
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.GraphProgram

open Qatlib.Papers.Instantaneous08.MainResults.XProgram
open Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

attribute [local instance] Classical.propDecidable

def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ)⁻¹ : ℂ)

def hAmp (a b : ZMod 2) : ℂ := invSqrtTwo * sgn2 (a * b)

def xExpAmp (θ : ℝ) (a b : ZMod 2) : ℂ :=
  if a = b then (Real.cos θ : ℂ)
  else if b = a + 1 then Complex.I * (Real.sin θ : ℂ) else 0

def plusAmp (m : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ)

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = ((2 : ℝ)⁻¹ : ℂ) := by
  unfold invSqrtTwo
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast h

theorem plusAmp_add (m l : ℕ) : plusAmp (m + l) = plusAmp m * plusAmp l := by
  unfold plusAmp
  have h : (Real.sqrt ((2 : ℝ) ^ (m + l)))⁻¹ =
      (Real.sqrt ((2 : ℝ) ^ m))⁻¹ * (Real.sqrt ((2 : ℝ) ^ l))⁻¹ := by
    rw [pow_add, Real.sqrt_mul (by positivity), mul_inv]
  exact_mod_cast h

theorem normSq_plusAmp (m : ℕ) : Complex.normSq (plusAmp m) = ((2 : ℝ) ^ m)⁻¹ := by
  unfold plusAmp
  rw [Complex.normSq_inv, Complex.normSq_ofReal]
  have h : Real.sqrt ((2 : ℝ) ^ m) * Real.sqrt ((2 : ℝ) ^ m) = (2 : ℝ) ^ m :=
    Real.mul_self_sqrt (by positivity)
  rw [h]

theorem plusAmp_sq_mul (m : ℕ) : plusAmp m * plusAmp m = (((2 : ℂ) ^ m)⁻¹) := by
  have h : plusAmp m * plusAmp m = (((2 : ℝ) ^ m)⁻¹ : ℂ) := by
    unfold plusAmp
    have hreal : (Real.sqrt ((2 : ℝ) ^ m))⁻¹ * (Real.sqrt ((2 : ℝ) ^ m))⁻¹ =
        ((2 : ℝ) ^ m)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    exact_mod_cast hreal
  rw [h]
  congr 1

theorem sqrt_two_pow (n : ℕ) : (Real.sqrt 2) ^ n = Real.sqrt ((2 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]

theorem invSqrtTwo_pow_eq (n : ℕ) : invSqrtTwo ^ n = plusAmp n := by
  unfold invSqrtTwo plusAmp
  have h : ((Real.sqrt 2)⁻¹) ^ n = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    rw [inv_pow, sqrt_two_pow]
  exact_mod_cast h

def graphAmp {n k : ℕ} (p : Fin k → F2Vec n) (x : F2Vec n) (y : F2Vec k) : ℂ :=
  plusAmp (n + k) * ∏ i, ∏ j, sgn2 (p i j * x j * y i)

def lin {n k : ℕ} (p : Fin k → F2Vec n) (zy : F2Vec k) : F2Vec n :=
  fun j => ∑ i, p i j * zy i

theorem lin_add {n k : ℕ} (p : Fin k → F2Vec n) (a b : F2Vec k) :
    lin p (a + b) = lin p a + lin p b := by
  funext j
  simp only [lin, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem lin_zero {n k : ℕ} (p : Fin k → F2Vec n) : lin p 0 = 0 := by
  funext j
  simp [lin]

theorem add_eq_zero_iff_eq_vec {n : ℕ} (x y : F2Vec n) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + 0 := (add_zero x).symm
      _ = x + (x + y) := by rw [h]
      _ = (x + x) + y := by abel
      _ = 0 + y := by rw [add_self_eq_zero_vec]
      _ = y := zero_add y
  · intro h
    rw [h, add_self_eq_zero_vec]

def measAmp {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) (y : F2Vec k) : ℂ :=
  ∑ zx : F2Vec n, ∑ zy : F2Vec k,
    (∏ j, hAmp (x j) (zx j)) * (∏ i, xExpAmp (θ i) (y i) (zy i)) *
      graphAmp p zx zy

theorem sgn2_constraint {k : ℕ} (x z : ZMod 2) (q : Fin k → ZMod 2) :
    sgn2 (x * z) * ∏ i, sgn2 (q i * z) = sgn2 (z * (x + ∑ i, q i)) := by
  have h1 : z * (x + ∑ i, q i) = z * x + ∑ i, z * q i := by
    rw [mul_add, Finset.mul_sum]
  rw [h1, sgn2_add, sgn2_sum]
  congr 1
  · rw [mul_comm]
  · apply Finset.prod_congr rfl
    intro i _
    rw [mul_comm]

theorem sum_zx {n k : ℕ} (p : Fin k → F2Vec n) (x : F2Vec n) (zy : F2Vec k) :
    (∑ zx : F2Vec n,
        (∏ j, hAmp (x j) (zx j)) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) =
      plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0) := by
  classical

  have hh : ∀ zx : F2Vec n,
      (∏ j, hAmp (x j) (zx j)) = invSqrtTwo ^ n * ∏ j, sgn2 (x j * zx j) := by
    intro zx
    simp only [hAmp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

  have hmerge : ∀ zx : F2Vec n,
      (∏ j, sgn2 (x j * zx j)) * (∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) =
        ∏ j, sgn2 (zx j * (x j + ∑ i, p i j * zy i)) := by
    intro zx
    have hswap : (∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) =
        ∏ j, ∏ i, sgn2 ((p i j * zy i) * zx j) := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i _
      rw [show p i j * zx j * zy i = (p i j * zy i) * zx j by ring]
    rw [hswap, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    exact sgn2_constraint (x j) (zx j) (fun i => p i j * zy i)
  calc (∑ zx : F2Vec n,
        (∏ j, hAmp (x j) (zx j)) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i))
      = ∑ zx : F2Vec n,
          invSqrtTwo ^ n * ∏ j, sgn2 (zx j * (x j + ∑ i, p i j * zy i)) := by
        apply Finset.sum_congr rfl
        intro zx _
        rw [hh]
        rw [mul_assoc, hmerge]
    _ = invSqrtTwo ^ n *
          ∑ zx : F2Vec n, ∏ j, sgn2 (zx j * (x j + ∑ i, p i j * zy i)) := by
        rw [Finset.mul_sum]
    _ = invSqrtTwo ^ n *
          (if (fun j => x j + ∑ i, p i j * zy i) = 0 then (2 : ℂ) ^ n else 0) := by
        congr 1
        have hchi : ∀ zx : F2Vec n,
            (∏ j, sgn2 (zx j * (x j + ∑ i, p i j * zy i))) =
              chi (fun j => x j + ∑ i, p i j * zy i) zx := by
          intro zx
          rw [chi_eq_prod]
          apply Finset.prod_congr rfl
          intro j _
          rw [mul_comm]
        simp_rw [hchi]
        exact charSum (fun j => x j + ∑ i, p i j * zy i)
    _ = plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0) := by
        rw [invSqrtTwo_pow_eq]
        congr 1
        by_cases h : x = lin p zy
        · have hc : (fun j => x j + ∑ i, p i j * zy i) = 0 := by
            rw [show (fun j => x j + ∑ i, p i j * zy i) = x + lin p zy from rfl,
              add_eq_zero_iff_eq_vec]
            exact h
          rw [if_pos hc, if_pos h]
        · have hc : ¬ ((fun j => x j + ∑ i, p i j * zy i) = 0) := by
            rw [show (fun j => x j + ∑ i, p i j * zy i) = x + lin p zy from rfl,
              add_eq_zero_iff_eq_vec]
            exact h
          rw [if_neg hc, if_neg h]

theorem measAmp_eq {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) (y : F2Vec k) :
    measAmp p θ x y =
      plusAmp k * ∑ zy : F2Vec k,
        (if lin p zy = x then (∏ i, xExpAmp (θ i) (y i) (zy i)) else 0) := by
  classical
  unfold measAmp graphAmp
  have hinner : ∀ zy : F2Vec k,
      (∑ zx : F2Vec n,
        (∏ j, hAmp (x j) (zx j)) * (∏ i, xExpAmp (θ i) (y i) (zy i)) *
          (plusAmp (n + k) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i))) =
        (∏ i, xExpAmp (θ i) (y i) (zy i)) *
          (plusAmp (n + k) *
            (plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0))) := by
    intro zy
    have hsum := sum_zx p x zy
    calc (∑ zx : F2Vec n,
          (∏ j, hAmp (x j) (zx j)) * (∏ i, xExpAmp (θ i) (y i) (zy i)) *
            (plusAmp (n + k) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)))
        = ∑ zx : F2Vec n,
            ((∏ i, xExpAmp (θ i) (y i) (zy i)) * plusAmp (n + k)) *
              ((∏ j, hAmp (x j) (zx j)) *
                ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) := by
          apply Finset.sum_congr rfl
          intro zx _
          ring
      _ = ((∏ i, xExpAmp (θ i) (y i) (zy i)) * plusAmp (n + k)) *
            ∑ zx : F2Vec n,
              ((∏ j, hAmp (x j) (zx j)) *
                ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) := by
          rw [← Finset.mul_sum]
      _ = ((∏ i, xExpAmp (θ i) (y i) (zy i)) * plusAmp (n + k)) *
            (plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0)) := by
          rw [hsum]
      _ = (∏ i, xExpAmp (θ i) (y i) (zy i)) *
            (plusAmp (n + k) *
              (plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0))) := by
          ring
  calc (∑ zx : F2Vec n, ∑ zy : F2Vec k,
        (∏ j, hAmp (x j) (zx j)) * (∏ i, xExpAmp (θ i) (y i) (zy i)) *
          (plusAmp (n + k) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)))
      = ∑ zy : F2Vec k, ∑ zx : F2Vec n,
          (∏ j, hAmp (x j) (zx j)) * (∏ i, xExpAmp (θ i) (y i) (zy i)) *
            (plusAmp (n + k) * ∏ i, ∏ j, sgn2 (p i j * zx j * zy i)) := by
        rw [Finset.sum_comm]
    _ = ∑ zy : F2Vec k,
          (∏ i, xExpAmp (θ i) (y i) (zy i)) *
            (plusAmp (n + k) *
              (plusAmp n * (if x = lin p zy then (2 : ℂ) ^ n else 0))) := by
        apply Finset.sum_congr rfl
        intro zy _
        rw [hinner]
    _ = plusAmp k * ∑ zy : F2Vec k,
          (if lin p zy = x then (∏ i, xExpAmp (θ i) (y i) (zy i)) else 0) := by
        have hconst : plusAmp (n + k) * (plusAmp n * (2 : ℂ) ^ n) = plusAmp k := by
          rw [plusAmp_add]
          rw [show plusAmp n * plusAmp k * (plusAmp n * (2 : ℂ) ^ n) =
            (plusAmp n * plusAmp n * (2 : ℂ) ^ n) * plusAmp k by ring]
          rw [plusAmp_sq_mul, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
          ring
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro zy _
        by_cases h : x = lin p zy
        · rw [if_pos h, if_pos h.symm]
          rw [show (∏ i, xExpAmp (θ i) (y i) (zy i)) *
              (plusAmp (n + k) * (plusAmp n * (2 : ℂ) ^ n)) =
              (plusAmp (n + k) * (plusAmp n * (2 : ℂ) ^ n)) *
                (∏ i, xExpAmp (θ i) (y i) (zy i)) by ring]
          rw [hconst]
        · rw [if_neg h, if_neg (Ne.symm h)]
          simp

theorem prob_measAmp {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) (y : F2Vec k) :
    Complex.normSq (measAmp p θ x y) =
      ((2 : ℝ) ^ k)⁻¹ * Complex.normSq
        (∑ zy : F2Vec k,
          (if lin p zy = x then (∏ i, xExpAmp (θ i) (y i) (zy i)) else 0)) := by
  rw [measAmp_eq, Complex.normSq_mul, normSq_plusAmp]

def outDist {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) (y' : F2Vec n) : ℝ :=
  ∑ y : F2Vec k, Complex.normSq (measAmp p θ (y' + lin p y) y)

theorem xExpAmp_shift (θ : ℝ) (a b : ZMod 2) :
    xExpAmp θ a (a + b) = if b = 0 then (Real.cos θ : ℂ)
      else Complex.I * (Real.sin θ : ℂ) := by
  unfold xExpAmp
  rcases _root_.Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.zmod2_eq_zero_or_one b with hb | hb
  · subst hb
    simp
  · subst hb
    have hne : ¬ (a = a + 1) := by
      intro h
      have h2 : a + 0 = a + 1 := by rw [add_zero]; exact h
      exact one_ne_zero (add_left_cancel h2).symm
    rw [if_neg hne, if_pos rfl]
    rw [if_neg (one_ne_zero (α := ZMod 2))]

theorem xExpAmp_shift_eq_pathCoeff (θ : ℝ) (a b : ZMod 2) :
    xExpAmp θ a (a + b) = pathCoeff θ (b = 1) := by
  rw [xExpAmp_shift]
  unfold pathCoeff
  rcases _root_.Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.zmod2_eq_zero_or_one b with hb | hb
  · subst hb
    simp
  · subst hb
    simp

theorem pathSample_eq_lin {n k : ℕ} (p : Fin k → F2Vec n) (a : F2Vec k) :
    pathSample p (fun i => a i = 1) = lin p a := by
  funext j
  simp only [pathSample, lin, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rcases _root_.Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.zmod2_eq_zero_or_one
      (a i) with h | h
  · simp [h]
  · simp [h]

theorem sum_shift_constraint {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (u : F2Vec k) (x' : F2Vec n) :
    (∑ zy : F2Vec k,
        (if lin p zy = x' + lin p u then (∏ i, xExpAmp (θ i) (u i) (zy i)) else 0)) =
      ∑ a : F2Vec k,
        (if lin p a = x' then (∏ i, pathCoeff (θ i) (a i = 1)) else 0) := by
  classical
  rw [← Equiv.sum_comp (Equiv.addRight u)
    (fun zy => (if lin p zy = x' + lin p u then
      (∏ i, xExpAmp (θ i) (u i) (zy i)) else 0))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_addRight]
  rw [lin_add]
  have hcond : (lin p a + lin p u = x' + lin p u) ↔ (lin p a = x') := by
    constructor
    · intro h
      have h' : lin p a + lin p u + lin p u = x' + lin p u + lin p u := by rw [h]
      have hl : lin p a + lin p u + lin p u = lin p a := by
        rw [add_assoc, add_self_eq_zero_vec, add_zero]
      have hr : x' + lin p u + lin p u = x' := by
        rw [add_assoc, add_self_eq_zero_vec, add_zero]
      rw [hl, hr] at h'
      exact h'
    · intro h
      rw [h]
  by_cases h : lin p a = x'
  · rw [if_pos h, if_pos (hcond.mpr h)]
    apply Finset.prod_congr rfl
    intro i _
    have harg : (a + u) i = u i + a i := by
      simp only [Pi.add_apply]
      rw [add_comm]
    rw [harg, xExpAmp_shift_eq_pathCoeff]
  · rw [if_neg h, if_neg (fun hh => h (hcond.mp hh))]

theorem sum_zmod_bool {k : ℕ} (g : (Fin k → Bool) → ℂ) :
    (∑ a : F2Vec k, g (fun i => a i = 1)) = ∑ b : Fin k → Bool, g b := by
  classical
  let bitEquiv : ZMod 2 ≃ Bool :=
    { toFun := fun z => z = 1
      invFun := fun b => if b then 1 else 0
      left_inv := by
        intro z
        rcases _root_.Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.zmod2_eq_zero_or_one z with h | h <;> simp [h]
      right_inv := by
        intro b; cases b <;> simp }
  have h := Equiv.sum_comp (Equiv.piCongrRight (fun _ : Fin k => bitEquiv)) g
  simpa [bitEquiv, Equiv.piCongrRight] using! h

theorem outDist_eq_prob {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (y' : F2Vec n) :
    outDist p θ y' = prob p θ y' := by
  classical
  unfold outDist
  have hterm : ∀ y : F2Vec k,
      Complex.normSq (measAmp p θ (y' + lin p y) y) =
        ((2 : ℝ) ^ k)⁻¹ * Complex.normSq (pathSum p θ y') := by
    intro y
    rw [prob_measAmp]
    congr 1
    rw [sum_shift_constraint p θ y y']
    have hstep : (∑ a : F2Vec k,
        (if lin p a = y' then (∏ i, pathCoeff (θ i) (a i = 1)) else 0)) =
        pathSum p θ y' := by
      calc (∑ a : F2Vec k,
            (if lin p a = y' then (∏ i, pathCoeff (θ i) (a i = 1)) else 0))
          = ∑ a : F2Vec k,
              (if pathSample p (fun i => a i = 1) = y' then
                pathWeight θ (fun i => a i = 1) else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [pathSample_eq_lin]
            rfl
        _ = ∑ b : Fin k → Bool,
              (if pathSample p b = y' then pathWeight θ b else 0) :=
            sum_zmod_bool
              (g := fun b => if pathSample p b = y' then pathWeight θ b else 0)
        _ = ∑ b : Fin k → Bool,
              (pathWeight θ b * (if pathSample p b = y' then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : pathSample p b = y'
            · rw [if_pos h, if_pos h, mul_one]
            · rw [if_neg h, if_neg h, mul_zero]
        _ = pathSum p θ y' := rfl
    rw [hstep]
  simp_rw [hterm]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [Fintype.card_fun]
  simp only [ZMod.card, Fintype.card_fin]
  push_cast
  rw [← mul_assoc, show ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k)⁻¹ = 1 by
    exact mul_inv_cancel₀ (pow_ne_zero k (by norm_num))]
  rw [one_mul, prob_eq_pathSum]

def vertexCount (n k : ℕ) : ℕ := n + k

def edgeCount {n k : ℕ} (p : Fin k → F2Vec n) : ℕ :=
  ∑ i, (Finset.univ.filter (fun j => p i j = 1)).card

theorem edgeCount_le {n k : ℕ} (p : Fin k → F2Vec n) :
    edgeCount p ≤ n * k := by
  unfold edgeCount
  calc ∑ i, (Finset.univ.filter (fun j => p i j = 1)).card
      ≤ ∑ _i : Fin k, n := by
        apply Finset.sum_le_sum
        intro i _
        calc (Finset.univ.filter (fun j => p i j = 1)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
          _ = n := by simp
    _ = k * n := by simp
    _ = n * k := by ring

end Qatlib.Papers.Instantaneous08.MainResults.GraphProgram
