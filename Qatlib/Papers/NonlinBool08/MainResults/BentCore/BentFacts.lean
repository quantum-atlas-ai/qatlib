/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.BentCore

lemma add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with h | h <;> simp [h, one_add_one_zmod2]

lemma add_self_bvec {n : ℕ} (u : BVec n) : u + u = 0 := by
  funext i
  exact add_self_zmod2 (u i)

lemma add_eq_zero_iff_eq_bvec {n : ℕ} (a b : BVec n) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (fun v => v + b) h
    simpa [add_assoc, add_self_bvec, zero_add] using h'
  · intro h
    rw [h, add_self_bvec]

lemma shift_injective {n : ℕ} (s : BVec n) :
    Function.Injective (fun x : BVec n => x + s) := by
  intro a b h
  exact add_right_cancel h

lemma shift_bijective {n : ℕ} (s : BVec n) :
    Function.Bijective (fun x : BVec n => x + s) :=
  (shift_injective s).bijective_of_finite

lemma lshift_bijective {n : ℕ} (s : BVec n) :
    Function.Bijective (fun x : BVec n => s + x) := by
  have hinj : Function.Injective (fun x : BVec n => s + x) := by
    intro a b h
    exact add_left_cancel h
  exact hinj.bijective_of_finite

lemma dot_add_dot {n : ℕ} (w x y : BVec n) :
    dot w (x + y) = dot w x + dot w y := by
  show dotProduct w (x + y) = dotProduct w x + dotProduct w y
  rw [dotProduct_add]

lemma dot_add_self {n : ℕ} (w x z : BVec n) :
    dot w x + dot w (x + z) = dot w z := by
  show dotProduct w x + dotProduct w (x + z) = dotProduct w z
  rw [dotProduct_add, ← add_assoc, add_self_zmod2, zero_add]

lemma dot_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : BVec n) :
    dot (A.mulVec x) y = dot x (Aᵀ.mulVec y) := by
  calc dot (A.mulVec x) y = dot y (A.mulVec x) := dotProduct_comm _ _
    _ = dot x (Aᵀ.mulVec y) := (Matrix.dotProduct_transpose_mulVec A x y).symm

lemma sum_w_eps_dot {n : ℕ} (v : BVec n) :
    ∑ w : BVec n, eps (dot w v) = if v = 0 then 2 ^ n else 0 := by
  rw [show (∑ w : BVec n, eps (dot w v)) = ∑ w : BVec n, eps (dot v w) from
    Finset.sum_congr rfl (fun w _ => by simp only [dot]; rw [dotProduct_comm])]
  exact sum_eps_dot v

lemma walsh_shift {n : ℕ} (f : BVec n → ZMod 2) (s : BVec n) (w : BVec n) :
    walsh (fun x => f (x + s)) w = eps (dot s w) * walsh f w := by
  rw [walsh, walsh]
  have h1 : (∑ x : BVec n, eps (dot w x) * eps (f (x + s)))
      = ∑ y : BVec n, eps (dot w (y + s)) * eps (f y) := by
    refine Fintype.sum_bijective (fun x : BVec n => x + s) (shift_bijective s) _ _ ?_
    intro x
    have hxx : x + s + s = x := by rw [add_assoc, add_self_bvec, add_zero]
    rw [hxx]
  rw [h1]
  have h2 : ∀ y : BVec n, eps (dot w (y + s)) * eps (f y)
      = eps (dot w s) * (eps (dot w y) * eps (f y)) := by
    intro y
    show eps (dotProduct w (y + s)) * eps (f y)
      = eps (dotProduct w s) * (eps (dotProduct w y) * eps (f y))
    rw [dotProduct_add, eps_add]
    ring
  simp only [h2]
  rw [← Finset.mul_sum]
  simp only [dot]
  rw [dotProduct_comm w s]

lemma walsh_sq_expand {n : ℕ} (f : BVec n → ZMod 2) (w : BVec n) :
    walsh f w ^ 2 = ∑ x : BVec n, ∑ y : BVec n,
      eps (dot w x + f x + (dot w y + f y)) := by
  rw [walsh_eq_sum_eps_add, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← eps_add]

lemma sum_swap3 {α : Type} [Fintype α] (F : α → α → α → ℤ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  conv_lhs => rw [Finset.sum_comm]

lemma walsh_sq_deriv {n : ℕ} (f : BVec n → ZMod 2) (w : BVec n) :
    walsh f w ^ 2 =
      ∑ z : BVec n, eps (dot w z) * ∑ x : BVec n, eps (f x + f (x + z)) := by
  rw [walsh_sq_expand]

  have hinner : ∀ x : BVec n,
      (∑ y : BVec n, eps (dot w x + f x + (dot w y + f y)))
        = ∑ z : BVec n, eps (dot w z + (f x + f (x + z))) := by
    intro x
    refine Fintype.sum_bijective (fun y : BVec n => x + y) (lshift_bijective x)
      _ _ ?_
    intro y
    show eps (dot w x + f x + (dot w y + f y))
        = eps (dot w (x + y) + (f x + f (x + (x + y))))
    rw [show x + (x + y) = y from by
      rw [← add_assoc, add_self_bvec, zero_add]]
    congr 1
    show dotProduct w x + f x + (dotProduct w y + f y)
        = dotProduct w (x + y) + (f x + f y)
    rw [dotProduct_add]
    ring
  simp only [hinner]
  rw [show (∑ x : BVec n, ∑ z : BVec n, eps (dot w z + (f x + f (x + z))))
      = ∑ x : BVec n, ∑ z : BVec n,
          eps (dot w z) * eps (f x + f (x + z)) from
    Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun z _ => by rw [eps_add]))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]

lemma walsh_sq_mul {n : ℕ} (f : BVec n → ZMod 2) (u : BVec n) :
    ∑ w : BVec n, walsh f w ^ 2 * eps (dot w u)
      = (2 : ℤ) ^ n * ∑ x : BVec n, eps (f x + f (x + u)) := by
  have h1 : ∑ w : BVec n, walsh f w ^ 2 * eps (dot w u)
      = ∑ w : BVec n, ∑ x : BVec n, ∑ y : BVec n,
          eps (dot w x + f x + (dot w y + f y)) * eps (dot w u) := by
    apply Finset.sum_congr rfl
    intro w _
    rw [walsh_sq_expand, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
  rw [h1]
  rw [sum_swap3]
  have hinner : ∀ x y : BVec n,
      (∑ w : BVec n, eps (dot w x + f x + (dot w y + f y)) * eps (dot w u))
      = eps (f x + f y) * (if x + y + u = 0 then 2 ^ n else 0) := by
    intro x y
    have hterm : ∀ w : BVec n,
        eps (dot w x + f x + (dot w y + f y)) * eps (dot w u)
        = eps ((f x + f y) + dot w (x + y + u)) := by
      intro w
      rw [← eps_add]
      congr 1
      show dotProduct w x + f x + (dotProduct w y + f y) + dotProduct w u
          = (f x + f y) + dotProduct w (x + y + u)
      rw [dotProduct_add, dotProduct_add]
      ring
    simp only [hterm]
    rw [show (∑ w : BVec n, eps ((f x + f y) + dot w (x + y + u)))
        = ∑ w : BVec n, eps (f x + f y) * eps (dot w (x + y + u)) from
      Finset.sum_congr rfl (fun w _ => by rw [eps_add])]
    rw [← Finset.mul_sum]
    rw [sum_w_eps_dot]
  simp only [hinner]
  have hcol : ∀ x : BVec n,
      (∑ y : BVec n, eps (f x + f y) * (if x + y + u = 0 then 2 ^ n else 0))
      = 2 ^ n * eps (f x + f (x + u)) := by
    intro x
    rw [Finset.sum_eq_single (x + u)]
    · have hzero : x + (x + u) + u = 0 := by
        rw [add_assoc, add_assoc, add_self_bvec, add_zero]
        exact add_self_bvec x
      rw [if_pos hzero]
      ring
    · intro y _ hy
      have hne : x + y + u ≠ 0 := by
        intro h0
        apply hy
        have key : (x + y) + u + u = 0 + u := by rw [h0]
        have key2 : x + y = u := by
          simpa [add_assoc, add_self_bvec, add_zero] using key
        have key3 : x + (x + y) = x + u := by rw [key2]
        have hyx : x + (x + y) = y := by
          rw [← add_assoc, add_self_bvec, zero_add]
        rw [hyx] at key3
        exact key3
      rw [if_neg hne, mul_zero]
    · intro hmem
      simp at hmem
  simp only [hcol]
  rw [Finset.mul_sum]

lemma bent_autocorrelation {n : ℕ} {f : BVec n → ZMod 2} (hf : Bent f) (u : BVec n) :
    ∑ x : BVec n, eps (f x + f (x + u)) = if u = 0 then 2 ^ n else 0 := by
  have h := walsh_sq_mul f u
  have hL : (∑ w : BVec n, walsh f w ^ 2 * eps (dot w u))
      = (2 : ℤ) ^ n * ∑ w : BVec n, eps (dot w u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hf w]
  rw [hL, sum_w_eps_dot u] at h
  have h2n : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  exact (mul_left_cancel₀ h2n h).symm

lemma bent_gram {n : ℕ} {f : BVec n → ZMod 2} (hf : Bent f) (x x' : BVec n) :
    ∑ y : BVec n, eps (f (x + y) + f (x' + y)) = if x = x' then 2 ^ n else 0 := by
  have hmain : (∑ y : BVec n, eps (f (x + y) + f (x' + y)))
      = ∑ z : BVec n, eps (f z + f (z + (x + x'))) := by
    refine Fintype.sum_bijective (fun y : BVec n => x + y) (lshift_bijective x)
      _ _ ?_
    intro y
    show eps (f (x + y) + f (x' + y))
        = eps (f (x + y) + f ((x + y) + (x + x')))
    congr 1
    have harg : (x + y) + (x + x') = x' + y := by
      calc (x + y) + (x + x') = (x + x) + (y + x') := by abel
        _ = 0 + (y + x') := by rw [add_self_bvec]
        _ = y + x' := by rw [zero_add]
        _ = x' + y := by rw [add_comm]
    rw [harg]
  rw [hmain, bent_autocorrelation hf]
  by_cases h : x = x'
  · rw [if_pos h, if_pos (by rw [h, add_self_bvec])]
  · rw [if_neg h, if_neg]
    intro hzero
    exact h ((add_eq_zero_iff_eq_bvec x x').mp hzero)

lemma sum_walsh_mul {n : ℕ} (f : BVec n → ZMod 2) (u : BVec n) :
    ∑ w : BVec n, eps (dot u w) * walsh f w = (2 : ℤ) ^ n * eps (f u) := by
  have h1 : (∑ w : BVec n, eps (dot u w) * walsh f w)
      = ∑ w : BVec n, ∑ x : BVec n,
          eps (dot u w) * (eps (dot w x) * eps (f x)) := by
    apply Finset.sum_congr rfl
    intro w _
    rw [walsh_eq_sum_eps_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [eps_add]
  rw [h1, Finset.sum_comm]
  have hinner : ∀ x : BVec n,
      (∑ w : BVec n, eps (dot u w) * (eps (dot w x) * eps (f x)))
      = eps (f x) * (if u + x = 0 then 2 ^ n else 0) := by
    intro x
    have hterm : ∀ w : BVec n,
        eps (dot u w) * (eps (dot w x) * eps (f x))
        = eps (f x) * eps (dot w (u + x)) := by
      intro w
      have hdu : dot w u = dot u w := by
        simp only [dot]
        rw [dotProduct_comm]
      have hwx : eps (dot w (u + x)) = eps (dot w u) * eps (dot w x) := by
        rw [dot_add_dot, eps_add]
      rw [hwx, hdu]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum]
    rw [sum_w_eps_dot]
  simp only [hinner]
  rw [Finset.sum_eq_single u]
  · rw [if_pos (by rw [add_self_bvec])]
    ring
  · intro x _ hx
    have hne : u + x ≠ 0 := fun h0 =>
      hx ((add_eq_zero_iff_eq_bvec u x).mp h0).symm
    rw [if_neg hne, mul_zero]
  · intro hmem
    simp at hmem

lemma bent_dual_bent {n : ℕ} {f ft : BVec n → ZMod 2}
    (hd : IsDual f ft)
    (hpow : (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) = (2 : ℤ) ^ n) :
    Bent ft := by
  intro u
  have hinv := sum_walsh_mul f u
  have h1 : (∑ w : BVec n, eps (dot u w) * walsh f w)
      = (2 : ℤ) ^ (n / 2) * walsh ft u := by
    rw [show walsh ft u = ∑ w : BVec n, eps (dot u w) * eps (ft w) from rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hd w]
    ring
  rw [h1] at hinv
  have hpow' : (2 : ℤ) ^ (n / 2) * ((2 : ℤ) ^ (n / 2) * eps (f u))
      = (2 : ℤ) ^ n * eps (f u) := by
    rw [← mul_assoc, hpow]
  have hc : (2 : ℤ) ^ (n / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hval : walsh ft u = (2 : ℤ) ^ (n / 2) * eps (f u) := by
    apply mul_left_cancel₀ hc
    rw [hinv, hpow']
  rw [hval, mul_pow, eps_sq, mul_one, pow_two]
  exact hpow

lemma pow_half_mul {n : ℕ} (hn : Even n) :
    (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) = (2 : ℤ) ^ n := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  have hdiv : (k + k) / 2 = k := by omega
  rw [hdiv, ← pow_add]

end Qatlib.Papers.NonlinBool08.MainResults.BentCore
