/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

structure EvenRep (m : ℕ) (f : Polynomial ℝ) where
  a : Polynomial ℝ
  b : Polynomial ℝ
  identity : f = a ^ 2 + X * (1 - X) * b ^ 2
  degreeA : a.degree ≤ (m : WithBot ℕ)
  degreeB : b.degree < (m : WithBot ℕ)

structure OddRep (m : ℕ) (f : Polynomial ℝ) where
  a : Polynomial ℝ
  b : Polynomial ℝ
  identity : f = X * a ^ 2 + (1 - X) * b ^ 2
  degreeA : a.degree ≤ (m : WithBot ℕ)
  degreeB : b.degree ≤ (m : WithBot ℕ)

def Representation (d : ℕ) (f : Polynomial ℝ) : Type :=
  if d % 2 = 0 then EvenRep (d / 2) f else OddRep (d / 2) f

noncomputable section

def zeroEven (m : ℕ) : EvenRep m 0 where
  a := 0
  b := 0
  identity := by simp
  degreeA := by simp
  degreeB := by simp

def zeroOdd (m : ℕ) : OddRep m 0 where
  a := 0
  b := 0
  identity := by simp
  degreeA := by simp
  degreeB := by simp

def constEven (c : ℝ) (hc : 0 ≤ c) : EvenRep 0 (C c) where
  a := C (Real.sqrt c)
  b := 0
  identity := by simp [← C_pow, Real.sq_sqrt hc]
  degreeA := degree_C_le
  degreeB := by simp

def linearLeft (r : ℝ) (hr : r ≤ 0) : OddRep 0 (X - C r) where
  a := C (Real.sqrt (1 - r))
  b := C (Real.sqrt (-r))
  identity := by
    rw [← C_pow, ← C_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - r),
      Real.sq_sqrt (neg_nonneg.mpr hr)]
    simp only [map_sub, map_one, map_neg]
    ring
  degreeA := degree_C_le
  degreeB := degree_C_le

def linearRight (r : ℝ) (hr : 1 ≤ r) : OddRep 0 (C r - X) where
  a := C (Real.sqrt (r - 1))
  b := C (Real.sqrt r)
  identity := by
    rw [← C_pow, ← C_pow, Real.sq_sqrt (sub_nonneg.mpr hr),
      Real.sq_sqrt (by linarith : 0 ≤ r)]
    simp only [map_sub, map_one]
    ring
  degreeA := degree_C_le
  degreeB := degree_C_le

def rootQuadratic (z : ℂ) : Polynomial ℝ :=
  X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)

theorem rootQuadratic_pos (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    0 < (rootQuadratic z).eval t := by
  simp only [rootQuadratic, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C]
  have hn := Complex.sq_norm_sub_sq_re z
  have hi : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  nlinarith [sq_nonneg (t - z.re)]

def quadraticRep (z : ℂ) : EvenRep 1 (rootQuadratic z) where
  a := C ‖z‖ - C (‖z‖ + ‖1 - z‖) * X
  b := C (Real.sqrt ((‖z‖ + ‖1 - z‖) ^ 2 - 1))
  identity := by
    have hs : 1 ≤ ‖z‖ + ‖1 - z‖ := by
      simpa using norm_add_le z (1 - z)
    have hrad : 0 ≤ (‖z‖ + ‖1 - z‖) ^ 2 - 1 := by nlinarith
    apply Polynomial.funext
    intro t
    simp only [rootQuadratic, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C,
      eval_one, Real.sq_sqrt hrad]
    have hu := Complex.sq_norm_sub_sq_re z
    have hv := Complex.sq_norm_sub_sq_re (1 - z)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, neg_sq] at hv
    have hrel : ‖1 - z‖ ^ 2 - ‖z‖ ^ 2 - 1 = -2 * z.re := by nlinarith
    nlinarith [congrArg (fun x : ℝ => x * t) hrel]
  degreeA := (degree_sub_le _ _).trans (max_le
    (degree_C_le.trans (by norm_num)) (degree_C_mul_X_le _))
  degreeB := degree_C_lt

private theorem degree_mul_bound {p q : Polynomial ℝ} {m n : ℕ}
    (hp : p.degree ≤ (m : WithBot ℕ)) (hq : q.degree ≤ (n : WithBot ℕ)) :
    (p * q).degree ≤ ((m + n : ℕ) : WithBot ℕ) := by
  simpa only [Nat.cast_add] using degree_mul_le_of_le hp hq

private theorem degree_mul_strict {p q : Polynomial ℝ} {m n : ℕ}
    (hp : p.degree ≤ (m : WithBot ℕ)) (hq : q.degree < (n : WithBot ℕ)) :
    (p * q).degree < ((m + n : ℕ) : WithBot ℕ) := by
  calc
    (p * q).degree ≤ p.degree + q.degree := degree_mul_le _ _
    _ ≤ (m : WithBot ℕ) + q.degree := add_le_add hp le_rfl
    _ < (m : WithBot ℕ) + n := WithBot.add_lt_add_left (by simp) hq
    _ = ((m + n : ℕ) : WithBot ℕ) := by simp

private theorem degree_linear_mul {l p : Polynomial ℝ} {m : ℕ}
    (hl : l.degree ≤ 1) (hp : p.degree < (m : WithBot ℕ)) :
    (l * p).degree ≤ (m : WithBot ℕ) := by
  calc
    (l * p).degree ≤ l.degree + p.degree := degree_mul_le _ _
    _ ≤ 1 + p.degree := add_le_add hl le_rfl
    _ ≤ m := by simpa only [add_comm] using Nat.WithBot.add_one_le_of_lt hp

private theorem degree_one_sub_X : (1 - (X : Polynomial ℝ)).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le (degree_one_le.trans (by norm_num)) degree_X_le)

def evenMulEven {m n : ℕ} {f g : Polynomial ℝ}
    (u : EvenRep m f) (v : EvenRep n g) : EvenRep (m + n) (f * g) where
  a := u.a * v.a - X * (1 - X) * u.b * v.b
  b := u.a * v.b + u.b * v.a
  identity := (congrArg₂ (· * ·) u.identity v.identity).trans (by ring)
  degreeA := by
    apply (degree_sub_le _ _).trans
    apply max_le (degree_mul_bound u.degreeA v.degreeA)
    rw [show X * (1 - X) * u.b * v.b = (X * u.b) * ((1 - X) * v.b) by ring]
    exact degree_mul_bound (degree_linear_mul degree_X_le u.degreeB)
      (degree_linear_mul degree_one_sub_X v.degreeB)
  degreeB := by
    apply (degree_add_le _ _).trans_lt
    apply max_lt (degree_mul_strict u.degreeA v.degreeB)
    simpa only [mul_comm, Nat.add_comm] using degree_mul_strict v.degreeA u.degreeB

def evenMulOdd {m n : ℕ} {f g : Polynomial ℝ}
    (u : EvenRep m f) (v : OddRep n g) : OddRep (m + n) (f * g) where
  a := u.a * v.a - (1 - X) * u.b * v.b
  b := u.a * v.b + X * u.b * v.a
  identity := (congrArg₂ (· * ·) u.identity v.identity).trans (by ring)
  degreeA := (degree_sub_le _ _).trans (max_le (degree_mul_bound u.degreeA v.degreeA)
    (degree_mul_bound (degree_linear_mul degree_one_sub_X u.degreeB) v.degreeB))
  degreeB := degree_add_le_of_degree_le (degree_mul_bound u.degreeA v.degreeB)
    (degree_mul_bound (degree_linear_mul degree_X_le u.degreeB) v.degreeA)

def oddMulOdd {m n : ℕ} {f g : Polynomial ℝ}
    (u : OddRep m f) (v : OddRep n g) : EvenRep (m + n + 1) (f * g) where
  a := X * u.a * v.a - (1 - X) * u.b * v.b
  b := u.a * v.b + u.b * v.a
  identity := (congrArg₂ (· * ·) u.identity v.identity).trans (by ring)
  degreeA := by
    apply (degree_sub_le _ _).trans
    apply max_le
    · simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
        degree_mul_bound (degree_mul_bound degree_X_le u.degreeA) v.degreeA
    · simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
        degree_mul_bound (degree_mul_bound degree_one_sub_X u.degreeB) v.degreeB
  degreeB := (degree_add_le_of_degree_le (degree_mul_bound u.degreeA v.degreeB)
    (degree_mul_bound u.degreeB v.degreeA)).trans_lt (by exact_mod_cast Nat.lt_succ_self (m + n))

def evenPad {m : ℕ} {f : Polynomial ℝ} (u : EvenRep m f) : OddRep m f where
  a := u.a + (1 - X) * u.b
  b := u.a - X * u.b
  identity := u.identity.trans (by ring)
  degreeA := degree_add_le_of_degree_le u.degreeA
    (degree_linear_mul degree_one_sub_X u.degreeB)
  degreeB := (degree_sub_le _ _).trans
    (max_le u.degreeA (degree_linear_mul degree_X_le u.degreeB))

def oddPad {m : ℕ} {f : Polynomial ℝ} (u : OddRep m f) : EvenRep (m + 1) f where
  a := X * u.a + (1 - X) * u.b
  b := u.a - u.b
  identity := u.identity.trans (by ring)
  degreeA := by
    apply degree_add_le_of_degree_le
    · simpa only [Nat.add_comm] using! degree_mul_bound degree_X_le u.degreeA
    · simpa only [Nat.add_comm] using! degree_mul_bound degree_one_sub_X u.degreeB
  degreeB := ((degree_sub_le _ _).trans (max_le u.degreeA u.degreeB)).trans_lt
    (by exact_mod_cast Nat.lt_succ_self m)

def repZero (d : ℕ) : Representation d 0 := by
  unfold Representation
  split
  · exact zeroEven _
  · exact zeroOdd _

def repConst (c : ℝ) (hc : 0 ≤ c) : Representation 0 (C c) := constEven c hc

def repLinearLeft (r : ℝ) (hr : r ≤ 0) : Representation 1 (X - C r) := linearLeft r hr

def repLinearRight (r : ℝ) (hr : 1 ≤ r) : Representation 1 (C r - X) := linearRight r hr

def repQuadratic (z : ℂ) : Representation 2 (rootQuadratic z) := quadraticRep z

def repMul {d e : ℕ} {f g : Polynomial ℝ}
    (u : Representation d f) (v : Representation e g) : Representation (d + e) (f * g) := by
  by_cases hd : d % 2 = 0 <;> by_cases he : e % 2 = 0
  · have hs : (d + e) % 2 = 0 := by omega
    have hh : (d + e) / 2 = d / 2 + e / 2 := by omega
    simp only [Representation, if_pos hd] at u
    simp only [Representation, if_pos he] at v
    simpa only [Representation, if_pos hs, hh] using evenMulEven u v
  · have hs : (d + e) % 2 ≠ 0 := by omega
    have hh : (d + e) / 2 = d / 2 + e / 2 := by omega
    simp only [Representation, if_pos hd] at u
    simp only [Representation, if_neg he] at v
    simpa only [Representation, if_neg hs, hh] using evenMulOdd u v
  · have hs : (d + e) % 2 ≠ 0 := by omega
    have hh : (d + e) / 2 = e / 2 + d / 2 := by omega
    simp only [Representation, if_neg hd] at u
    simp only [Representation, if_pos he] at v
    simpa only [Representation, if_neg hs, hh, mul_comm] using evenMulOdd v u
  · have hs : (d + e) % 2 = 0 := by omega
    have hh : (d + e) / 2 = d / 2 + e / 2 + 1 := by omega
    simp only [Representation, if_neg hd] at u
    simp only [Representation, if_neg he] at v
    simpa only [Representation, if_pos hs, hh] using oddMulOdd u v

def repSucc {d : ℕ} {f : Polynomial ℝ} (u : Representation d f) :
    Representation (d + 1) f := by
  by_cases hd : d % 2 = 0
  · have hs : (d + 1) % 2 ≠ 0 := by omega
    have hh : (d + 1) / 2 = d / 2 := by omega
    simp only [Representation, if_pos hd] at u
    simpa only [Representation, if_neg hs, hh] using evenPad u
  · have hs : (d + 1) % 2 = 0 := by omega
    have hh : (d + 1) / 2 = d / 2 + 1 := by omega
    simp only [Representation, if_neg hd] at u
    simpa only [Representation, if_pos hs, hh] using oddPad u

def repMono {d e : ℕ} {f : Polynomial ℝ} (hde : d ≤ e)
    (u : Representation d f) : Representation e f :=
  Nat.leRecOn hde (fun v => repSucc v) u

end

end Qatlib.Concepts.QsvtCore.PolyApprox
