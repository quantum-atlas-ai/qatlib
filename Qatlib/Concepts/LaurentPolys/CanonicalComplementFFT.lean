/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.LaurentPolys.CircleComplement
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Canonical polynomial complements and Fourier approximation

This module constructs a polynomial complement with positive real value at zero and no zeros in
the closed unit disk for a polynomial strictly bounded by one on the unit circle. It proves
Schwarz-integral and Fourier-series representations, coefficient decay, sampling alias
identities, and a discrete reconstruction error bound. Polynomial complementation is a component
of quantum signal processing [LowChuang2017].

`radixTwoFourier` supplies an explicit radix-two transform with its Fourier semantics and two
operation counters. The remaining estimates control logarithmic projection, exponentiation, and
recovery of the complementary polynomial coefficients.

## Main statements

* `canonical_complement_outer_exists`: existence of a normalized zero-free complement.
* `canonical_complement_schwarz_representation`: the exponential Schwarz-integral
  representation.
* `canonical_complement_discrete_fourier_accuracy`: coefficient accuracy under an explicit
  sampling threshold.
* `radix_two_fourier_actual_recursion_and_cost`: transform semantics and recorded costs.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LaurentPolys.CircleComplement

namespace Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
open Polynomial
open scoped Classical BigOperators ComplexOrder

/-- The recursive radix-two discrete Fourier transform on `2^m` samples, returned with two
accumulated arithmetic-operation counters. -/
def radixTwoFourier : (m : ℕ) → (Fin (2^m) → ℂ) →
    ((Fin (2^m) → ℂ) × ℕ × ℕ)
  | 0, f => (f, 0, 0)
  | m+1, f =>
    let e := radixTwoFourier m
      (fun j => f ⟨2*j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
    let o := radixTwoFourier m
      (fun j => f ⟨2*j.val+1, by rw [pow_succ]; have := j.isLt; omega⟩)
    let ω := Complex.exp ((-2*Real.pi/(2^(m+1) : ℕ) : ℝ)*Complex.I)
    (fun j => let j' : Fin (2^m) := ⟨j.val % 2^m, Nat.mod_lt _ (by positivity)⟩
              e.1 j' + (if j.val < 2^m then ω^j'.val*o.1 j'
                else -(ω^j'.val*o.1 j')),
      e.2.1+o.2.1+2^m, e.2.2+o.2.2+2^(m+1))

/-- At transform size one, `radixTwoFourier` returns the input with both operation counters
zero. -/
@[simp] theorem radixTwoFourier_zero (f : Fin (2^0) → ℂ) :
    radixTwoFourier 0 f = (f, 0, 0) := rfl

/-- The two counters returned by `radixTwoFourier m f` equal `m * 2^m / 2` and `m * 2^m`,
respectively. -/
theorem radixTwoFourier_cost (m : ℕ) (f : Fin (2^m) → ℂ) :
    (radixTwoFourier m f).2.1 = m*2^m/2 ∧
      (radixTwoFourier m f).2.2 = m*2^m := by
  have aux : ∀ m (f : Fin (2^m) → ℂ),
      2*(radixTwoFourier m f).2.1 = m*2^m ∧
        (radixTwoFourier m f).2.2 = m*2^m := by
    intro m
    induction m with
    | zero => intro f; simp [radixTwoFourier]
    | succ m ih =>
      intro f
      have he := ih (fun j => f ⟨2*j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
      have ho := ih (fun j => f ⟨2*j.val+1, by rw [pow_succ]; have := j.isLt; omega⟩)
      change 2*(_+_+2^m) = (m+1)*2^(m+1) ∧ _+_+2^(m+1) = (m+1)*2^(m+1)
      constructor <;> nlinarith [he.1, he.2, ho.1, ho.2, pow_succ 2 m]
  obtain ⟨hm, ha⟩ := aux m f
  constructor
  · rw [← hm]; omega
  · exact ha

/-- Splits a sum over `Fin (n * 2)` into its even-indexed and odd-indexed terms. -/
private theorem sum_even_odd (n : ℕ) (f : Fin (n*2) → ℂ) :
    ∑ l, f l =
      (∑ l : Fin n, f ⟨2*l.val, by have := l.isLt; omega⟩) +
      ∑ l : Fin n, f ⟨2*l.val+1, by have := l.isLt; omega⟩ := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := n) (n := 2)), Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, finProdFinEquiv, Equiv.coe_fn_mk,
    Fin.val_zero, Fin.val_one]
  simp only [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> congr 1 <;> apply Fin.ext <;> simp [add_comm]

/-- When `w^n = -1` and `j < 2*n`, rewrites the even-index Fourier power using `w^2` and `j %
n`. -/
private theorem fourier_even_power (n j k : ℕ) (_hn : 0 < n) (hj : j < n*2)
    (w : ℂ) (hw : w^n = -1) :
    w^(j*(2*k)) = (w^2)^((j%n)*k) := by
  by_cases h : j < n
  · rw [Nat.mod_eq_of_lt h, ← pow_mul]
    congr 1
    ring
  · have hm : j%n = j-n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have he : j = j%n+n := by omega
    rw [he]
    have hp : (j%n+n)*(2*k) = n*(2*k)+2*((j%n)*k) := by ring
    rw [hp, pow_add, pow_mul w n, hw, pow_mul (-1 : ℂ) 2, neg_one_sq,
      one_pow, one_mul, pow_mul]
    congr 2
    rw [Nat.add_mod_right, Nat.mod_mod]

/-- When `w^n = -1` and `j < 2*n`, splits the odd-index Fourier power into a reduced-index power
and a sign determined by the half containing `j`. -/
private theorem fourier_odd_power (n j k : ℕ) (hn : 0 < n) (hj : j < n*2)
    (w : ℂ) (hw : w^n = -1) :
    w^(j*(2*k+1)) =
      (if j<n then w^(j%n) else -(w^(j%n))) * (w^2)^((j%n)*k) := by
  have he := fourier_even_power n j k hn hj w hw
  have ha : j*(2*k+1) = j*(2*k)+j := by ring
  rw [ha, pow_add, he, mul_comm]
  congr 1
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · have hm : j%n = j-n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hsplit : j = n+j%n := by omega
    calc
      w^j = w^(n+j%n) := by rw [← hsplit]
      _ = -(w^(j%n)) := by rw [pow_add, hw]; ring

/-- Decomposes a length-`2*n` Fourier sum into even and odd length-`n` sums with the
corresponding twiddle factor and sign. -/
private theorem fourier_sum_butterfly (n : ℕ) (hn : 0 < n)
    (f : Fin (n*2) → ℂ) (j : Fin (n*2)) (w : ℂ) (hw : w^n = -1) :
    (∑ l, f l*w^(j.val*l.val)) =
      (∑ l : Fin n, f ⟨2*l.val, by have := l.isLt; omega⟩ *
        (w^2)^((j.val%n)*l.val)) +
      (if j.val<n then w^(j.val%n) *
        (∑ l : Fin n, f ⟨2*l.val+1, by have := l.isLt; omega⟩ *
          (w^2)^((j.val%n)*l.val))
       else -(w^(j.val%n) *
        (∑ l : Fin n, f ⟨2*l.val+1, by have := l.isLt; omega⟩ *
          (w^2)^((j.val%n)*l.val)))) := by
  rw [sum_even_odd]
  simp only [fourier_even_power n j.val _ hn j.isLt w hw,
    fourier_odd_power n j.val _ hn j.isLt w hw]
  split_ifs <;> simp only [Finset.mul_sum, ← Finset.sum_neg_distrib] <;>
    congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> ring

/-- The complex Fourier root `exp (-2πi / N)`. -/
private def fourierRoot (N : ℕ) : ℂ :=
  Complex.exp ((-2*Real.pi/(N : ℝ) : ℝ)*Complex.I)

/-- Expresses a natural power of `fourierRoot N` as the corresponding complex exponential. -/
private theorem fourierRoot_power (N j l : ℕ) :
    fourierRoot N^(j*l) =
      Complex.exp ((-2*Real.pi*j*l/(N : ℕ) : ℝ)*Complex.I) := by
  rw [fourierRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- For positive `n`, squaring the Fourier root for size `2*n` gives the Fourier root for size
`n`. -/
private theorem fourierRoot_square (n : ℕ) (hn : 0 < n) :
    fourierRoot (n*2)^2 = fourierRoot n := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold fourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- For positive `n`, the `n`th power of the Fourier root for size `2*n` equals minus one. -/
private theorem fourierRoot_half (n : ℕ) (hn : 0 < n) :
    fourierRoot (n*2)^n = -1 := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold fourierRoot
  rw [← Complex.exp_nat_mul]
  have ha : (n : ℂ)*((-2*Real.pi/(n*2 : ℕ) : ℝ)*Complex.I) =
      -(Real.pi*Complex.I) := by
    push_cast
    field_simp
  rw [ha, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The value returned by the radix-two recursion is the Fourier sum expressed through powers of
`fourierRoot (2^m)`. -/
private theorem radixTwoFourier_power_semantics (m : ℕ) (f : Fin (2^m) → ℂ)
    (j : Fin (2^m)) :
    (radixTwoFourier m f).1 j = ∑ l, f l*fourierRoot (2^m)^(j.val*l.val) := by
  induction m with
  | zero =>
    have hj : j.val = 0 := by have := j.isLt; norm_num at this; omega
    have hj' : j = 0 := Fin.ext hj
    simp [radixTwoFourier, hj']
  | succ m ih =>
    let n := 2^m
    have hn : 0 < n := by dsimp [n]; positivity
    let e : Fin n → ℂ := fun l => f ⟨2*l.val, by rw [pow_succ]; have := l.isLt; omega⟩
    let o : Fin n → ℂ := fun l => f ⟨2*l.val+1, by rw [pow_succ]; have := l.isLt; omega⟩
    let j' : Fin n := ⟨j.val % n, Nat.mod_lt _ hn⟩
    have he := ih e j'
    have ho := ih o j'
    change (radixTwoFourier m e).1 j' +
      (if j.val < n then fourierRoot (2^(m+1))^j'.val*(radixTwoFourier m o).1 j'
       else -(fourierRoot (2^(m+1))^j'.val*(radixTwoFourier m o).1 j')) = _
    rw [he, ho]
    let g : Fin (n*2) → ℂ := fun l => f (Fin.cast (pow_succ 2 m).symm l)
    let jb : Fin (n*2) := Fin.cast (pow_succ 2 m) j
    have hs := fourier_sum_butterfly n hn g jb (fourierRoot (n*2))
      (fourierRoot_half n hn)
    rw [fourierRoot_square n hn] at hs
    have hsum : (∑ l : Fin (n*2), g l*fourierRoot (n*2)^(jb.val*l.val)) =
        ∑ l : Fin (2^(m+1)), f l*fourierRoot (2^(m+1))^(j.val*l.val) := by
      apply Fintype.sum_equiv (finCongr (pow_succ 2 m).symm)
      intro l
      simp only [n, g, jb, finCongr_apply, Fin.val_cast, ← pow_succ]
    rw [hsum] at hs
    simpa only [e, o, g, jb, j', Fin.val_cast, Fin.cast_mk, ← pow_succ] using! hs.symm

/-- The radix-two recursion computes the unnormalized discrete Fourier transform with negative
exponential phase. -/
theorem radixTwoFourier_semantics (m : ℕ) (f : Fin (2^m) → ℂ)
    (j : Fin (2^m)) :
    (radixTwoFourier m f).1 j = ∑ l : Fin (2^m),
      f l*Complex.exp ((-2*Real.pi*j.val*l.val/(2^m : ℕ) : ℝ)*Complex.I) := by
  simpa only [fourierRoot_power] using! radixTwoFourier_power_semantics m f j

/-- There exists a radix-two transform satisfying the stated butterfly recursion, exact discrete
Fourier semantics, and counter formulas `m * 2^m / 2` and `m * 2^m`. -/
theorem radix_two_fourier_actual_recursion_and_cost :
    ∃ F : (m : ℕ) → (Fin (2^m) → ℂ) →
        ((Fin (2^m) → ℂ) × ℕ × ℕ),
      (∀ f, F 0 f = (f,0,0)) ∧
      (∀ (m : ℕ) (f : Fin (2^(m+1)) → ℂ),
        let e := F m (fun j => f ⟨2*j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
        let o := F m (fun j => f ⟨2*j.val+1, by rw [pow_succ]; have := j.isLt; omega⟩)
        let ω := Complex.exp ((-2*Real.pi/(2^(m+1) : ℕ) : ℝ)*Complex.I)
        F (m+1) f =
          (fun j => let j' : Fin (2^m) := ⟨j.val % 2^m, Nat.mod_lt _ (by positivity)⟩
                    e.1 j' + (if j.val < 2^m then ω^j'.val*o.1 j' else -(ω^j'.val*o.1 j')),
            e.2.1+o.2.1+2^m, e.2.2+o.2.2+2^(m+1))) ∧
      (∀ (m : ℕ) (f : Fin (2^m) → ℂ),
        (∀ j : Fin (2^m), (F m f).1 j = ∑ l : Fin (2^m),
          f l*Complex.exp ((-2*Real.pi*j.val*l.val/(2^m : ℕ) : ℝ)*Complex.I)) ∧
        (F m f).2.1 = m*2^m/2 ∧ (F m f).2.2 = m*2^m) := by
  refine ⟨radixTwoFourier, fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro m f
  exact ⟨radixTwoFourier_semantics m f, radixTwoFourier_cost m f⟩

/-- On the unit circle, reflecting the linear factor associated with `r` preserves its norm: `‖1
- star r * z‖ = ‖z - r‖`. -/
private theorem reflected_factor_circle_norm (r z : ℂ) (hz : ‖z‖ = 1) :
    ‖1-star r*z‖ = ‖z-r‖ := by
  have hzz : z*star z = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  calc
    ‖1-star r*z‖ = ‖z*star (z-r)‖ := by
      congr 1
      rw [star_sub, mul_sub, hzz]
      ring
    _ = ‖z-r‖ := by rw [norm_mul, hz, norm_star, one_mul]

/-- If `‖r‖ < 1` and `‖z‖ ≤ 1`, the reflected factor `1 - star r * z` is nonzero. -/
private theorem reflected_factor_ne_zero (r z : ℂ) (hr : ‖r‖ < 1) (hz : ‖z‖ ≤ 1) :
    1-star r*z ≠ 0 := by
  intro he
  have he' : star r*z = 1 := by linear_combination -he
  have hh : ‖r‖*‖z‖ = 1 := by simpa [norm_mul] using! congrArg norm he'
  have hle : ‖r‖*‖z‖ ≤ ‖r‖ := by nlinarith [norm_nonneg r]
  linarith

/-- A polynomial nonvanishing on the unit circle has a polynomial of no greater degree that is
zero-free on the closed disk and has the same boundary norm. -/
theorem polynomial_outer_circle_factor (A : Polynomial ℂ)
    (ha : ∀ z : ℂ, ‖z‖ = 1 → A.eval z ≠ 0) :
    ∃ B : Polynomial ℂ, B.natDegree ≤ A.natDegree ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → B.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖B.eval z‖ = ‖A.eval z‖) := by
  generalize hd : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    have ha0 : A ≠ 0 := by
      intro he
      have h := ha 1 (by simp)
      simp [he] at h
    by_cases hdeg : A.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have hane : a ≠ 0 := by simpa using! ha 1 (by simp)
      exact ⟨C a, by simp, fun _ _ => by simpa using! hane, fun _ _ => rfl⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using! hr
    obtain ⟨g, hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g ≠ 0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree = 1+g.natDegree := by
      rw [hAg, natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C]
    have hgc : ∀ z : ℂ, ‖z‖ = 1 → g.eval z ≠ 0 := by
      intro z hz hg
      apply ha z hz
      simp [hAg, hg]
    have hrnorm : ‖r‖ ≠ 1 := by
      intro h
      exact ha r h hr'
    obtain ⟨B, hBd, hBn, hBc⟩ := ih g.natDegree (by omega) g hgc rfl
    by_cases hrin : ‖r‖ < 1
    · let b : Polynomial ℂ := C 1-C (star r)*X
      have hbd : b.natDegree ≤ 1 := by
        apply le_trans (natDegree_sub_le _ _)
        simp only [natDegree_C, max_le_iff, zero_le, true_and]
        exact (natDegree_mul_le).trans (by simp)
      refine ⟨b*B, ?_, ?_, ?_⟩
      · exact (natDegree_mul_le).trans (by omega)
      · intro z hz
        simp only [eval_mul]
        apply mul_ne_zero _ (hBn z hz)
        simpa [b] using! reflected_factor_ne_zero r z hrin hz
      · intro z hz
        simp only [eval_mul, norm_mul]
        rw [hBc z hz, hAg, eval_mul, norm_mul]
        congr 1
        simpa [b] using! reflected_factor_circle_norm r z hz
    · have hrout : 1 < ‖r‖ := lt_of_le_of_ne (le_of_not_gt hrin) hrnorm.symm
      refine ⟨(X-C r)*B, ?_, ?_, ?_⟩
      · have hh := natDegree_mul_le (p := X-C r) (q := B)
        rw [natDegree_X_sub_C] at hh
        omega
      · intro z hz
        simp only [eval_mul, eval_sub, eval_X, eval_C]
        apply mul_ne_zero _ (hBn z hz)
        intro he
        have hz' : z = r := sub_eq_zero.mp he
        rw [hz'] at hz
        linarith
      · intro z hz
        simp only [eval_mul, norm_mul]
        rw [hBc z hz, hAg, eval_mul, norm_mul]

/-- A polynomial of degree at most `d` bounded by `1 - δ` on the unit circle, with `0 < δ < 1`,
has a degree-at-most-`d` complement that is zero-free on the closed disk and positive real
at zero. -/
theorem canonical_complement_outer_exists (P : Polynomial ℂ) (d : ℕ) (δ : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ d ∧ 0 < (Q.eval 0).re ∧
      (Q.eval 0).im = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) := by
  obtain ⟨A, hAd, hAc⟩ := circle_complement_zero_margin_exists P d hp
    (fun z hz => (hP z hz).trans (by linarith))
  have han : ∀ z : ℂ, ‖z‖ = 1 → A.eval z ≠ 0 := by
    intro z hz he
    have hc := hAc z hz
    have hb := hP z hz
    simp only [he, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hc
    nlinarith [norm_nonneg (P.eval z)]
  obtain ⟨B, hBd, hBn, hBc⟩ := polynomial_outer_circle_factor A han
  have hb0 : B.eval 0 ≠ 0 := hBn 0 (by simp)
  let c : ℂ := (‖B.eval 0‖ : ℂ)/B.eval 0
  have hcn : ‖c‖ = 1 := by
    simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hb0)
  have hc0 : c*B.eval 0 = (‖B.eval 0‖ : ℂ) := by
    exact div_mul_cancel₀ _ hb0
  refine ⟨C c*B, ?_, ?_, ?_, ?_, ?_⟩
  · exact (natDegree_mul_le).trans (by simpa using! hBd.trans hAd)
  · simp only [eval_mul, eval_C, hc0, Complex.ofReal_re]
    exact norm_pos_iff.mpr hb0
  · simp only [eval_mul, eval_C, hc0, Complex.ofReal_im]
  · intro z hz
    simp only [eval_mul, eval_C]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hcn]; norm_num)) (hBn z hz)
  · intro z hz
    simpa only [eval_mul, eval_C, norm_mul, hcn, one_mul, hBc z hz] using! hAc z hz

/-- A polynomial with no zeros on the closed unit disk possesses a holomorphic logarithm on the
open disk that is continuous on the closed disk. -/
private theorem polynomial_disk_log_exists (A : Polynomial ℂ)
    (ha : ∀ z : ℂ, ‖z‖ ≤ 1 → A.eval z ≠ 0) :
    ∃ H : ℂ → ℂ, DiffContOnCl ℂ H (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Complex.exp (H z) = A.eval z) := by
  generalize hd : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    have ha0 : A ≠ 0 := by intro h; have := ha 0 (by simp); simp [h] at this
    by_cases hdeg : A.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have hane : a ≠ 0 := by simpa using! ha 0 (by simp)
      exact ⟨fun _ => Complex.log a, diffContOnCl_const,
        fun _ _ => by simpa using! Complex.exp_log hane⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using! hr
    obtain ⟨g, hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g ≠ 0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree = 1+g.natDegree := by
      rw [hAg, natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C]
    have hgc : ∀ z : ℂ, ‖z‖ ≤ 1 → g.eval z ≠ 0 := by
      intro z hz hg
      apply ha z hz
      simp [hAg, hg]
    have hrnorm : 1 < ‖r‖ := lt_of_not_ge (fun h => ha r h hr')
    have hr0 : r ≠ 0 := by intro h; norm_num [h] at hrnorm
    obtain ⟨H, hHd, hHe⟩ := ih g.natDegree (by omega) g hgc rfl
    have hslit (z : ℂ) (hz : ‖z‖ ≤ 1) : 1-z/r ∈ Complex.slitPlane := by
      have hh : ‖-(z/r)‖ < 1 := by
        rw [norm_neg, norm_div, div_lt_one (by positivity)]
        exact hz.trans_lt hrnorm
      simpa only [sub_eq_add_neg] using! Complex.mem_slitPlane_of_norm_lt_one hh
    have hlog : DiffContOnCl ℂ (fun z : ℂ => Complex.log (1-z/r)) (Metric.ball 0 1) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.clog (by fun_prop)
      exact hslit z (by simpa [Metric.mem_closedBall, dist_eq_norm] using! hz)
    refine ⟨fun z => Complex.log (-r)+Complex.log (1-z/r)+H z,
      (diffContOnCl_const.add hlog).add hHd, ?_⟩
    intro z hz
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hr0),
      Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)), hHe z hz, hAg,
      eval_mul, eval_sub, eval_X, eval_C]
    field_simp
    ring

set_option maxHeartbeats 800000 in

/-- Recovers a holomorphic function from the Schwarz-kernel circle average of its real part when
its value at zero has zero imaginary part. -/
private theorem schwarz_circle_average (H : ℂ → ℂ)
    (hH : DiffContOnCl ℂ H (Metric.ball 0 1)) (hH0 : (H 0).im = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Real.circleAverage (fun u : ℂ => (u+z)/(u-z)*(H u).re) 0 1 = H z := by
  let K : ℂ → ℂ := fun u => (u+z)/(u-z)
  let C : ℂ → ℂ := fun u => u/(u-z)
  have hzs : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_eq_norm] using! hz
  have hden (u : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1) : u-z ≠ 0 := by
    intro he
    have he' : u = z := sub_eq_zero.mp he
    have hu' : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using! hu
    rw [he'] at hu'
    linarith
  have hHc : ContinuousOn H (Metric.sphere (0 : ℂ) 1) := by
    apply hH.2.mono
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall
  have hKc : ContinuousOn K (Metric.sphere (0 : ℂ) 1) := by
    dsimp [K]
    fun_prop (disch := exact hden _ ‹_›)
  have hCc : ContinuousOn C (Metric.sphere (0 : ℂ) 1) := by
    dsimp [C]
    fun_prop (disch := exact hden _ ‹_›)
  have hiH : CircleIntegrable H 0 1 := hHc.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiC : CircleIntegrable (fun u => C u*H u) 0 1 :=
      (hCc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiK : CircleIntegrable (fun u => K u*H u) 0 1 :=
      (hKc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hKrc : ContinuousOn (fun u => ((K u).re : ℂ)) (Metric.sphere (0 : ℂ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hKc)
  have hiR : CircleIntegrable (fun u => (K u).re*H u) 0 1 :=
      (hKrc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiS : CircleIntegrable (fun u => star (K u)*H u) 0 1 :=
      (hKc.star.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hHabs : DiffContOnCl ℂ H (Metric.ball 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using! hH
  have hC : Real.circleAverage (fun u => C u*H u) 0 1 = H z := by
    simpa only [C, sub_zero, smul_eq_mul] using! hHabs.circleAverage_smul_div
      (by simpa only [abs_one] using! hzs)
  have hA : Real.circleAverage H 0 1 = H 0 := hHabs.circleAverage
  have hR : Real.circleAverage (fun u => (K u).re*H u) 0 1 = H z := by
    simpa [K, smul_eq_mul] using! hH.circleAverage_re_herglotzRieszKernel_smul' hzs
  have hK : Real.circleAverage (fun u => K u*H u) 0 1 = 2*H z-H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • (C u*H u)-H u) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro u hu
        have hu' : u ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [abs_one] using! hu
        dsimp [K, C]
        change (u+z)/(u-z)*H u = 2*(u/(u-z)*H u)-H u
        field_simp [hden u hu']
        ring
      _ = 2*H z-H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • (C u*H u)) hiC.const_smul hiH,
          Real.circleAverage_fun_smul, hC, hA, smul_eq_mul]
  have hS : Real.circleAverage (fun u => star (K u)*H u) 0 1 = H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • ((K u).re*H u)-K u*H u) 0 1 := by
        congr 1
        funext u
        simp only [smul_eq_mul]
        have hr : star (K u) = 2*(K u).re-K u := by
          apply Complex.ext <;> simp
          ring
        rw [hr]
        ring
      _ = H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • ((K u).re*H u)) hiR.const_smul hiK,
          Real.circleAverage_fun_smul, hR, hK, smul_eq_mul]
        ring
  have hT : Real.circleAverage (fun u => K u*star (H u)) 0 1 = H 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hiS
    have h0 : star (H 0) = H 0 := by
      apply Complex.ext <;> simp [hH0]
    change Real.circleAverage (fun u => star (star (K u)*H u)) 0 1 =
      star (Real.circleAverage (fun u => star (K u)*H u) 0 1) at hh
    rw [hS, h0] at hh
    simpa only [star_mul, star_star, mul_comm] using! hh
  calc
    _ = Real.circleAverage (fun u => (2 : ℂ)⁻¹ • (K u*H u+K u*star (H u))) 0 1 := by
      congr 1
      funext u
      change K u*(H u).re = (2 : ℂ)⁻¹*(K u*H u+K u*star (H u))
      have hr : ((H u).re : ℂ) = (2 : ℂ)⁻¹*(H u+star (H u)) := by
        apply Complex.ext <;> simp
        ring
      rw [hr]
      ring
    _ = H z := by
      have hiT : CircleIntegrable (fun u => K u*star (H u)) 0 1 :=
        (hKc.mul hHc.star).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.circleAverage_fun_smul, Real.circleAverage_fun_add hiK hiT, hK, hT,
        smul_eq_mul]
      ring

/-- A strictly contractive polynomial on the unit circle has a normalized zero-free polynomial
complement represented inside the disk by the exponential of the stated Schwarz integral of
the logarithmic residual. -/
theorem canonical_complement_schwarz_representation :
    ∀ (P : Polynomial ℂ) (d : ℕ) (δ : ℝ), P.natDegree ≤ d → 0 < δ → δ < 1 →
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) →
      ∃ Q : Polynomial ℂ, Q.natDegree ≤ d ∧ 0 < (Q.eval 0).re ∧ (Q.eval 0).im = 0 ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) ∧
        (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) ∧
        (∀ z : ℂ, ‖z‖ < 1 → Q.eval z = Complex.exp
          ((1/(4*Real.pi) : ℝ) •
            (∫ θ : ℝ in 0..2*Real.pi,
              (Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
              ((Real.log (1-‖P.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ)))) := by
  intro P d δ hp hδ hδ1 hP
  obtain ⟨Q, hQd, hQr, hQi, hQn, hQc⟩ := canonical_complement_outer_exists P d δ hp hδ hδ1 hP
  obtain ⟨H, hHd, hHe⟩ := polynomial_disk_log_exists Q hQn
  let c : ℂ := (Real.log (Q.eval 0).re : ℝ)
  have hQ0 : Q.eval 0 ≠ 0 := hQn 0 (by simp)
  have hc : Complex.exp c = Q.eval 0 := by
    simp only [c, ← Complex.ofReal_exp, Real.exp_log hQr]
    apply Complex.ext <;> simp [hQi]
  let L : ℂ → ℂ := fun z => H z+c-H 0
  have hLd : DiffContOnCl ℂ L (Metric.ball 0 1) :=
    (hHd.add diffContOnCl_const).sub diffContOnCl_const
  have hLe (z : ℂ) (hz : ‖z‖ ≤ 1) : Complex.exp (L z) = Q.eval z := by
    dsimp [L]
    rw [Complex.exp_sub, Complex.exp_add, hHe z hz, hc, hHe 0 (by simp)]
    exact mul_div_cancel_right₀ _ hQ0
  have hL0 : (L 0).im = 0 := by simp [L, c]
  have hLre (u : ℂ) (hu : ‖u‖ = 1) :
      (L u).re = (1/2 : ℝ)*Real.log (1-‖P.eval u‖^2) := by
    have hs : 1-‖P.eval u‖^2 = ‖Q.eval u‖^2 := by linarith [hQc u hu]
    have hl : Real.log ‖Q.eval u‖ = (L u).re := by
      rw [← hLe u hu.le, Complex.norm_exp, Real.log_exp]
    rw [hs, Real.log_pow, hl]
    ring
  refine ⟨Q, hQd, hQr, hQi, hQn, hQc, ?_⟩
  intro z hz
  rw [← hLe z hz.le]
  congr 1
  calc
    L z = Real.circleAverage (fun u : ℂ => (u+z)/(u-z)*(L u).re) 0 1 :=
      (schwarz_circle_average L hLd hL0 z hz).symm
    _ = (1/(4*Real.pi) : ℝ) •
        (∫ θ : ℝ in 0..2*Real.pi,
          (Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
          ((Real.log (1-‖P.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ)) := by
      rw [Real.circleAverage_def]
      have hf : (fun θ : ℝ => (circleMap 0 1 θ+z)/(circleMap 0 1 θ-z)*(L (circleMap 0 1 θ)).re) =
          (fun θ : ℝ => (1/2 : ℝ) •
            ((Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
              ((Real.log (1-‖P.eval (Complex.exp (θ*Complex.I))‖^2) : ℝ) : ℂ))) := by
        funext θ
        simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
        rw [hLre _ (Complex.norm_exp_ofReal_mul_I θ)]
        simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat, Complex.real_smul]
        ring
      rw [hf, intervalIntegral.integral_smul, smul_smul]
      congr 1
      field_simp
      ring

/-- For `0 < δ` and `‖z‖ ≤ 1 - δ`, bounds `‖Complex.log (1 - z)‖` by `Real.log (1 / δ)`. -/
theorem canonicalComplement_log_bound (z : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hz : ‖z‖ ≤ 1-δ) :
    ‖Complex.log (1-z)‖ ≤ Real.log (1/δ) := by
  have hzn : ‖z‖ < 1 := by linarith
  have hs := Complex.hasSum_taylorSeries_neg_log hzn
  have hs' : HasSum (fun n : ℕ => z^(n+1)/(n+1)) (-Complex.log (1-z)) := by
    have hs0 : HasSum (fun n : ℕ => z^n/(n : ℂ))
        (-Complex.log (1-z) + ∑ i ∈ Finset.range 1, z^i/(i : ℂ)) := by
      simpa using! hs
    simpa only [Nat.cast_add, Nat.cast_one] using! (hasSum_nat_add_iff 1).mpr hs0
  have ht := Real.hasSum_pow_div_log_of_abs_lt_one (x := ‖z‖)
    (by simpa only [abs_of_nonneg (norm_nonneg z)] using! hzn)
  have hh : ‖Complex.log (1-z)‖ ≤ -Real.log (1-‖z‖) := by
    simpa only [norm_neg] using! hs'.norm_le_of_bounded ht (fun n => by
      simp only [norm_div, norm_pow]
      have he : ‖(n : ℂ)+1‖ = (n : ℝ)+1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using! Complex.norm_natCast (n+1)
      rw [he])
  rw [one_div, Real.log_inv]
  exact hh.trans (neg_le_neg (Real.log_le_log hδ (by linarith)))

/-- A uniform norm bound for a polynomial on the unit circle also holds throughout the closed
unit disk. -/
theorem canonicalComplement_polynomial_disk_bound (P : Polynomial ℂ) (c : ℝ)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ c)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖P.eval z‖ ≤ c := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.ball (0 : ℂ) 1) Metric.isBounded_ball
    P.differentiable.diffContOnCl
  · intro u hu
    rw [frontier_ball 0 (by norm_num : (1 : ℝ) ≠ 0)] at hu
    exact hP u (by simpa [Metric.mem_sphere, dist_eq_norm] using! hu)
  · rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    simpa [Metric.mem_closedBall, dist_eq_norm] using! hz

/-- Outside the unit disk, a polynomial of degree at most `d` with boundary norm at most `c` is
bounded by `‖z‖^d * c`. -/
theorem canonicalComplement_polynomial_exterior_bound (P : Polynomial ℂ) (d : ℕ)
    (c : ℝ) (hp : P.natDegree ≤ d)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ c)
    (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖P.eval z‖ ≤ ‖z‖^d*c := by
  have hr : ∀ u : ℂ, ‖u‖ = 1 → ‖P.reverse.eval u‖ ≤ c := by
    intro u hu
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
    letI := invertibleOfNonzero (inv_ne_zero hu0)
    have he := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) u⁻¹ P
    simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at he
    have hn := congrArg norm he
    simp only [norm_mul, norm_pow, norm_inv, hu, inv_one, one_pow, mul_one] at hn
    rw [hn]
    exact hP u⁻¹ (by simp [hu])
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  letI := invertibleOfNonzero hz0
  have he := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z P
  simp only [invOf_eq_inv, Polynomial.eval₂_id] at he
  rw [← he, norm_mul, norm_pow, mul_comm]
  apply mul_le_mul (pow_le_pow_right₀ hz hp)
    (canonicalComplement_polynomial_disk_bound P.reverse c hr z⁻¹ ?_)
    (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hz

/-- Under the stated degree, margin, and radius conditions, bounds `‖P(z) * star (P((star
z)⁻¹))‖` by `1 - δ` on the annulus `1/r ≤ ‖z‖ ≤ r`. -/
theorem canonicalComplement_annulus_residual_bound (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (z : ℂ) (hzl : 1/r ≤ ‖z‖) (hzu : ‖z‖ ≤ r) :
    ‖P.eval z*star (P.eval ((star z)⁻¹))‖ ≤ 1-δ := by
  have hr0 : 0 < r := by linarith
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (one_div_pos.mpr hr0) hzl
  have hi : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by simp
  have hir : ‖(star z)⁻¹‖ ≤ r := by
    rw [hi]
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hr0) hzl
    simpa only [one_div, inv_inv] using! h
  have houter (u : ℂ) (hu : 1 ≤ ‖u‖) (hur : ‖u‖ ≤ r) : ‖P.eval u‖ ≤ 1 := by
    apply (canonicalComplement_polynomial_exterior_bound P d (1-δ) hp hP u hu).trans
    apply le_trans _ hrc
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hur _) (by linarith)
  rw [norm_mul, norm_star]
  by_cases hz : 1 ≤ ‖z‖
  · have hw : ‖(star z)⁻¹‖ ≤ 1 := by rw [hi]; exact inv_le_one_of_one_le₀ hz
    simpa only [one_mul] using! mul_le_mul (houter z hz hzu)
      (canonicalComplement_polynomial_disk_bound P (1-δ) hP _ hw)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hz' : ‖z‖ ≤ 1 := le_of_not_ge hz
    have hw : 1 ≤ ‖(star z)⁻¹‖ := by rw [hi]; exact one_le_inv₀ hz0 |>.mpr hz'
    simpa only [mul_one] using! mul_le_mul
      (canonicalComplement_polynomial_disk_bound P (1-δ) hP z hz')
      (houter _ hw hir) (norm_nonneg _) (by linarith : 0 ≤ 1-δ)

/-- Under the stated degree, margin, and radius conditions, bounds the logarithmic residual norm
by `log (1 / δ)` on the annulus `1/r ≤ ‖z‖ ≤ r`. -/
theorem canonicalComplement_annulus_log_bound (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (z : ℂ) (hzl : 1/r ≤ ‖z‖) (hzu : ‖z‖ ≤ r) :
    ‖Complex.log (1-P.eval z*star (P.eval ((star z)⁻¹)))‖ ≤ Real.log (1/δ) := by
  exact canonicalComplement_log_bound _ δ hδ
    (canonicalComplement_annulus_residual_bound P d δ r hp hδ hδ1 hr hrc hP z hzl hzu)

/-- Bounds the distance from `Complex.exp z` to one by `Real.exp ‖z‖ - 1`. -/
theorem canonicalComplement_exp_majorant (z : ℂ) :
    ‖Complex.exp z-1‖ ≤ Real.exp ‖z‖-1 := by
  have hc : HasSum (fun n : ℕ => z^n/(n.factorial : ℂ)) (Complex.exp z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using! NormedSpace.expSeries_div_hasSum_exp z
  have hr : HasSum (fun n : ℕ => ‖z‖^n/(n.factorial : ℝ)) (Real.exp ‖z‖) := by
    simpa only [Real.exp_eq_exp_ℝ] using! NormedSpace.expSeries_div_hasSum_exp ‖z‖
  have hc' : HasSum (fun n : ℕ => z^(n+1)/((n+1).factorial : ℂ)) (Complex.exp z-1) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => z^n/(n.factorial : ℂ)) 1).mpr
    simpa using! hc
  have hr' : HasSum (fun n : ℕ => ‖z‖^(n+1)/((n+1).factorial : ℝ)) (Real.exp ‖z‖-1) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => ‖z‖^n/(n.factorial : ℝ)) 1).mpr
    simpa using! hr
  exact hc'.norm_le_of_bounded hr' (fun n => by simp)

/-- For `0 < ε < 1`, the exponential error majorant `exp (2*ε/3) - 1` is strictly less than ε. -/
theorem canonicalComplement_exp_two_thirds_lt (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.exp (2*ε/3)-1 < ε := by
  have hl := strictConcaveOn_log_Ioi.2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) ≠ 2)
    (by linarith : 0 < 1-ε) hε (by ring : 1-ε+ε=1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hl
  have he : (1-ε)*1+ε*2 = 1+ε := by ring
  rw [he] at hl
  have hl2 : 2*ε/3 < Real.log (1+ε) := by nlinarith [Real.log_two_gt_d9]
  have he2 := Real.exp_lt_exp.mpr hl2
  rw [Real.exp_log (by linarith : 0 < 1+ε)] at he2
  linarith

/-- If `‖exp x‖ ≤ 1` and `‖y - x‖ ≤ 2*ε/3` with `0 < ε < 1`, then `‖exp y - exp x‖ < ε`. -/
theorem canonicalComplement_exp_perturbation (x y : ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hx : ‖Complex.exp x‖ ≤ 1)
    (hxy : ‖y-x‖ ≤ 2*ε/3) : ‖Complex.exp y-Complex.exp x‖ < ε := by
  have he : Complex.exp y-Complex.exp x =
      Complex.exp x*(Complex.exp (y-x)-1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    rw [show x+(y-x)=y by ring]
  rw [he, norm_mul]
  calc
    _ ≤ 1*(Real.exp ‖y-x‖-1) := mul_le_mul hx
      (canonicalComplement_exp_majorant (y-x)) (norm_nonneg _) (by norm_num)
    _ ≤ Real.exp (2*ε/3)-1 := by
      rw [one_mul]
      exact sub_le_sub_right (Real.exp_le_exp.mpr hxy) 1
    _ < ε := canonicalComplement_exp_two_thirds_lt ε hε hε1

/-- For `r > 1` and `A > 0`, the stated ceiling threshold on `2*K` implies `A ≤ r^K`. -/
theorem canonicalComplement_threshold_power (r A : ℝ) (K : ℕ)
    (hr : 1 < r) (hA : 0 < A)
    (hN : (Nat.ceil (2/Real.log r*Real.log A) : ℕ) ≤ 2*K) : A ≤ r^K := by
  have hr0 : 0 < r := by linarith
  have hl : 0 < Real.log r := Real.log_pos hr
  have hh := Nat.ceil_le.mp hN
  have hid : 2/Real.log r*Real.log A = (2*Real.log A)/Real.log r := by ring
  rw [hid, div_le_iff₀ hl] at hh
  push_cast at hh
  have hh' : Real.log A ≤ Real.log r*(K : ℝ) := by nlinarith
  calc
    A = Real.exp (Real.log A) := (Real.exp_log hA).symm
    _ ≤ Real.exp (Real.log r*(K : ℝ)) := Real.exp_le_exp.mpr hh'
    _ = r^K := by rw [← Real.rpow_def_of_pos hr0, Real.rpow_natCast]

/-- For a primitive `N`th root and indices below positive `N`, the Fourier character sum is `N`
when the indices agree and zero otherwise. -/
private theorem canonicalComplement_root_orthogonality (N k n : ℕ) (ω : ℂ) (hN : 0 < N)
    (hω : IsPrimitiveRoot ω N) (hk : k < N) (hn : n < N) :
    (∑ j : Fin N, ω^(k*j.val)*ω^(-(n*j.val : ℤ))) =
      if k=n then (N : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hp (j : ℕ) : ω^(k*j)*ω^(-(n*j : ℤ)) = (ω^((k : ℤ)-n))^j := by
    rw [← zpow_natCast ω (k*j), ← zpow_add₀ hω0,
      ← zpow_natCast (ω^((k : ℤ)-n)) j, ← zpow_mul]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (ω^((k : ℤ)-n))^j) N]
  by_cases hkn : k=n
  · simp [hkn]
  · rw [if_neg hkn, geom_sum_eq]
    · have he : (ω^((k : ℤ)-n))^N = 1 := by
        rw [← zpow_natCast (ω^((k : ℤ)-n)) N, ← zpow_mul, mul_comm, zpow_mul, hω.zpow_eq_one]
        simp
      rw [he, sub_self, zero_div]
    · intro he
      rw [zpow_sub₀ hω0, zpow_natCast, zpow_natCast] at he
      exact hkn (hω.pow_inj hk hn (eq_of_div_eq_one he))

/-- A normalized discrete Fourier sum of a polynomial's values at primitive `N`th roots recovers
each coefficient below `N` when its degree is less than `N`. -/
theorem canonicalComplement_polynomial_dft_exact (Q : Polynomial ℂ) (N : ℕ) (hN : 0 < N) (hQ : Q.natDegree < N)
    (ω : ℂ) (hω : IsPrimitiveRoot ω N) (n : ℕ) (hn : n < N) :
    (N : ℂ)⁻¹*∑ j : Fin N, Q.eval (ω^j.val)*ω^(-(n*j.val : ℤ)) = Q.coeff n := by
  have he (j : Fin N) : Q.eval (ω^j.val) =
      ∑ k ∈ Finset.range N, Q.coeff k*ω^(k*j.val) := by
    rw [Polynomial.eval_eq_sum_range' hQ]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pow_mul, Nat.mul_comm j.val]
  calc
    _ = (N : ℂ)⁻¹*∑ k ∈ Finset.range N,
        Q.coeff k*(∑ j : Fin N, ω^(k*j.val)*ω^(-(n*j.val : ℤ))) := by
      simp_rw [he, Finset.sum_mul]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (N : ℂ)⁻¹*∑ k ∈ Finset.range N,
        Q.coeff k*(if k=n then (N : ℂ) else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [canonicalComplement_root_orthogonality N k n ω hN hω (Finset.mem_range.mp hk) hn]
    _ = Q.coeff n := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, if_pos hn]
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp

/-- The principal complex logarithm of one minus the product of `P(z)` and the
conjugate-coefficient polynomial evaluated at `z⁻¹`. -/
def canonicalComplementLogResidual (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  Complex.log (1-P.eval z*(P.map (starRingEnd ℂ)).eval z⁻¹)

/-- Expresses `canonicalComplementLogResidual` using the conjugate value of `P` at `(star z)⁻¹`. -/
theorem canonicalComplementLogResidual_eq (P : Polynomial ℂ) (z : ℂ) :
    canonicalComplementLogResidual P z = Complex.log (1-P.eval z*star (P.eval ((star z)⁻¹))) := by
  have he := Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) ((star z)⁻¹)
  simp only [map_inv₀, starRingEnd_apply, star_star] at he
  rw [canonicalComplementLogResidual, he]

/-- The logarithmic residual is complex differentiable at every point of the stated annulus
under the degree, margin, and radius conditions. -/
theorem canonicalComplementLogResidual_differentiable (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (z : ℂ) (hzl : 1/r ≤ ‖z‖) (hzu : ‖z‖ ≤ r) :
    DifferentiableAt ℂ (canonicalComplementLogResidual P) z := by
  have hr0 : 0 < r := by linarith
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_lt_of_le (one_div_pos.mpr hr0) hzl))
  have he := Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) ((star z)⁻¹)
  simp only [map_inv₀, starRingEnd_apply, star_star] at he
  have hn := canonicalComplement_annulus_residual_bound P d δ r hp hδ hδ1 hr hrc hP z hzl hzu
  rw [← he] at hn
  have hs : 1-P.eval z*(P.map (starRingEnd ℂ)).eval z⁻¹ ∈ Complex.slitPlane := by
    have hn' : ‖-(P.eval z*(P.map (starRingEnd ℂ)).eval z⁻¹)‖ < 1 := by
      rw [norm_neg]; linarith
    simpa only [sub_eq_add_neg] using! Complex.mem_slitPlane_of_norm_lt_one hn'
  have hd : DifferentiableAt ℂ
      (fun u : ℂ => 1-P.eval u*(P.map (starRingEnd ℂ)).eval u⁻¹) z := by
    fun_prop (disch := exact hz0)
  exact hd.clog hs

/-- The contour-integral coefficient of the logarithmic residual at the nonnegative frequency
`n` on the unit circle. -/
def canonicalComplementLogCoefficient (P : Polynomial ℂ) (n : ℕ) : ℂ :=
  (2*Real.pi*Complex.I : ℂ)⁻¹ •
    ∮ z : ℂ in C(0,1), z^(-((n+1 : ℕ) : ℤ))*canonicalComplementLogResidual P z

/-- Under the stated degree, margin, and radius conditions, the `n`th logarithmic coefficient
has norm at most `log (1 / δ) / r^n`. -/
theorem canonicalComplementLogCoefficient_bound (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) (n : ℕ) :
    ‖canonicalComplementLogCoefficient P n‖ ≤ Real.log (1/δ)/r^n := by
  have hr0 : 0 < r := by linarith
  have hi1 : 1/r ≤ 1 := by
    simpa using! one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr
  let f : ℂ → ℂ := fun z => z^(-((n+1 : ℕ) : ℤ))*canonicalComplementLogResidual P z
  have hd (z : ℂ) (hz1 : 1 ≤ ‖z‖) (hzr : ‖z‖ ≤ r) : DifferentiableAt ℂ f z := by
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    have hdp : DifferentiableAt ℂ (fun u : ℂ => u^(-((n+1 : ℕ) : ℤ))) z := by
      simpa only [zpow_neg, zpow_natCast] using!
        (differentiableAt_id.pow (n+1)).inv (pow_ne_zero _ hz0)
    exact hdp.mul (canonicalComplementLogResidual_differentiable P d δ r hp hδ hδ1 hr hrc hP z
      (hi1.trans hz1) hzr)
  have hc : ContinuousOn f (Metric.closedBall 0 r \ Metric.ball 0 1) := by
    intro z hz
    have hz' : ‖z‖ ≤ r ∧ 1 ≤ ‖z‖ := by
      simpa only [Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
          not_lt] using! hz
    exact (hd z hz'.2 hz'.1).continuousAt.continuousWithinAt
  have he : (∮ z in C(0,r), f z) = ∮ z in C(0,1), f z := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (by norm_num : (0 : ℝ) < 1) hr Set.countable_empty hc
    intro z hz
    have hz' : ‖z‖ < r ∧ 1 < ‖z‖ := by
      simpa only [Set.mem_diff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        Set.mem_empty_iff_false, not_false_eq_true, and_true, not_le] using! hz
    exact hd z hz'.2.le hz'.1.le
  unfold canonicalComplementLogCoefficient
  change ‖(2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ z in C(0,1), f z‖ ≤ _
  rw [← he]
  have hb : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      ‖f z‖ ≤ (r^(n+1))⁻¹*Real.log (1/δ) := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using! hz
    dsimp only [f]
    rw [norm_mul, norm_zpow, hzr, zpow_neg, zpow_natCast, canonicalComplementLogResidual_eq]
    exact mul_le_mul_of_nonneg_left
      (canonicalComplement_annulus_log_bound P d δ r hp hδ hδ1 hr hrc hP z
        (by rw [hzr]; exact hi1.trans hr) hzr.le) (by positivity)
  apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr0.le hb).trans
  have hpow : r^n ≠ 0 := pow_ne_zero _ hr0.ne'
  rw [pow_succ]
  field_simp
  exact le_rfl

local instance canonicalComplementPeriodPos : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Identifies a nonnegative Fourier coefficient of a circle-parametrized function with its
circle average weighted by the corresponding inverse power. -/
theorem canonicalComplement_fourierCoeff_eq_circleAverage (f : ℂ → ℂ) (n : ℕ) :
    fourierCoeff (T := 2*Real.pi) (fun θ => f (θ.toCircle : ℂ)) (n : ℤ) =
      Real.circleAverage (fun z => z^(-(n : ℤ))*f z) 0 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc (θ : ℝ) : (AddCircle.toCircle (θ : AddCircle (2*Real.pi)) : ℂ) =
      Complex.exp (θ*Complex.I) := by
    rw [← fourier_one, fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, Real.circleAverage]
  simp only [zero_add, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, fourier_coe_apply, circleMap, zero_add, Complex.ofReal_one, one_mul]
  rw [hc, ← Complex.exp_int_mul]
  congr 1
  congr 1
  push_cast
  field_simp

/-- Expresses the logarithmic contour coefficient as the unit-circle average of the logarithmic
residual times the inverse `n`th power. -/
theorem canonicalComplementLogCoefficient_eq_circleAverage (P : Polynomial ℂ) (n : ℕ) : canonicalComplementLogCoefficient P n =
    Real.circleAverage (fun z => z^(-(n : ℤ))*canonicalComplementLogResidual P z) 0 1 := by
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  unfold canonicalComplementLogCoefficient
  congr 1
  apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using! hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz1]; norm_num)
  simp only [sub_zero, smul_eq_mul]
  rw [← zpow_neg_one, ← mul_assoc, ← zpow_add₀ hz0]
  rw [show -((n+1 : ℕ) : ℤ) = (-1 : ℤ)+(-(n : ℤ)) by omega]

/-- The `n`th logarithmic contour coefficient equals the nonnegative Fourier coefficient of the
residual pulled back to `AddCircle (2*π)`. -/
theorem canonicalComplementLogCoefficient_eq_fourierCoeff (P : Polynomial ℂ) (n : ℕ) :
    canonicalComplementLogCoefficient P n =
      fourierCoeff (T := 2*Real.pi)
        (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ)) (n : ℤ) := by
  rw [canonicalComplementLogCoefficient_eq_circleAverage,
    canonicalComplement_fourierCoeff_eq_circleAverage]

/-- Bounds the norm of the nonnegative `n`th Fourier coefficient of the logarithmic residual by
`log (1 / δ) / r^n` under the stated hypotheses. -/
theorem canonicalComplement_fourierCoeff_bound (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) (n : ℕ) :
    ‖fourierCoeff (T := 2*Real.pi)
      (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ)) (n : ℤ)‖ ≤
        Real.log (1/δ)/r^n := by
  rw [← canonicalComplementLogCoefficient_eq_fourierCoeff]
  exact canonicalComplementLogCoefficient_bound P d δ r hp hδ hδ1 hr hrc hP n

/-- On the unit circle, the logarithmic residual equals the real logarithm of `1 - ‖P.eval
z‖^2`, embedded in the complex numbers. -/
theorem canonicalComplementLogResidual_circle (P : Polynomial ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (z : ℂ) (hz : ‖z‖ = 1) :
    canonicalComplementLogResidual P z =
      ((Real.log (1-‖P.eval z‖^2) : ℝ) : ℂ) := by
  have hinv : (star z)⁻¹ = z := by
    apply inv_eq_of_mul_eq_one_left
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  have hpos : 0 ≤ 1-‖P.eval z‖^2 := by
    nlinarith [hP z hz, norm_nonneg (P.eval z)]
  rw [canonicalComplementLogResidual_eq, hinv]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using! (Complex.ofReal_log hpos).symm

/-- For a real-valued complex function on the circle, the Fourier coefficient at `-k` is the
conjugate of the coefficient at `k`. -/
private theorem canonicalComplement_fourierCoeff_neg_of_real
    (f : AddCircle (2*Real.pi) → ℂ) (hf : ∀ x, star (f x) = f x) (k : ℤ) :
    fourierCoeff f (-k) = star (fourierCoeff f k) := by
  unfold fourierCoeff
  rw [Complex.star_def, ← integral_conj]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [smul_eq_mul, map_mul, ← fourier_neg, neg_neg]
    rw [← Complex.star_def, hf])

/-- Bounds the norm of every integer Fourier coefficient of the logarithmic residual by `log (1
/ δ) / r^|k|` under the stated hypotheses. -/
theorem canonicalComplement_fourierCoeff_int_bound
    (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 ≤ r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) (k : ℤ) :
    ‖fourierCoeff (T := 2*Real.pi)
      (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ)) k‖ ≤
        Real.log (1/δ)/r^k.natAbs := by
  have hreal (θ : AddCircle (2*Real.pi)) :
      star (canonicalComplementLogResidual P (θ.toCircle : ℂ)) =
        canonicalComplementLogResidual P (θ.toCircle : ℂ) := by
    rw [canonicalComplementLogResidual_circle P δ hδ hδ1 hP _ θ.toCircle.norm_coe]
    simp
  cases k with
  | ofNat n => exact canonicalComplement_fourierCoeff_bound P d δ r hp hδ hδ1 hr hrc hP n
  | negSucc n =>
    have hs := canonicalComplement_fourierCoeff_neg_of_real
      (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ)) hreal (n+1 : ℕ)
    have hb := canonicalComplement_fourierCoeff_bound P d δ r hp hδ hδ1 hr hrc hP (n+1)
    change ‖fourierCoeff (T := 2*Real.pi)
      (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ))
        (-((n+1 : ℕ) : ℤ))‖ ≤ Real.log (1/δ)/r^(n+1)
    rw [hs, norm_star]
    exact hb

/-- For an admissible annulus radius `r > 1`, the integer Fourier coefficients of the
logarithmic residual are summable. -/
theorem canonicalComplement_fourierCoeff_summable
    (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 < r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) :
    Summable (fourierCoeff (T := 2*Real.pi)
      (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ))) := by
  have hr0 : 0 < r := by linarith
  have hgeom : Summable (fun n : ℕ => (r⁻¹)^n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
      ((inv_lt_one₀ hr0).mpr hr)
  have hnat : Summable (fun n : ℕ => Real.log (1/δ)/r^n) := by
    simpa only [div_eq_mul_inv, inv_pow] using! hgeom.mul_left (Real.log (1/δ))
  have hint : Summable (fun k : ℤ => Real.log (1/δ)/r^k.natAbs) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa only [Int.natAbs_natCast, Int.natAbs_neg] using! hnat
  exact hint.of_norm_bounded
    (canonicalComplement_fourierCoeff_int_bound P d δ r hp hδ hδ1 hr.le hrc hP)

/-- Under the stated strict-margin and annulus hypotheses, the Fourier series of the logarithmic
residual sums to its value at every circle point. -/
theorem canonicalComplement_fourier_reconstruction
    (P : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 < r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (θ : AddCircle (2*Real.pi)) :
    HasSum (fun k : ℤ =>
      fourierCoeff (T := 2*Real.pi)
        (fun u => canonicalComplementLogResidual P (u.toCircle : ℂ)) k * fourier k θ)
      (canonicalComplementLogResidual P (θ.toCircle : ℂ)) := by
  have hcont : Continuous (fun θ : AddCircle (2*Real.pi) =>
      canonicalComplementLogResidual P (θ.toCircle : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hd := canonicalComplementLogResidual_differentiable P d δ 1 hp hδ hδ1
      (by norm_num) (by simpa using! (show 1-δ ≤ 1 by linarith)) hP
      (θ.toCircle : ℂ) (by simp) (by simp)
    exact hd.continuousAt.comp (f := fun u : AddCircle (2*Real.pi) => (u.toCircle : ℂ))
      (show ContinuousAt (fun u : AddCircle (2*Real.pi) => (u.toCircle : ℂ)) θ by fun_prop)
  let f : C(AddCircle (2*Real.pi), ℂ) := ⟨_, hcont⟩
  have hs : Summable (fourierCoeff f) :=
    canonicalComplement_fourierCoeff_summable P d δ r hp hδ hδ1 hr hrc hP
  simpa only [smul_eq_mul] using! has_pointwise_sum_fourier_series_of_summable hs θ

/-- A polynomial zero-free on the closed disk and positive real at zero possesses a holomorphic
logarithm continuous on the closed disk whose value at zero is the real logarithm of that
positive value. -/
private theorem canonicalComplement_normalized_log (Q : Polynomial ℂ)
    (hQr : 0 < (Q.eval 0).re) (hQi : (Q.eval 0).im = 0)
    (hQn : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) :
    ∃ L : ℂ → ℂ, DiffContOnCl ℂ L (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → Complex.exp (L z) = Q.eval z) ∧
      L 0 = (Real.log (Q.eval 0).re : ℝ) := by
  obtain ⟨H, hHd, hHe⟩ := polynomial_disk_log_exists Q hQn
  let c : ℂ := (Real.log (Q.eval 0).re : ℝ)
  have hQ0 : Q.eval 0 ≠ 0 := hQn 0 (by simp)
  have hc : Complex.exp c = Q.eval 0 := by
    simp only [c, ← Complex.ofReal_exp, Real.exp_log hQr]
    apply Complex.ext <;> simp [hQi]
  let L : ℂ → ℂ := fun z => H z+c-H 0
  refine ⟨L, (hHd.add diffContOnCl_const).sub diffContOnCl_const, ?_, ?_⟩
  · intro z hz
    dsimp [L]
    rw [Complex.exp_sub, Complex.exp_add, hHe z hz, hc, hHe 0 (by simp)]
    exact mul_div_cancel_right₀ _ hQ0
  · simp [L, c]

/-- For a primitive root of positive order `N`, the integer-frequency character sum is `N`
exactly when `N` divides the frequency, and zero otherwise. -/
private theorem canonicalComplement_root_orthogonality_int (N : ℕ) (k : ℤ)
    (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) :
    (∑ j : Fin N, ω^(k*j.val)) = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hpower (j : ℕ) : ω^(k*j) = (ω^k)^j := by
    rw [← zpow_natCast (ω^k), ← zpow_mul]
  simp_rw [hpower]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (ω^k)^j) N]
  by_cases hk : (N : ℤ) ∣ k
  · rw [(hω.zpow_eq_one_iff_dvd k).mpr hk]
    simp [hk]
  · rw [if_neg hk, geom_sum_eq]
    · have he : (ω^k)^N = 1 := by
        rw [← zpow_natCast (ω^k), ← zpow_mul, mul_comm, zpow_mul, hω.zpow_eq_one]
        simp
      rw [he, sub_self, zero_div]
    · exact fun he => hk ((hω.zpow_eq_one_iff_dvd k).mp he)

/-- For a circle-integrable logarithmic residual, its nonnegative coefficient series at an
interior disk point sums to the stated Cauchy-kernel circle average. -/
private theorem canonicalComplement_positive_series_cauchy
    (P : Polynomial ℂ) (hi : CircleIntegrable (canonicalComplementLogResidual P) 0 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => canonicalComplementLogCoefficient P n * z^n)
      (Real.circleAverage (fun u : ℂ => u/(u-z)*canonicalComplementLogResidual P u) 0 1) := by
  have hs := hasSum_cauchyPowerSeries_integral hi hz
  have hterm (n : ℕ) :
      canonicalComplementLogCoefficient P n * z^n =
        cauchyPowerSeries (canonicalComplementLogResidual P) 0 1 n (fun _ => z) := by
    rw [cauchyPowerSeries_apply, canonicalComplementLogCoefficient]
    simp only [smul_eq_mul, sub_zero]
    calc
      _ = (2*Real.pi*Complex.I : ℂ)⁻¹ *
          (z^n * ∮ u in C(0,1), u^(-((n+1 : ℕ) : ℤ))*canonicalComplementLogResidual P u) := by ring
      _ = _ := by
        rw [← circleIntegral.integral_const_mul]
        congr 1
        apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
        intro u hu
        simp only [zpow_neg, zpow_natCast, div_pow, pow_succ]
        ring
  have hvalue : Real.circleAverage
      (fun u : ℂ => u/(u-z)*canonicalComplementLogResidual P u) 0 1 =
      (2*Real.pi*Complex.I : ℂ)⁻¹ •
        ∮ u in C(0,1), (u-(0+z))⁻¹ • canonicalComplementLogResidual P u := by
    rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
    simp only [sub_zero, zero_add, smul_eq_mul]
    congr 1
    apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using! hu
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu1]; norm_num)
    simp only [div_eq_mul_inv]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  rw [hvalue]
  simpa only [← hterm] using! hs

/-- The nonnegative logarithmic coefficient series with half of its constant coefficient
subtracted. -/
def canonicalComplementLogSeries (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  (∑' n : ℕ, canonicalComplementLogCoefficient P n * z^n) -
    canonicalComplementLogCoefficient P 0 / 2

/-- For a normalized zero-free complement and the stated strict-margin and annulus conditions,
exponentiating `canonicalComplementLogSeries P` recovers the complement on the closed unit
disk. -/
theorem canonicalComplementLogSeries_exp (P Q : Polynomial ℂ) (d : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 < r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ)
    (hQr : 0 < (Q.eval 0).re) (hQi : (Q.eval 0).im = 0)
    (hQn : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0)
    (hQc : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Complex.exp (canonicalComplementLogSeries P z) = Q.eval z := by
  obtain ⟨L, hLd, hLe, hL0⟩ := canonicalComplement_normalized_log Q hQr hQi hQn
  have hL0im : (L 0).im = 0 := by rw [hL0]; simp
  have hLre (u : ℂ) (hu : ‖u‖ = 1) :
      ((L u).re : ℂ) = canonicalComplementLogResidual P u / 2 := by
    have hs : 1-‖P.eval u‖^2 = ‖Q.eval u‖^2 := by linarith [hQc u hu]
    have hl : Real.log ‖Q.eval u‖ = (L u).re := by
      rw [← hLe u hu.le, Complex.norm_exp, Real.log_exp]
    rw [canonicalComplementLogResidual_circle P δ hδ hδ1 hP u hu, hs, Real.log_pow, hl]
    push_cast
    ring
  have hSc : ContinuousOn (canonicalComplementLogResidual P) (Metric.sphere 0 1) := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using! hu
    exact (canonicalComplementLogResidual_differentiable P d δ 1 hp hδ hδ1
      (by norm_num) (by simpa using! (show 1-δ ≤ 1 by linarith)) hP u
      (by simp [hu1]) (by simp [hu1])).continuousAt.continuousWithinAt
  have hiS : CircleIntegrable (canonicalComplementLogResidual P) 0 1 :=
    hSc.circleIntegrable (by norm_num)
  have hid (w : ℂ) (hw : ‖w‖ < 1) : canonicalComplementLogSeries P w = L w := by
    let C : ℂ → ℂ := fun u => u/(u-w)
    have hden (u : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1) : u-w ≠ 0 := by
      intro he
      have he' : u = w := sub_eq_zero.mp he
      have hu' : ‖u‖ = 1 := by simpa using! hu
      rw [he'] at hu'
      linarith
    have hCc : ContinuousOn C (Metric.sphere (0 : ℂ) 1) := by
      dsimp [C]
      fun_prop (disch := exact hden _ ‹_›)
    have hiCS : CircleIntegrable (fun u => C u*canonicalComplementLogResidual P u) 0 1 :=
      (hCc.mul hSc).circleIntegrable (by norm_num)
    have hzero : canonicalComplementLogCoefficient P 0 =
        Real.circleAverage (canonicalComplementLogResidual P) 0 1 := by
      simp [canonicalComplementLogCoefficient_eq_circleAverage]
    have hsum := (canonicalComplement_positive_series_cauchy P hiS w hw).tsum_eq
    have hsch := schwarz_circle_average L hLd hL0im w hw
    calc
      canonicalComplementLogSeries P w =
          Real.circleAverage (fun u => C u*canonicalComplementLogResidual P u) 0 1 -
            Real.circleAverage (canonicalComplementLogResidual P) 0 1 / 2 := by
        rw [canonicalComplementLogSeries, hsum, hzero]
      _ = Real.circleAverage (fun u : ℂ => (u+w)/(u-w)*(L u).re) 0 1 := by
        calc
          _ = Real.circleAverage (fun u =>
              (C u*canonicalComplementLogResidual P u) -
                (2 : ℂ)⁻¹ • canonicalComplementLogResidual P u) 0 1 := by
            have hsub := Real.circleAverage_fun_sub
              (f₁ := fun u => C u*canonicalComplementLogResidual P u)
              (f₂ := fun u => (2 : ℂ)⁻¹ • canonicalComplementLogResidual P u)
              hiCS hiS.const_smul
            have hmul : Real.circleAverage
                (fun u => (2 : ℂ)⁻¹ • canonicalComplementLogResidual P u) 0 1 =
                (2 : ℂ)⁻¹ • Real.circleAverage (canonicalComplementLogResidual P) 0 1 :=
              Real.circleAverage_fun_smul
            rw [hmul] at hsub
            simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using! hsub.symm
          _ = _ := by
            apply Real.circleAverage_congr_sphere
            intro u hu
            have hu1 : ‖u‖ = 1 := by simpa using! hu
            (try dsimp only)
            rw [hLre u hu1]
            dsimp [C]
            field_simp [hden u (by simpa using! hu)]
            ring
      _ = L w := hsch
  have hr0 : 0 < r := by linarith
  have hgeom := (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
    ((inv_lt_one₀ hr0).mpr hr)).mul_left (Real.log (1/δ))
  have hseries : ContinuousOn (canonicalComplementLogSeries P) (Metric.closedBall 0 1) := by
    apply ContinuousOn.sub ?_ continuousOn_const
    apply continuousOn_tsum (fun _ => by fun_prop) hgeom
    intro n w hw
    have hwn : ‖w‖ ≤ 1 := by simpa using! hw
    have hpow : ‖w^n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hwn
    calc
      ‖canonicalComplementLogCoefficient P n * w^n‖ ≤
          ‖canonicalComplementLogCoefficient P n‖ := by
        rw [norm_mul]
        simpa using! mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ ≤ Real.log (1/δ)/r^n :=
        canonicalComplementLogCoefficient_bound P d δ r hp hδ hδ1 hr.le hrc hP n
      _ = Real.log (1/δ)*(r⁻¹)^n := by rw [div_eq_mul_inv, inv_pow]
  have heq : Set.EqOn (fun w => Complex.exp (canonicalComplementLogSeries P w))
      (fun w => Q.eval w) (Metric.ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa using! hw
    (try dsimp only)
    rw [hid w hwn]
    exact hLe w hwn.le
  have hclosed := heq.of_subset_closure hseries.cexp (by fun_prop)
    Metric.ball_subset_closedBall (by rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)])
  exact hclosed (by simpa using! hz)

/-- A normalized Fourier sum of samples of a summable integer-frequency series equals the sum of
coefficients in the selected residue class modulo `N`. -/
theorem canonicalComplement_sample_alias (N : ℕ) (n : ℤ) (ω : ℂ)
    (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (hωnorm : ‖ω‖ = 1)
    (a : ℤ → ℂ) (ha : Summable a) (samples : Fin N → ℂ)
    (hs : ∀ j : Fin N, HasSum (fun k : ℤ => a k * ω^(k*j.val)) (samples j)) :
    (N : ℂ)⁻¹ * ∑ j : Fin N, samples j * ω^(-(n*j.val)) =
      ∑' k : ℤ, if (N : ℤ) ∣ k-n then a k else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hterms (j : Fin N) : Summable (fun k : ℤ => a k * ω^((k-n)*j.val)) := by
    apply ha.norm.of_norm_bounded
    intro k
    simp only [norm_mul, norm_zpow, hωnorm, one_zpow, mul_one]
    exact le_rfl
  have hcomm := Summable.tsum_finsetSum
    (s := (Finset.univ : Finset (Fin N))) (fun j _ => hterms j)
  have hsample (j : Fin N) : samples j * ω^(-(n*j.val)) =
      ∑' k : ℤ, a k * ω^((k-n)*j.val) := by
    rw [← (hs j).tsum_eq, ← (hs j).summable.tsum_mul_right]
    apply tsum_congr
    intro k
    rw [mul_assoc, ← zpow_add₀ hω0]
    congr 2
    ring
  simp_rw [hsample]
  rw [← hcomm]
  have hsum : Summable (fun k : ℤ => ∑ j : Fin N, a k * ω^((k-n)*j.val)) :=
    summable_sum (fun j _ => hterms j)
  rw [← hsum.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← Finset.mul_sum, canonicalComplement_root_orthogonality_int N (k-n) ω hN hω]
  by_cases hk : (N : ℤ) ∣ k-n
  · simp only [hk, if_true]
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  · simp [hk]

/-- The discrete Fourier coefficient of sampled real logarithmic residual values equals the sum
of the continuous Fourier coefficients congruent to that frequency modulo `N`. -/
theorem canonicalComplement_actual_sample_alias
    (P : Polynomial ℂ) (d N : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 < r) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) (hN : 0 < N) (n : ℤ) :
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
    (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val)) =
      ∑' k : ℤ, if (N : ℤ) ∣ k-n then
        fourierCoeff (T := 2*Real.pi)
          (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ)) k else 0 := by
  (try dsimp only)
  let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
  have hω : IsPrimitiveRoot ω N := by
    convert! Complex.isPrimitiveRoot_exp N hN.ne' using 1
    dsimp [ω]
    congr 1
    push_cast
    ring
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hgrid (j : Fin N) :
      (AddCircle.toCircle ((2*Real.pi*j.val/(N : ℝ) : ℝ) : AddCircle (2*Real.pi)) : ℂ) = ω^j.val := by
    rw [← fourier_one, fourier_coe_apply]
    dsimp [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hmode (j : Fin N) (k : ℤ) :
      fourier k ((2*Real.pi*j.val/(N : ℝ) : ℝ) : AddCircle (2*Real.pi)) = ω^(k*j.val) := by
    rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, hgrid,
      ← zpow_natCast ω j.val, ← zpow_mul]
    congr 1
    ring
  apply canonicalComplement_sample_alias N n ω hN hω hωnorm _
    (canonicalComplement_fourierCoeff_summable P d δ r hp hδ hδ1 hr hrc hP)
  intro j
  have hs := canonicalComplement_fourier_reconstruction P d δ r hp hδ hδ1 hr hrc hP
    ((2*Real.pi*j.val/(N : ℝ) : ℝ) : AddCircle (2*Real.pi))
  simp_rw [hmode, hgrid] at hs
  rw [canonicalComplementLogResidual_circle P δ hδ hδ1 hP _ (by simp [norm_pow, hωnorm])] at hs
  exact hs

/-- The periodic frequency weight selecting residues from zero through `K` modulo `2*K`, with
weight one half at residue zero. -/
private def canonicalComplementProjectionWeight (K : ℕ) (k : ℤ) : ℝ :=
  if k % (2*K : ℕ) = 0 then 1/2 else if k % (2*K : ℕ) ≤ K then 1 else 0
/-- The frequency weight equal to one half at zero, one at positive frequencies, and zero at
negative frequencies. -/
private def canonicalComplementOuterWeight (k : ℤ) : ℝ := if k=0 then 1/2 else if 0<k then 1 else 0

/-- The pointwise difference between the periodic projection weight and the outer-series weight
has absolute value at most one. -/
private theorem canonicalComplementProjectionWeight_bound (K : ℕ) (k : ℤ) : |canonicalComplementProjectionWeight K k-canonicalComplementOuterWeight k| ≤ 1 := by
  unfold canonicalComplementProjectionWeight canonicalComplementOuterWeight
  split_ifs <;> norm_num

/-- For positive `K` and frequencies of absolute value less than `K`, the periodic projection
weight equals the outer-series weight. -/
private theorem canonicalComplementProjectionWeight_low (K : ℕ) (hK : 0 < K) (k : ℤ) (hk : k.natAbs < K) : canonicalComplementProjectionWeight K k = canonicalComplementOuterWeight k := by
  cases k with
  | ofNat n =>
    have hn : n < K := hk
    have he : (n : ℤ) % (2*K : ℕ) = n := Int.emod_eq_of_lt (by omega) (by omega)
    change canonicalComplementProjectionWeight K (n : ℤ) = canonicalComplementOuterWeight (n : ℤ)
    dsimp only [canonicalComplementProjectionWeight, canonicalComplementOuterWeight]
    rw [he]
    split_ifs <;> first | rfl | omega
  | negSucc n =>
    have hn : n+1 < K := hk
    have he : (Int.negSucc n) % (2*K : ℕ) = (2*K : ℕ)-(n+1) := by
      change (-(n+1 : ℤ)) % (2*K : ℕ) = (2*K : ℕ)-(n+1)
      push_cast
      rw [show -(n+1 : ℤ) = (2*(K:ℤ)-(n+1))-2*K by ring, Int.sub_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    change canonicalComplementProjectionWeight K (-(n+1 : ℤ)) = canonicalComplementOuterWeight
        (-(n+1 : ℤ))
    dsimp only [canonicalComplementProjectionWeight, canonicalComplementOuterWeight]
    change (-(n+1 : ℤ)) % (2*K : ℕ) = (2*K : ℕ)-(n+1) at he
    rw [he]
    split_ifs <;> first | rfl | omega

/-- For positive `K`, summing the half-weighted zero mode and unit-weighted modes through `K` in
the selected residue class gives the periodic projection weight. -/
private theorem canonicalComplementProjectionWeight_filtered (K : ℕ) (hK : 0 < K) (k : ℤ) :
    (∑ l ∈ Finset.range (K+1), if ((2*K : ℕ) : ℤ) ∣ k-l then
      (if l=0 then (1/2 : ℝ) else 1) else 0) = canonicalComplementProjectionWeight K k := by
  have hN : (2*K : ℤ) ≠ 0 := by omega
  obtain ⟨v, hv⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k hN)
  have hv' : k % ((2*K : ℕ) : ℤ) = v := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hv
  have hfilter (l : ℕ) (hl : l ∈ Finset.range (K+1)) :
      ((2*K : ℕ) : ℤ) ∣ k-l ↔ v=l := by
    have hln : l < K+1 := Finset.mem_range.mp hl
    have hlmod : (l : ℤ) % (2*K : ℕ) = l := Int.emod_eq_of_lt (by omega) (by omega)
    rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, hv', hlmod]
    exact Nat.cast_inj
  calc
    _ = ∑ l ∈ Finset.range (K+1), if v=l then
        (if l=0 then (1/2 : ℝ) else 1) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [hfilter l hl]
    _ = canonicalComplementProjectionWeight K k := by
      dsimp only [canonicalComplementProjectionWeight]
      rw [hv']
      simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.cast_eq_zero, Nat.cast_le]
      split_ifs <;> first | rfl | omega

/-- For `M ≥ 0` and `r > 1`, the geometric tail from `K` equals `M * r / (r - 1) / r^K`. -/
private theorem canonicalComplement_nat_tail (M r : ℝ) (hM : 0 ≤ M) (hr : 1 < r) (K : ℕ) :
    (∑' n : ℕ, if K ≤ n then M/r^n else 0) = M*r/(r-1)/r^K := by
  have hr0 : 0 < r := by linarith
  have hgeom := (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
    ((inv_lt_one₀ hr0).mpr hr)).mul_left M
  have hbase : Summable (fun n : ℕ => M/r^n) := by
    simpa only [div_eq_mul_inv, inv_pow] using! hgeom
  have hs : Summable (fun n : ℕ => if K ≤ n then M/r^n else 0) := by
    apply hbase.of_norm_bounded
    intro n
    have hpos : 0 ≤ M/r^n := by positivity
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using! (le_refl (M/r^n))
    · simpa only [norm_zero] using! hpos
  have hzero : (∑ n ∈ Finset.range K, if K ≤ n then M/r^n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [show ¬ K ≤ n by have := Finset.mem_range.mp hn; omega]
  have he := hs.sum_add_tsum_nat_add K
  rw [hzero, zero_add] at he
  rw [← he]
  simp only [Nat.le_add_left, if_true, pow_add]
  calc
    _ = (M/r^K) * ∑' n : ℕ, (r⁻¹)^n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [inv_pow]
      ring
    _ = M*r/(r-1)/r^K := by
      rw [tsum_geometric_of_lt_one (inv_nonneg.mpr hr0.le) ((inv_lt_one₀ hr0).mpr hr)]
      field_simp

/-- For positive `K`, `M ≥ 0`, and `r > 1`, the two-sided geometric tail at frequencies of
absolute value at least `K` equals `2 * M * r / (r - 1) / r^K`. -/
private theorem canonicalComplement_int_tail (M r : ℝ) (hM : 0 ≤ M) (hr : 1 < r) (K : ℕ) (hK : 0 < K) :
    (∑' k : ℤ, if K ≤ k.natAbs then M/r^k.natAbs else 0) = 2*M*r/(r-1)/r^K := by
  have hr0 : 0 < r := by linarith
  have hgeom := (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
    ((inv_lt_one₀ hr0).mpr hr)).mul_left M
  have hn : Summable (fun n : ℕ => M/r^n) := by
    simpa only [div_eq_mul_inv, inv_pow] using! hgeom
  have hbase : Summable (fun k : ℤ => M/r^k.natAbs) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa only [Int.natAbs_natCast, Int.natAbs_neg] using! hn
  let f : ℤ → ℝ := fun k => if K ≤ k.natAbs then M/r^k.natAbs else 0
  have hf : Summable f := by
    apply hbase.of_norm_bounded
    intro k
    have hpos : 0 ≤ M/r^k.natAbs := by positivity
    dsimp only [f]
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using! (le_refl (M/r^k.natAbs))
    · simpa only [norm_zero] using! hpos
  have hfpos := (summable_int_iff_summable_nat_and_neg.mp hf).1
  have hfneg := (summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp hf).2
  have hz : f 0 = 0 := by simp [f, hK.ne']
  have hshift : (∑' n : ℕ, f (-((n+1 : ℕ) : ℤ))) = ∑' n : ℕ, f n := by
    have he := hfpos.tsum_eq_zero_add
    simp only [Nat.cast_zero, hz, zero_add] at he
    simpa only [f, Int.natAbs_natCast, Int.natAbs_neg, Nat.cast_add, Nat.cast_one] using! he.symm
  change (∑' k : ℤ, f k) = _
  simp only [Nat.cast_add, Nat.cast_one] at hshift
  rw [tsum_of_nat_of_neg_add_one hfpos hfneg, hshift]
  have htail : (∑' n : ℕ, f n) = M*r/(r-1)/r^K := by
    simpa only [f, Int.natAbs_natCast] using! canonicalComplement_nat_tail M r hM hr K
  rw [htail]
  ring

/-- For coefficients bounded by `M / r^|k|` with `1 < r ≤ 2`, bounds the difference between the
periodic projection and outer-series sums by `4*M / ((r - 1)*r^K)`. -/
private theorem canonicalComplement_half_projection_tail_bound (a : ℤ → ℂ) (ha : Summable a)
    (M r : ℝ) (hM : 0 ≤ M) (hr : 1 < r) (hr2 : r ≤ 2)
    (hcoeff : ∀ k : ℤ, ‖a k‖ ≤ M/r^k.natAbs)
    (K : ℕ) (hK : 0 < K) (ω : ℂ) (hω : ‖ω‖ = 1) (j : ℤ) :
    ‖(∑' k : ℤ, (canonicalComplementProjectionWeight K k : ℂ)*a k*ω^(k*j)) -
      (∑' k : ℤ, (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j))‖ ≤
      4*M/((r-1)*r^K) := by
  have hr0 : 0 < r := by linarith
  have hgeom := (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le)
    ((inv_lt_one₀ hr0).mpr hr)).mul_left M
  have hn : Summable (fun n : ℕ => M/r^n) := by
    simpa only [div_eq_mul_inv, inv_pow] using! hgeom
  have hbase : Summable (fun k : ℤ => M/r^k.natAbs) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa only [Int.natAbs_natCast, Int.natAbs_neg] using! hn
  let tail : ℤ → ℝ := fun k => if K ≤ k.natAbs then M/r^k.natAbs else 0
  have ht : Summable tail := by
    apply hbase.of_norm_bounded
    intro k
    have hpos : 0 ≤ M/r^k.natAbs := by positivity
    dsimp only [tail]
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using! (le_refl (M/r^k.natAbs))
    · simpa only [norm_zero] using! hpos
  have hweight (k : ℤ) : ‖(canonicalComplementProjectionWeight K k : ℂ)‖ ≤ 1 ∧
      ‖(canonicalComplementOuterWeight k : ℂ)‖ ≤ 1 := by
    constructor
    · unfold canonicalComplementProjectionWeight
      split_ifs <;> norm_num
    · unfold canonicalComplementOuterWeight
      split_ifs <;> norm_num
  have hb : Summable (fun k : ℤ => (canonicalComplementProjectionWeight K k : ℂ)*a k*ω^(k*j)) := by
    apply ha.norm.of_norm_bounded
    intro k
    simp only [norm_mul, norm_zpow, hω, one_zpow, mul_one]
    simpa using! mul_le_mul_of_nonneg_right (hweight k).1 (norm_nonneg (a k))
  have hc : Summable (fun k : ℤ => (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j)) := by
    apply ha.norm.of_norm_bounded
    intro k
    simp only [norm_mul, norm_zpow, hω, one_zpow, mul_one]
    simpa using! mul_le_mul_of_nonneg_right (hweight k).2 (norm_nonneg (a k))
  let e : ℤ → ℂ := fun k =>
    ((canonicalComplementProjectionWeight K k-canonicalComplementOuterWeight k : ℝ) : ℂ)*a k*ω^(k*j)
  have he (k : ℤ) : ‖e k‖ ≤ tail k := by
    dsimp only [e, tail]
    by_cases hk : k.natAbs < K
    · rw [canonicalComplementProjectionWeight_low K hK k hk, sub_self]
      simp [show ¬ K ≤ k.natAbs by omega]
    · rw [if_pos (by omega : K ≤ k.natAbs)]
      simp only [norm_mul, norm_zpow, hω, one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (canonicalComplementProjectionWeight_bound K k) (hcoeff k)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hes : Summable e := ht.of_norm_bounded he
  have hdiff :
      (∑' k : ℤ, (canonicalComplementProjectionWeight K k : ℂ)*a k*ω^(k*j)) -
      (∑' k : ℤ, (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j)) = ∑' k : ℤ, e k := by
    rw [← hb.tsum_sub hc]
    apply tsum_congr
    intro k
    dsimp only [e]
    push_cast
    ring
  rw [hdiff]
  calc
    ‖∑' k : ℤ, e k‖ ≤ ∑' k : ℤ, ‖e k‖ := norm_tsum_le_tsum_norm hes.norm
    _ ≤ ∑' k : ℤ, tail k := hes.norm.tsum_le_tsum he ht
    _ = 2*M*r/(r-1)/r^K := canonicalComplement_int_tail M r hM hr K hK
    _ ≤ 4*M/((r-1)*r^K) := by
      rw [div_div]
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < (r-1)*r^K)).mpr
      nlinarith

/-- Identifies the finite half-weighted projection of aliased coefficient sums with the infinite
series weighted by the periodic projection weight. -/
private theorem canonicalComplement_project_alias_series
    (K : ℕ) (hK : 0 < K) (ω : ℂ) (hω : IsPrimitiveRoot ω (2*K))
    (a : ℤ → ℂ) (ha : Summable a) (j : ℕ) :
    (∑ l ∈ Finset.range (K+1),
      (if l=0 then (2 : ℂ)⁻¹ else 1) *
        (∑' k : ℤ, if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) * ω^(l*j)) =
      ∑' k : ℤ, (canonicalComplementProjectionWeight K k : ℂ)*a k*ω^(k*j) := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have halias (l : ℕ) : Summable (fun k : ℤ =>
      if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) := by
    apply ha.norm.of_norm_bounded
    intro k
    split_ifs <;> simp
  let α : ℕ → ℂ := fun l => if l=0 then (2 : ℂ)⁻¹ else 1
  have hterms (l : ℕ) : Summable (fun k : ℤ =>
      α l * (if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) * ω^(l*j)) :=
    ((halias l).mul_left (α l)).mul_right (ω^(l*j))
  have hcomm := Summable.tsum_finsetSum (s := Finset.range (K+1)) (fun l _ => hterms l)
  have hexpand (l : ℕ) : α l *
      (∑' k : ℤ, if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) * ω^(l*j) =
      ∑' k : ℤ, α l * (if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) * ω^(l*j) := by
    rw [← (halias l).tsum_mul_left, ← ((halias l).mul_left (α l)).tsum_mul_right]
  change (∑ l ∈ Finset.range (K+1), α l *
    (∑' k : ℤ, if ((2*K : ℕ) : ℤ) ∣ k-l then a k else 0) * ω^(l*j)) = _
  simp_rw [hexpand]
  rw [← hcomm]
  apply tsum_congr
  intro k
  have hw : (∑ l ∈ Finset.range (K+1),
      if ((2*K : ℕ) : ℤ) ∣ k-l then α l else 0) =
      (canonicalComplementProjectionWeight K k : ℂ) := by
    dsimp only [α]
    have hh := congrArg (fun x : ℝ => (x : ℂ))
      (canonicalComplementProjectionWeight_filtered K hK k)
    norm_num only [Complex.ofReal_sum, apply_ite, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_zero, Complex.ofReal_inv, one_div] at hh ⊢
    exact hh
  calc
    _ = (∑ l ∈ Finset.range (K+1),
        if ((2*K : ℕ) : ℤ) ∣ k-l then α l else 0) * a k * ω^(k*j) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hkl : ((2*K : ℕ) : ℤ) ∣ k-l
      · simp only [hkl, if_true]
        have hphase : ω^(l*j) = ω^(k*j) := by
          have he := (hω.zpow_eq_one_iff_dvd (k-l)).mpr hkl
          rw [zpow_sub₀ hω0, zpow_natCast] at he
          have hp := congrArg (fun u : ℂ => u^j) (eq_of_div_eq_one he)
          simpa only [← zpow_natCast, ← zpow_mul] using! hp.symm
        rw [hphase]
      · simp only [if_neg hkl, mul_zero, zero_mul]
    _ = _ := by rw [hw]

/-- Expresses the outer-weighted integer series as its nonnegative-frequency series minus half
the zero-frequency coefficient. -/
private theorem canonicalComplement_outer_series
    (a : ℤ → ℂ) (ha : Summable a) (ω : ℂ) (hω : ‖ω‖ = 1) (j : ℕ) :
    (∑' k : ℤ, (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j)) =
      (∑' n : ℕ, a n * ω^(n*j)) - a 0 / 2 := by
  let g : ℤ → ℂ := fun k => (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j)
  have hg : Summable g := by
    apply ha.norm.of_norm_bounded
    intro k
    have hc : ‖(canonicalComplementOuterWeight k : ℂ)‖ ≤ 1 := by
      unfold canonicalComplementOuterWeight
      split_ifs <;> norm_num
    dsimp only [g]
    simp only [norm_mul, norm_zpow, hω, one_zpow, mul_one]
    simpa using! mul_le_mul_of_nonneg_right hc (norm_nonneg (a k))
  have hgpos := (summable_int_iff_summable_nat_and_neg.mp hg).1
  have hgzero (n : ℕ) : g (-((n+1 : ℕ) : ℤ)) = 0 := by
    have hn0 : -((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hnneg : ¬ 0 < -((n+1 : ℕ) : ℤ) := by omega
    dsimp only [g, canonicalComplementOuterWeight]
    simp only [if_neg hn0, if_neg hnneg, Complex.ofReal_zero, zero_mul]
  have hgn : Summable (fun n : ℕ => g (-((n+1 : ℕ) : ℤ))) := by
    simp_rw [hgzero]
    exact summable_zero
  have hnat : Summable (fun n : ℕ => a n * ω^(n*j)) := by
    apply (summable_int_iff_summable_nat_and_neg.mp ha).1.norm.of_norm_bounded
    intro n
    simp only [norm_mul, norm_pow, hω, one_pow, mul_one]
    exact le_rfl
  change (∑' k : ℤ, g k) = _
  rw [tsum_of_nat_of_neg_add_one hgpos hgn]
  have hnzero : (∑' n : ℕ, g (-((n+1 : ℕ) : ℤ))) = 0 := by
    simp_rw [hgzero]
    exact tsum_zero
  simp only [Nat.cast_add, Nat.cast_one] at hnzero
  rw [hnzero, add_zero, hgpos.tsum_eq_zero_add, hnat.tsum_eq_zero_add]
  have htail : (∑' n : ℕ, g ((n+1 : ℕ) : ℤ)) =
      ∑' n : ℕ, a ((n+1 : ℕ) : ℤ) * ω^((n+1)*j) := by
    apply tsum_congr
    intro n
    have hn0 : ((n+1 : ℕ) : ℤ) ≠ 0 := by omega
    have hnpos : 0 < ((n+1 : ℕ) : ℤ) := by omega
    dsimp only [g, canonicalComplementOuterWeight]
    simp only [if_neg hn0, if_pos hnpos, Complex.ofReal_one, one_mul]
    rw [show ((n+1 : ℕ) : ℤ)*(j : ℤ) = (((n+1)*j : ℕ) : ℤ) by push_cast; rfl,
      zpow_natCast]
  rw [htail]
  simp only [g, canonicalComplementOuterWeight, Nat.cast_zero, if_true, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, zero_mul, zpow_zero, mul_one, pow_zero]
  ring

/-- Under the stated degree, margin, and annulus conditions, the logarithmic projection from
`2*K` samples differs from the canonical logarithmic series by at most `4*log (1/δ) / ((r -
1)*r^K)` at grid powers. -/
theorem canonicalComplement_discrete_log_error
    (P : Polynomial ℂ) (d K : ℕ) (δ r : ℝ)
    (hp : P.natDegree ≤ d) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : 1 < r) (hr2 : r ≤ 2) (hrc : r^d*(1-δ) ≤ 1)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) (hK : 0 < K) (j : ℕ) :
    let N := 2*K
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
    let A := fun n : ℕ => (N : ℂ)⁻¹ * ∑ l : Fin N,
      ((Real.log (1-‖P.eval (ω^l.val)‖^2) : ℝ) : ℂ) * ω^(-(n*l.val : ℤ))
    ‖(2 : ℂ)⁻¹*A 0 +
      (∑ l ∈ Finset.range (K+1), if l=0 then 0 else A l*ω^(l*j)) -
      canonicalComplementLogSeries P (ω^j)‖ ≤
      4*Real.log (1/δ)/((r-1)*r^K) := by
  (try dsimp only)
  let N := 2*K
  let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
  let A := fun n : ℕ => (N : ℂ)⁻¹ * ∑ l : Fin N,
    ((Real.log (1-‖P.eval (ω^l.val)‖^2) : ℝ) : ℂ) * ω^(-(n*l.val : ℤ))
  let a : ℤ → ℂ := fourierCoeff (T := 2*Real.pi)
    (fun θ => canonicalComplementLogResidual P (θ.toCircle : ℂ))
  have hN : 0 < N := by dsimp [N]; omega
  have hω : IsPrimitiveRoot ω N := by
    convert! Complex.isPrimitiveRoot_exp N hN.ne' using 1
    dsimp [ω]
    congr 1
    push_cast
    ring
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have ha : Summable a := canonicalComplement_fourierCoeff_summable P d δ r hp hδ hδ1 hr hrc hP
  have hA (n : ℕ) : A n = ∑' k : ℤ, if (N : ℤ) ∣ k-n then a k else 0 := by
    simpa only [Nat.cast_mul] using!
      canonicalComplement_actual_sample_alias P d N δ r hp hδ hδ1 hr hrc hP hN (n : ℤ)
  have hfinite : (∑ l ∈ Finset.range (K+1),
      (if l=0 then (2 : ℂ)⁻¹ else 1)*A l*ω^(l*j)) =
      (2 : ℂ)⁻¹*A 0 + ∑ l ∈ Finset.range (K+1), if l=0 then 0 else A l*ω^(l*j) := by
    have hterm (l : ℕ) : (if l=0 then (2 : ℂ)⁻¹ else 1)*A l*ω^(l*j) =
        (if l=0 then (2 : ℂ)⁻¹*A 0 else 0) + (if l=0 then 0 else A l*ω^(l*j)) := by
      by_cases hl : l=0 <;> simp [hl]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp
  have hproject : (2 : ℂ)⁻¹*A 0 +
      (∑ l ∈ Finset.range (K+1), if l=0 then 0 else A l*ω^(l*j)) =
      ∑' k : ℤ, (canonicalComplementProjectionWeight K k : ℂ)*a k*ω^(k*j) := by
    rw [← hfinite]
    simp_rw [hA]
    exact canonicalComplement_project_alias_series K hK ω hω a ha j
  have houter : canonicalComplementLogSeries P (ω^j) =
      ∑' k : ℤ, (canonicalComplementOuterWeight k : ℂ)*a k*ω^(k*j) := by
    rw [canonicalComplement_outer_series a ha ω hωnorm j]
    unfold canonicalComplementLogSeries
    have hcoeff (n : ℕ) : a n = canonicalComplementLogCoefficient P n :=
      (canonicalComplementLogCoefficient_eq_fourierCoeff P n).symm
    have hzero : a 0 = canonicalComplementLogCoefficient P 0 := by
      simpa only [Nat.cast_zero] using! hcoeff 0
    rw [hzero]
    simp_rw [hcoeff]
    congr 1
    apply tsum_congr
    intro n
    rw [← pow_mul, Nat.mul_comm]
  change ‖(2 : ℂ)⁻¹*A 0 +
    (∑ l ∈ Finset.range (K+1), if l=0 then 0 else A l*ω^(l*j)) -
    canonicalComplementLogSeries P (ω^j)‖ ≤ _
  rw [hproject, houter]
  have hM : 0 ≤ Real.log (1/δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  exact canonicalComplement_half_projection_tail_bound a ha (Real.log (1/δ)) r hM hr hr2
    (canonicalComplement_fourierCoeff_int_bound P d δ r hp hδ hδ1 hr.le hrc hP) K hK ω hωnorm j

/-- If all root-of-unity samples approximate a polynomial of degree below `N` within ε, their
normalized Fourier sums approximate each coefficient below `N` within ε. -/
private theorem canonicalComplement_dft_sample_error
    (Q : Polynomial ℂ) (N : ℕ) (hN : 0 < N) (hQ : Q.natDegree < N)
    (ω : ℂ) (hω : IsPrimitiveRoot ω N) (samples : Fin N → ℂ)
    (ε : ℝ) (hε : 0 < ε) (herror : ∀ j : Fin N, ‖samples j-Q.eval (ω^j.val)‖ < ε)
    (n : ℕ) (hn : n < N) :
    ‖Q.coeff n-(N : ℂ)⁻¹*∑ j : Fin N, samples j*ω^(-(n*j.val : ℤ))‖ < ε := by
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  rw [← canonicalComplement_polynomial_dft_exact Q N hN hQ ω hω n hn]
  have hid : (N : ℂ)⁻¹*(∑ j : Fin N, Q.eval (ω^j.val)*ω^(-(n*j.val : ℤ))) -
      (N : ℂ)⁻¹*(∑ j : Fin N, samples j*ω^(-(n*j.val : ℤ))) =
      (N : ℂ)⁻¹*∑ j : Fin N, (Q.eval (ω^j.val)-samples j)*ω^(-(n*j.val : ℤ)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum : (∑ j : Fin N, ‖Q.eval (ω^j.val)-samples j‖) < (N : ℝ)*ε := by
    have hs : (∑ j : Fin N, ‖Q.eval (ω^j.val)-samples j‖) < ∑ _j : Fin N, ε := by
      apply Finset.sum_lt_sum
      · intro j _
        simpa only [norm_sub_rev] using! (herror j).le
      · exact ⟨⟨0,hN⟩, Finset.mem_univ _, by simpa only [norm_sub_rev] using! herror ⟨0,hN⟩⟩
    simpa using! hs
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ j : Fin N, ‖Q.eval (ω^j.val)-samples j‖ := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hpos.le)
      simpa only [norm_mul, norm_zpow, hωnorm, one_zpow, mul_one] using!
        norm_sum_le (Finset.univ : Finset (Fin N))
          (fun j => (Q.eval (ω^j.val)-samples j)*ω^(-(n*j.val : ℤ)))
    _ < (N : ℝ)⁻¹*((N : ℝ)*ε) := mul_lt_mul_of_pos_left hsum (inv_pos.mpr hpos)
    _ = ε := by field_simp

/-- Under the stated strict-margin hypotheses and explicit power-of-two sample threshold, the
logarithm-projection, exponentiation, and discrete Fourier reconstruction approximate every
complement coefficient through degree `d` within ε. -/
theorem canonical_complement_discrete_fourier_accuracy :
∀ (P Q : Polynomial ℂ) (d m : ℕ) (δ ε : ℝ),
      0 < d → P.natDegree ≤ d → Q.natDegree ≤ d → 0 < δ → δ < 1 → 0 < ε → ε < 1 →
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1-δ) →
      0 < (Q.eval 0).re → (Q.eval 0).im = 0 →
      (∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) →
      (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) →
      let N := 2^m
      let ρ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
      let r := min (2 : ℝ) ρ
      1 ≤ m → d+1 ≤ N →
      (Nat.ceil (2/Real.log r * Real.log (max (2 : ℝ) (8*Real.log (1/δ)/(r-1)/ε))) : ℕ) ≤ N →
      let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ) * Complex.I)
      let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
        ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(n*j.val : ℤ))
      let q := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
        Complex.exp ((2 : ℂ)⁻¹*a 0 +
          ∑ l ∈ Finset.range (N/2+1), if l=0 then 0 else a l*ω^(l*j.val)) *
          ω^(-(n*j.val : ℤ))
      ∀ n : ℕ, n ≤ d → ‖Q.coeff n-q n‖ < ε := by
  intro P Q d m δ ε hd hPd hQd hδ hδ1 hε hε1 hP hQr hQi hQn hQc
  (try dsimp only)
  intro hm hgrid hthreshold n hn
  cases m with
  | zero => omega
  | succ k =>
    have hpower : 2^(k+1) = 2*2^k := by rw [pow_succ]; omega
    generalize hsize : 2^(k+1) = size at hgrid hthreshold ⊢
    rw [hpower] at hsize
    subst size
    simp only [Nat.mul_div_cancel_left (2^k) (by norm_num : 0 < 2)]
    let K := 2^k
    let N := 2*K
    let ρ : ℝ := (1/(1-δ))^(1/(d : ℝ) : ℝ)
    let r : ℝ := min 2 ρ
    let M := Real.log (1/δ)
    let ω := Complex.exp ((2*Real.pi/(N : ℝ) : ℝ)*Complex.I)
    let A := fun l : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1-‖P.eval (ω^j.val)‖^2) : ℝ) : ℂ) * ω^(-(l*j.val : ℤ))
    let E := fun j : Fin N => (2 : ℂ)⁻¹*A 0 +
      ∑ l ∈ Finset.range (K+1), if l=0 then 0 else A l*ω^(l*j.val)
    change ‖Q.coeff n-(N : ℂ)⁻¹*∑ j : Fin N, Complex.exp (E j)*ω^(-(n*j.val : ℤ))‖ < ε
    have hK : 0 < K := by dsimp [K]; positivity
    have hN : 0 < N := by dsimp [N]; omega
    have hgrid' : d+1 ≤ N := hgrid
    have hbase : 1 < (1/(1-δ) : ℝ) := by
      rw [lt_div_iff₀ (by linarith : 0 < 1-δ)]
      linarith
    have hρ : 1 < ρ := Real.one_lt_rpow hbase (by positivity)
    have hr : 1 < r := lt_min (by norm_num) hρ
    have hr2 : r ≤ 2 := min_le_left _ _
    have hρpow : ρ^d = 1/(1-δ) := by
      simpa only [ρ, one_div] using!
        (Real.rpow_inv_natCast_pow (by positivity : 0 ≤ (1/(1-δ) : ℝ)) hd.ne')
    have hrc : r^d*(1-δ) ≤ 1 := by
      calc
        _ ≤ ρ^d*(1-δ) := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith : 0 ≤ r) (min_le_right 2 ρ) d) (by linarith)
        _ = 1 := by
          rw [hρpow]
          field_simp [show 1-δ ≠ 0 by linarith]
    have hω : IsPrimitiveRoot ω N := by
      convert! Complex.isPrimitiveRoot_exp N hN.ne' using 1
      dsimp [ω]
      congr 1
      push_cast
      ring
    have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
    have hT : max 2 (8*M/(r-1)/ε) ≤ r^K :=
      canonicalComplement_threshold_power r (max 2 (8*M/(r-1)/ε)) K hr
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)) hthreshold
    have hlarge : 8*M/(r-1)/ε ≤ r^K := (le_max_right _ _).trans hT
    have hsmall : 4*M/((r-1)*r^K) ≤ ε/2 := by
      rw [div_le_iff₀ hε, div_le_iff₀ (by linarith : 0 < r-1)] at hlarge
      apply (div_le_iff₀ (by positivity : 0 < (r-1)*r^K)).mpr
      nlinarith
    have herror (j : Fin N) : ‖Complex.exp (E j)-Q.eval (ω^j.val)‖ < ε := by
      have hz : ‖ω^j.val‖ = 1 := by rw [norm_pow, hωnorm, one_pow]
      have hseries := canonicalComplementLogSeries_exp P Q d δ r hPd hδ hδ1 hr hrc hP
        hQr hQi hQn hQc (ω^j.val) hz.le
      have hx : ‖Complex.exp (canonicalComplementLogSeries P (ω^j.val))‖ ≤ 1 := by
        rw [hseries]
        nlinarith [hQc (ω^j.val) hz, norm_nonneg (Q.eval (ω^j.val)), sq_nonneg ‖P.eval (ω^j.val)‖]
      have hlog : ‖E j-canonicalComplementLogSeries P (ω^j.val)‖ ≤ ε/2 :=
        (canonicalComplement_discrete_log_error P d K δ r hPd hδ hδ1 hr hr2 hrc hP hK j.val).trans hsmall
      have hexp := canonicalComplement_exp_perturbation
        (canonicalComplementLogSeries P (ω^j.val)) (E j) ε hε hε1 hx (by linarith)
      rwa [hseries] at hexp
    exact canonicalComplement_dft_sample_error Q N hN (by omega) ω hω
      (fun j => Complex.exp (E j)) ε hε herror n (by omega)

end Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
