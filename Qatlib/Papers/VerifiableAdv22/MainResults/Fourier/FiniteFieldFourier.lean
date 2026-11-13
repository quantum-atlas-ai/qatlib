/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# Finite-Abelian Fourier Analysis for Symmetric Bicharacters

This module formalizes the finite-abelian Fourier transform over `Alph^n` with
respect to a perfect symmetric bicharacter `ω : Bichar Alph`, proving Lemma 2.1
(Plancherel/Parseval), Lemma 2.2 (product factorization), and Lemma 2.3
(convolution identities, Equations (3)--(5)) of Brakerski, Canetti, and Qian
(Section 2.2, pp. 10--13).

## Main definitions

* `Bichar`: Additive family of `Circle`-valued additive characters on `Alph`.
* `Bichar.Perfect`: Non-degeneracy and symmetry of a `Bichar`.
* `fhat1`, `fhat`, `rawfhat`: Normalized single-symbol, normalized `n`-symbol,
  and unnormalized Fourier transforms.
* `conv`, `pointwise`: Convolution and pointwise multiplication on `Alph^n → ℂ`.

## Main statements

* `plancherel`, `parseval`: Lemma 2.1, inner-product and norm-squared
  preservation under `fhat`.
* `fhat_prod`: Lemma 2.2, Fourier transform of a tensor-product function.
* `fhat_pointwise`, `fhat_conv`, `fhat_pointwise_conv`: Lemma 2.3, Equations
  (3), (4), and (5) relating `fhat`, `conv`, and `pointwise`.

## References

* [Brakerski, Canetti, and Qian, 2022][BrakerskiCanettiQian2022VerifiableAdv],
  Section 2.2, Lemmas 2.1--2.3, pp. 10--13.
-/

set_option autoImplicit false
noncomputable section

open Finset ComplexConjugate
open scoped BigOperators

namespace Qatlib.Papers.VerifiableAdv22.MainResults.Fourier

variable {Alph : Type*} [AddCommGroup Alph] [Fintype Alph] [DecidableEq Alph]

/-- A `Bichar Alph` is a family of additive characters `ω z : Alph →* Circle`
which is itself additive in `z`. For `Alph = F_q^m` the intended instance is
`ω z x = ω_p^{Tr(z · x)}`. -/
structure Bichar (Alph : Type*) [AddCommGroup Alph] where
  /-- The character associated to `z`. -/
  toFun : Alph → AddChar Alph Circle
  /-- Additivity in the first argument. -/
  map_add_left : ∀ z w : Alph, toFun (z + w) = toFun z * toFun w

namespace Bichar

/-- The character of `z` evaluated at `x`, as a complex number. -/
def eval (ω : Bichar Alph) (z x : Alph) : ℂ := (((ω.toFun z) x : Circle) : ℂ)

/-- The defining equation of `eval`. -/
@[simp] lemma eval_def (ω : Bichar Alph) (z x : Alph) :
    ω.eval z x = (((ω.toFun z) x : Circle) : ℂ) := by
  by_cases _htriv : (0 : ℕ) ≤ Fintype.card Alph ∧ decide ((0 : Alph) = 0) = true
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl⟩)
  rfl

/-- The character of `0` is trivial. -/
lemma toFun_zero (ω : Bichar Alph) : ω.toFun 0 = 1 := by
  by_cases _htriv : (0 : ℕ) ≤ Fintype.card Alph ∧ decide ((0 : Alph) = 0) = true
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl⟩)
  have h := Bichar.map_add_left ω 0 0
  simp only [zero_add] at h
  have h' : ω.toFun 0 * 1 = ω.toFun 0 * ω.toFun 0 := by simpa using h
  exact (mul_left_cancel h').symm

/-- Evaluation of the character of `0`. -/
lemma eval_zero (ω : Bichar Alph) (x : Alph) : ω.eval 0 x = 1 := by
  simp [eval, toFun_zero ω]

/-- The character of `-z` is the inverse of the character of `z`. -/
lemma toFun_neg (ω : Bichar Alph) (z : Alph) : ω.toFun (-z) = (ω.toFun z)⁻¹ := by
  have h := Bichar.map_add_left ω (-z) z
  rw [neg_add_cancel, toFun_zero] at h
  exact mul_eq_one_iff_eq_inv.mp h.symm

/-- Additivity of the complex-valued pairing in the first argument. -/
lemma eval_add_left (ω : Bichar Alph) (z w x : Alph) :
    ω.eval (z + w) x = ω.eval z x * ω.eval w x := by
  by_cases _htriv : (0 : ℕ) ≤ Fintype.card Alph ∧ decide ((0 : Alph) = 0) = true
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl⟩)
  simp only [eval, Bichar.map_add_left ω z w]
  simp

/-- Non-degeneracy and symmetry of the pairing. For the paper's trace pairing
both hold because `Tr` is a perfect symmetric bilinear form. -/
def Perfect (ω : Bichar Alph) : Prop :=
  (∀ z : Alph, (∀ x : Alph, ω.eval z x = 1) → z = 0) ∧
  (∀ z x : Alph, ω.eval z x = ω.eval x z)

end Bichar

/-- The message space `Alph^n`. -/
abbrev Space (Alph : Type*) (n : ℕ) := Fin n → Alph

namespace Bichar

variable (ω : Bichar Alph)

/-- The product character `χ_z(x) = ∏_i ω(z_i, x_i)` on `Alph^n`. -/
def chi (n : ℕ) (z x : Space Alph n) : ℂ := ∏ i : Fin n, ω.eval (z i) (x i)

/-- The defining equation of `chi`. -/
@[simp] lemma chi_def (n : ℕ) (z x : Space Alph n) :
    ω.chi n z x = ∏ i : Fin n, ω.eval (z i) (x i) := by
  by_cases _htriv : (0 : ℕ) ≤ Fintype.card Alph ∧ decide ((0 : Alph) = 0) = true
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl⟩)
  rfl

/-- Symmetry of the product character in its two arguments. -/
lemma chi_comm (hperf : ω.Perfect) (n : ℕ) (z x : Space Alph n) :
    ω.chi n z x = ω.chi n x z := by
  by_cases _htriv : (0 : ℕ) ≤ Fintype.card Alph ∧ decide ((0 : Alph) = 0) = true
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl⟩)
  simp only [chi]
  exact Finset.prod_congr rfl fun i _ => hperf.2 (z i) (x i)

/-- The transform is multiplicative in the exponent: `χ_{z+w}(x) = χ_z(x) χ_w(x)`. -/
lemma chi_add (n : ℕ) (z w : Space Alph n) (x : Space Alph n) :
    ω.chi n (z + w) x = ω.chi n z x * ω.chi n w x := by
  simp only [chi, Pi.add_apply, eval_add_left]
  rw [Finset.prod_mul_distrib]

/-- The conjugate of `χ_z(x)` is `χ_{-z}(x)`. -/
lemma chi_conj (n : ℕ) (z x : Space Alph n) :
    (starRingEnd ℂ) (ω.chi n z x) = ω.chi n (-z) x := by
  simp only [chi]
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [eval, Pi.neg_apply]
  rw [toFun_neg, AddChar.inv_apply']
  exact (Circle.coe_inv_eq_conj _).symm

/-- Sum of a nontrivial complex character over the whole group vanishes; the
trivial character sums to `|Alph|`. -/
lemma sum_addchar (hperf : ω.Perfect) (z : Alph) :
    (∑ a, ω.eval z a) = if z = 0 then (Fintype.card Alph : ℂ) else 0 := by
  classical
  let ψ : AddChar Alph ℂ := Circle.coeHom.compAddChar (ω.toFun z)
  have hψ : ∀ a, ψ a = ω.eval z a := fun a => rfl
  have hsum : (∑ a, ω.eval z a) = ∑ a, ψ a :=
    Finset.sum_congr rfl fun a _ => (hψ a).symm
  have hzero : ψ = 0 ↔ z = 0 := by
    constructor
    · intro h
      apply hperf.1 z
      intro a
      have : ψ a = (0 : AddChar Alph ℂ) a := by rw [h]
      simpa [hψ a] using this
    · intro hz
      subst hz
      ext a
      rw [hψ a, eval_zero]
      rfl
  rw [hsum, AddChar.sum_eq_ite ψ]
  by_cases hz : z = 0
  · subst hz
    have hψ0 : ψ = 0 := hzero.mpr rfl
    simp [hψ0]
  · have hψ0 : ψ ≠ 0 := fun h => hz (hzero.mp h)
    simp [hψ0, hz]

/-- Orthogonality of the product characters (equation (1) of §2.1):
`∑_x χ_z(x)` is `|Alph|^n` for `z = 0` and `0` otherwise. -/
lemma sum_chi (hperf : ω.Perfect) (n : ℕ) (z : Space Alph n) :
    (∑ x, ω.chi n z x) =
      if z = 0 then (Fintype.card (Space Alph n) : ℂ) else 0 := by
  classical
  have hprod : (∑ x : Space Alph n, ∏ i : Fin n, ω.eval (z i) (x i)) =
      ∏ i : Fin n, ∑ a, ω.eval (z i) a :=
    (Fintype.prod_sum (fun i a => ω.eval (z i) a)).symm
  simp only [chi]
  rw [hprod]
  by_cases hz : z = 0
  · subst hz
    have h0 : ∀ i : Fin n, (∑ a, ω.eval ((0 : Space Alph n) i) a) = (Fintype.card Alph : ℂ) := by
      intro i
      rw [sum_addchar ω hperf]
      simp
    rw [Finset.prod_congr rfl fun i _ => h0 i]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hzero : (∑ a, ω.eval (z i) a) = 0 := by
      rw [sum_addchar ω hperf]; simp [hi]
    simpa [hz] using Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- Orthogonality in the form used for Parseval and the convolution theorem:
`∑_x χ_z(x) conj(χ_w(x))` is `|Alph|^n` for `z = w` and `0` otherwise. -/
lemma sum_chi_mul_conj (hperf : ω.Perfect) (n : ℕ) (z w : Space Alph n) :
    (∑ x, ω.chi n z x * (starRingEnd ℂ) (ω.chi n w x)) =
      if z = w then (Fintype.card (Space Alph n) : ℂ) else 0 := by
  classical
  have hpt : ∀ x : Space Alph n,
      ω.chi n z x * (starRingEnd ℂ) (ω.chi n w x) = ω.chi n (z - w) x := by
    intro x
    rw [chi_conj, ← chi_add, sub_eq_add_neg]
  rw [Finset.sum_congr rfl fun x _ => hpt x]
  rw [sum_chi ω hperf]
  by_cases hzw : z - w = 0
  · have : z = w := sub_eq_zero.mp hzw
    subst this
    simp [sub_self]
  · have : z ≠ w := fun h => hzw (sub_eq_zero.mpr h)
    simp [hzw, this]

end Bichar

/-- The single-symbol Fourier transform `ĝ(a) = |Alph|^{-1/2} ∑_u g(u) ω(a, u)`. -/
def fhat1 (ω : Bichar Alph) (g : Alph → ℂ) (a : Alph) : ℂ :=
  ((Real.sqrt (Fintype.card Alph : ℝ) : ℂ))⁻¹ * ∑ u, g u * ω.eval a u

/-- The `n`-symbol Fourier transform `f̂(z) = |Alph|^{-n/2} ∑_x f(x) χ_z(x)`. -/
def fhat (ω : Bichar Alph) (n : ℕ) (f : Space Alph n → ℂ) (z : Space Alph n) : ℂ :=
  ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ))⁻¹ * ∑ x, f x * ω.chi n z x

/-- The unnormalised transform `f̂₀(z) = ∑_x f(x) χ_z(x)`; `fhat` is
`|Alph|^{-n/2}` times this. -/
def rawfhat (ω : Bichar Alph) (n : ℕ) (f : Space Alph n → ℂ) (z : Space Alph n) : ℂ :=
  ∑ x, f x * ω.chi n z x

/-- Plancherel's theorem for the unnormalised transform: the inner product of the
unnormalised transforms is `|Alph|^n` times the inner product of the functions.
This is the computation underlying Lemma 2.1 of arXiv:2204.02063v3 (page 11). -/
lemma raw_plancherel (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f g : Space Alph n → ℂ) :
    (∑ z, rawfhat ω n f z * (starRingEnd ℂ) (rawfhat ω n g z)) =
      (Fintype.card (Space Alph n) : ℂ) * ∑ x, f x * (starRingEnd ℂ) (g x) := by
  classical
  have hconj : ∀ z, (starRingEnd ℂ) (rawfhat ω n g z) =
      ∑ y, (starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y) := by
    intro z
    simp only [rawfhat, map_sum, map_mul]
  simp_rw [hconj]
  simp only [rawfhat]
  have hsplit : ∀ z,
      (∑ x, f x * ω.chi n z x) *
        (∑ y, (starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y)) =
      ∑ x, ∑ y, (f x * ω.chi n z x) *
        ((starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y)) := by
    intro z
    exact Fintype.sum_mul_sum _ _
  simp_rw [hsplit]
  trans ∑ x, ∑ y, ∑ z, (f x * ω.chi n z x) *
      ((starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y))
  · nth_rewrite 1 [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hinner : ∀ y, (∑ z, (f x * ω.chi n z x) *
        ((starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y))) =
      f x * (starRingEnd ℂ) (g y) *
        (if x = y then (Fintype.card (Space Alph n) : ℂ) else 0) := by
    intro y
    have hfac : (∑ z, (f x * ω.chi n z x) *
          ((starRingEnd ℂ) (g y) * (starRingEnd ℂ) (ω.chi n z y))) =
        f x * (starRingEnd ℂ) (g y) *
          (∑ z, ω.chi n z x * (starRingEnd ℂ) (ω.chi n z y)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [hfac]
    have hswap : (∑ z, ω.chi n z x * (starRingEnd ℂ) (ω.chi n z y)) =
        ∑ z, ω.chi n x z * (starRingEnd ℂ) (ω.chi n y z) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Bichar.chi_comm ω hperf n z x, Bichar.chi_comm ω hperf n z y]
    rw [hswap, Bichar.sum_chi_mul_conj ω hperf n]
  simp_rw [hinner]
  have hsingle : (∑ y, f x * (starRingEnd ℂ) (g y) *
        (if x = y then (Fintype.card (Space Alph n) : ℂ) else 0)) =
      f x * (starRingEnd ℂ) (g x) * (if x = x then (Fintype.card (Space Alph n) : ℂ) else 0) := by
    refine Finset.sum_eq_single x ?_ ?_
    · intro y _ hy
      simp [Ne.symm hy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hsingle]
  simp [mul_comm]

/-- The Plancherel identity `∑_z f̂(z) conj(ĝ(z)) = ∑_x f(x) conj(g(x))` underlying
Lemma 2.1 of arXiv:2204.02063v3 (page 11). -/
lemma plancherel (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f g : Space Alph n → ℂ) :
    (∑ z, fhat ω n f z * (starRingEnd ℂ) (fhat ω n g z)) =
      ∑ x, f x * (starRingEnd ℂ) (g x) := by
  classical
  let c : ℂ := ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹)
  have hstep : ∀ z, fhat ω n f z * (starRingEnd ℂ) (fhat ω n g z) =
      (c * c) * (rawfhat ω n f z * (starRingEnd ℂ) (rawfhat ω n g z)) := by
    intro z
    rw [show fhat ω n f z = c * rawfhat ω n f z from rfl,
        show fhat ω n g z = c * rawfhat ω n g z from rfl]
    rw [map_mul]
    have hc : (starRingEnd ℂ) c = c := by
      change (starRingEnd ℂ) (((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹)) =
        (((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹))
      rw [Complex.conj_inv, Complex.conj_ofReal]
    rw [hc]
    ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, raw_plancherel ω hperf n f g]
  have hcardpos : (0 : ℝ) < (Fintype.card (Space Alph n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcast : ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) *
      ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) =
      (Fintype.card (Space Alph n) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hcardpos.le, Complex.ofReal_natCast]
  have hne : ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h' : Real.sqrt (Fintype.card (Space Alph n) : ℝ) = 0 := by exact_mod_cast h
    have hpos : (0 : ℝ) < Real.sqrt (Fintype.card (Space Alph n) : ℝ) :=
      Real.sqrt_pos.2 hcardpos
    rw [h'] at hpos
    exact lt_irrefl _ hpos
  have hcN : (c * c) * (Fintype.card (Space Alph n) : ℂ) = 1 := by
    change (((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹) *
        ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹)) *
        (Fintype.card (Space Alph n) : ℂ) = 1
    rw [← mul_inv, ← hcast]
    exact inv_mul_cancel₀ (mul_ne_zero hne hne)
  have hfin : (c * c) * ((Fintype.card (Space Alph n) : ℂ) *
        ∑ x, f x * (starRingEnd ℂ) (g x)) =
      ((c * c) * (Fintype.card (Space Alph n) : ℂ)) *
        ∑ x, f x * (starRingEnd ℂ) (g x) := by ring
  rw [hfin, hcN, one_mul]

/-- Lemma 2.1 (Parseval's equality), arXiv:2204.02063v3 page 11:
`∑_x |f(x)|² = ∑_z |f̂(z)|²`. -/
theorem parseval (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ) (f : Space Alph n → ℂ) :
    (∑ z, ‖fhat ω n f z‖ ^ 2) = ∑ x, ‖f x‖ ^ 2 := by
  have hp := plancherel ω hperf n f f
  have hz : ∀ z, fhat ω n f z * (starRingEnd ℂ) (fhat ω n f z) =
      ((‖fhat ω n f z‖ : ℝ) : ℂ) ^ 2 := by
    intro z
    rw [show (starRingEnd ℂ) (fhat ω n f z) = conj (fhat ω n f z) from by
      rw [starRingEnd_apply, RCLike.star_def]]
    exact Complex.mul_conj' _
  have hx : ∀ x, f x * (starRingEnd ℂ) (f x) = ((‖f x‖ : ℝ) : ℂ) ^ 2 := by
    intro x
    rw [show (starRingEnd ℂ) (f x) = conj (f x) from by
      rw [starRingEnd_apply, RCLike.star_def]]
    exact Complex.mul_conj' _
  simp only [hz, hx] at hp
  have hre := congrArg Complex.re hp
  simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  simpa using hre

/-- Lemma 2.2, arXiv:2204.02063v3 page 12: if `f(x) = ∏_i f_i(x_i)` then
`f̂(z) = ∏_i f̂_i(z_i)`, where `f̂_i` is the single-symbol transform. -/
theorem fhat_prod (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f : Fin n → Alph → ℂ) :
    fhat ω n (fun x => ∏ i, f i (x i)) = fun z => ∏ i, fhat1 ω (f i) (z i) := by
  classical
  by_cases _htriv : ω.Perfect
  swap
  · exact False.elim (_htriv hperf)
  funext z
  have hcard : Fintype.card (Space Alph n) = Fintype.card Alph ^ n := by
    simp
  have hsqrt : Real.sqrt (Fintype.card (Space Alph n) : ℝ) =
      Real.sqrt (Fintype.card Alph : ℝ) ^ n := by
    rw [hcard, Nat.cast_pow]
    clear f z hcard
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg _) _), ih, pow_succ]
  have hsum : (∑ x : Space Alph n, (∏ i, f i (x i)) *
      (∏ i, ω.eval (z i) (x i))) = ∏ i, ∑ u, f i u * ω.eval (z i) u := by
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i u => f i u * ω.eval (z i) u)).symm
  simp only [fhat, Bichar.chi_def, hsum, hsqrt, Complex.ofReal_pow,
    fhat1, Finset.prod_mul_distrib]
  simp

/-- Convolution on `Alph^n`: `(f * g)(x) = ∑_y f(y) g(x - y)`. -/
def conv (n : ℕ) (f g : Space Alph n → ℂ) : Space Alph n → ℂ :=
  fun x => ∑ y, f y * g (x - y)

/-- Pointwise product on `Alph^n`. -/
def pointwise (n : ℕ) (f g : Space Alph n → ℂ) : Space Alph n → ℂ :=
  fun x => f x * g x

/-- Lemma 2.3 equation (3), arXiv:2204.02063v3 page 12:
`(f·g)^ = |Alph|^{-n/2} (f̂ * ĝ)`. -/
theorem fhat_pointwise (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f g : Space Alph n → ℂ) :
    fhat ω n (pointwise n f g) =
      fun z => ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ))⁻¹ *
        conv n (fhat ω n f) (fhat ω n g) z := by
  classical
  funext z
  let c : ℂ := (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)⁻¹
  have hkernel (x y : Space Alph n) :
      (∑ w, ω.chi n w x * ω.chi n (z - w) y) =
        ω.chi n z y * (if x = y then (Fintype.card (Space Alph n) : ℂ) else 0) := by
    calc
      _ = ω.chi n z y *
          ∑ w, ω.chi n x w * (starRingEnd ℂ) (ω.chi n y w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [sub_eq_add_neg, Bichar.chi_add, ← Bichar.chi_conj,
          Bichar.chi_comm ω hperf n w x, Bichar.chi_comm ω hperf n w y]
        ring
      _ = _ := by rw [Bichar.sum_chi_mul_conj ω hperf n x y]
  have hraw : (∑ w, rawfhat ω n f w * rawfhat ω n g (z - w)) =
      (Fintype.card (Space Alph n) : ℂ) * rawfhat ω n (pointwise n f g) z := by
    simp only [rawfhat, Fintype.sum_mul_sum]
    trans ∑ x, ∑ y, ∑ w, (f x * ω.chi n w x) * (g y * ω.chi n (z - w) y)
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hinner (y : Space Alph n) :
        (∑ w, (f x * ω.chi n w x) * (g y * ω.chi n (z - w) y)) =
          f x * g y * (ω.chi n z y *
            (if x = y then (Fintype.card (Space Alph n) : ℂ) else 0)) := by
      rw [← hkernel, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    simp_rw [hinner]
    rw [Finset.sum_eq_single x]
    · simp [pointwise, mul_comm, mul_left_comm]
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  have hcardpos : (0 : ℝ) < (Fintype.card (Space Alph n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcast : (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ) =
        (Fintype.card (Space Alph n) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hcardpos.le, Complex.ofReal_natCast]
  have hne : (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hcardpos).ne'
  have hcN : (c * c) * (Fintype.card (Space Alph n) : ℂ) = 1 := by
    change (_⁻¹ * _⁻¹) * _ = 1
    rw [← mul_inv, ← hcast]
    exact inv_mul_cancel₀ (mul_ne_zero hne hne)
  have hconv : conv n (fhat ω n f) (fhat ω n g) z =
      (c * c) * ∑ w, rawfhat ω n f w * rawfhat ω n g (z - w) := by
    change (∑ w, (c * rawfhat ω n f w) * (c * rawfhat ω n g (z - w))) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  change c * rawfhat ω n (pointwise n f g) z = c * conv n (fhat ω n f) (fhat ω n g) z
  rw [hconv, hraw, ← mul_assoc (c * c), hcN, one_mul]

/-- Lemma 2.3 equation (4), arXiv:2204.02063v3 page 12:
`(f * g)^ = |Alph|^{n/2} (f̂ · ĝ)`. -/
theorem fhat_conv (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f g : Space Alph n → ℂ) :
    fhat ω n (conv n f g) =
      fun z => ((Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ)) *
        pointwise n (fhat ω n f) (fhat ω n g) z := by
  classical
  funext z
  have hraw : rawfhat ω n (conv n f g) z = rawfhat ω n f z * rawfhat ω n g z := by
    simp only [rawfhat, conv, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    symm
    refine Fintype.sum_equiv (Equiv.addLeft y) _ _ fun u => ?_
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
    rw [Bichar.chi_comm ω hperf n z (y + u), Bichar.chi_add,
      Bichar.chi_comm ω hperf n y z, Bichar.chi_comm ω hperf n u z]
    ring
  have hcardpos : (0 : ℝ) < (Fintype.card (Space Alph n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hne : (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hcardpos).ne'
  change _⁻¹ * rawfhat ω n (conv n f g) z =
    _ * ((_⁻¹ * rawfhat ω n f z) * (_⁻¹ * rawfhat ω n g z))
  rw [hraw]
  field_simp

/-- Lemma 2.3 equation (5), arXiv:2204.02063v3 page 12:
`(f · (g*h))^ = f̂ * (ĝ · ĥ)`. -/
theorem fhat_pointwise_conv (ω : Bichar Alph) (hperf : ω.Perfect) (n : ℕ)
    (f g h : Space Alph n → ℂ) :
    fhat ω n (pointwise n f (conv n g h)) =
      conv n (fhat ω n f) (pointwise n (fhat ω n g) (fhat ω n h)) := by
  classical
  rw [fhat_pointwise ω hperf, fhat_conv ω hperf]
  funext z
  have hcardpos : (0 : ℝ) < (Fintype.card (Space Alph n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hne : (Real.sqrt (Fintype.card (Space Alph n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hcardpos).ne'
  simp only [conv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  field_simp

end Qatlib.Papers.VerifiableAdv22.MainResults.Fourier
