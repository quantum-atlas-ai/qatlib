/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSLWEISIS25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Relations Between S|LWE⟩ and IC|LWE⟩ States

This module formalizes Propositions 3--6 of Chailloux and Hermouet on the
discrete Fourier transform of the S|LWE⟩ states `|ψ_s⟩` and the index-coset
states `|W_y⟩`, their dual-lattice support on `Λ_y^⊥(A)`, their mutual linear
inversion formulas, and the average norm weight `E_y[w_y] = q^n`.

## Main statements

* `psiHat_apply`: Proposition 3, `ψ̂_s(x) = ω^{(A x)·s} f̂(x)`.
* `WHat_apply`: Proposition 4, shifted dual-lattice support of `|Ŵ_y⟩`.
* `Wvec_eq_sum` / `psi_eq_sum_W`: Proposition 5, mutual Fourier superpositions
  relating `|ψ_s⟩` and `|W_y⟩`.
* `expect_wNorm`: Proposition 6, `E_y[w_y] = q^n` for normalized `f`.

## References

* [Chailloux and Hermouet, 2025][ChaillouxHermouet2025SLWE], Section 3.1,
  Propositions 3--6, pp. 11--12.
-/

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QSLWEISIS25.MainResults

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {q n m : ℕ} [NeZero q]

omit [NeZero q] in
/-- The inner product `⟨x, y⟩` over `ZMod q` is symmetric. -/
lemma dot_comm {k : ℕ} (x y : Fin k → ZMod q) : dot x y = dot y x := by
  simp [dot, mul_comm]

/-- `dotChar` is additive in the second argument. -/
lemma dotChar_add_right {k : ℕ} (x v w : Fin k → ZMod q) :
    dotChar x (v + w) = dotChar x v * dotChar x w := by
  simp only [dotChar_apply]
  have h : dot x (v + w) = dot x v + dot x w := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  rw [h, AddChar.map_add_eq_mul]

/-- `dotChar` quotients by differences: `ω^{x·a} (ω^{x·b})⁻¹ = ω^{x·(a - b)}`. -/
lemma dotChar_sub_right {k : ℕ} (x a b : Fin k → ZMod q) :
    dotChar x a * (dotChar x b)⁻¹ = dotChar x (a - b) := by
  rw [← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

/-- Character orthogonality summed over the frequency variable. -/
lemma sum_dotChar_freq {k : ℕ} (c : Fin k → ZMod q) :
    (∑ y : Fin k → ZMod q, dotChar y c) = if c = 0 then (q : ℂ) ^ k else 0 := by
  have h : ∀ y : Fin k → ZMod q, dotChar y c = dotChar c y := by
    intro y
    simp only [dotChar_apply, dot_comm]
  simp_rw [h]
  exact sum_dotChar c

/-- The normalization factor `√(q^m)` is nonzero. -/
lemma sqrtVol_ne_zero (m : ℕ) : sqrtVol q m ≠ 0 := by
  unfold sqrtVol
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h : (0 : ℝ) < (q : ℝ) ^ m := pow_pos hq m
  exact_mod_cast (Real.sqrt_pos.mpr h).ne'

omit [NeZero q] in
/-- The normalization factor squares to `q^m`. -/
lemma sqrtVol_mul_self (m : ℕ) : sqrtVol q m * sqrtVol q m = (q : ℂ) ^ m := by
  unfold sqrtVol
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The DFT is homogeneous under scalar multiplication. -/
lemma dft_const_mul (c : ℂ) (Ψ : Vec q m → ℂ) (x : Vec q m) :
    dft (fun v => c * Ψ v) x = c * dft Ψ x := by
  unfold dft
  rw [show (∑ v, dotChar x v * (c * Ψ v)) = c * ∑ v, dotChar x v * Ψ v from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)]
  ring

/-- `ψ̂` equals the unnormalized DFT divided by `√(q^m)`. -/
lemma mul_sqrtVol_psiHat (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (s : Secret q n) (x : Vec q m) :
    sqrtVol q m * psiHat A f s x = ∑ v, dotChar x v * psi A f s v := by
  rw [psiHat, dft, ← mul_assoc, mul_inv_cancel₀ (sqrtVol_ne_zero m), one_mul]

/-- **Proposition 3**: the Fourier transform of `|ψ_s⟩` satisfies
`ψ̂_s(x) = ω^{(A x)·s} f̂(x)`. -/
theorem psiHat_apply (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (s : Secret q n) (x : Vec q m) :
    psiHat A f s x = dotChar (A.mulVec x) s * fhat f x := by
  unfold psiHat fhat dft
  have h : (∑ v, dotChar x v * psi A f s v)
      = ∑ v, dotChar x ((v - A.transpose.mulVec s) + A.transpose.mulVec s)
          * f (v - A.transpose.mulVec s) := by
    apply Finset.sum_congr rfl
    intro v _
    simp [psi]
  rw [h, sum_sub_shift (F := fun e => dotChar x (e + A.transpose.mulVec s) * f e)
    (c := A.transpose.mulVec s)]
  have hshift : dotChar x (A.transpose.mulVec s) = dotChar (A.mulVec x) s := by
    rw [dotChar_apply, dotChar_apply, dot_transpose_mulVec, dot_comm]
  have hterm : ∀ e, dotChar x (e + A.transpose.mulVec s) * f e
      = dotChar (A.mulVec x) s * (dotChar x e * f e) := by
    intro e
    rw [dotChar_add_right, hshift]
    ring
  simp only [hterm]
  rw [show (∑ e, dotChar (A.mulVec x) s * (dotChar x e * f e))
      = dotChar (A.mulVec x) s * ∑ e, dotChar x e * f e from by rw [Finset.mul_sum]]
  ring

/-- Unnormalized Fourier transform `dft(W_y) = q^n · 1_{Λ_y^⊥(A)} · f̂`. -/
lemma dft_Wraw (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) (x : Vec q m) :
    dft (Wraw A f y) x
      = (if A.mulVec x = y then (q : ℂ) ^ n else 0) * fhat f x := by
  have hexp : dft (Wraw A f y) x
      = (sqrtVol q m)⁻¹ * ∑ s, dotChar (-y) s * (sqrtVol q m * psiHat A f s x) := by
    unfold dft
    congr 1
    calc (∑ v, dotChar x v * Wraw A f y v)
        = ∑ s, dotChar (-y) s * (∑ v, dotChar x v * psi A f s v) := by
          rw [show Wraw A f y = fun v => ∑ s, dotChar (-y) s * psi A f s v from rfl]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun v _ => by ring))
      _ = ∑ s, dotChar (-y) s * (sqrtVol q m * psiHat A f s x) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [mul_sqrtVol_psiHat]
  rw [hexp]
  have hfac : (sqrtVol q m)⁻¹ * ∑ s, dotChar (-y) s * (sqrtVol q m * psiHat A f s x)
      = ∑ s, dotChar (-y) s * psiHat A f s x := by
    have : (∑ s, dotChar (-y) s * (sqrtVol q m * psiHat A f s x))
        = sqrtVol q m * ∑ s, dotChar (-y) s * psiHat A f s x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [this, ← mul_assoc, inv_mul_cancel₀ (sqrtVol_ne_zero m), one_mul]
  rw [hfac]
  have hterm : ∀ s, dotChar (-y) s * psiHat A f s x
      = dotChar (A.mulVec x - y) s * fhat f x := by
    intro s
    rw [psiHat_apply]
    have hadd : dotChar (-y) s * dotChar (A.mulVec x) s
        = dotChar (A.mulVec x - y) s := by
      rw [← dotChar_add]
      congr 1
      abel_nf
    rw [← hadd]
    ring
  simp only [hterm]
  have hsum : (∑ s : Secret q n, dotChar (A.mulVec x - y) s)
      = if A.mulVec x = y then (q : ℂ) ^ n else 0 := by
    rw [sum_dotChar]
    simp [sub_eq_zero]
  rw [← Finset.sum_mul, hsum]

/-- **Proposition 4**: `|Ŵ_y⟩` is supported on the shifted dual lattice `A x = y`
with amplitude `(q^n / √w_y) f̂(x)`. -/
theorem WHat_apply (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) (x : Vec q m) :
    WHat A f y x
      = if A.mulVec x = y
          then ((q : ℂ) ^ n / (Real.sqrt (wNorm A f y) : ℂ)) * fhat f x
          else 0 := by
  unfold WHat Wvec
  rw [dft_const_mul, dft_Wraw]
  by_cases h : A.mulVec x = y
  · simp only [h, ↓reduceIte, div_eq_mul_inv]
    ring
  · simp [h]

/-- **Proposition 5 (forward)**: `|W_y⟩` as the `ω^{-y·s}`-weighted superposition
of `|ψ_s⟩`, normalized by `√w_y`. -/
theorem Wvec_eq_sum (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) (v : Vec q m) :
    Wvec A f y v
      = ((Real.sqrt (wNorm A f y) : ℂ))⁻¹ * ∑ s, dotChar (-y) s * psi A f s v := rfl

/-- **Proposition 5 (inverse)**: `|ψ_s⟩ = q^{-n} ∑_y ω^{y·s} √w_y |W_y⟩` whenever
all weights `w_y` are positive. -/
theorem psi_eq_sum_W (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (s : Secret q n) (hw : ∀ y, 0 < wNorm A f y) (v : Vec q m) :
    psi A f s v
      = ((q : ℂ) ^ n)⁻¹ *
          ∑ y, dotChar y s * (Real.sqrt (wNorm A f y) : ℂ) * Wvec A f y v := by
  have hstep : ∀ y, (Real.sqrt (wNorm A f y) : ℂ) * Wvec A f y v = Wraw A f y v := by
    intro y
    rw [Wvec_eq_sum]
    have hne : (Real.sqrt (wNorm A f y) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw y)).ne'
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rfl
  rw [show (∑ y, dotChar y s * (Real.sqrt (wNorm A f y) : ℂ) * Wvec A f y v)
      = ∑ y, dotChar y s * Wraw A f y v from by
        exact Finset.sum_congr rfl (fun y _ => by rw [mul_assoc, hstep y])]
  have hexp : (∑ y, dotChar y s * Wraw A f y v)
      = ∑ t : Secret q n,
          (∑ y : Secret q n, dotChar y (s - t)) * f (v - A.transpose.mulVec t) := by
    simp only [Wraw, psi]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [dotChar_neg, ← mul_assoc, dotChar_sub_right]
  rw [hexp]
  have hcollapse :
      (∑ t : Secret q n,
          (∑ y : Secret q n, dotChar y (s - t)) * f (v - A.transpose.mulVec t))
        = (q : ℂ) ^ n * f (v - A.transpose.mulVec s) := by
    have hinner : ∀ t : Secret q n,
        (∑ y : Secret q n, dotChar y (s - t)) = if s = t then (q : ℂ) ^ n else 0 := by
      intro t
      rw [sum_dotChar_freq]
      simp [sub_eq_zero]
    simp only [hinner]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      simp [Ne.symm hts]
    · intro hs
      exact absurd (Finset.mem_univ s) hs
  rw [hcollapse, psi]
  have hq : ((q : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne q)
  field_simp

private lemma sum_norm_sq_dotChar (a : Secret q n → ℂ) :
    (∑ y : Secret q n, ‖∑ s : Secret q n, dotChar (-y) s * a s‖ ^ 2)
      = (q : ℝ) ^ n * ∑ s : Secret q n, ‖a s‖ ^ 2 := by
  have hnorm (z : ℂ) : (‖z‖ : ℂ) ^ 2 = z * star z :=
    (Complex.mul_conj' z).symm
  have hconj (y s : Secret q n) : star (dotChar (-y) s) = dotChar y s := by
    calc
      star (dotChar (-y) s) = (dotChar (-y) s)⁻¹ :=
        (AddChar.inv_apply_eq_conj (dotChar (-y)) s).symm
      _ = dotChar y s := by rw [dotChar_neg, inv_inv]
  have hprod (y s t : Secret q n) :
      dotChar (-y) s * star (dotChar (-y) t) = dotChar y (t - s) := by
    rw [hconj, dotChar_neg, mul_comm, dotChar_sub_right]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast, hnorm]
  calc
    (∑ y : Secret q n,
        (∑ s : Secret q n, dotChar (-y) s * a s) *
          star (∑ t : Secret q n, dotChar (-y) t * a t))
        = ∑ y : Secret q n, ∑ s : Secret q n, ∑ t : Secret q n,
            (dotChar (-y) s * star (dotChar (-y) t)) * (a s * star (a t)) := by
          simp only [star_sum, star_mul, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun s _ =>
            Finset.sum_congr rfl (fun t _ => ?_)))
          ring
    _ = ∑ s : Secret q n, ∑ t : Secret q n,
          (∑ y : Secret q n, dotChar y (t - s)) * (a s * star (a t)) := by
          simp_rw [hprod]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
    _ = (q : ℂ) ^ n * ∑ s : Secret q n, a s * star (a s) := by
          simp_rw [sum_dotChar_freq, sub_eq_zero]
          simp [Finset.mul_sum]

/-- **Proposition 6**: for a unit-norm amplitude `f`, the uniform expectation of
`w_y` over `y ∈ Z_q^n` equals `q^n`. -/
theorem expect_wNorm (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (hf : stateNormSq f = 1) :
    (Fintype.card (Secret q n) : ℝ)⁻¹ * ∑ y, wNorm A f y = (q : ℝ) ^ n := by
  have hcard : (Fintype.card (Secret q n) : ℝ) = (q : ℝ) ^ n := by
    simp [Secret, ZMod.card]
  have hq : (q : ℝ) ^ n ≠ 0 :=
    (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) n).ne'
  have hpsi (s : Secret q n) : stateNormSq (psi A f s) = 1 := by
    calc
      stateNormSq (psi A f s) = stateNormSq f := by
        apply Complex.ofReal_injective
        simpa only [stateNormSq, psi, Complex.ofReal_sum] using
          sum_sub_shift (F := fun e => ((‖f e‖ ^ 2 : ℝ) : ℂ))
            (c := A.transpose.mulVec s)
      _ = 1 := hf
  have hsum : (∑ y, wNorm A f y) = (q : ℝ) ^ n * (q : ℝ) ^ n := by
    calc
      (∑ y, wNorm A f y)
          = ∑ v : Vec q m, ∑ y : Secret q n,
              ‖∑ s : Secret q n, dotChar (-y) s * psi A f s v‖ ^ 2 := by
                simp only [wNorm, Wraw]
                rw [Finset.sum_comm]
      _ = ∑ v : Vec q m, (q : ℝ) ^ n * ∑ s : Secret q n, ‖psi A f s v‖ ^ 2 := by
            exact Finset.sum_congr rfl (fun v _ => sum_norm_sq_dotChar (fun s => psi A f s v))
      _ = (q : ℝ) ^ n * ∑ s : Secret q n, stateNormSq (psi A f s) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            rfl
      _ = (q : ℝ) ^ n * (q : ℝ) ^ n := by simp only [hpsi, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  rw [hcard, hsum, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end Qatlib.Papers.QSLWEISIS25.MainResults
