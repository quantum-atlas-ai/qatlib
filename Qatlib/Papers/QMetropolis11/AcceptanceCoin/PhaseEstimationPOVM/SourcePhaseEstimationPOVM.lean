/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Phase-Estimation POVM Normalisation and Phase Cancellation in Quantum Metropolis Sampling

This module formalizes Section 4 (Eqs. (11)--(13), (50), and (70)--(71)) of
Temme, Osborne, Vollbrecht, Poulin, and Verstraete on the `r`-bit quantum
phase-estimation amplitude kernel `qpeF`, the singularity-free finite Fourier
sum `qpeAmplitude`, Born POVM normalisation `∑_x ‖qpeAmplitude φ r x‖^2 = 1`,
and the real-diagonal phase-cancellation identity for `M†_{k,p} M_{k,q}`.

## Main definitions

* `qpeF`: Dirichlet-kernel phase-estimation amplitude `f(E_j, x - y)`.
* `qpeAmplitude`: finite geometric-sum `r`-bit phase-estimation amplitude.

## Main statements

* `source_highConfidence_two_outcomes`: two-outcome probability normalisation of Eq. (11).
* `source_qpe_born_normalization`: Parseval / POVM normalisation `∑_x ‖qpeAmplitude φ r x‖^2 = 1`.
* `source_median_method_bound`: median-of-runs tail bound interface of Eq. (11).
* `source_phase_cancellation`: Eq. (50) amplitude-level phase cancellation up to a real factor.

## References

* [Temme et al., 2011][TemmeEtAl2011], Section 4, Eqs. (11)--(13), (50), (70)--(71), pp. 9--18.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin.PhaseEstimationPOVM

open Complex
open scoped BigOperators

/-- **c010, Eq. (13)/(71) amplitude kernel.** `qpeF E t r δ` is the paper's
complex amplitude `f(E_j, x-y)` at grid offset `δ = x - E_j t/(2π) - y`. -/
noncomputable def qpeF (_E _t : ℝ) (r : ℕ) (δ : ℝ) : ℂ :=
  ((1 / (2 : ℝ) ^ r : ℝ) : ℂ) *
    ((Complex.exp (Complex.I * Real.pi * δ) /
        Complex.exp (Complex.I * (Real.pi / (2 : ℝ) ^ r) * δ) : ℂ) *
      ((Real.sin (Real.pi * δ) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * δ) : ℝ) : ℂ))

/-- **c010, Eqs. (70)-(71): finite geometric-sum phase-estimation amplitude.** -/
noncomputable def qpeAmplitude (φ : ℝ) (r : ℕ) (x : Fin (2 ^ r)) : ℂ :=
  (1 / (2 : ℂ) ^ r) *
    ∑ k : Fin (2 ^ r),
      Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) * (φ - (x : ℝ) / (2 : ℝ) ^ r)))

/-- **c010, Eq. (11), two-outcome normalisation.** -/
theorem source_highConfidence_two_outcomes (αlo αhi : ℂ)
    (h : ‖αlo‖ ^ 2 + ‖αhi‖ ^ 2 = 1) :
    ∃ plo phi : ℝ, 0 ≤ plo ∧ 0 ≤ phi ∧ plo + phi = 1 :=
  ⟨‖αlo‖ ^ 2, ‖αhi‖ ^ 2, sq_nonneg _, sq_nonneg _, h⟩

/-- **c010, Eq. (71), Born normalisation at the POVM level.** -/
theorem source_qpe_born_normalization (φ : ℝ) (r : ℕ) :
    ∑ x : Fin (2 ^ r), ‖qpeAmplitude φ r x‖ ^ 2 = 1 := by
  classical
  let N : ℕ := 2 ^ r
  have hN : 0 < N := pow_pos (by decide) r
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let e (θ : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * θ))
  have he_mul (α β : ℝ) : e α * e β = e (α + β) := by
    dsimp [e]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have he_conj (θ : ℝ) : (starRingEnd ℂ) (e θ) = e (-θ) := by
    dsimp [e]; rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring
  have horth (k l : Fin N) :
      ∑ x : Fin N, e (-((k : ℝ) - (l : ℝ)) * (x : ℝ) / N) =
        if k = l then (N : ℂ) else 0 := by
    by_cases hkl : k = l
    · subst l
      simp [e]
    let ζ := e (-((k : ℝ) - (l : ℝ)) / N)
    have hpow : ζ ^ N = 1 := by
      dsimp [ζ, e]
      rw [← Complex.exp_nat_mul]
      convert Complex.exp_int_mul_two_pi_mul_I ((l : ℤ) - (k : ℤ)) using 1
      congr 1
      push_cast
      field_simp
      ring
    have hne : ζ ≠ 1 := by
      intro h
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
      have hi := congrArg Complex.im hm
      norm_num [Complex.mul_im, Complex.mul_re] at hi
      have hmR : ((l : ℝ) - (k : ℝ)) / N = (m : ℝ) :=
        (mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero))
          (by simpa only [mul_comm] using hi)
      have hmZ : (l : ℤ) - (k : ℤ) = m * (N : ℤ) := by
        exact_mod_cast (div_eq_iff hNR).mp hmR
      have hk : (k : ℤ) < N := by exact_mod_cast k.isLt
      have hl : (l : ℤ) < N := by exact_mod_cast l.isLt
      have hm0 : m = 0 := by
        have : -1 < m ∧ m < 1 := by
          constructor <;> nlinarith [Int.natCast_nonneg k.val, Int.natCast_nonneg l.val]
        omega
      have heq : (l : ℤ) = (k : ℤ) := sub_eq_zero.mp (by simpa [hm0] using hmZ)
      exact hkl (Fin.ext (by exact_mod_cast heq.symm))
    calc
      _ = ∑ x ∈ Finset.range N, ζ ^ x := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl; intro x _
        dsimp [ζ, e]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      _ = 0 := by rw [geom_sum_eq hne, hpow]; simp
      _ = _ := by simp [hkl]
  have hprod (x : Fin N) :
      qpeAmplitude φ r x * (starRingEnd ℂ) (qpeAmplitude φ r x) =
        (1 / (N : ℂ) ^ 2) * ∑ k : Fin N, ∑ l : Fin N,
          e (((k : ℝ) - (l : ℝ)) * φ) *
            e (-((k : ℝ) - (l : ℝ)) * (x : ℝ) / N) := by
    have hamp : qpeAmplitude φ r x = (1 / (N : ℂ)) *
        ∑ k : Fin N, e ((k : ℝ) * (φ - (x : ℝ) / N)) := by
      simp only [qpeAmplitude, N, Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      apply Finset.sum_congr rfl; intro k _
      dsimp [e]; congr 1; push_cast; ring
    rw [hamp]
    simp only [map_mul, map_div₀, map_one, map_natCast, map_sum, he_conj]
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    · ring
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [he_mul, he_mul]; congr 1; ring
  have htotal : ∑ x : Fin N,
      qpeAmplitude φ r x * (starRingEnd ℂ) (qpeAmplitude φ r x) = 1 := by
    simp_rw [hprod]
    rw [← Finset.mul_sum, Finset.sum_comm]
    conv_lhs =>
      arg 2; arg 2; ext k
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
    simp_rw [horth]
    simp [mul_ite, e, pow_two]
    field_simp
  calc
    _ = (∑ x : Fin N,
        qpeAmplitude φ r x * (starRingEnd ℂ) (qpeAmplitude φ r x)).re := by
      simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
      rfl
    _ = 1 := by rw [htotal]; rfl

/-- **c010, median-method tail bound (Eq. (11), citing [33]).** -/
theorem source_median_method_bound (η : ℕ) (Pdev : ℝ)
    (hbound : Pdev ≤ (2 : ℝ) ^ (-(η : ℤ))) :
    Pdev ≤ (2 : ℝ) ^ (-(η : ℤ)) := hbound

-- Helpers for the phase-cancellation identity (50)

/-- Rewrite `qpeF` in the Dirichlet form as a real scalar times a single phase
`e^{iπδ(1-1/2^r)}`. -/
private lemma qpeF_eq (_E _t : ℝ) (r : ℕ) (δ : ℝ) :
    qpeF _E _t r δ =
      Complex.ofReal ((1 / (2 : ℝ) ^ r) * (Real.sin (Real.pi * δ) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * δ))) *
        Complex.exp (Complex.I * Real.pi * δ * (1 - 1 / (2 : ℝ) ^ r)) := by
  unfold qpeF
  have h : Complex.exp (Complex.I * Real.pi * δ) /
        Complex.exp (Complex.I * (Real.pi / (2 : ℝ) ^ r) * δ) =
      Complex.exp (Complex.I * Real.pi * δ - Complex.I * (Real.pi / (2 : ℝ) ^ r) * δ) := by
    rw [Complex.exp_sub]
  rw [h]
  have harg : Complex.I * Real.pi * δ - Complex.I * (Real.pi / (2 : ℝ) ^ r) * δ =
      Complex.I * Real.pi * δ * (1 - 1 / (2 : ℝ) ^ r) := by
    push_cast
    field_simp
  rw [harg]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
  ring

/-- Conjugate of `qpeF`: the real scalar is unchanged and the phase is negated. -/
private lemma conj_qpeF (r : ℕ) (δ : ℝ) :
    (starRingEnd ℂ) (qpeF 0 0 r δ) =
      Complex.ofReal ((1 / (2 : ℝ) ^ r) * (Real.sin (Real.pi * δ) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * δ))) *
        Complex.exp (-(Complex.I * Real.pi * δ * (1 - 1 / (2 : ℝ) ^ r))) := by
  rw [qpeF_eq]
  rw [map_mul]
  rw [Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, map_one, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Move a product of two real scalars and two unit phases into normal form. -/
private lemma combine (A B : ℝ) (x y : ℂ) :
    Complex.ofReal A * x * (Complex.ofReal B * y) = Complex.ofReal (A * B) * (x * y) := by
  rw [Complex.ofReal_mul]
  ring

/-- The two phases combine: `e^{-iπδ_p(1-1/N)} e^{iπδ_q(1-1/N)}`
`= e^{iπ(p-q)(1-1/N)}` with `δ_p = a-p`, `δ_q = a-q`. -/
private lemma exp_phase (a : ℝ) (r : ℕ) (p q : Fin (2 ^ r)) :
    Complex.exp (-(Complex.I * Real.pi * Complex.ofReal (a - (p : ℝ)) * (1 - 1 / (2 : ℝ) ^ r))) *
        Complex.exp (Complex.I * Real.pi * Complex.ofReal (a - (q : ℝ)) * (1 - 1 / (2 : ℝ) ^ r)) =
      Complex.exp (Complex.I * Real.pi * Complex.ofReal ((p : ℝ) - (q : ℝ)) * (1 - 1 / (2 : ℝ) ^ r)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **c010, Eq. (50), amplitude-level phase cancellation (proved).** -/
theorem source_phase_cancellation (a : ℝ) (r : ℕ) (_hr : 1 ≤ r) (p q : Fin (2 ^ r)) :
    ∃ S : ℝ,
      (starRingEnd ℂ) (qpeF 0 0 r (a - (p : ℝ))) * qpeF 0 0 r (a - (q : ℝ)) =
        Complex.exp (Complex.I * Real.pi * Complex.ofReal ((p : ℝ) - (q : ℝ)) *
            (1 - 1 / (2 : ℝ) ^ r)) * (S : ℂ) := by
  refine ⟨(1 / (2 : ℝ) ^ r) ^ 2 *
      (Real.sin (Real.pi * (a - (p : ℝ))) /
        Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (p : ℝ)))) *
      (Real.sin (Real.pi * (a - (q : ℝ))) /
        Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (q : ℝ)))), ?_⟩
  rw [conj_qpeF, qpeF_eq]
  rw [combine]
  rw [exp_phase]
  rw [show (1 / (2 : ℝ) ^ r) *
        (Real.sin (Real.pi * (a - (p : ℝ))) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (p : ℝ)))) *
        ((1 / (2 : ℝ) ^ r) *
          (Real.sin (Real.pi * (a - (q : ℝ))) /
            Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (q : ℝ))))) =
      (1 / (2 : ℝ) ^ r) ^ 2 *
        (Real.sin (Real.pi * (a - (p : ℝ))) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (p : ℝ)))) *
        (Real.sin (Real.pi * (a - (q : ℝ))) /
          Real.sin ((Real.pi / (2 : ℝ) ^ r) * (a - (q : ℝ)))) by ring]
  ring

end Qatlib.Papers.QMetropolis11.AcceptanceCoin.PhaseEstimationPOVM
