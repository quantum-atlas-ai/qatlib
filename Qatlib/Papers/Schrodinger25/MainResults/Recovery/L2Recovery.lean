/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — L² recovery error (Theorem 5.2)

Fixed paper version: arXiv:2505.00370.  Source statement: Theorem 5.2, p. 27.
If `ψ ∈ L²(ℝ)` satisfies condition (H2) (p. 23): `|ψ(p) − e^{−p}| ≤ ε` for
`p ∈ [p*, R]`, the recovery `u_f*(T,p) = e^p w(T,p)` obeys

  `(1/L*) ∫_{p*+λ⁺T}^{R−λ⁻T} ‖u_f*(T,p) − u_f(T)‖² dp ≲ ε² ‖u_I‖²`,

where `L* = R − p* − (λ⁺ + λ⁻)T` is the length of the recovery domain.

The paper's proof (p. 27) is "Theorem 5.1 and Remark 5.1".  In the
characteristic model this is the computation

  `e^p(ψ(p−λ_jT) − e^{−(p−λ_jT)}) u_j = e^p δ_j u_j`,  `|δ_j| ≤ ε`,

so the squared error is at most `e^{2p}ε²‖u_I‖²`; averaging over the recovery
interval and bounding `e^{2p}` by its value at the right endpoint gives the
stated average bound with the explicit constant `e^{2(R−λ⁻T)}`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset MeasureTheory

namespace Qatlib.Papers.Schrodinger25.MainResults.Recovery

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Pointwise recovery error under (H2): if every footpoint `p − λ_j T` lies in
`[p*, R]`, then `‖u_f*(T,p) − u_f(T)‖² ≤ e^{2p} ε² ‖u_I‖²`. -/
theorem recovery_error_pointwise
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (pstar R T ε p : ℝ)
    (hε : 0 ≤ ε)
    (hH2 : ∀ q, q ∈ Set.Icc pstar R → ‖ψ q - Complex.exp (-(q : ℂ))‖ ≤ ε)
    (hin : ∀ j, p - lam j * T ∈ Set.Icc pstar R) :
    vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j)
      ≤ Real.exp (2 * p) * ε ^ 2 * vecNormSq u := by
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (2 * p) := (Real.exp_pos _).le
  unfold vecNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hq : p - lam j * T ∈ Set.Icc pstar R := hin j
  have hdiff : recovery ψ lam u T p j - evolved lam u T j
      = (Real.exp p : ℂ) * (ψ (p - lam j * T) - Complex.exp (-((p - lam j * T : ℝ) : ℂ))) * u j := by
    have hmain : (Real.exp p : ℂ) * Complex.exp (-((p - lam j * T : ℝ) : ℂ))
        = (Real.exp (lam j * T) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.ofReal_exp]
      congr 1
      push_cast
      ring_nf
    simp only [recovery, charSolution, evolved]
    rw [← hmain]
    ring
  have hexpp : ‖(Real.exp p : ℂ)‖ = Real.exp p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos p)]
  have hδ : ‖ψ (p - lam j * T) - Complex.exp (-((p - lam j * T : ℝ) : ℂ))‖ ≤ ε :=
    hH2 (p - lam j * T) hq
  have hnorm : ‖recovery ψ lam u T p j - evolved lam u T j‖
      = Real.exp p * ‖ψ (p - lam j * T) - Complex.exp (-((p - lam j * T : ℝ) : ℂ))‖ * ‖u j‖ := by
    rw [hdiff, norm_mul, norm_mul, hexpp]
  rw [hnorm]
  have hstep : Real.exp p *
      ‖ψ (p - lam j * T) - Complex.exp (-((p - lam j * T : ℝ) : ℂ))‖ * ‖u j‖
      ≤ Real.exp p * ε * ‖u j‖ := by
    have := mul_le_mul_of_nonneg_left hδ (Real.exp_pos p).le
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  calc (Real.exp p *
        ‖ψ (p - lam j * T) - Complex.exp (-((p - lam j * T : ℝ) : ℂ))‖ * ‖u j‖) ^ 2
      ≤ (Real.exp p * ε * ‖u j‖) ^ 2 := pow_le_pow_left₀ (by positivity) hstep 2
    _ = Real.exp (2 * p) * ε ^ 2 * ‖u j‖ ^ 2 := by
        rw [show Real.exp (2 * p) = Real.exp p * Real.exp p from by
          rw [← Real.exp_add]; ring_nf]
        ring

/-- Continuity in `p` of the squared recovery error. -/
theorem continuous_recovery_error
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (lam : ι → ℝ) (u : ι → ℂ) (T : ℝ) :
    Continuous fun p : ℝ =>
      vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j) := by
  unfold vecNormSq recovery charSolution evolved
  refine continuous_finsetSum _ fun j _ => ?_
  have hexp : Continuous fun p : ℝ => (Real.exp p : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_exp
  have hψt : Continuous fun p : ℝ => ψ (p - lam j * T) :=
    hψ.comp (continuous_id.sub continuous_const)
  have h1 : Continuous fun p : ℝ =>
      (Real.exp p : ℂ) * (ψ (p - lam j * T) * u j) - (Real.exp (lam j * T) : ℂ) * u j :=
    (hexp.mul (hψt.mul continuous_const)).sub (continuous_const.mul continuous_const)
  exact (h1.norm).pow 2

/-- **Theorem 5.2** (p. 27).  Average L² recovery error under (H2):
with `L* = (R − λ⁻T) − (p* + λ⁺T) > 0`,

  `(1/L*) ∫ ‖u_f*(T,p) − u_f(T)‖² dp ≤ e^{2(R−λ⁻T)} ε² ‖u_I‖²`,

the explicit constant realizing the paper's `≲ ε²‖u_I‖²`. -/
theorem theorem_five_two_recovery_L2_error
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (lam : ι → ℝ) (u : ι → ℂ)
    (pstar R lamPos lamNeg T ε : ℝ)
    (hT : 0 ≤ T) (hpos : ∀ j, lam j ≤ lamPos) (hneg : ∀ j, -lamNeg ≤ lam j)
    (hε : 0 ≤ ε)
    (hH2 : ∀ q, q ∈ Set.Icc pstar R → ‖ψ q - Complex.exp (-(q : ℂ))‖ ≤ ε)
    (hL : 0 < (R - lamNeg * T) - (pstar + lamPos * T)) :
    (1 / ((R - lamNeg * T) - (pstar + lamPos * T))) *
        (∫ p in (pstar + lamPos * T)..(R - lamNeg * T),
          vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j))
      ≤ Real.exp (2 * (R - lamNeg * T)) * ε ^ 2 * vecNormSq u := by
  set a := pstar + lamPos * T with ha_def
  set b := R - lamNeg * T with hb_def
  have hcont := continuous_recovery_error ψ hψ lam u T
  have hfInt : IntervalIntegrable
      (fun p : ℝ => vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j)) volume a b :=
    hcont.intervalIntegrable a b
  have hbound : ∀ p ∈ Set.Icc a b,
      vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j)
        ≤ Real.exp (2 * b) * ε ^ 2 * vecNormSq u := by
    intro p hp
    have hin : ∀ j, p - lam j * T ∈ Set.Icc pstar R := by
      intro j
      have h1 : lam j * T ≤ lamPos * T := mul_le_mul_of_nonneg_right (hpos j) hT
      have h3 : -lamNeg * T ≤ lam j * T := mul_le_mul_of_nonneg_right (hneg j) hT
      have hp1 : pstar + lamPos * T ≤ p := by simpa [ha_def] using hp.1
      have hp2 : p ≤ R - lamNeg * T := by simpa [hb_def] using hp.2
      constructor <;> linarith
    have hr := recovery_error_pointwise ψ lam u pstar R T ε p hε hH2 hin
    have hexp_le : Real.exp (2 * p) ≤ Real.exp (2 * b) :=
      Real.exp_le_exp.mpr (by linarith [hp.2])
    have hW : 0 ≤ vecNormSq u := vecNormSq_nonneg u
    calc vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j)
        ≤ Real.exp (2 * p) * ε ^ 2 * vecNormSq u := hr
      _ ≤ Real.exp (2 * b) * ε ^ 2 * vecNormSq u := by
          have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
          have : Real.exp (2 * p) * (ε ^ 2 * vecNormSq u)
              ≤ Real.exp (2 * b) * (ε ^ 2 * vecNormSq u) :=
            mul_le_mul_of_nonneg_right hexp_le (mul_nonneg hε2 hW)
          linarith [this]
  have hab : a ≤ b := by linarith
  have hInt : (∫ p in a..b,
        vecNormSq (fun j => recovery ψ lam u T p j - evolved lam u T j))
      ≤ (b - a) * (Real.exp (2 * b) * ε ^ 2 * vecNormSq u) := by
    have h := intervalIntegral.integral_mono_on hab hfInt intervalIntegrable_const hbound
    rw [intervalIntegral.integral_const] at h
    have hEq : (b - a) • (Real.exp (2 * b) * ε ^ 2 * vecNormSq u)
        = (b - a) * (Real.exp (2 * b) * ε ^ 2 * vecNormSq u) := by rw [smul_eq_mul]
    rw [hEq] at h
    exact h
  have hpos_inv : 0 ≤ 1 / (b - a) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hInt hpos_inv
  have hcancel : (1 / (b - a)) * ((b - a) * (Real.exp (2 * b) * ε ^ 2 * vecNormSq u))
      = Real.exp (2 * b) * ε ^ 2 * vecNormSq u := by
    field_simp
  rw [hcancel] at hmul
  simpa [ha_def, hb_def] using hmul

end Qatlib.Papers.Schrodinger25.MainResults.Recovery
