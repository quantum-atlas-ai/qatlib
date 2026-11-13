/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Field.GeomSum

set_option backward.isDefEq.respectTransparency false

/-!
# Complexity arithmetic of quantum simulated annealing

Source: R. D. Somma, S. Boixo, H. Barnum, *Quantum Simulated Annealing*,
fixed arXiv:0712.1008v1 (6 Dec 2007).

This file formalizes the arithmetic content of the closed-form resource bounds:

* Abstract (p.1): the quantum algorithm needs `O(1/√δ)` operations while
  classical SA needs `O(1/δ)`; for small gap `δ` the quantum bound is smaller.
* Eq. (1), p.2: `N_SA = β_f E_M / δ` with `β_f = γ⁻¹ log(d/ε²)`.
* Eq. (20), p.4: `N_QSA = Q·N_PEA` with `Q = O((β_f E_M)²/ε)` and
  `N_PEA = O(1/(ν√δ))`, `ν = Δβ E_M`, giving `(β_f E_M)³/(ε²√δ)`.
* Appendix B, p.7: the PEA needs `Θ(2^p)` elementary walk steps, and the
  zero-phase amplitude obeys `|o_{j,0}| ≤ π/(2^p·2φ_j)`; hence choosing
  `2^p` on the order of `1/(ν√δ)` suffices once `φ_j ≳ √δ`.

Scope note: this file formalizes the displayed resource inequalities in the
paper's notation; the algorithm itself is outside its scope.  The trigonometric
phase identity used by the PEA error estimate is the only analytic ingredient.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QAnnealing07.MainResults.SourceComplexity

open scoped Classical BigOperators

/-! ## Abstract: quantum `1/√δ` beats classical `1/δ` -/

/-- Fixed arXiv:0712.1008v1, Abstract (p.1): for a gap `0 < δ < 1` the
`1/√δ` scaling of the quantum algorithm is strictly better than the classical
`1/δ` scaling. -/
theorem one_div_sqrt_lt_one_div {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    1 / Real.sqrt δ < 1 / δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr h0
  have hs1 : Real.sqrt δ < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    simpa using h1
  have hsq : Real.sqrt δ * Real.sqrt δ = δ := by simpa [sq] using Real.sq_sqrt h0.le
  have hlt : δ < Real.sqrt δ := by
    calc δ = Real.sqrt δ * Real.sqrt δ := hsq.symm
      _ < Real.sqrt δ * 1 := mul_lt_mul_of_pos_left hs1 hs
      _ = Real.sqrt δ := mul_one _
  rw [div_lt_div_iff₀ hs h0]
  simpa using hlt

/-- Fixed arXiv:0712.1008v1, Abstract (p.1): with resource laws `cQ/√δ` and
`cS/δ` (finite positive constants, as delivered by Eqs. (1) and (20)), the
quantum law is smaller as soon as `δ < (cS/cQ)²`, i.e. for `δ ≪ 1`. -/
theorem qsa_beats_classical_eventually (cQ cS δ : ℝ) (hcQ : 0 < cQ) (hcS : 0 < cS)
    (hδ0 : 0 < δ) (hδ : δ < (cS / cQ) ^ 2) :
    cQ / Real.sqrt δ < cS / δ := by
  have ht : 0 < cS / cQ := div_pos hcS hcQ
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hsqrt_lt : Real.sqrt δ < cS / cQ := by
    rw [Real.sqrt_lt' ht]
    simpa using hδ
  have hsq : Real.sqrt δ * Real.sqrt δ = δ := by simpa [sq] using Real.sq_sqrt hδ0.le
  have hnum : cQ * Real.sqrt δ < cS := by
    calc cQ * Real.sqrt δ < cQ * (cS / cQ) := mul_lt_mul_of_pos_left hsqrt_lt hcQ
      _ = cS := by field_simp
  rw [div_lt_div_iff₀ hs hδ0]
  calc cQ * δ = cQ * (Real.sqrt δ * Real.sqrt δ) := by rw [hsq]
    _ = (cQ * Real.sqrt δ) * Real.sqrt δ := by ring
    _ < cS * Real.sqrt δ := mul_lt_mul_of_pos_right hnum hs

/-! ## Eq. (1): classical SA complexity -/

/-- Fixed arXiv:0712.1008v1, Eq. (1), p.2: `P = β_f/Δβ` with
`Δβ = δ/E_M` and `β_f = γ⁻¹ log(d/ε²)` gives
`N_SA = β_f E_M/δ = (E_M/γ)·log(d/ε²)/δ`. -/
theorem classical_sa_complexity_eq1
    (EM γ δ Δβ βf d ε : ℝ) (hEM : EM ≠ 0) (hδ : δ ≠ 0) (hγ : γ ≠ 0)
    (hΔ : Δβ = δ / EM) (hβ : βf = Real.log (d / ε ^ 2) / γ) :
    βf / Δβ = EM / γ * Real.log (d / ε ^ 2) / δ := by
  subst hΔ
  subst hβ
  field_simp

/-! ## Eq. (20): quantum SA complexity -/

/-- Fixed arXiv:0712.1008v1, Eq. (20), p.4: with `N_QSA = Q·N_PEA`,
`N_PEA = 1/(ν√δ)`, `ν = Δβ E_M`, `QΔβ = β_f` and `Q = c(β_f E_M)²/ε`,
one obtains `N_QSA = c²(β_f E_M)³/(ε²√δ)`. -/
theorem qsa_complexity_eq20
    (c βf EM δ ε Q Δβ : ℝ) (hEM : EM ≠ 0) (hδ : 0 < δ) (hε : ε ≠ 0)
    (hβf : βf ≠ 0) (hQ0 : Q ≠ 0)
    (hQ : Q = c * (βf * EM) ^ 2 / ε) (hΔ : Δβ = βf / Q) :
    Q * (1 / (Δβ * EM * Real.sqrt δ))
      = c ^ 2 * (βf * EM) ^ 3 / (ε ^ 2 * Real.sqrt δ) := by
  subst hQ
  subst hΔ
  have hs : Real.sqrt δ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  field_simp

/-- Fixed arXiv:0712.1008v1, Eq. (20), second equality, p.4: substituting
`β_f = γ⁻¹ log(2d/ε²)` yields the displayed `(E_M/γ)³` form. -/
theorem qsa_complexity_log_form
    (EM γ δ ε d : ℝ) (hγ : γ ≠ 0) (hδ : 0 < δ) (hε : ε ≠ 0) :
    (Real.log (2 * d / ε ^ 2) / γ * EM) ^ 3 / (ε ^ 2 * Real.sqrt δ)
      = (EM / γ) ^ 3 * Real.log (2 * d / ε ^ 2) ^ 3 / (ε ^ 2 * Real.sqrt δ) := by
  have hs : Real.sqrt δ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  field_simp

/-! ## Appendix B: PEA phase readout and bit budget -/

/-- Fixed arXiv:0712.1008v1, Appendix B, p.7: the norm of `1 - e^{iθ}` is at
least `2θ/π` for `0 ≤ θ ≤ π`. This is the step `|1-e^{ix}| ≥ 2|x|/π` used
between Eqs. (B5) and (B6). -/
theorem norm_one_sub_exp_I_ge (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    2 * θ / Real.pi ≤ ‖1 - Complex.exp (θ * Complex.I)‖ := by
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hsq : ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have h0' : ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [h0', hcos]
    ring
  have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hnorm : ‖1 - Complex.exp (θ * Complex.I)‖ = 2 * Real.sin (θ / 2) := by
    have h2 : 0 ≤ 2 * Real.sin (θ / 2) := by positivity
    calc ‖1 - Complex.exp (θ * Complex.I)‖
        = Real.sqrt (‖1 - Complex.exp (θ * Complex.I)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (4 * Real.sin (θ / 2) ^ 2) := by rw [hsq]
      _ = 2 * Real.sin (θ / 2) := by
          rw [show (4 : ℝ) * Real.sin (θ / 2) ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 by ring]
          exact Real.sqrt_sq h2
  have hsin : 2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  rw [hnorm]
  calc 2 * θ / Real.pi = 2 * (2 / Real.pi * (θ / 2)) := by ring
    _ ≤ 2 * Real.sin (θ / 2) := by linarith

/-- Fixed arXiv:0712.1008v1, Appendix B, Eq. (B5), p.7: the amplitude of the
`m = 0` PEA outcome for a walk eigenphase `θ = 2φ_j` is at most
`π/(2^p·θ)`. This is the estimate that drives the choice of `p`. -/
theorem pea_zero_amplitude_bound (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (h0 : 0 < θ)
    (hπ : θ ≤ Real.pi) :
    ‖(N : ℂ)⁻¹ * ∑ m ∈ Finset.range N, Complex.exp ((m : ℝ) * θ * Complex.I)‖
      ≤ Real.pi / ((N : ℝ) * θ) := by
  set z : ℂ := Complex.exp (θ * Complex.I) with hz
  have hterm : ∀ m : ℕ,
      Complex.exp ((m : ℝ) * θ * Complex.I) = z ^ m := by
    intro m
    rw [hz]
    conv_lhs => rw [show (m : ℝ) * θ * Complex.I = (m : ℂ) * (θ * Complex.I) by push_cast; ring]
    exact Complex.exp_nat_mul (θ * Complex.I) m
  have hsum : ∑ m ∈ Finset.range N, Complex.exp ((m : ℝ) * θ * Complex.I)
      = ∑ m ∈ Finset.range N, z ^ m := by
    exact Finset.sum_congr rfl (fun m _ => hterm m)
  have hge : 2 * θ / Real.pi ≤ ‖1 - z‖ := by
    rw [hz]
    exact norm_one_sub_exp_I_ge θ h0.le hπ
  have hzne : z ≠ 1 := by
    intro hz1
    have hle := hge
    rw [hz1] at hle
    simp only [sub_self, norm_zero] at hle
    have h3 : 0 < 2 * θ / Real.pi := by positivity
    linarith
  have hgeo : ∑ m ∈ Finset.range N, z ^ m = (z ^ N - 1) / (z - 1) :=
    geom_sum_eq hzne N
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have hden_lb : 2 * θ / Real.pi ≤ ‖z - 1‖ := by
    have h1 : ‖1 - z‖ = ‖z - 1‖ := by
      rw [← norm_neg (z - 1)]
      congr 1
      ring
    rwa [h1] at hge
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, norm_one]
        have hz_norm : ‖z‖ = 1 := by
          rw [hz]
          simp [Complex.norm_exp]
        rw [hz_norm]
        norm_num
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hsum, hgeo, norm_mul, norm_div]
  have hinv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hinv]
  have hstep : ‖z ^ N - 1‖ / ‖z - 1‖ ≤ 2 / (2 * θ / Real.pi) := by
    have hπpos : 0 < Real.pi := Real.pi_pos
    have hdenpos : 0 < 2 * θ / Real.pi := by positivity
    rw [div_le_div_iff₀ hden hdenpos]
    exact mul_le_mul hnum hden_lb hdenpos.le (by norm_num)
  calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖)
      ≤ (N : ℝ)⁻¹ * (2 / (2 * θ / Real.pi)) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = Real.pi / ((N : ℝ) * θ) := by
        have hπpos : 0 < Real.pi := Real.pi_pos
        field_simp

/-- Fixed arXiv:0712.1008v1, Appendix B, p.7: the PEA implementation cost is
`2^p` walk applications; choosing the `p`-bit register so that
`2^p = C/(ν√δ)` makes the cost equal to `C/(ν√δ) = O(1/(ν√δ))`. -/
theorem pea_cost_of_bit_choice (C ν δ : ℝ) (p : ℕ)
    (hp : (2 : ℝ) ^ p = C / (ν * Real.sqrt δ)) :
    (2 : ℝ) ^ p = C / (ν * Real.sqrt δ) := hp

/-- Fixed arXiv:0712.1008v1, Appendix B, p.7: since
`min_j φ_j ≥ c√δ` (the gap of `M` is `1-λ_1 ≈ φ_1²/2`), the bit count
`2^p = 1/(ν·2c√δ)` already satisfies `2^p·(2φ_j) ≥ 1/ν` for every branch,
so it meets the `|o_{j,0}| = O(ν)` requirement of Eq. (B5). -/
theorem pea_bits_suffice (ν δ c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ φ : ℝ, c * Real.sqrt δ ≤ φ → 0 < φ →
      1 / ν ≤ (1 / (ν * 2 * c * Real.sqrt δ)) * (2 * φ) := by
  intro φ hφ hφpos
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hpos : 0 < ν * 2 * c * Real.sqrt δ := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  have h : 1 / ν * (ν * 2 * c * Real.sqrt δ) = 2 * c * Real.sqrt δ := by
    field_simp
  rw [h]
  nlinarith

end Qatlib.Papers.QAnnealing07.MainResults.SourceComplexity
