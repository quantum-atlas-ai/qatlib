/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# MomentumBound — source interface for the maximum single-particle momentum

WaveletQFT14 (arXiv:1412.0750), fixed version v2 (2015-03-12).
Fixed source: https://arxiv.org/abs/1412.0750v2.

This file formalises Section III C "Particle creation in the free field
theory", Eq. (41), Eq. (42), Eq. (43) and Table I.  The two-mode state
`|E⟩ = (α_{r,n} b̂†_r(n) + β_{r,m} b̂†_r(m)) |G⟩` with `r ≥ k` and
`|α|² + |β|² = 1` has momentum expectation

`⟨E| p̂ |E⟩ = 2^r P_{0,n-m}^{0,0} Im[α β*]`          (Eq. 42)

where `P_{0,n-m}^{0,0}` is the overlap integral of Eq. (40).  For `n - m = -1`,
`α = 1/√2`, `β = ∓ i/√2` this is `±2^{r-1} P_{0,-1}^{0,0} = ±0.663 × 2^r`
(Table I: `|P_{0,-1}^{0,0}| = 1.32599`), hence

`p_max = 0.663 × 2^{l_max}`.                          (Eq. 43)

Boundary: this is the amplitude-level two-mode momentum algebra of the paper
(rigid wavelet translates at a fixed scale).  It does not reconstruct the
bosonic Fock space, the field/momentum operators of Eq. (39), nor the ground
state of Eq. (35); those are consumed as the paper's granted semantics.
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WaveletQFT14.MainResults.MomentumBound

open scoped ComplexConjugate



/-- Momentum expectation `⟨E| p̂ |E⟩` of the two-mode state of Eq. (42),
with `P` standing for the overlap integral `P_{0,n-m}^{0,0}` of Eq. (40).

`momentumExpectation r P α β = 2^r · P · Im[α · conj β]`, which is verbatim
the paper's Eq. (42) (arXiv:1412.0750, p. 6). -/
def momentumExpectation (r : ℕ) (P : ℝ) (α β : ℂ) : ℝ :=
  (2 : ℝ) ^ r * P * (α * conj β).im

/-- Eq. (41) check: a *single* mode excitation has vanishing momentum
expectation.  With `|E⟩ = b̂†_r(n)|G⟩` the state is `α = 1`, `β = 0`, and
`Im[1 · conj 0] = 0`, matching `-2^r/2 · P_{0,0} = 0` since Table I gives
`P_{0,0}^{0,0} = 0`.  (arXiv:1412.0750, Eq. (41), p. 6.) -/
theorem single_mode_expectation_zero (r : ℕ) (P : ℝ) :
    momentumExpectation r P 1 0 = 0 := by
  unfold momentumExpectation
  simp

/-- Core amplitude inequality behind Eq. (43): if `|α|² + |β|² = 1` then
`|Im[α · conj β]| ≤ 1/2`.  This is the AM-GM bound
`2|α||β| ≤ |α|² + |β|²`, together with `|Im z| ≤ ‖z‖`.
(arXiv:1412.0750, Eq. (42)–(43), p. 6.) -/
lemma abs_im_mul_conj_le_half {α β : ℂ}
    (h : Complex.normSq α + Complex.normSq β = 1) :
    |(α * conj β).im| ≤ 1 / 2 := by
  have hnorm : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact h
  have hsq : 0 ≤ (‖α‖ - ‖β‖) ^ 2 := sq_nonneg _
  have hab : 2 * ‖α‖ * ‖β‖ ≤ 1 := by nlinarith
  have h1 : |(α * conj β).im| ≤ ‖α * conj β‖ := Complex.abs_im_le_norm _
  rw [norm_mul, Complex.norm_conj] at h1
  nlinarith [norm_nonneg α, norm_nonneg β]

/-- Eq. (43) upper bound at the amplitude level: for `r ≥ 1` and normalised
amplitudes, `|⟨E| p̂ |E⟩| ≤ 2^{r-1} |P|`.  The paper reaches the maximal
magnitude `2^{r-1} P_{0,-1}^{0,0}` precisely in this bound.
(arXiv:1412.0750, Eq. (42) and Eq. (43), p. 6.) -/
theorem momentum_expectation_abs_le {r : ℕ} (hr : 1 ≤ r) {P : ℝ} {α β : ℂ}
    (h : Complex.normSq α + Complex.normSq β = 1) :
    |momentumExpectation r P α β| ≤ (2 : ℝ) ^ (r - 1) * |P| := by
  have hkey := abs_im_mul_conj_le_half h
  have hval : |momentumExpectation r P α β|
      = (2 : ℝ) ^ r * |P| * |(α * conj β).im| := by
    unfold momentumExpectation
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r)]
  have hstep : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    calc (2 : ℝ) ^ r = (2 : ℝ) ^ ((r - 1) + 1) := by
          rw [Nat.sub_add_cancel hr]
      _ = 2 * (2 : ℝ) ^ (r - 1) := by rw [pow_succ]; ring
  rw [hval]
  calc (2 : ℝ) ^ r * |P| * |(α * conj β).im|
      ≤ (2 : ℝ) ^ r * |P| * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (2 : ℝ) ^ (r - 1) * |P| := by
        rw [hstep]; ring

/-- The special amplitudes of Eq. (43) attain the bound: with
`α = 1/√2` and `β = -i/√2` (i.e. `n - m = -1`), `⟨E| p̂ |E⟩ = 2^r P / 2`.
(arXiv:1412.0750, Eq. (43), p. 6.) -/
theorem momentum_expectation_attained (r : ℕ) (P : ℝ) :
    momentumExpectation r P ((1 / Real.sqrt 2 : ℝ) : ℂ)
        (-(Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)))
      = (2 : ℝ) ^ r * P * (1 / 2) := by
  have hsq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have him : (((1 / Real.sqrt 2 : ℝ) : ℂ) *
      conj (-(Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)))).im = 1 / 2 := by
    have hconj : conj (-(Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)))
        = Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
      rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj]
    have hprod : ((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ))
        = Complex.I * (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) := by
      ring
    rw [hprod, Complex.I_mul_im]
    have hcc : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
      rw [← sq]; exact hsq
    rw [← Complex.ofReal_mul, hcc]
    norm_num
  unfold momentumExpectation
  rw [him]

/-- Paper's Table I value: `|P_{0,-1}^{0,0}| = 1.32599` for Daubechies
`K = 3` wavelets (arXiv:1412.0750, Table I, p. 6). -/
def overlapAbsValue : ℝ := 132599 / 100000

/-- Eq. (43), exact numerical value with Table I: the maximal momentum at
scale `lmax` is `0.662995 × 2^{lmax}` (the paper rounds this to `0.663`).
(arXiv:1412.0750, Eq. (43) and Table I, p. 6.) -/
theorem pmax_value (lmax : ℕ) :
    |momentumExpectation lmax (-(overlapAbsValue))
        ((1 / Real.sqrt 2 : ℝ) : ℂ) (-(Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)))|
      = (132599 / 200000) * (2 : ℝ) ^ lmax := by
  rw [momentum_expectation_attained]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ lmax := pow_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ lmax * (-(overlapAbsValue)) * (1 / 2) < 0 := by
    unfold overlapAbsValue
    nlinarith
  rw [abs_of_neg hneg]
  unfold overlapAbsValue
  ring

/-- Eq. (43) as printed: `p_max = 0.663 × 2^{lmax}` (upper bound with the
rounded constant `0.663`; here `663/1000`).
(arXiv:1412.0750, Eq. (43), p. 6.) -/
theorem pmax_le_paper (lmax : ℕ) :
    |momentumExpectation lmax (-(overlapAbsValue))
        ((1 / Real.sqrt 2 : ℝ) : ℂ) (-(Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)))|
      ≤ (663 / 1000) * (2 : ℝ) ^ lmax := by
  rw [pmax_value lmax]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ lmax := by positivity
  have hc : (132599 / 200000 : ℝ) ≤ 663 / 1000 := by norm_num
  nlinarith

/-- Corpus of Eq. (43): every single-particle two-mode state whose overlap
`|P|` is bounded by the Table I value `|P_{0,-1}^{0,0}| = 1.32599`, at any
scale `1 ≤ r ≤ lmax`, has momentum expectation bounded by
`0.663 × 2^{lmax}`.  This is the paper's statement that the maximum momentum
of a single particle state is `p_max = 0.663 × 2^{lmax}`.
(arXiv:1412.0750, Eq. (42)–(43) and Table I, p. 6.) -/
theorem single_particle_momentum_le {lmax r : ℕ} (hl : 1 ≤ lmax) (hr1 : 1 ≤ r)
    (hr : r ≤ lmax) {P : ℝ} (hP : |P| ≤ overlapAbsValue) {α β : ℂ}
    (h : Complex.normSq α + Complex.normSq β = 1) :
    |momentumExpectation r P α β| ≤ (663 / 1000) * (2 : ℝ) ^ lmax := by
  have h1 := momentum_expectation_abs_le (P := P) hr1 h
  have hP' : |P| ≤ 132599 / 100000 := hP
  have hpow : (2 : ℝ) ^ (r - 1) ≤ (2 : ℝ) ^ (lmax - 1) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hbound : (2 : ℝ) ^ (r - 1) * |P|
      ≤ (2 : ℝ) ^ (lmax - 1) * (132599 / 100000) := by
    refine mul_le_mul hpow hP' (abs_nonneg P) (by positivity)
  have hconst : (2 : ℝ) ^ (lmax - 1) * (132599 / 100000)
      = (132599 / 200000) * (2 : ℝ) ^ lmax := by
    have hstep : (2 : ℝ) ^ lmax = 2 * (2 : ℝ) ^ (lmax - 1) := by
      calc (2 : ℝ) ^ lmax = (2 : ℝ) ^ ((lmax - 1) + 1) := by
            rw [Nat.sub_add_cancel hl]
        _ = 2 * (2 : ℝ) ^ (lmax - 1) := by rw [pow_succ]; ring
    rw [hstep]; ring
  rw [hconst] at hbound
  have hfinal : (132599 / 200000 : ℝ) * (2 : ℝ) ^ lmax
      ≤ (663 / 1000) * (2 : ℝ) ^ lmax := by
    have hc : (132599 / 200000 : ℝ) ≤ 663 / 1000 := by norm_num
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  exact le_trans h1 (le_trans hbound hfinal)

/-- Consistency of the constant: `2 × 0.662995 = 1.32599`, i.e. the rounding
`0.663 ≈ 1.32599 / 2` used in Eq. (43).  (arXiv:1412.0750, Eq. (43).) -/
theorem rounded_constant_consistent :
    2 * (132599 / 200000 : ℝ) = 132599 / 100000 := by
  norm_num

end Qatlib.Papers.WaveletQFT14.MainResults.MomentumBound
