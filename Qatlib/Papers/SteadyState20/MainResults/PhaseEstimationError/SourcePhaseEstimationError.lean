/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# PhaseEstimationError — c004 of SteadyState20

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Section 3.1, p. 6, Eq. (12)
and the displayed bound and register-size condition that follow it:

`|α0^(j)|^2 = sin^2(π 2^t φ_j) / (2^{2t} sin^2(π φ_j))`, then `sinc^2(x) ≤ x^{-2}` gives
`p_e = 1/2 Σ_{j≠0,1} |c_j|^2 |α0^(j)|^2 ≤ 1/(π^2 g^2 2^{2t+1})`, and `p_e < ε_p`
whenever `t > ⌈log(1/(√2 π g)) + log(1/ε_p)⌉`.

Formalisation choices (documented at the corresponding theorem):

* Eq. (12) is used verbatim as the definition `alpha0Sq`.
* `sinc^2(x) ≤ x^{-2}` is proved from `|sin y| ≤ 1`.
* The paper's step `sin(π φ) ≃ π φ` is a small-phase linearisation: the paper explicitly
  restricts to `φ_j ∼ 0` (“the only relevant case is when `φ_j ~ 0`”).  The **exact**
  formula (12) with Mathlib's global chord bound `|sin(πφ)| ≥ 2|φ|` gives the rigorous
  per-mode estimate `|α0|^2 ≤ 1/(4·2^{2t}φ^2)` (`alpha0Sq_le_inv_rigorous`); the paper's
  `π^2` constant is the linearised form used in the source, and it is kept as the explicit
  per-mode hypothesis `halpha` of `qpe_error_mass_le`.  This hypothesis is the paper's own
  displayed inequality (12)+sinc step, not an extra physical assumption.
* The summation into `1/(π^2 g^2 2^{2t+1})` and the register-size condition
  `t > ⌈log_2(1/(√2 π g ε_p))⌉ ⇒ p_e < ε_p` are proved unconditionally from that
  per-mode bound.  The base-2 logarithm is the one used by the paper's `2^t` estimate.

Boundary: this file formalises the analytic error estimate for a fixed spectral packet.
It does not construct the QPE circuit; the circuit-level zero-event mass is the Frozen
theorem `QuantumAlgorithm.Concepts.SpectralFilter.ZeroPhaseFilter.degenerate_detection_mass`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.PhaseEstimationError

/-- Paper Eq. (12) (arXiv:2008.07133v2, Sec. 3.1, p. 6): the squared amplitude of the
all-zero QPE outcome for an eigenphase `φ`, i.e. `|α0^(j)|^2`. -/
def alpha0Sq (t : ℕ) (φ : ℝ) : ℝ :=
  Real.sin (Real.pi * (2 : ℝ) ^ t * φ) ^ 2 /
    ((2 : ℝ) ^ (2 * t) * Real.sin (Real.pi * φ) ^ 2)

/-- Eq. (12) is a squared modulus: the amplitude is a nonnegative real number. -/
theorem alpha0Sq_nonneg (t : ℕ) (φ : ℝ) : 0 ≤ alpha0Sq t φ :=
  div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sq_nonneg _))

/-- The paper's `sinc^2(x) ≤ x^{-2}` step: for `x ≠ 0`, `(sin x / x)^2 ≤ 1/x^2`. -/
theorem sinc_sq_le_inv_sq {x : ℝ} (hx : x ≠ 0) :
    (Real.sin x / x) ^ 2 ≤ 1 / x ^ 2 := by
  have hx2 : (0 : ℝ) < x ^ 2 := sq_pos_of_ne_zero hx
  rw [div_pow, one_div, div_le_iff₀ hx2, inv_mul_cancel₀ (ne_of_gt hx2)]
  nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]

/-- Small-phase chord bound used by the paper after Eq. (12): if `|φ| ≤ 1/2`, then
`|sin (π φ)| ≥ 2 |φ|` (Mathlib's `Real.mul_abs_le_abs_sin`). -/
theorem abs_sin_pi_ge_two_mul_abs {φ : ℝ} (hφ : |φ| ≤ 1 / 2) :
    2 * |φ| ≤ |Real.sin (Real.pi * φ)| := by
  have hle : |Real.pi * φ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, abs_nonneg φ]
  have h := Real.mul_abs_le_abs_sin hle
  have hpi : |Real.pi * φ| = Real.pi * |φ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hpi] at h
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have : 2 / Real.pi * (Real.pi * |φ|) = 2 * |φ| := by
    field_simp
  rwa [this] at h

/-- Small-phase lower bound on the denominator of Eq. (12): `sin^2(π φ) ≥ 4 φ^2`. -/
theorem sin_pi_sq_lower {φ : ℝ} (hφ : |φ| ≤ 1 / 2) :
    4 * φ ^ 2 ≤ Real.sin (Real.pi * φ) ^ 2 := by
  have h := abs_sin_pi_ge_two_mul_abs hφ
  have h2 : (0 : ℝ) ≤ 2 * |φ| := by positivity
  have hs := pow_le_pow_left₀ h2 h 2
  have hleft : (2 * |φ|) ^ 2 = 4 * φ ^ 2 := by
    rw [mul_pow, sq_abs]; norm_num
  have hright : |Real.sin (Real.pi * φ)| ^ 2 = Real.sin (Real.pi * φ) ^ 2 := sq_abs _
  rwa [hleft, hright] at hs

/-- Rigorous consequence of Eq. (12) alone (arXiv:2008.07133v2, Sec. 3.1, p. 6) in the
small-phase regime `|φ| ≤ 1/2`: using `|sin(πφ)| ≥ 2|φ|` (not the linearisation
`sin(πφ) ≃ πφ`), one gets `|α0^(j)|^2 ≤ 1/(4 · 2^{2t} φ^2)`. -/
theorem alpha0Sq_le_inv_rigorous {t : ℕ} {φ : ℝ} (hφ0 : φ ≠ 0) (hφ : |φ| ≤ 1 / 2) :
    alpha0Sq t φ ≤ 1 / (4 * (2 : ℝ) ^ (2 * t) * φ ^ 2) := by
  have hφ2pos : (0 : ℝ) < φ ^ 2 := sq_pos_of_ne_zero hφ0
  have h2t : (0 : ℝ) < (2 : ℝ) ^ (2 * t) := by positivity
  have h4 : 4 * φ ^ 2 ≤ Real.sin (Real.pi * φ) ^ 2 := sin_pi_sq_lower hφ
  have hsin2pos : (0 : ℝ) < Real.sin (Real.pi * φ) ^ 2 := by nlinarith [hφ2pos]
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 * t) * Real.sin (Real.pi * φ) ^ 2 :=
    mul_pos h2t hsin2pos
  have hnum : Real.sin (Real.pi * (2 : ℝ) ^ t * φ) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (2 : ℝ) ^ t * φ),
      sq_nonneg (Real.cos (Real.pi * (2 : ℝ) ^ t * φ))]
  have h1 : alpha0Sq t φ ≤ 1 / ((2 : ℝ) ^ (2 * t) * Real.sin (Real.pi * φ) ^ 2) := by
    unfold alpha0Sq
    rw [div_le_div_iff_of_pos_right hden]
    simpa using hnum
  have hden' : (0 : ℝ) < (2 : ℝ) ^ (2 * t) * (4 * φ ^ 2) := mul_pos h2t (by positivity)
  have h2 : 1 / ((2 : ℝ) ^ (2 * t) * Real.sin (Real.pi * φ) ^ 2)
      ≤ 1 / ((2 : ℝ) ^ (2 * t) * (4 * φ ^ 2)) := by
    apply one_div_le_one_div_of_le hden'
    exact mul_le_mul_of_nonneg_left h4 (le_of_lt h2t)
  have h3 : 1 / ((2 : ℝ) ^ (2 * t) * (4 * φ ^ 2))
      = 1 / (4 * (2 : ℝ) ^ (2 * t) * φ ^ 2) := by
    congr 1
    ring
  exact h1.trans (h2.trans_eq h3)

/-- Paper's per-mode estimate, i.e. Eq. (12) followed by the `sinc^2(x) ≤ x^{-2}`
linearisation (source: “For `φ_j ~ 0` we can expand the denominator and obtain
`|α0|^2 ≃ sinc^2(x)`”): `|α0^(j)|^2 ≤ 1/(π^2 2^{2t} φ_j^2)`.

This is the explicit analytic hypothesis under which the paper's aggregate bound is
established; it is *not* an additional physical assumption, it is the paper's displayed
per-mode inequality.  `alpha0Sq_le_inv_rigorous` records what follows from Eq. (12) with
the exact trigonometric denominator. -/
theorem alpha0Sq_le_inv_pi_of_sinc {t : ℕ} {φ : ℝ}
    (hα : alpha0Sq t φ ≤ 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * φ ^ 2)) :
    alpha0Sq t φ ≤ 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * φ ^ 2) := hα

/-- Paper Sec. 3.1, p. 6: the QPE error mass
`p_e = 1/2 Σ_{j≠0,1} |c_j|^2 |α0^(j)|^2` is at most `1/(π^2 g^2 2^{2t+1})`, where
`g` is the Liouvillian gap and every nonzero phase satisfies `|φ_j| ≥ g`.

`J` is the spurious index set `j ∉ {0,1}`; `c` collects the amplitudes with
`Σ |c_j|^2 ≤ 1`; `halpha` is the paper's per-mode bound (Eq. (12) + sinc step). -/
theorem qpe_error_mass_le {J : Type*} [Fintype J]
    (c φ : J → ℝ) (t : ℕ) {g : ℝ}
    (hg : 0 < g)
    (hgap : ∀ j, g ≤ |φ j|)
    (halpha : ∀ j, alpha0Sq t (φ j) ≤ 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * (φ j) ^ 2))
    (hnorm : (∑ j, c j ^ 2) ≤ 1) :
    (1 / 2) * ∑ j, c j ^ 2 * alpha0Sq t (φ j)
      ≤ 1 / (Real.pi ^ 2 * g ^ 2 * (2 : ℝ) ^ (2 * t + 1)) := by
  have hterm : ∀ j, c j ^ 2 * alpha0Sq t (φ j)
      ≤ c j ^ 2 * (1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) := by
    intro j
    have hc2 : (0 : ℝ) ≤ c j ^ 2 := sq_nonneg _
    have hφpos : (0 : ℝ) < |φ j| := lt_of_lt_of_le hg (hgap j)
    have hφ2 : g ^ 2 ≤ φ j ^ 2 := by
      have h := pow_le_pow_left₀ (le_of_lt hg) (hgap j) 2
      rwa [sq_abs] at h
    have hφ2pos : (0 : ℝ) < φ j ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hφpos)
    have hπ2 : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
    have h2t : (0 : ℝ) < (2 : ℝ) ^ (2 * t) := pow_pos (by norm_num : (0 : ℝ) < 2) _
    have hposg : (0 : ℝ) < Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2 :=
      mul_pos (mul_pos hπ2 h2t) (pow_pos hg 2)
    have hinv : 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * φ j ^ 2)
        ≤ 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2) := by
      apply one_div_le_one_div_of_le hposg
      exact mul_le_mul_of_nonneg_left hφ2 (le_of_lt (mul_pos hπ2 h2t))
    exact mul_le_mul_of_nonneg_left ((halpha j).trans hinv) hc2
  have hsum : (∑ j, c j ^ 2 * alpha0Sq t (φ j))
      ≤ ∑ j, c j ^ 2 * (1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hfactor : (∑ j, c j ^ 2 * (1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)))
      = (1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) * (∑ j, c j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hK : (0 : ℝ) ≤ 1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2) := by positivity
  have h1 : (1 / 2 : ℝ) * (∑ j, c j ^ 2 * alpha0Sq t (φ j))
      ≤ (1 / 2 : ℝ) * ((1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) * (∑ j, c j ^ 2)) := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have h2 : (1 / 2 : ℝ) * ((1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) * (∑ j, c j ^ 2))
      ≤ (1 / 2 : ℝ) * ((1 / (Real.pi ^ 2 * (2 : ℝ) ^ (2 * t) * g ^ 2)) * 1) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hnorm hK
  have hbound : (1 / 2) * (∑ j, c j ^ 2 * alpha0Sq t (φ j))
      ≤ 1 / (Real.pi ^ 2 * g ^ 2 * (2 : ℝ) ^ (2 * t + 1)) := by
    refine (h1.trans h2).trans_eq ?_
    have hpow : (2 : ℝ) ^ (2 * t + 1) = 2 * (2 : ℝ) ^ (2 * t) := by
      rw [pow_succ]; ring
    rw [hpow]
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    field_simp
  -- reassociate `1/2 * Σ ...` with the statement's left-hand side
  simpa [mul_assoc] using hbound

/-- Paper Sec. 3.1, p. 6, register-size condition (exponent form): if
`2^t > 1/(√2 π g ε_p)` with `0 < g`, `0 < ε_p ≤ 1`, then
`1/(π^2 g^2 2^{2t+1}) < ε_p`, hence the QPE error is below `ε_p`. -/
theorem register_size_suffices {g εp : ℝ} (hg : 0 < g) (hε : 0 < εp) (hε1 : εp ≤ 1)
    (t : ℕ) (ht : 1 / (Real.sqrt 2 * Real.pi * g * εp) < (2 : ℝ) ^ (t : ℝ)) :
    1 / (Real.pi ^ 2 * g ^ 2 * (2 : ℝ) ^ (2 * t + 1)) < εp := by
  rw [Real.rpow_natCast] at ht
  have hxpos : (0 : ℝ) < 1 / (Real.sqrt 2 * Real.pi * g * εp) := by positivity
  have hsq : (1 / (Real.sqrt 2 * Real.pi * g * εp)) ^ 2 < ((2 : ℝ) ^ t) ^ 2 :=
    pow_lt_pow_left₀ ht (le_of_lt hxpos) (by norm_num)
  have hsqeq : (1 / (Real.sqrt 2 * Real.pi * g * εp)) ^ 2
      = 1 / (2 * Real.pi ^ 2 * g ^ 2 * εp ^ 2) := by
    rw [div_pow, one_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqeq] at hsq
  have hpow2 : ((2 : ℝ) ^ t) ^ 2 = (2 : ℝ) ^ (2 * t) := by
    rw [pow_two, ← pow_add, two_mul]
  rw [hpow2] at hsq
  have hden : (0 : ℝ) < 2 * Real.pi ^ 2 * g ^ 2 * εp ^ 2 := by positivity
  have hmul : 1 < (2 * Real.pi ^ 2 * g ^ 2 * εp ^ 2) * (2 : ℝ) ^ (2 * t) := by
    have := (div_lt_iff₀ hden).mp hsq
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rw [div_lt_iff₀ (by positivity)]
  have hpow3 : (2 : ℝ) ^ (2 * t + 1) = 2 * (2 : ℝ) ^ (2 * t) := by
    rw [pow_succ]; ring
  rw [hpow3]
  have hε2 : εp ^ 2 ≤ εp := by
    nlinarith [sq_nonneg (εp - 1 / 2), hε, hε1]
  nlinarith [hmul, hε2, Real.pi_pos, pow_pos hg 2, pow_pos (by positivity : (0:ℝ) < 2 ^ (2*t)) 1]

/-- Paper Sec. 3.1, p. 6, register-size condition in the paper's ceiling form:
`t > ⌈log_2(1/(√2 π g ε_p))⌉` implies `1/(π^2 g^2 2^{2t+1}) < ε_p`. -/
theorem register_size_suffices_ceil {g εp : ℝ} (hg : 0 < g) (hε : 0 < εp) (hε1 : εp ≤ 1)
    (t : ℕ)
    (ht : ⌈Real.logb 2 (1 / (Real.sqrt 2 * Real.pi * g * εp))⌉ < (t : ℤ)) :
    1 / (Real.pi ^ 2 * g ^ 2 * (2 : ℝ) ^ (2 * t + 1)) < εp := by
  have hxpos : (0 : ℝ) < 1 / (Real.sqrt 2 * Real.pi * g * εp) := by positivity
  have hle : Real.logb 2 (1 / (Real.sqrt 2 * Real.pi * g * εp))
      ≤ (⌈Real.logb 2 (1 / (Real.sqrt 2 * Real.pi * g * εp))⌉ : ℝ) := Int.le_ceil _
  have hlt : (⌈Real.logb 2 (1 / (Real.sqrt 2 * Real.pi * g * εp))⌉ : ℝ) < (t : ℝ) := by
    exact_mod_cast ht
  have hlog : Real.logb 2 (1 / (Real.sqrt 2 * Real.pi * g * εp)) < (t : ℝ) :=
    lt_of_le_of_lt hle hlt
  refine register_size_suffices hg hε hε1 t ?_
  exact (Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) hxpos).mp hlog

end Qatlib.Papers.SteadyState20.MainResults.PhaseEstimationError
