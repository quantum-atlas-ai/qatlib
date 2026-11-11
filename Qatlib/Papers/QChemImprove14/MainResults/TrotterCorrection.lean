/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c003 — corrected Hamiltonian for a nonzero Trotter step

Hastings--Wecker--Bauer--Troyer, fixed arXiv:1403.1539v2 (23 Mar 2014),
Sec. 5 "Corrected Hamiltonian", Eq. (7) and Eq. (8).

For a nonzero Trotter step `δ_t` the second-order Trotter-Suzuki energy shift
picks up a correction factor `f`; the authors simulate a *modified* Hamiltonian
in which

  `V_pqrs ← V_pqrs · f(δ_t (ω_p + ω_q − ω_r − ω_s))`,  (Eq. 8)
  `t_pq    ← t_pq    · f(δ_t (ω_p − ω_q))`,

with the function `f` of Eq. (7).  As `δ_t → 0` the argument tends to `0`, and
`f → 1`, so the modification disappears in the continuous-time limit.

`f` as printed in Eq. (7) is
`f(x) = sqrt(2 (1 − cos x)) / sin x` (the radical covers the numerator).
On the physical branch `0 < x < π` this equals `1 / cos(x/2)`, which is
`slightly larger than 1` and tends to `1` as `x → 0⁺`, exactly as the text
states ("the function `f` is slightly larger than 1 for `x ≠ 0`, so it
increases the off-diagonal terms and goes to 1 as `δ_t → 0`").  We formalize
that branch; the odd extension to negative arguments is not used, since Eq. (8)
is stated for the positive Trotter step `δ_t > 0`.

Note: the OCR of the source splits the radical over both numerator and
denominator, which would give `f → 0`; that reading contradicts the prose and
the derivation `sqrt(2(1−cos x)) = 2|sin(x/2)|`.  We use the prose-consistent
(and physically correct) reading.
-/

set_option autoImplicit false
open Filter
open scoped Topology

namespace Qatlib.Papers.QChemImprove14.MainResults

/-! ## The correction factor `f` of Eq. (7) -/

/-- The correction factor `f` of Eq. (7), `f(x) = sqrt(2(1 − cos x)) / sin x`. -/
noncomputable def trotterFactor (x : ℝ) : ℝ :=
  Real.sqrt (2 * (1 - Real.cos x)) / Real.sin x

/-- Squaring removes the square root: `f(x)^2 = 2(1 − cos x) / sin(x)^2`
(Eq. (7), away from `sin x = 0`). -/
theorem trotterFactor_sq (x : ℝ) :
    trotterFactor x ^ 2 = 2 * (1 - Real.cos x) / Real.sin x ^ 2 := by
  unfold trotterFactor
  have hA : (0 : ℝ) ≤ 2 * (1 - Real.cos x) := by nlinarith [Real.cos_le_one x]
  rw [div_pow, Real.sq_sqrt hA]

/-- On the physical branch `0 < x < π`, Eq. (7) reduces to
`f(x) = 1 / cos(x/2)`.  This is the form in which the text's statements
("`f > 1` for `x ≠ 0`", "`f → 1`") are manifest. -/
theorem trotterFactor_eq_inv_cos (x : ℝ) (h0 : 0 < x) (hπ : x < Real.pi) :
    trotterFactor x = 1 / Real.cos (x / 2) := by
  unfold trotterFactor
  have hx2pos : 0 < x / 2 := by linarith
  have hx2π : x / 2 < Real.pi := by linarith [Real.pi_pos]
  have hsin2 : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi hx2pos hx2π
  have hcos2 : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo (by constructor <;> linarith [Real.pi_pos])
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (x / 2)
    rwa [show 2 * (x / 2) = x by ring] at this
  have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    have := Real.sin_two_mul (x / 2)
    rwa [show 2 * (x / 2) = x by ring] at this
  have hsq := Real.sin_sq_add_cos_sq (x / 2)
  have harg : 2 * (1 - Real.cos x) = (2 * Real.sin (x / 2)) ^ 2 := by
    nlinarith [hcos, hsq]
  have hsqrt : Real.sqrt (2 * (1 - Real.cos x)) = 2 * Real.sin (x / 2) := by
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  rw [hsqrt, hsin]
  field_simp

/-- **Claim c003 (`f > 1` for `x ≠ 0`)**: on `0 < x < π` the correction factor
is strictly larger than `1`, matching the text's "slightly larger than 1". -/
theorem trotterFactor_ge_one (x : ℝ) (h0 : 0 < x) (hπ : x < Real.pi) :
    1 ≤ trotterFactor x := by
  rw [trotterFactor_eq_inv_cos x h0 hπ]
  have hc0 : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo (by constructor <;> linarith [Real.pi_pos])
  have hc1 : Real.cos (x / 2) ≤ 1 := Real.cos_le_one _
  have h := div_le_div_of_nonneg_right hc1 (le_of_lt hc0)
  rwa [div_self (ne_of_gt hc0)] at h

/-- **Claim c003 (`f → 1` as `δ_t → 0`)**: the correction factor tends to `1`
along the physical branch `x → 0⁺`, so the modification disappears in the
continuous-time limit. -/
theorem trotterFactor_tendsto_one :
    Tendsto trotterFactor (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hpi : Set.Iio Real.pi ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds Real.pi_pos)
  have hev : trotterFactor =ᶠ[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => 1 / Real.cos (x / 2)) := by
    filter_upwards [self_mem_nhdsWithin, hpi] with x hx hxπ
    exact trotterFactor_eq_inv_cos x hx hxπ
  have hdiv : Tendsto (fun x : ℝ => x / 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_id.div_const (2 : ℝ) :
      Tendsto (fun x : ℝ => x / 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) / 2)))
  have hcomp : Tendsto (fun x : ℝ => Real.cos (x / 2)) (𝓝 0) (𝓝 1) := by
    have := (Real.continuous_cos.continuousAt (x := (0 : ℝ))).tendsto.comp hdiv
    simpa [Real.cos_zero, Function.comp_def] using this
  have hinv : Tendsto (fun x : ℝ => 1 / Real.cos (x / 2)) (𝓝 0) (𝓝 1) := by
    have h := hcomp.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [one_div] using h
  exact Tendsto.congr' hev.symm (hinv.mono_left nhdsWithin_le_nhds)

/-! ## The modified Hamiltonian of Eq. (8) -/

/-- The modified two-body coefficient `V_pqrs ← V_pqrs · f(δ_t(ω_p+ω_q−ω_r−ω_s))`
of Eq. (8). -/
noncomputable def correctedV (V δ ωp ωq ωr ωs : ℝ) : ℝ :=
  V * trotterFactor (δ * (ωp + ωq - ωr - ωs))

/-- The modified one-body coefficient `t_pq ← t_pq · f(δ_t(ω_p−ω_q))` of Eq. (8). -/
noncomputable def correctedT (t δ ωp ωq : ℝ) : ℝ :=
  t * trotterFactor (δ * (ωp - ωq))

/-- **Claim c003 (`δ_t → 0` limit, two-body)**: for a positive frequency
combination `ω_p+ω_q−ω_r−ω_s > 0`, the corrected `V` tends to `V` as
`δ_t → 0⁺`, i.e. the modification vanishes in the continuous-time limit. -/
theorem correctedV_tendsto (V : ℝ) (ωp ωq ωr ωs : ℝ)
    (hω : 0 < ωp + ωq - ωr - ωs) :
    Tendsto (fun δ : ℝ => correctedV V δ ωp ωq ωr ωs)
      (𝓝[>] (0 : ℝ)) (𝓝 V) := by
  unfold correctedV
  have hg : Tendsto (fun δ : ℝ => δ * (ωp + ωq - ωr - ωs))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using h0.mul_const (ωp + ωq - ωr - ωs)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos hδ hω
  have hcomp := trotterFactor_tendsto_one.comp hg
  have hmul := hcomp.const_mul V
  simpa [mul_one] using hmul

/-- **Claim c003 (`δ_t → 0` limit, one-body)**: for a positive frequency gap
`ω_p−ω_q > 0`, the corrected `t` tends to `t` as `δ_t → 0⁺`. -/
theorem correctedT_tendsto (t : ℝ) (ωp ωq : ℝ) (hω : 0 < ωp - ωq) :
    Tendsto (fun δ : ℝ => correctedT t δ ωp ωq)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
  unfold correctedT
  have hg : Tendsto (fun δ : ℝ => δ * (ωp - ωq))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using h0.mul_const (ωp - ωq)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos hδ hω
  have hcomp := trotterFactor_tendsto_one.comp hg
  have hmul := hcomp.const_mul t
  simpa [mul_one] using hmul

end Qatlib.Papers.QChemImprove14.MainResults
