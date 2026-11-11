/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.TightDirichletBoundsStat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sharp quadratic bounds for amplification gain ratios

This module proves `Clause7TightDirichletBounds_answer`, bounding the normalized sine ratio
between quadratic expressions with coefficients 1/6 and `(4 * Real.pi - 8) / Real.pi ^ 3`. It
constructs witnesses showing both coefficients are sharp for natural amplification factors at
least three and angles without overshoot, and computes `gainLoss 3` exactly.

Sine amplification and its gain ratios arise in amplitude amplification [BrassardEtAl2002]. For
sharp Dirichlet-kernel bounds for tunable amplification, see [LowSu2026].

## Main statements

* `Clause7TightDirichletBounds_answer`: Proves the two sharp ratio bounds, their optimality, and
  the triple-angle gain identity.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical

/-- The derivative of `Real.cos u - 1 + u ^ 2 / 2` at `t` is `t - Real.sin t`. -/
private theorem hasDerivAt_cos_sub (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos u - 1 + u ^ 2 / 2) (t - Real.sin t) t := by
  have a : HasDerivAt (fun u : ℝ => Real.cos u) (-Real.sin t) t := Real.hasDerivAt_cos t
  have b : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using! (hasDerivAt_id t).pow 2
    have e := this.div_const 2
    have ht : (2 * t : ℝ) / 2 = t := by ring
    rw [ht] at e
    exact e
  have c : HasDerivAt (fun u : ℝ => Real.cos u - 1 + u ^ 2 / 2) ((-Real.sin t - 0) + t) t :=
    (a.sub (hasDerivAt_const t (1:ℝ))).add b
  have hd : (-Real.sin t - 0) + t = t - Real.sin t := by ring
  rw [hd] at c
  exact c

/-- The derivative of `Real.sin u - u + u ^ 3 / 6` at `t` is `Real.cos t - 1 + t ^ 2 / 2`. -/
private theorem hasDerivAt_sin_sub (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin u - u + u ^ 3 / 6)
      (Real.cos t - 1 + t ^ 2 / 2) t := by
  have a : HasDerivAt (fun u : ℝ => Real.sin u) (Real.cos t) t := Real.hasDerivAt_sin t
  have b : HasDerivAt (fun u : ℝ => u) (1:ℝ) t := hasDerivAt_id t
  have c : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (t ^ 2 / 2) t := by
    have d : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ 2) t := by
      simpa using! (hasDerivAt_id t).pow 3
    have e := d.div_const 6
    have ht : (3 * t ^ 2 : ℝ) / 6 = t ^ 2 / 2 := by ring
    rw [ht] at e
    exact e
  have f : HasDerivAt (fun u : ℝ => Real.sin u - u) (Real.cos t - 1) t := a.sub b
  exact f.add c

/-- The derivative of the fifth-order sine polynomial minus sine is the fourth-order cosine
polynomial minus cosine. -/
private theorem hasDerivAt_five (t : ℝ) :
    HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120 - Real.sin u)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
  have a : HasDerivAt (fun u : ℝ => u) (1:ℝ) t := hasDerivAt_id t
  have b : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (t ^ 2 / 2) t := by
    have d : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ 2) t := by
      simpa using! (hasDerivAt_id t).pow 3
    have e := d.div_const 6
    have ht : (3 * t ^ 2 : ℝ) / 6 = t ^ 2 / 2 := by ring
    rw [ht] at e
    exact e
  have c : HasDerivAt (fun u : ℝ => u ^ 5 / 120) (t ^ 4 / 24) t := by
    have d : HasDerivAt (fun u : ℝ => u ^ 5) (5 * t ^ 4) t := by
      simpa using! (hasDerivAt_id t).pow 5
    have e := d.div_const 120
    have ht : (5 * t ^ 4 : ℝ) / 120 = t ^ 4 / 24 := by ring
    rw [ht] at e
    exact e
  have f : HasDerivAt (fun u : ℝ => Real.sin u) (Real.cos t) t := Real.hasDerivAt_sin t
  have g1 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6) (1 - t ^ 2 / 2) t := a.sub b
  have g2 : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120)
      ((1 - t ^ 2 / 2) + t ^ 4 / 24) t := g1.add c
  exact g2.sub f

/-- The derivative of `1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u` is `-u + u ^ 3 / 6 + Real.sin
u`. -/
private theorem hasDerivAt_four (t : ℝ) :
    HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u)
      (-t + t ^ 3 / 6 + Real.sin t) t := by
  have a : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have d : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using! (hasDerivAt_id t).pow 2
    have e := d.div_const 2
    have ht : (2 * t : ℝ) / 2 = t := by ring
    rw [ht] at e
    exact e
  have b : HasDerivAt (fun u : ℝ => u ^ 4 / 24) (t ^ 3 / 6) t := by
    have d : HasDerivAt (fun u : ℝ => u ^ 4) (4 * t ^ 3) t := by
      simpa using! (hasDerivAt_id t).pow 4
    have e := d.div_const 24
    have ht : (4 * t ^ 3 : ℝ) / 24 = t ^ 3 / 6 := by ring
    rw [ht] at e
    exact e
  have c : HasDerivAt (fun u : ℝ => Real.cos u) (-Real.sin t) t := Real.hasDerivAt_cos t
  have g1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24)
      ((0 - t) + t ^ 3 / 6) t :=
    (hasDerivAt_const t (1:ℝ)).sub a |>.add b
  have g2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u)
      (((0 - t) + t ^ 3 / 6) - (-Real.sin t)) t := g1.sub c
  have hd : ((0 - t) + t ^ 3 / 6) - (-Real.sin t) = -t + t ^ 3 / 6 + Real.sin t := by ring
  rw [hd] at g2
  exact g2

/-- For every real `t`, `Real.cos t - 1 + t ^ 2 / 2` is nonnegative. -/
private theorem cos_sub_one_add_sq_nonneg (t : ℝ) : 0 ≤ Real.cos t - 1 + t ^ 2 / 2 := by
  have hsq : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := Real.sin_sq_le_sq
  have h2 : Real.sin (t / 2) ^ 2 = (1 - Real.cos t) / 2 := by
    have := Real.sin_sq_eq_half_sub (t / 2)
    rw [show (2:ℝ) * (t / 2) = t by ring] at this
    have : (1 / 2 : ℝ) - Real.cos t / 2 = (1 - Real.cos t) / 2 := by ring
    linarith
  nlinarith

/-- For nonnegative `x`, sine is bounded below by `x - x ^ 3 / 6`. -/
private theorem sin_ge_sub_cube (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hg_mono : Monotone (fun t : ℝ => Real.sin t - t + t ^ 3 / 6) := by
    apply monotone_of_deriv_nonneg
    · exact fun t => (hasDerivAt_sin_sub t).differentiableAt
    · intro t
      rw [(hasDerivAt_sin_sub t).deriv]
      exact cos_sub_one_add_sq_nonneg t
  have := hg_mono hx
  have hg0 : (fun t : ℝ => Real.sin t - t + t ^ 3 / 6) 0 = 0 := by simp
  linarith

/-- For nonnegative `x`, sine is bounded above by `x - x ^ 3 / 6 + x ^ 5 / 120`. -/
private theorem sin_le_add_five (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hh_mono : MonotoneOn (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (((continuous_id.sub ((continuous_id.pow 3).div_const 6)).add
        ((continuous_id.pow 5).div_const 120)).sub Real.continuous_sin).continuousOn
    · exact Differentiable.differentiableOn fun t => (hasDerivAt_five t).differentiableAt
    · intro t ht
      have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
      rw [(hasDerivAt_five t).deriv]
      have h4mono : MonotoneOn (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u)
          (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact (((continuous_const.sub ((continuous_id.pow 2).div_const 2)).add
            ((continuous_id.pow 4).div_const 24)).sub Real.continuous_cos).continuousOn
        · exact Differentiable.differentiableOn fun u => (hasDerivAt_four u).differentiableAt
        · intro u hu
          have hu0 : 0 ≤ u := Set.mem_Ici.mp (interior_subset hu)
          rw [(hasDerivAt_four u).deriv]
          have := sin_ge_sub_cube u hu0
          linarith
      have h40 : (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u) 0 = 0 := by
        simp
      have := h4mono (by simp : (0:ℝ) ∈ Set.Ici 0) (by simpa using! ht0) ht0
      linarith [this, h40]
  have h0 : (0:ℝ) ∈ Set.Ici 0 := by simp
  have hx' : x ∈ Set.Ici 0 := by simpa using! hx
  have := hh_mono h0 hx' hx
  have hh0 : (fun t : ℝ => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) 0 = 0 := by simp
  linarith [this, hh0]

/-- For amplitudes in the unit interval, `gainLoss 3 a = 1 - (4 / 3) * a ^ 2`. -/
private theorem gainLoss_three (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    gainLoss 3 a = 1 - (4/3)*a^2 := by
  unfold gainLoss
  split_ifs with ha
  · subst ha
    simp
  · push_cast
    have hsin : Real.sin (Real.arcsin a) = a := Real.sin_arcsin (by linarith) ha1
    have h3 : Real.sin (3 * Real.arcsin a) = 3 * a - 4 * a ^ 3 := by
      rw [Real.sin_three_mul, hsin]
    rw [h3]
    have ha3 : (3:ℝ) * a ≠ 0 := by
      have agt : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
      nlinarith
    field_simp

/-- For natural `ρ ≥ 3` and `0 ≤ ρ * θ ≤ Real.pi / 2` with `θ ≥ 0`, the amplified sine is at
least `ρ * Real.sin θ - ρ ^ 3 * Real.sin θ ^ 3 / 6`. -/
private theorem sin_rho_theta_ge (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 ≤ θ)
    (hle : ρ * θ ≤ Real.pi / 2) :
    Real.sin (ρ * θ) ≥ (ρ:ℝ) * Real.sin θ - (ρ:ℝ) ^ 3 * Real.sin θ ^ 3 / 6 := by
  have hρ0 : (0:ℝ) ≤ ρ := by positivity
  have hθle : θ ≤ Real.pi / 2 := by
    have h1 : (ρ:ℝ) * θ ≤ Real.pi / 2 := by exact_mod_cast hle
    have h2 : (0:ℝ) < ρ := by positivity
    have h3 : θ ≤ Real.pi / 2 / ρ := by
      rw [le_div_iff₀ h2]
      nlinarith
    have h4 : Real.pi / 2 / ρ ≤ Real.pi / 2 := by
      have h5 : (1:ℝ) ≤ ρ := by
        have : (1:ℕ) ≤ ρ := by omega
        exact_mod_cast this
      rw [div_le_iff₀ h2]
      nlinarith [Real.pi_pos]
    linarith
  have hsinθ : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos, Real.two_le_pi])
  have hsinθ_le : Real.sin θ ≤ θ := Real.sin_le hθ
  have hρsinθ : (0:ℝ) ≤ (ρ:ℝ) * Real.sin θ := mul_nonneg hρ0 hsinθ
  have hρsinθ_le : (ρ:ℝ) * Real.sin θ ≤ ρ * θ := by
    nlinarith [hsinθ_le, hρ0]
  have hρθ_le : ρ * θ ≤ Real.pi / 2 := by exact_mod_cast hle
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by nlinarith [hρsinθ, Real.pi_pos, Real.two_le_pi] : -(Real.pi/2) ≤ (ρ:ℝ)*Real.sin θ)
    (hρθ_le) (hρsinθ_le)
  have hcube := sin_ge_sub_cube ((ρ:ℝ) * Real.sin θ) hρsinθ
  nlinarith [hmono, hcube, hsinθ_le, hρ0]

/-- The absolute sine of a natural multiple of an angle is at most that multiple of its absolute
sine. -/
private theorem abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) :
    |Real.sin ((n:ℝ) * θ)| ≤ (n:ℝ) * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hadd : Real.sin (((n:ℝ) + 1) * θ)
        = Real.sin ((n:ℝ) * θ) * Real.cos θ + Real.cos ((n:ℝ) * θ) * Real.sin θ := by
      rw [add_mul, one_mul, Real.sin_add]
    push_cast
    rw [hadd]
    have h1 : |Real.sin ((n:ℝ) * θ) * Real.cos θ + Real.cos ((n:ℝ) * θ) * Real.sin θ|
        ≤ |Real.sin ((n:ℝ) * θ) * Real.cos θ| + |Real.cos ((n:ℝ) * θ) * Real.sin θ| :=
      abs_add_le _ _
    have h2 : |Real.sin ((n:ℝ) * θ) * Real.cos θ| + |Real.cos ((n:ℝ) * θ) * Real.sin θ|
        = |Real.sin ((n:ℝ) * θ)| * |Real.cos θ| + |Real.cos ((n:ℝ) * θ)| * |Real.sin θ| := by
      rw [abs_mul, abs_mul]
    have h3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h4 : |Real.cos ((n:ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h5 : (0:ℝ) ≤ |Real.sin ((n:ℝ) * θ)| := abs_nonneg _
    have h6 : (0:ℝ) ≤ |Real.sin θ| := abs_nonneg _
    have h7 : |Real.sin ((n:ℝ) * θ)| * |Real.cos θ| + |Real.cos ((n:ℝ) * θ)| * |Real.sin θ|
        ≤ |Real.sin ((n:ℝ) * θ)| * 1 + 1 * |Real.sin θ| := by
      nlinarith [mul_le_mul_of_nonneg_left h3 h5, mul_le_mul_of_nonneg_left h4 h6]
    have h8 : ((n:ℝ) + 1) * |Real.sin θ| = (n:ℝ) * |Real.sin θ| + |Real.sin θ| := by ring
    nlinarith [ih, h1, h2, h7, h8]

/-- For nonnegative angles and an amplified angle at most `Real.pi / 2`, the amplified sine is
at most the natural amplification factor times the original sine. -/
private theorem sin_nat_mul_le (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθle : θ ≤ Real.pi / 2)
    (hle : (n:ℝ) * θ ≤ Real.pi / 2) : Real.sin ((n:ℝ) * θ) ≤ (n:ℝ) * Real.sin θ := by
  have h1 : 0 ≤ Real.sin ((n:ℝ) * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos, Real.two_le_pi])
  have h2 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos, Real.two_le_pi])
  have := abs_sin_nat_mul_le n θ
  rw [abs_of_nonneg h1, abs_of_nonneg h2] at this
  exact this

/-- For `ρ ≥ 3` and a nonnegative angle without overshoot, the normalized sine ratio, defined as
one at zero, is at least `1 - ρ ^ 2 * Real.sin θ ^ 2 / 6`. -/
private theorem dirichlet_lower (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 ≤ θ)
    (hle : ρ * θ ≤ Real.pi / 2) :
    1 - (ρ:ℝ) ^ 2 * (Real.sin θ) ^ 2 / 6 ≤
      if θ = 0 then 1 else Real.sin (ρ * θ) / (ρ * Real.sin θ) := by
  by_cases hθ0 : θ = 0
  · subst hθ0
    simp
  · rw [if_neg hθ0]
    have h := sin_rho_theta_ge ρ θ hρ hθ hle
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
    have hθle : θ ≤ Real.pi / 2 := by
      have h1 : (ρ:ℝ) * θ ≤ Real.pi / 2 := by exact_mod_cast hle
      have h2 : (0:ℝ) < ρ := by positivity
      have h3 : θ ≤ Real.pi / 2 / ρ := by
        rw [le_div_iff₀ h2]; nlinarith
      have h4 : Real.pi / 2 / ρ ≤ Real.pi / 2 := by
        have h5 : (1:ℝ) ≤ ρ := by
          have : (1:ℕ) ≤ ρ := by omega
          exact_mod_cast this
        rw [div_le_iff₀ h2]; nlinarith [Real.pi_pos]
      linarith
    have hsinθpos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos, Real.two_le_pi])
    have hρpos : (0:ℝ) < ρ := by positivity
    have hpos : (0:ℝ) < (ρ:ℝ) * Real.sin θ := mul_pos hρpos hsinθpos
    rw [le_div_iff₀ hpos]
    nlinarith [h, hsinθpos, hρpos, hθ, Real.sin_le hθ]

/-- For `r ≥ 2` and positive `θ` with `r * θ ≤ Real.pi / 2`, the cubic drop minus its
fifth-order correction is nonnegative. -/
private theorem cubic_drop_nonneg (r θ : ℝ) (hr : 2 ≤ r) (hθ : 0 < θ)
    (hle : r * θ ≤ Real.pi / 2) :
    0 ≤ θ ^ 3 * (r ^ 3 - r) / 6 - r ^ 5 * θ ^ 5 / 120 := by
  have hposr : 0 < r := by linarith
  have hθ0 : 0 ≤ θ := le_of_lt hθ

  have hsq : (0:ℝ) ≤ 2 * r * θ := by positivity
  have hlin : 2 * r * θ ≤ Real.pi := by nlinarith [hle]
  have hprod : (0:ℝ) ≤ (Real.pi - 2 * r * θ) * (Real.pi + 2 * r * θ) :=
    mul_nonneg (by nlinarith) (by nlinarith [Real.pi_pos, hsq])
  have hring : (Real.pi - 2 * r * θ) * (Real.pi + 2 * r * θ)
      = Real.pi ^ 2 - 4 * r ^ 2 * θ ^ 2 := by ring
  have h4 : 4 * r ^ 2 * θ ^ 2 ≤ Real.pi ^ 2 := by nlinarith [hring, hprod]

  have hpi2 : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]

  have h4b : r ^ 4 * θ ^ 2 ≤ 4 * r ^ 2 := by
    have h := h4
    have hsq2 : 0 ≤ r ^ 2 := by positivity
    have : 4 * r ^ 4 * θ ^ 2 = r ^ 2 * (4 * r ^ 2 * θ ^ 2) := by ring
    nlinarith [this, h, hsq2, hpi2]

  have hkey : r ^ 2 * 20 - 20 ≥ r ^ 4 * θ ^ 2 := by
    have : r ^ 2 * 20 - 20 - r ^ 4 * θ ^ 2 = (r ^ 2 - 1) * 20 - r ^ 4 * θ ^ 2 := by ring
    have hre : r ^ 2 * 20 - 20 ≥ 4 * r ^ 2 := by nlinarith [hr]
    nlinarith [h4b, hre, sq_nonneg r]

  have hfactor : θ ^ 3 * (r ^ 3 - r) / 6 - r ^ 5 * θ ^ 5 / 120
      = θ ^ 3 * r * ((r ^ 2 - 1) / 6 - r ^ 4 * θ ^ 2 / 120) := by ring
  rw [hfactor]
  have hθ3 : (0:ℝ) ≤ θ ^ 3 := by positivity
  have hbase : (0:ℝ) ≤ θ ^ 3 * r := mul_nonneg hθ3 (le_of_lt hposr)
  apply mul_nonneg hbase
  have hrearr : (r ^ 2 - 1) / 6 - r ^ 4 * θ ^ 2 / 120
      = (r ^ 2 * 20 - 20 - r ^ 4 * θ ^ 2) / 120 := by ring
  rw [hrearr]
  apply div_nonneg _ (by norm_num)
  nlinarith [hkey]

/-- For `ρ ≥ 3` and a positive angle without overshoot, the drop in normalized sine ratio is at
least `θ ^ 2 * (ρ ^ 2 - 1) / 6 - ρ ^ 4 * θ ^ 4 / 120`. -/
private theorem drop_ge_poly (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 < θ)
    (hle : ρ * θ ≤ Real.pi / 2) :
    1 - Real.sin (ρ * θ) / (ρ * Real.sin θ) ≥
      θ ^ 2 * ((ρ:ℝ) ^ 2 - 1) / 6 - (ρ:ℝ) ^ 4 * θ ^ 4 / 120 := by
  have hρpos : (0:ℝ) < ρ := by positivity
  have hρ0 : (0:ℝ) ≤ ρ := le_of_lt hρpos
  have hθ0 : 0 ≤ θ := le_of_lt hθ
  have hρθ_le : (ρ:ℝ) * θ ≤ Real.pi / 2 := by exact_mod_cast hle
  have hθle : θ ≤ Real.pi / 2 := by
    have h3 : θ ≤ Real.pi / 2 / ρ := by
      rw [le_div_iff₀ hρpos]; nlinarith
    have h4 : Real.pi / 2 / ρ ≤ Real.pi / 2 := by
      have h5 : (1:ℝ) ≤ ρ := by
        have : (1:ℕ) ≤ ρ := by omega
        exact_mod_cast this
      rw [div_le_iff₀ hρpos]; nlinarith [Real.pi_pos]
    linarith
  have hsinθpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos, Real.two_le_pi])
  have hsinθ_le : Real.sin θ ≤ θ := Real.sin_le hθ0
  have hlo := sin_ge_sub_cube θ hθ0
  have hhi : Real.sin (ρ * θ) ≤ (ρ:ℝ) * θ - ((ρ:ℝ) * θ) ^ 3 / 6 + ((ρ:ℝ) * θ) ^ 5 / 120 := by
    simpa [mul_comm] using! sin_le_add_five (ρ * θ) (by positivity)
  have hN : (ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ) ≥
      (ρ:ℝ) * (θ - θ ^ 3 / 6) - ((ρ:ℝ) * θ - ((ρ:ℝ) * θ) ^ 3 / 6 + ((ρ:ℝ) * θ) ^ 5 / 120) := by
    nlinarith [hlo, hhi, hρ0]
  have hN2 : (ρ:ℝ) * (θ - θ ^ 3 / 6) - ((ρ:ℝ) * θ - ((ρ:ℝ) * θ) ^ 3 / 6 + ((ρ:ℝ) * θ) ^ 5 / 120)
      = θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120 := by ring
  rw [hN2] at hN
  have hNnonneg : (0:ℝ) ≤ (ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ) := by
    have hsinle := sin_nat_mul_le ρ θ hθ0 hθle hρθ_le
    nlinarith [hsinle]
  have hden : (0:ℝ) < (ρ:ℝ) * Real.sin θ := mul_pos hρpos hsinθpos
  have hsplit : 1 - Real.sin (ρ * θ) / (ρ * Real.sin θ)
      = ((ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ)) / ((ρ:ℝ) * Real.sin θ) := by
    have hne : ((ρ:ℝ) * Real.sin θ) ≠ 0 := ne_of_gt hden
    have h1 : (1:ℝ) = ((ρ:ℝ) * Real.sin θ) / ((ρ:ℝ) * Real.sin θ) := (div_self hne).symm
    rw [h1, ← sub_div]
  rw [hsplit]
  have hdiv : (θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120) / ((ρ:ℝ) * θ)
      = θ ^ 2 * ((ρ:ℝ) ^ 2 - 1) / 6 - (ρ:ℝ) ^ 4 * θ ^ 4 / 120 := by
    have hmul : θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120
        = (θ ^ 2 * ((ρ:ℝ) ^ 2 - 1) / 6 - (ρ:ℝ) ^ 4 * θ ^ 4 / 120) * ((ρ:ℝ) * θ) := by
      ring
    rw [hmul, mul_div_cancel_right₀ _ (ne_of_gt (by positivity : (0:ℝ) < (ρ:ℝ) * θ))]
  have hlow_nneg : (0:ℝ) ≤ θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120 := by
    have hρ2 : (2:ℝ) ≤ ρ := by
      have : (2:ℕ) ≤ ρ := by omega
      exact_mod_cast this
    exact cubic_drop_nonneg (ρ:ℝ) θ hρ2 hθ hρθ_le
  have hstep1 : (θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120) / ((ρ:ℝ) * θ)
      ≤ ((ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ)) / ((ρ:ℝ) * Real.sin θ) := by
    have hA : θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120
        ≤ (ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ) := by linarith
    have hB : (0:ℝ) < (ρ:ℝ) * θ := by positivity
    calc (θ ^ 3 * ((ρ:ℝ) ^ 3 - ρ) / 6 - (ρ:ℝ) ^ 5 * θ ^ 5 / 120) / ((ρ:ℝ) * θ)
        ≤ ((ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ)) / ((ρ:ℝ) * θ) :=
          div_le_div_of_nonneg_right hA (le_of_lt hB)
      _ ≤ ((ρ:ℝ) * Real.sin θ - Real.sin (ρ * θ)) / ((ρ:ℝ) * Real.sin θ) :=
          div_le_div_of_nonneg_left hNnonneg hden (by nlinarith [hsinθ_le, hρ0])
  linarith [hstep1, hdiv]

/-- Evaluating the quadratic-minus-quartic drop polynomial at `1 / r ^ 2` gives `(20 * r ^ 2 -
21) / (120 * r ^ 4)` for positive `r`. -/
private theorem small_angle_poly (r : ℝ) (hr : 0 < r) :
    (1 / r ^ 2) ^ 2 * (r ^ 2 - 1) / 6 - r ^ 4 * (1 / r ^ 2) ^ 4 / 120
      = (20 * r ^ 2 - 21) / (120 * r ^ 4) := by
  have hr2 : r ^ 2 ≠ 0 := by positivity
  have hr4 : r ^ 4 ≠ 0 := by positivity
  field_simp [hr2, hr4]
  ring

/-- For `c < 1 / 6` and sufficiently large `r ≥ 3` as specified, the small-angle polynomial
exceeds `c / r ^ 2`. -/
private theorem small_angle_ratio (r c : ℝ) (hr : 3 ≤ r) (hc : c < 1 / 6)
    (hε : (0:ℝ) < 20 - 120 * c) (hbig : 21 / (20 - 120 * c) < r) :
    (20 * r ^ 2 - 21) / (120 * r ^ 4) > c / r ^ 2 := by
  have hcle : r * (20 - 120 * c) > 21 := by
    have := hbig
    rwa [div_lt_iff₀ hε] at this
  have hkey : r * (20 - 120 * c) - 21 > 0 := by linarith
  have hposr : (0:ℝ) < r := by linarith
  have hgt : c / r ^ 2 < (20 * r ^ 2 - 21) / (120 * r ^ 4) := by
    rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < r ^ 2)
        (by positivity : (0:ℝ) < 120 * r ^ 4)]
    have hmain : (20:ℝ) * r ^ 2 - 21 - 120 * c * r ^ 2 > 0 := by
      nlinarith [hcle, hposr]
    nlinarith [hmain, sq_nonneg r, sq_nonneg (r ^ 2)]
  exact hgt

/-- Every coefficient smaller than `1 / 6` fails as a uniform quadratic lower-bound coefficient
for the normalized sine ratio without overshoot. -/
private theorem witness_small_c (c : ℝ) (hc : c < 1 / 6) :
    ∃ (ρ : ℕ) (θ : ℝ), 3 ≤ ρ ∧ 0 < θ ∧ ρ * θ ≤ Real.pi / 2 ∧
      Real.sin (ρ * θ) / (ρ * Real.sin θ) < 1 - c * (ρ:ℝ) ^ 2 * (Real.sin θ) ^ 2 := by
  have hε : (0:ℝ) < 20 - 120 * c := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (21 / (20 - 120 * c))
  set ρ := max 3 n
  have hρ3 : 3 ≤ ρ := le_max_left _ _
  have hρbig : (21 / (20 - 120 * c) : ℝ) < ρ := by
    have : (21 / (20 - 120 * c) : ℝ) < n := hn
    exact lt_of_lt_of_le this (le_max_right _ _ |> (Nat.cast_le.mpr ·))
  have hρcast : (21 / (20 - 120 * c) : ℝ) < (ρ:ℝ) := by exact_mod_cast hρbig
  refine ⟨ρ, 1 / (ρ:ℝ) ^ 2, hρ3, ?_, ?_, ?_⟩
  · positivity
  · have hρpos : (0:ℝ) < ρ := by positivity
    have hρ1 : (1:ℝ) ≤ ρ := by
      have : (1:ℕ) ≤ ρ := by omega
      exact_mod_cast this
    have hθeq : (ρ:ℝ) * (1 / (ρ:ℝ) ^ 2) = 1 / (ρ:ℝ) := by
      field_simp [hρpos.ne']
    rw [hθeq]
    have : (1:ℝ) / (ρ:ℝ) ≤ 1 := by
      rw [div_le_iff₀ hρpos]; nlinarith
    nlinarith [Real.pi_pos, Real.two_le_pi]
  · have hρpos : (0:ℝ) < ρ := by positivity
    have hρ2 : (2:ℝ) ≤ ρ := by
      have : (2:ℕ) ≤ ρ := by omega
      exact_mod_cast this
    have hθ : 0 < 1 / (ρ:ℝ) ^ 2 := by positivity
    have hle : (ρ:ℝ) * (1 / (ρ:ℝ) ^ 2) ≤ Real.pi / 2 := by
      have hρ1 : (1:ℝ) ≤ ρ := by
        have : (1:ℕ) ≤ ρ := by omega
        exact_mod_cast this
      have hθeq : (ρ:ℝ) * (1 / (ρ:ℝ) ^ 2) = 1 / (ρ:ℝ) := by
        field_simp [hρpos.ne']
      rw [hθeq]
      have : (1:ℝ) / (ρ:ℝ) ≤ 1 := by
        rw [div_le_iff₀ hρpos]; nlinarith
      nlinarith [Real.pi_pos, Real.two_le_pi]
    have hsmall : (1:ℝ) / (ρ:ℝ) ^ 2 ≤ 1 := by
      have hρ1 : (1:ℝ) ≤ ρ := by
        have : (1:ℕ) ≤ ρ := by omega
        exact_mod_cast this
      have hρ2pos : (0:ℝ) < (ρ:ℝ) ^ 2 := by positivity
      rw [div_le_iff₀ hρ2pos]
      nlinarith [hρ1]

    have hdrop := drop_ge_poly ρ (1 / (ρ:ℝ) ^ 2) hρ3 hθ hle
    have hpoly := small_angle_poly (ρ:ℝ) hρpos
    rw [hpoly] at hdrop
    have hratio := small_angle_ratio (ρ:ℝ) c (by exact_mod_cast hρ3) hc hε hρcast
    have hpos_drop : (20 * (ρ:ℝ) ^ 2 - 21) / (120 * (ρ:ℝ) ^ 4) > 0 := by
      have hρ1 : (3:ℝ) ≤ ρ := by exact_mod_cast hρ3
      apply div_pos
      · nlinarith [hρ1]
      · positivity
    have hDdrop : 1 - Real.sin ((ρ:ℝ) * (1 / (ρ:ℝ) ^ 2))
        / ((ρ:ℝ) * Real.sin (1 / (ρ:ℝ) ^ 2))
        ≥ (20 * (ρ:ℝ) ^ 2 - 21) / (120 * (ρ:ℝ) ^ 4) := by
      simpa [mul_comm] using! hdrop

    by_cases hcp : 0 < c
    · have hsinθ_le : Real.sin (1 / (ρ:ℝ) ^ 2) ≤ 1 / (ρ:ℝ) ^ 2 := by
        apply Real.sin_le
        positivity
      have hsin2 : (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 ≤ (1 / (ρ:ℝ) ^ 2) ^ 2 := by
        have hnn : 0 ≤ Real.sin (1 / (ρ:ℝ) ^ 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by linarith [Real.pi_pos, Real.two_le_pi, hsmall])
        nlinarith [hsinθ_le, hnn]
      have hbound : c * (ρ:ℝ) ^ 2 * (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 ≤ c / (ρ:ℝ) ^ 2 := by
        have hρ2pos : (0:ℝ) < (ρ:ℝ) ^ 2 := by positivity
        have : c * (ρ:ℝ) ^ 2 * (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2
            ≤ c * (ρ:ℝ) ^ 2 * ((1:ℝ) / (ρ:ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsin2 (mul_nonneg (le_of_lt hcp) (le_of_lt hρ2pos))
        have hcancel : c * (ρ:ℝ) ^ 2 * ((1:ℝ) / (ρ:ℝ) ^ 2) ^ 2 = c / (ρ:ℝ) ^ 2 := by
          field_simp [hρ2pos.ne']
        nlinarith [this, hcancel]
      have hfin : 1 - Real.sin ((ρ:ℝ) * (1 / (ρ:ℝ) ^ 2))
          / ((ρ:ℝ) * Real.sin (1 / (ρ:ℝ) ^ 2))
          > c * (ρ:ℝ) ^ 2 * (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 := by
        linarith [hDdrop, hratio, hbound]
      have hcastρ : Real.sin (ρ * (1 / (ρ:ℝ) ^ 2))
          = Real.sin ((ρ:ℝ) * (1 / (ρ:ℝ) ^ 2)) := rfl
      have hcastρ2 : ρ * Real.sin (1 / (ρ:ℝ) ^ 2)
          = (ρ:ℝ) * Real.sin (1 / (ρ:ℝ) ^ 2) := rfl
      rw [hcastρ, hcastρ2]
      linarith [hfin]
    · have hcn : c ≤ 0 := by linarith
      have hle0 : c * (ρ:ℝ) ^ 2 * (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 ≤ 0 := by
        have hsq : (0:ℝ) ≤ (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 := sq_nonneg _
        have hpos2 : (0:ℝ) ≤ (ρ:ℝ) ^ 2 := by positivity
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hcn (mul_nonneg hpos2 hsq)]
      have hfin : 1 - Real.sin ((ρ:ℝ) * (1 / (ρ:ℝ) ^ 2))
          / ((ρ:ℝ) * Real.sin (1 / (ρ:ℝ) ^ 2))
          > c * (ρ:ℝ) ^ 2 * (Real.sin (1 / (ρ:ℝ) ^ 2)) ^ 2 := by
        linarith [hDdrop, hpos_drop, hle0]
      have hcastρ : Real.sin (ρ * (1 / (ρ:ℝ) ^ 2))
          = Real.sin ((ρ:ℝ) * (1 / (ρ:ℝ) ^ 2)) := rfl
      have hcastρ2 : ρ * Real.sin (1 / (ρ:ℝ) ^ 2)
          = (ρ:ℝ) * Real.sin (1 / (ρ:ℝ) ^ 2) := rfl
      rw [hcastρ, hcastρ2]
      linarith [hfin]

/-- For `y ≤ 1`, the cubic Bernoulli bound `1 - 3 * y ≤ (1 - y) ^ 3` holds. -/
private theorem bernoulli_cube (y : ℝ) (_hy : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - 3 * y ≤ (1 - y) ^ 3 := by
  have h : (1 - y) ^ 3 - (1 - 3 * y) = y ^ 2 * (3 - y) := by ring
  nlinarith [sq_nonneg y]

/-- The coefficient `(4 * Real.pi - 8) / Real.pi ^ 3` equals `(Real.pi / 2 - 1) / (Real.pi / 2)
^ 3`. -/
private theorem c0_eq : (4 * Real.pi - 8) / Real.pi ^ 3
    = (Real.pi / 2 - 1) / ((Real.pi / 2) ^ 3) := by
  have h1 : Real.pi / 2 - 1 = (Real.pi - 2) / 2 := by ring
  have h2 : (Real.pi / 2) ^ 3 = Real.pi ^ 3 / 8 := by
    have : (Real.pi / 2) ^ 3 = Real.pi ^ 3 / 2 ^ 3 := by ring
    rw [this]
    norm_num
  rw [h1, h2]
  have h3 : (4 * Real.pi - 8) = 4 * (Real.pi - 2) := by ring
  rw [h3]
  have hpi : Real.pi ≠ 0 := by positivity
  field_simp [hpi]
  ring

/-- For a coefficient above `(4 * Real.pi - 8) / Real.pi ^ 3` and sufficiently large `r ≥ 3`,
the endpoint cubic sine expression is strictly less than one. -/
private theorem endpoint_core (r c : ℝ) (hr : 3 ≤ r)
    (hc : (4 * Real.pi - 8) / Real.pi ^ 3 < c)
    (hbig : c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) < r ^ 2) :
    r * Real.sin (Real.pi / (2 * r)) - c * r ^ 3 * (Real.sin (Real.pi / (2 * r))) ^ 3 < 1 := by
  have hposr : 0 < r := by linarith
  have hx : 0 < Real.pi / (2 * r) := by
    have : 0 < 2 * r := by positivity
    positivity
  have hrx : r * (Real.pi / (2 * r)) = Real.pi / 2 := by
    field_simp [hposr.ne']
  have hxle : Real.pi / (2 * r) ≤ Real.pi / 6 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * r) (by norm_num : (0:ℝ) < 6)]
    nlinarith [Real.pi_pos]
  have hxsmall : Real.pi / (2 * r) ≤ 1 := by
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have : Real.pi / (2 * r) ≤ Real.pi / 6 := hxle
    linarith
  have hx2 : (Real.pi / (2 * r)) ^ 2 / 6 ≤ 1 := by
    nlinarith [sq_nonneg (Real.pi / (2 * r)), hxsmall]
  have hsin_le : Real.sin (Real.pi / (2 * r)) ≤ Real.pi / (2 * r) :=
    Real.sin_le (le_of_lt hx)
  have hsin_ge : Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6
      ≤ Real.sin (Real.pi / (2 * r)) :=
    sin_ge_sub_cube _ (le_of_lt hx)
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * r)) :=
    Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_gt_three, Real.pi_pos, hxle])
  have hpos3 : 0 < Real.pi / 2 - 1 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hc0pos : 0 < (4 * Real.pi - 8) / Real.pi ^ 3 := by
    rw [c0_eq]
    exact div_pos hpos3 (by positivity)
  have hcc : 0 < c := by nlinarith [hc0pos]

  have hbern : 1 - (Real.pi / (2 * r)) ^ 2 / 2
      ≤ (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
    have h := bernoulli_cube ((Real.pi / (2 * r)) ^ 2 / 6) (by positivity) (by nlinarith [hx2])
    have : 1 - 3 * ((Real.pi / (2 * r)) ^ 2 / 6) = 1 - (Real.pi / (2 * r)) ^ 2 / 2 := by ring
    rw [this] at h
    exact h

  have hxeq : (Real.pi / (2 * r)) ^ 2 = Real.pi ^ 2 / (4 * r ^ 2) := by
    have : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    rw [show (Real.pi / (2 * r)) ^ 2 = Real.pi ^ 2 / (2 * r) ^ 2 by field_simp [hposr.ne'],
      this]

  have hupper : r * Real.sin (Real.pi / (2 * r)) ≤ Real.pi / 2 := by
    nlinarith [hsin_le, hrx]

  have hcube : (Real.sin (Real.pi / (2 * r))) ^ 3
      ≥ (Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6) ^ 3 := by
    have hnn : 0 ≤ Real.sin (Real.pi / (2 * r)) := le_of_lt hsin_pos
    have hnn2 : 0 ≤ Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6 := by
      have : (Real.pi / (2 * r)) ^ 3 ≤ Real.pi / (2 * r) := by
        nlinarith [hx, hxsmall, sq_nonneg (Real.pi / (2 * r))]
      nlinarith
    nlinarith [hsin_ge, mul_nonneg hnn hnn2,
      sq_nonneg (Real.sin (Real.pi / (2 * r)) - (Real.pi / (2 * r) - (Real.pi / (2 * r))^3/6))]
  have hexpand : (Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6) ^ 3
      = (Real.pi / (2 * r)) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
    have h : Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6
        = (Real.pi / (2 * r)) * (1 - (Real.pi / (2 * r)) ^ 2 / 6) := by ring
    rw [h]
    ring
  have hden : r ^ 3 * (Real.sin (Real.pi / (2 * r))) ^ 3
      ≥ (Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
    have h1 : r ^ 3 * (Real.sin (Real.pi / (2 * r))) ^ 3
        ≥ r ^ 3 * (Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6) ^ 3 := by
      have hnn : (0:ℝ) ≤ r ^ 3 := by positivity
      nlinarith [hcube, hnn]
    have h2 : r ^ 3 * (Real.pi / (2 * r) - (Real.pi / (2 * r)) ^ 3 / 6) ^ 3
        = (Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
      rw [hexpand, ← mul_assoc]
      have hkey2 : r ^ 3 * (Real.pi / (2 * r)) ^ 3 = (Real.pi / 2) ^ 3 := by
        have : r ^ 3 * (Real.pi / (2 * r)) ^ 3 = (r * (Real.pi / (2 * r))) ^ 3 := by ring
        rw [this, hrx]
      rw [hkey2]
    nlinarith [h1, h2]

  have hkey : Real.pi / 2 - 1 < c * ((Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3) := by

    have h3 : 1 - Real.pi ^ 2 / (8 * r ^ 2)
        ≤ (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
      have h4 : 1 - Real.pi ^ 2 / (8 * r ^ 2)
          = 1 - (Real.pi / (2 * r)) ^ 2 / 2 := by
        rw [hxeq]
        field_simp [hposr.ne']
        ring
      rw [h4]
      exact hbern

    have h5 : (4 * Real.pi - 8) / Real.pi ^ 3 / c < 1 - Real.pi ^ 2 / (8 * r ^ 2) := by
      have hcdiff : 0 < c - (4 * Real.pi - 8) / Real.pi ^ 3 := by linarith
      have hbig2 : c * Real.pi ^ 2 < 8 * r ^ 2 * (c - (4 * Real.pi - 8) / Real.pi ^ 3) := by
        have h := hbig
        have hcle : 0 < c - (4 * Real.pi - 8) / Real.pi ^ 3 := hcdiff
        have hform : c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3))
            = c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) := rfl
        have hpos8 : 0 < 8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3) := by positivity
        rw [div_lt_iff₀ hpos8] at h
        nlinarith
      have hpos8 : 0 < 8 * r ^ 2 := by positivity
      have : Real.pi ^ 2 / (8 * r ^ 2) < (c - (4 * Real.pi - 8) / Real.pi ^ 3) / c := by
        have htr : (0:ℝ) < 8 * r ^ 2 := by positivity
        have hcross : Real.pi ^ 2 * c < (c - (4 * Real.pi - 8) / Real.pi ^ 3) * (8 * r ^ 2) := by
          nlinarith [hbig2, hcc]
        rw [div_lt_div_iff₀ htr hcc]
        nlinarith
      have hsplit : (c - (4 * Real.pi - 8) / Real.pi ^ 3) / c
          = 1 - (4 * Real.pi - 8) / Real.pi ^ 3 / c := by
        field_simp [hcc.ne']
      rw [hsplit] at this
      linarith

    have h6 : (4 * Real.pi - 8) / Real.pi ^ 3 < c * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 := by
      have := h5
      rw [div_lt_iff₀ hcc] at this
      nlinarith [h3, hcc]
    have hppos : 0 < (Real.pi / 2) ^ 3 := by positivity
    have hmul : ((4 * Real.pi - 8) / Real.pi ^ 3) * ((Real.pi / 2) ^ 3) = Real.pi / 2 - 1 := by
      rw [c0_eq]
      have hne : (Real.pi / 2) ^ 3 ≠ 0 := by positivity
      field_simp [hne]
    have h6mul : ((4 * Real.pi - 8) / Real.pi ^ 3) * ((Real.pi / 2) ^ 3)
        < c * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 * ((Real.pi / 2) ^ 3) :=
      mul_lt_mul_of_pos_right h6 hppos
    have hrearr : c * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3 * ((Real.pi / 2) ^ 3)
        = c * ((Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3) := by
      ring
    rw [hrearr] at h6mul
    linarith [h6mul, hmul]

  have hfin : r * Real.sin (Real.pi / (2 * r)) - c * r ^ 3 * (Real.sin (Real.pi / (2 * r))) ^ 3
      ≤ Real.pi / 2 - c * ((Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3) := by
    have hdn : (Real.pi / 2) ^ 3 * (1 - (Real.pi / (2 * r)) ^ 2 / 6) ^ 3
        ≤ r ^ 3 * (Real.sin (Real.pi / (2 * r))) ^ 3 := hden
    nlinarith [hupper, hdn, mul_le_mul_of_nonneg_left hdn (le_of_lt hcc)]
  nlinarith [hfin, hkey]

/-- Every coefficient greater than `(4 * Real.pi - 8) / Real.pi ^ 3` fails as a uniform
quadratic upper-bound coefficient for the normalized sine ratio without overshoot. -/
private theorem witness_large_c (c : ℝ) (hc : (4 * Real.pi - 8) / Real.pi ^ 3 < c) :
    ∃ (ρ : ℕ) (θ : ℝ), 3 ≤ ρ ∧ 0 < θ ∧ ρ * θ ≤ Real.pi / 2 ∧
      1 - c * (ρ:ℝ) ^ 2 * (Real.sin θ) ^ 2 < Real.sin (ρ * θ) / (ρ * Real.sin θ) := by
  have hcdiff : 0 < c - (4 * Real.pi - 8) / Real.pi ^ 3 := by linarith
  have hc0pos : 0 < (4 * Real.pi - 8) / Real.pi ^ 3 := by
    rw [c0_eq]
    exact div_pos (by nlinarith [Real.pi_gt_three, Real.pi_pos]) (by positivity)
  have hcc : 0 < c := by nlinarith [hc0pos]
  have hthreshold : 0 < c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) := by
    apply div_pos
    · exact mul_pos hcc (by positivity)
    · positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)))
  set ρ := max 3 n
  have hρ3 : 3 ≤ ρ := le_max_left _ _
  have hρbig : (c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) : ℝ) < ρ := by
    have : (c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) : ℝ) < n := hn
    exact lt_of_lt_of_le this (le_max_right _ _ |> (Nat.cast_le.mpr ·))
  have hρcast : (c * Real.pi ^ 2 / (8 * (c - (4 * Real.pi - 8) / Real.pi ^ 3)) : ℝ) < (ρ:ℝ) :=
    by exact_mod_cast hρbig
  refine ⟨ρ, Real.pi / (2 * (ρ:ℝ)), hρ3, ?_, ?_, ?_⟩
  · have hρpos : (0:ℝ) < ρ := by positivity
    have : 0 < 2 * (ρ:ℝ) := by positivity
    positivity
  · have hρpos : (0:ℝ) < ρ := by positivity
    have h1 : (ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ))) = Real.pi / 2 := by
      field_simp [hρpos.ne']
    rw [h1]
  · have hρpos : (0:ℝ) < ρ := by positivity
    have hρ2 : (2:ℝ) ≤ ρ := by
      have : (2:ℕ) ≤ ρ := by omega
      exact_mod_cast this
    have hle : (ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ))) ≤ Real.pi / 2 := by
      have h1 : (ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ))) = Real.pi / 2 := by
        field_simp [hρpos.ne']
      rw [h1]
    have hθpos : 0 < Real.pi / (2 * (ρ:ℝ)) := by
      have : 0 < 2 * (ρ:ℝ) := by positivity
      positivity
    have hcore := endpoint_core (ρ:ℝ) c (by exact_mod_cast hρ3) hc (by
      have := hρcast
      have hsq : (ρ:ℝ) ^ 2 = (ρ:ℝ) * (ρ:ℝ) := by ring
      have hρ1 : (1:ℝ) ≤ ρ := by
        have : (1:ℕ) ≤ ρ := by omega
        exact_mod_cast this

      nlinarith [this, hρpos, hρ1])

    have hsinpos : 0 < Real.sin (Real.pi / (2 * (ρ:ℝ))) :=
      Real.sin_pos_of_pos_of_lt_pi hθpos (by
        have : Real.pi / (2 * (ρ:ℝ)) ≤ Real.pi / 6 := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (ρ:ℝ)) (by norm_num : (0:ℝ) < 6)]
          have hρ3r : (3:ℝ) ≤ ρ := by exact_mod_cast hρ3
          nlinarith [Real.pi_pos]
        linarith [Real.pi_gt_three, Real.pi_pos, this])
    have hden : 0 < (ρ:ℝ) * Real.sin (Real.pi / (2 * (ρ:ℝ))) := mul_pos hρpos hsinpos
    have hsin_pi_div_two : Real.sin ((ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ)))) = 1 := by
      have h1 : (ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ))) = Real.pi / 2 := by
        field_simp [hρpos.ne']
      rw [h1, Real.sin_pi_div_two]
    have hform : Real.sin (ρ * (Real.pi / (2 * (ρ:ℝ))))
        = Real.sin ((ρ:ℝ) * (Real.pi / (2 * (ρ:ℝ)))) := rfl
    have hform2 : ρ * Real.sin (Real.pi / (2 * (ρ:ℝ)))
        = (ρ:ℝ) * Real.sin (Real.pi / (2 * (ρ:ℝ))) := rfl
    rw [hform, hform2, hsin_pi_div_two]

    rw [lt_div_iff₀ hden]

    have hcalc : (1 - c * (ρ:ℝ) ^ 2 * (Real.sin (Real.pi / (2 * (ρ:ℝ)))) ^ 2)
        * ((ρ:ℝ) * Real.sin (Real.pi / (2 * (ρ:ℝ))))
        = (ρ:ℝ) * Real.sin (Real.pi / (2 * (ρ:ℝ)))
          - c * (ρ:ℝ) ^ 3 * (Real.sin (Real.pi / (2 * (ρ:ℝ)))) ^ 3 := by
      ring
    rw [hcalc]
    exact hcore

/-- The sharp upper-bound coefficient `(4 * Real.pi - 8) / Real.pi ^ 3` is at most `4 / 27`. -/
private theorem c0_le_four_div_27 :
    (4 * Real.pi - 8) / Real.pi ^ 3 ≤ 4 / 27 := by
  have hpi3 : 0 < Real.pi ^ 3 := by positivity
  have hfac : (4:ℝ) * Real.pi ^ 3 - 27 * (4 * Real.pi - 8)
      = 4 * (Real.pi - 3) ^ 2 * (Real.pi + 6) := by ring
  have hnn : 0 ≤ (4:ℝ) * (Real.pi - 3) ^ 2 * (Real.pi + 6) := by
    nlinarith [sq_nonneg (Real.pi - 3), Real.pi_pos]
  have hmain : 27 * (4 * Real.pi - 8) ≤ (4:ℝ) * Real.pi ^ 3 := by nlinarith [hfac, hnn]
  rw [div_le_iff₀ hpi3]
  have h27 : (0:ℝ) < 27 := by norm_num
  have hdiv : (4 * Real.pi - 8) ≤ (4:ℝ) * Real.pi ^ 3 / 27 := by
    rw [le_div_iff₀ h27]
    have : (4 * Real.pi - 8) * 27 = 27 * (4 * Real.pi - 8) := by ring
    rw [this]
    exact hmain
  have hform : (4:ℝ) * Real.pi ^ 3 / 27 = (4 / 27) * Real.pi ^ 3 := by ring
  rw [hform] at hdiv
  exact hdiv

/-- The derivative of `Real.sin v - v * Real.cos v` at `u` is `u * Real.sin u`. -/
private theorem hasDerivAt_sin_sub_u_mul_cos (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.sin v - v * Real.cos v) (u * Real.sin u) u := by
  have a : HasDerivAt (fun v : ℝ => Real.sin v) (Real.cos u) u := Real.hasDerivAt_sin u
  have b : HasDerivAt (fun v : ℝ => v * Real.cos v)
      (Real.cos u + u * (-Real.sin u)) u := by
    have b1 : HasDerivAt (fun v : ℝ => v) (1:ℝ) u := hasDerivAt_id u
    have b2 : HasDerivAt (fun v : ℝ => Real.cos v) (-Real.sin u) u := Real.hasDerivAt_cos u
    have := b1.mul b2
    simpa [one_mul] using! this
  have c := a.sub b
  have hd : Real.cos u - (Real.cos u + u * (-Real.sin u)) = u * Real.sin u := by ring
  rw [hd] at c
  exact c

/-- For `u` between zero and `Real.pi / 2`, `u * Real.cos u ≤ Real.sin u`. -/
private theorem sin_ge_mul_cos (u : ℝ) (hu : 0 ≤ u) (hle : u ≤ Real.pi / 2) :
    u * Real.cos u ≤ Real.sin u := by
  have hmono : MonotoneOn (fun t : ℝ => Real.sin t - t * Real.cos t)
      (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · have : Continuous (fun t : ℝ => Real.sin t - t * Real.cos t) := by continuity
      exact this.continuousOn
    · exact Differentiable.differentiableOn
        fun t => (hasDerivAt_sin_sub_u_mul_cos t).differentiableAt
    · intro t ht
      have htm : t ∈ Set.Icc 0 (Real.pi / 2) := interior_subset ht
      rw [(hasDerivAt_sin_sub_u_mul_cos t).deriv]
      exact mul_nonneg htm.1 (Real.sin_nonneg_of_nonneg_of_le_pi htm.1
        (by linarith [Real.pi_pos, htm.2]))
  have h0 : (0:ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hu' : u ∈ Set.Icc 0 (Real.pi / 2) := ⟨hu, hle⟩
  have := hmono h0 hu' hu
  have hf0 : (fun t : ℝ => Real.sin t - t * Real.cos t) 0 = 0 := by simp
  linarith

/-- The derivative of `2 * (1 - Real.cos v) - v * Real.sin v` at `u` is `Real.sin u - u *
Real.cos u`. -/
private theorem hasDerivAt_two_one_sub_cos (u : ℝ) :
    HasDerivAt (fun v : ℝ => 2 * (1 - Real.cos v) - v * Real.sin v)
      (Real.sin u - u * Real.cos u) u := by
  have a : HasDerivAt (fun v : ℝ => 1 - Real.cos v) (Real.sin u) u := by
    have a1 : HasDerivAt (fun v : ℝ => Real.cos v) (-Real.sin u) u := Real.hasDerivAt_cos u
    have a2 : HasDerivAt (fun v : ℝ => (1:ℝ)) (0:ℝ) u := hasDerivAt_const u 1
    have := a2.sub a1
    have hd : (0:ℝ) - -Real.sin u = Real.sin u := by ring
    rw [hd] at this
    exact this
  have b : HasDerivAt (fun v : ℝ => 2 * (1 - Real.cos v)) (2 * Real.sin u) u :=
    a.const_mul 2
  have c : HasDerivAt (fun v : ℝ => v * Real.sin v) (Real.sin u + u * Real.cos u) u := by
    have c1 : HasDerivAt (fun v : ℝ => v) (1:ℝ) u := hasDerivAt_id u
    have c2 : HasDerivAt (fun v : ℝ => Real.sin v) (Real.cos u) u := Real.hasDerivAt_sin u
    have := c1.mul c2
    simpa [one_mul] using! this
  have d := b.sub c
  have hd : 2 * Real.sin u - (Real.sin u + u * Real.cos u)
      = Real.sin u - u * Real.cos u := by ring
  rw [hd] at d
  exact d

/-- The derivative of `v * (2 + Real.cos v) - 3 * Real.sin v` is `2 * (1 - Real.cos v) - v *
Real.sin v`. -/
private theorem hasDerivAt_u_two_add_cos (u : ℝ) :
    HasDerivAt (fun v : ℝ => v * (2 + Real.cos v) - 3 * Real.sin v)
      (2 * (1 - Real.cos u) - u * Real.sin u) u := by
  have a : HasDerivAt (fun v : ℝ => v * (2 + Real.cos v))
      (2 + Real.cos u + u * (-Real.sin u)) u := by
    have a1 : HasDerivAt (fun v : ℝ => v) (1:ℝ) u := hasDerivAt_id u
    have a2 : HasDerivAt (fun v : ℝ => 2 + Real.cos v) (-Real.sin u) u := by
      have a2a : HasDerivAt (fun v : ℝ => Real.cos v) (-Real.sin u) u := Real.hasDerivAt_cos u
      have a2b : HasDerivAt (fun v : ℝ => (2:ℝ)) (0:ℝ) u := hasDerivAt_const u 2
      have := a2b.add a2a
      have hd : (0:ℝ) + -Real.sin u = -Real.sin u := by ring
      rw [hd] at this
      exact this
    have := a1.mul a2
    simpa [one_mul] using! this
  have b : HasDerivAt (fun v : ℝ => 3 * Real.sin v) (3 * Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul 3
  have c := a.sub b
  have hd : (2 + Real.cos u + u * (-Real.sin u)) - 3 * Real.cos u
      = 2 * (1 - Real.cos u) - u * Real.sin u := by ring
  rw [hd] at c
  exact c

/-- For `u` between zero and `Real.pi / 2`, `3 * Real.sin u ≤ u * (2 + Real.cos u)`. -/
private theorem three_sin_le_u_mul_two_add_cos (u : ℝ) (hu : 0 ≤ u) (hle : u ≤ Real.pi / 2) :
    3 * Real.sin u ≤ u * (2 + Real.cos u) := by
  have hh'mono : MonotoneOn (fun v : ℝ => 2 * (1 - Real.cos v) - v * Real.sin v)
      (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · have : Continuous (fun v : ℝ => 2 * (1 - Real.cos v) - v * Real.sin v) := by continuity
      exact this.continuousOn
    · exact Differentiable.differentiableOn
        fun v => (hasDerivAt_two_one_sub_cos v).differentiableAt
    · intro v hv
      have hvm : v ∈ Set.Icc 0 (Real.pi / 2) := interior_subset hv
      rw [(hasDerivAt_two_one_sub_cos v).deriv]
      have := sin_ge_mul_cos v hvm.1 hvm.2
      linarith
  have hh'0 : (fun v : ℝ => 2 * (1 - Real.cos v) - v * Real.sin v) 0 = 0 := by simp
  have h0 : (0:ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hu' : u ∈ Set.Icc 0 (Real.pi / 2) := ⟨hu, hle⟩
  have hh'ge : 0 ≤ 2 * (1 - Real.cos u) - u * Real.sin u := by
    have := hh'mono h0 hu' hu
    linarith
  have hhmono : MonotoneOn (fun v : ℝ => v * (2 + Real.cos v) - 3 * Real.sin v)
      (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · have : Continuous (fun v : ℝ => v * (2 + Real.cos v) - 3 * Real.sin v) := by continuity
      exact this.continuousOn
    · exact Differentiable.differentiableOn
        fun v => (hasDerivAt_u_two_add_cos v).differentiableAt
    · intro v hv
      have hvm : v ∈ Set.Icc 0 (Real.pi / 2) := interior_subset hv
      rw [(hasDerivAt_u_two_add_cos v).deriv]
      have := hh'mono h0 ⟨hvm.1, hvm.2⟩ hvm.1
      linarith
  have hh0 : (fun v : ℝ => v * (2 + Real.cos v) - 3 * Real.sin v) 0 = 0 := by simp
  have := hhmono h0 hu' hu
  linarith

/-- For positive `x`, the derivative of `(y - Real.sin y) / y ^ 3` at `x` is `(3 * Real.sin x -
2 * x - x * Real.cos x) / x ^ 4`. -/
private theorem hasDerivAt_sub_sin_div_cube (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y - Real.sin y) / y ^ 3)
      ((3 * Real.sin x - 2 * x - x * Real.cos x) / x ^ 4) x := by
  have a : HasDerivAt (fun y : ℝ => y - Real.sin y) (1 - Real.cos x) x := by
    have a1 : HasDerivAt (fun y : ℝ => y) (1:ℝ) x := hasDerivAt_id x
    have a2 : HasDerivAt (fun y : ℝ => Real.sin y) (Real.cos x) x := Real.hasDerivAt_sin x
    exact a1.sub a2
  have b : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using! (hasDerivAt_id x).pow 3
  have h3 : x ^ 3 ≠ 0 := by positivity
  have := a.div b h3
  have hd : ((1 - Real.cos x) * x ^ 3 - (x - Real.sin x) * (3 * x ^ 2)) / (x ^ 3) ^ 2
      = (3 * Real.sin x - 2 * x - x * Real.cos x) / x ^ 4 := by
    have hx3 : x ^ 3 ≠ 0 := by positivity
    have hx4 : x ^ 4 ≠ 0 := by positivity
    field_simp [hx3, hx4]
    ring
  rw [hd] at this
  exact this

/-- For positive `x`, the function `(y - Real.sin y) / y ^ 3` is antitone on the interval from
`x` to `Real.pi / 2`. -/
private theorem sub_sin_div_cube_antitoneOn (x : ℝ) (hx : 0 < x) (_hxle : x ≤ Real.pi / 2) :
    AntitoneOn (fun y : ℝ => (y - Real.sin y) / y ^ 3) (Set.Icc x (Real.pi / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · refine ContinuousOn.div (continuousOn_id.sub Real.continuous_sin.continuousOn)
      (continuousOn_id.pow 3) ?_
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx (Set.mem_Icc.mp hy).1
    positivity
  · intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx (Set.mem_Icc.mp (interior_subset hy)).1
    exact (hasDerivAt_sub_sin_div_cube y hypos).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx (Set.mem_Icc.mp (interior_subset hy)).1
    rw [(hasDerivAt_sub_sin_div_cube y hypos).deriv]
    have hle := three_sin_le_u_mul_two_add_cos y (le_of_lt hypos)
      (Set.mem_Icc.mp (interior_subset hy)).2
    have hform : y * (2 + Real.cos y) = 2 * y + y * Real.cos y := by ring
    have hnum : 3 * Real.sin y - 2 * y - y * Real.cos y ≤ 0 := by nlinarith [hle, hform]
    have hy4 : 0 ≤ y ^ 4 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hy4

/-- For `x` between zero and `Real.pi / 2`, the sine deficit `x - Real.sin x` is at least `(4 *
Real.pi - 8) / Real.pi ^ 3` times `x ^ 3`. -/
private theorem sub_sin_ge_c0_mul_cube (x : ℝ) (hx : 0 ≤ x) (hle : x ≤ Real.pi / 2) :
    ((4 * Real.pi - 8) / Real.pi ^ 3) * x ^ 3 ≤ x - Real.sin x := by
  by_cases h0 : x = 0
  · subst h0; simp
  · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hanti := sub_sin_div_cube_antitoneOn x hpos hle
    have hxmem : x ∈ Set.Icc x (Real.pi / 2) := ⟨le_rfl, hle⟩
    have hpmem : (Real.pi / 2) ∈ Set.Icc x (Real.pi / 2) := ⟨hle, le_rfl⟩
    have hanti' : ((Real.pi / 2) - Real.sin (Real.pi / 2)) / (Real.pi / 2) ^ 3
        ≤ (x - Real.sin x) / x ^ 3 :=
      hanti hxmem hpmem hle
    rw [Real.sin_pi_div_two] at hanti'
    have hc0 := c0_eq
    have h3pos : 0 < x ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hanti' (le_of_lt h3pos)
    have hcancel : ((x - Real.sin x) / x ^ 3) * x ^ 3 = x - Real.sin x := by
      field_simp [h0]
    rw [hcancel] at hmul
    rw [hc0]
    exact hmul

/-- For positive `u`, the derivative of `Real.sin v / v` at `u` is `(u * Real.cos u - Real.sin
u) / u ^ 2`. -/
private theorem hasDerivAt_sin_div (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => Real.sin v / v)
      ((u * Real.cos u - Real.sin u) / u ^ 2) u := by
  have a : HasDerivAt (fun v : ℝ => Real.sin v) (Real.cos u) u := Real.hasDerivAt_sin u
  have b : HasDerivAt (fun v : ℝ => v) (1:ℝ) u := hasDerivAt_id u
  have := a.div b (ne_of_gt hu)
  have hd : (Real.cos u * u - Real.sin u * 1) / u ^ 2
      = (u * Real.cos u - Real.sin u) / u ^ 2 := by ring
  rw [hd] at this
  exact this

/-- The function `Real.sin v / v` is antitone on every interval with positive left endpoint and
right endpoint at most `Real.pi / 2`. -/
private theorem sin_div_antitoneOn (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    AntitoneOn (fun v : ℝ => Real.sin v / v) (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · refine ContinuousOn.div Real.continuous_sin.continuousOn continuousOn_id ?_
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le ha (Set.mem_Icc.mp hy).1
    positivity
  · intro y hy
    have hypos : 0 < y := lt_of_lt_of_le ha (Set.mem_Icc.mp (interior_subset hy)).1
    exact (hasDerivAt_sin_div y hypos).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := lt_of_lt_of_le ha (Set.mem_Icc.mp (interior_subset hy)).1
    rw [(hasDerivAt_sin_div y hypos).deriv]
    have hyme : y ∈ Set.Icc a b := interior_subset hy
    have homega := sin_ge_mul_cos y (le_of_lt hypos) (le_trans hyme.2 hb)
    have hnum : y * Real.cos y - Real.sin y ≤ 0 := by linarith
    have hy2 : 0 ≤ y ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hy2

/-- For `0 < x ≤ y ≤ Real.pi / 2`, `Real.sin y / y ≤ Real.sin x / x`. -/
private theorem sin_div_anti (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.pi / 2) :
    Real.sin y / y ≤ Real.sin x / x :=
  sin_div_antitoneOn x y hx hxy hy ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- An exact algebraic identity expresses a cubic's value relative to its endpoint chord, with
remainder `c * t ^ 3 * (w - a) * (1 - w) * (1 - a) * (1 + a + w)`. -/
private theorem chord_cubic (c t s a w : ℝ) :
    (1 - a) * (t * w - c * t ^ 3 * w ^ 3 - s)
      = (1 - w) * (t * a - c * t ^ 3 * a ^ 3 - s)
        + (w - a) * (t - c * t ^ 3 - s)
        + c * t ^ 3 * (w - a) * (1 - w) * (1 - a) * (1 + a + w) := by
  ring

/-- For `ρ ≥ 3` and a nonnegative angle without overshoot, the normalized sine ratio, defined as
one at zero, is at most `1 - ((4 * Real.pi - 8) / Real.pi ^ 3) * ρ ^ 2 * Real.sin θ ^ 2`. -/
private theorem dirichlet_upper (ρ : ℕ) (θ : ℝ) (hρ : 3 ≤ ρ) (hθ : 0 ≤ θ)
    (hle : ρ * θ ≤ Real.pi / 2) :
    (if θ = 0 then 1 else Real.sin (ρ * θ) / (ρ * Real.sin θ)) ≤
      1 - ((4 * Real.pi - 8) / Real.pi ^ 3) * (ρ:ℝ) ^ 2 * (Real.sin θ) ^ 2 := by
  by_cases hθ0 : θ = 0
  · subst hθ0
    simp
  · rw [if_neg hθ0]
    have hρpos : (0:ℝ) < ρ := by positivity
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
    have hρ3 : (3:ℝ) ≤ ρ := by exact_mod_cast hρ
    have hθle : θ ≤ Real.pi / 6 := by
      have h3 : θ ≤ Real.pi / 2 / ρ := by
        rw [le_div_iff₀ hρpos]
        nlinarith
      have h4 : Real.pi / 2 / ρ ≤ Real.pi / 6 := by
        rw [div_le_div_iff₀ hρpos (by norm_num : (0:ℝ) < 6)]
        have hform : Real.pi / 2 * 6 = 3 * Real.pi := by ring
        nlinarith [Real.pi_pos, hρ3]
      linarith
    have hsinθpos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθpos
        (by linarith [Real.pi_pos, Real.two_le_pi, hθle])
    have hden : (0:ℝ) < (ρ:ℝ) * Real.sin θ := mul_pos hρpos hsinθpos
    have hcore : Real.sin (ρ * θ) ≤ (ρ:ℝ) * Real.sin θ
        - ((4 * Real.pi - 8) / Real.pi ^ 3) * (ρ:ℝ) ^ 3 * (Real.sin θ) ^ 3 := by
      set t : ℝ := (ρ:ℝ) * θ with htdef
      set c0 : ℝ := (4 * Real.pi - 8) / Real.pi ^ 3 with hc0def
      have htpos : 0 < t := mul_pos hρpos hθpos
      have htle : t ≤ Real.pi / 2 := hle
      have hθne : θ ≠ 0 := hθ0
      set v : ℝ := Real.sin θ / θ with hvdef
      set a : ℝ := 3 * Real.sin (t / 3) / t with ha_eq

      have hv_le : v ≤ 1 := by
        rw [hvdef, div_le_iff₀ hθpos]
        nlinarith [Real.sin_le hθ]
      have ht3pos : 0 < t / 3 := by positivity
      have hsin_t3 : 0 < Real.sin (t / 3) :=
        Real.sin_pos_of_pos_of_lt_pi ht3pos (by linarith [Real.pi_pos, htle])
      have ha_pos : 0 < a := by
        rw [ha_eq]
        positivity
      have ha_lt : a < 1 := by
        rw [ha_eq, div_lt_iff₀ htpos]
        have hlt : Real.sin (t / 3) < t / 3 := Real.sin_lt ht3pos
        nlinarith
      have hθ_le_t3 : θ ≤ t / 3 := by
        rw [htdef]
        nlinarith [hρ3, hρpos]
      have ha_le_v : a ≤ v := by
        have hdiv := sin_div_anti θ (t / 3) hθpos hθ_le_t3
          (by linarith [Real.pi_pos, htle])
        rw [hvdef, ha_eq]
        have hform : 3 * Real.sin (t / 3) / t = Real.sin (t / 3) / (t / 3) := by
          field_simp
        rw [hform]
        exact hdiv

      have hf1 : t - c0 * t ^ 3 - Real.sin t ≥ 0 := by
        have h := sub_sin_ge_c0_mul_cube t (le_of_lt htpos) htle
        rw [hc0def]
        nlinarith

      have hfa : t * a - c0 * t ^ 3 * a ^ 3 - Real.sin t ≥ 0 := by
        rw [ha_eq]
        have hmul : t * (3 * Real.sin (t / 3) / t)
            - c0 * t ^ 3 * (3 * Real.sin (t / 3) / t) ^ 3
            = 3 * Real.sin (t / 3) - 27 * c0 * Real.sin (t / 3) ^ 3 := by
          have htne : t ≠ 0 := ne_of_gt htpos
          field_simp [htne]
          ring
        have h3 : Real.sin t = 3 * Real.sin (t / 3) - 4 * Real.sin (t / 3) ^ 3 := by
          have h : Real.sin t = Real.sin (3 * (t / 3)) := by congr 1; ring
          rw [h, Real.sin_three_mul]
        rw [hmul, h3]
        have hrearr : 3 * Real.sin (t / 3) - 27 * c0 * Real.sin (t / 3) ^ 3
            - (3 * Real.sin (t / 3) - 4 * Real.sin (t / 3) ^ 3)
            = Real.sin (t / 3) ^ 3 * (4 - 27 * c0) := by ring
        rw [hrearr]
        have hge : 0 ≤ 4 - 27 * c0 := by
          have h1 := c0_le_four_div_27
          rw [hc0def]
          have h27 : (0:ℝ) < 27 := by norm_num
          have h2 : 27 * ((4 * Real.pi - 8) / Real.pi ^ 3) ≤ 4 := by
            have := mul_le_mul_of_nonneg_left h1 (le_of_lt h27)
            have h3 : 27 * ((4:ℝ) / 27) = 4 := by ring
            rw [h3] at this
            exact this
          linarith
        exact mul_nonneg (pow_nonneg (le_of_lt hsin_t3) 3) hge

      have hchord_v := chord_cubic c0 t (Real.sin t) a v
      have hnonneg : 0 ≤ c0 * t ^ 3 * (v - a) * (1 - v) * (1 - a) * (1 + a + v) := by
        have hc0pos : 0 < c0 := by
          rw [hc0def, c0_eq]
          exact div_pos (by nlinarith [Real.pi_gt_three, Real.pi_pos]) (by positivity)
        have ht3pos' : 0 < t ^ 3 := by positivity
        have hva : 0 ≤ v - a := by linarith
        have h1v : 0 ≤ 1 - v := by linarith
        have h1a : 0 ≤ 1 - a := by linarith
        have h1av : 0 ≤ 1 + a + v := by positivity
        have haux1 : 0 ≤ c0 * t ^ 3 := mul_nonneg (le_of_lt hc0pos) (le_of_lt ht3pos')
        have haux2 : 0 ≤ (v - a) * (1 - v) := mul_nonneg hva h1v
        have haux3 : 0 ≤ (1 - a) * (1 + a + v) := mul_nonneg h1a h1av
        have haux4 : 0 ≤ (c0 * t ^ 3) * ((v - a) * (1 - v)) := mul_nonneg haux1 haux2
        have haux5 : 0 ≤ ((c0 * t ^ 3) * ((v - a) * (1 - v))) * ((1 - a) * (1 + a + v)) :=
          mul_nonneg haux4 haux3
        convert! haux5 using 1
        ring
      have h1a_pos : 0 < 1 - a := by linarith
      have hle0 : 0 ≤ (1 - a) * (t * v - c0 * t ^ 3 * v ^ 3 - Real.sin t) := by
        rw [hchord_v]
        have h1 : 0 ≤ (1 - v) * (t * a - c0 * t ^ 3 * a ^ 3 - Real.sin t) :=
          mul_nonneg (by linarith) hfa
        have h2 : 0 ≤ (v - a) * (t - c0 * t ^ 3 - Real.sin t) :=
          mul_nonneg (by linarith) hf1
        have h3 : 0 ≤ (1 - v) * (t * a - c0 * t ^ 3 * a ^ 3 - Real.sin t)
            + (v - a) * (t - c0 * t ^ 3 - Real.sin t) := add_nonneg h1 h2
        exact add_nonneg h3 hnonneg
      have hfv : 0 ≤ t * v - c0 * t ^ 3 * v ^ 3 - Real.sin t := by
        have h1ane : 1 - a ≠ 0 := ne_of_gt h1a_pos
        have hform : t * v - c0 * t ^ 3 * v ^ 3 - Real.sin t
            = ((1 - a) * (t * v - c0 * t ^ 3 * v ^ 3 - Real.sin t)) / (1 - a) := by
          field_simp [h1ane]
        rw [hform]
        exact div_nonneg hle0 (le_of_lt h1a_pos)

      have hkey : t * v - c0 * t ^ 3 * v ^ 3
          = (ρ:ℝ) * Real.sin θ - c0 * (ρ:ℝ) ^ 3 * (Real.sin θ) ^ 3 := by
        rw [htdef, hvdef]
        have hθne : θ ≠ 0 := hθ0
        have hθ3ne : θ ^ 3 ≠ 0 := by positivity
        have hv3 : (Real.sin θ / θ) ^ 3 = Real.sin θ ^ 3 / θ ^ 3 := by
          field_simp [hθne]
        have ht3 : ((ρ:ℝ) * θ) ^ 3 = (ρ:ℝ) ^ 3 * θ ^ 3 := by ring
        rw [hv3, ht3]
        field_simp [hθne, hθ3ne]
      linarith [hfv, hkey]
    rw [div_le_iff₀ hden]
    have hexpand : (1 - ((4 * Real.pi - 8) / Real.pi ^ 3) * (ρ:ℝ) ^ 2 * (Real.sin θ) ^ 2)
        * ((ρ:ℝ) * Real.sin θ)
        = (ρ:ℝ) * Real.sin θ
          - ((4 * Real.pi - 8) / Real.pi ^ 3) * (ρ:ℝ) ^ 3 * (Real.sin θ) ^ 3 := by
      ring
    rw [hexpand]
    exact hcore

/-- Establishes the sharp quadratic bounds, optimality witnesses for both coefficients, and the
exact triple-angle gain formula in `Clause7TightDirichletBounds`. See [Low and Su,
Proposition 16][LowSu2026]. -/
theorem Clause7TightDirichletBounds_answer : Clause7TightDirichletBounds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ θ hρ hθ hle
    (try dsimp only)
    exact ⟨dirichlet_lower ρ θ hρ hθ hle, dirichlet_upper ρ θ hρ hθ hle⟩
  · intro c hc
    exact witness_small_c c hc
  · intro c hc
    exact witness_large_c c hc
  · intro a ha0 ha1
    exact gainLoss_three a ha0 ha1

end Qatlib.Concepts.QlsReadoutSpec.Amplification
