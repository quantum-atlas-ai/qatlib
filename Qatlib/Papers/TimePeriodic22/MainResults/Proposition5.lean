/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TimePeriodic22.MainResults.SourceModel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option backward.isDefEq.respectTransparency false

/-!
# Floquet Truncation Tail Bound and Monotonicity (Proposition 5)

This module formalizes Proposition 5 for the Floquet truncation error profile
`f(x) = (κ / x)^x`: for `κ > 0`, `f` is monotonically decreasing on `[κ / e, ∞)`,
and for `0 < η < 1`, `f(x) ≤ η` whenever `x ≥ e κ + 4 log(1/η) / log(e + κ⁻¹ log(1/η))`.

## Main statements

* `prop5f`, `prop5rpow`, `prop5Threshold`: exponential form, real-power form,
  and truncation threshold `e κ + 4 log(1/η) / log(e + κ⁻¹ log(1/η))`.
* `monotoneOn_prop5rpow`: `x ↦ (κ / x)^x` is antitone on `[κ / e, ∞)`.
* `tail_bound`: `(κ / x)^x ≤ η` for all `x ≥ prop5Threshold κ η`.
* `proposition5`: combined monotonicity and tail bound.

## References

* [Mizuta and Fujii, 2023][MizutaFujii2023TimePeriodic], Section 4.2,
  Proposition 5, Eqs. (57)--(58), p. 13.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TimePeriodic22.MainResults

open scoped BigOperators

/-- `f(x) = (κ / x)^x` written through the exponential form `exp (x log (κ / x))`. -/
def prop5f (κ x : ℝ) : ℝ := Real.exp (x * Real.log (κ / x))

/-- `f(x) = (κ / x)^x` written using real exponentiation. -/
def prop5rpow (κ x : ℝ) : ℝ := (κ / x) ^ x

/-- The exponential form `prop5f` agrees with the real-power form `prop5rpow`
for positive `κ` and `x`. -/
lemma prop5f_eq_rpow {κ x : ℝ} (hx : 0 < x) (hκ : 0 < κ) :
    prop5f κ x = prop5rpow κ x := by
  have hpos : 0 < κ / x := div_pos hκ hx
  simp only [prop5f, prop5rpow, Real.rpow_def_of_pos hpos, mul_comm]

/-- `prop5f κ` is continuous on `[κ / e, ∞)` for `κ > 0`. -/
lemma prop5f_continuousOn (κ : ℝ) (hκ : 0 < κ) :
    ContinuousOn (fun x : ℝ => prop5f κ x) (Set.Ici (κ / Real.exp 1)) := by
  have hbase : (0 : ℝ) < κ / Real.exp 1 := div_pos hκ (Real.exp_pos 1)
  have hdiv : ContinuousOn (fun x : ℝ => κ / x) (Set.Ici (κ / Real.exp 1)) :=
    continuousOn_const.div continuousOn_id (fun x hx => (lt_of_lt_of_le hbase hx).ne')
  have hlog : ContinuousOn (fun x : ℝ => Real.log (κ / x)) (Set.Ici (κ / Real.exp 1)) :=
    hdiv.log (fun x hx => div_ne_zero hκ.ne' (lt_of_lt_of_le hbase hx).ne')
  have hmul : ContinuousOn (fun x : ℝ => x * Real.log (κ / x)) (Set.Ici (κ / Real.exp 1)) :=
    continuousOn_id.mul hlog
  exact Real.continuous_exp.comp_continuousOn hmul

/-- Arithmetic helper: `(κ / x)⁻¹ * (-(κ / x^2)) = -x⁻¹`. -/
lemma deriv_log_div_arith {κ x : ℝ} (hx : x ≠ 0) (hκ : κ ≠ 0) :
    ((κ / x)⁻¹) * (-(κ / x ^ 2)) = -(x)⁻¹ := by
  field_simp

/-- Arithmetic helper: `x * (-x⁻¹) = -1`. -/
lemma mul_neg_inv_self {x : ℝ} (hx : x ≠ 0) : x * (-(x)⁻¹) = -1 := by
  field_simp

/-- Derivative of `prop5f κ` on `(κ / e, ∞)`. -/
lemma hasDerivAt_prop5f {κ x : ℝ} (hκ : 0 < κ) (hx : κ / Real.exp 1 < x) :
    HasDerivAt (fun y : ℝ => prop5f κ y)
      (prop5f κ x * (Real.log (κ / x) - 1)) x := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hxpos : (0 : ℝ) < x := lt_trans (div_pos hκ he) hx
  have hκx : 0 < κ / x := div_pos hκ hxpos
  have hdiv : HasDerivAt (fun y : ℝ => κ / y) (-(κ / x ^ 2)) x := by
    have hc : HasDerivAt (fun _ : ℝ => κ) 0 x := hasDerivAt_const (x := x) (c := κ)
    have h := hc.fun_div (hasDerivAt_id x) hxpos.ne'
    simpa [neg_div] using h
  have hlog : HasDerivAt (fun y : ℝ => Real.log (κ / y)) (-(x)⁻¹) x := by
    have h := (Real.hasDerivAt_log hκx.ne').comp x hdiv
    rw [deriv_log_div_arith hxpos.ne' hκ.ne'] at h
    exact h
  have hinner : HasDerivAt (fun y : ℝ => y * Real.log (κ / y))
      (Real.log (κ / x) - 1) x := by
    have h := (hasDerivAt_id x).mul hlog
    convert! h using 1
    simp [id_eq, mul_neg_inv_self hxpos.ne', sub_eq_add_neg]
  have hexp := Real.hasDerivAt_exp (x * Real.log (κ / x))
  have hfin := hexp.comp x hinner
  convert! hfin using 1

/-- The derivative of `prop5f κ` is nonpositive on `(κ / e, ∞)`. -/
lemma deriv_prop5f_nonpos {κ x : ℝ} (hκ : 0 < κ) (hx : κ / Real.exp 1 < x) :
    deriv (fun y : ℝ => prop5f κ y) x ≤ 0 := by
  rw [(hasDerivAt_prop5f hκ hx).deriv]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hxpos : (0 : ℝ) < x := lt_trans (div_pos hκ he) hx
  have hfpos : 0 < prop5f κ x := Real.exp_pos _
  have hlog : Real.log (κ / x) - 1 ≤ 0 := by
    have hlt : κ / x < Real.exp 1 := by
      rw [div_lt_iff₀ hxpos]
      have h1 : κ = (κ / Real.exp 1) * Real.exp 1 := by field_simp
      calc κ = (κ / Real.exp 1) * Real.exp 1 := h1
        _ < x * Real.exp 1 := by nlinarith [hx, he]
        _ = Real.exp 1 * x := by ring
    have h2 := Real.log_lt_log (div_pos hκ hxpos) hlt
    rw [Real.log_exp] at h2
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos hfpos.le hlog

/-- **Proposition 5 (part 1)**: `f(x) = (κ / x)^x` is monotonically decreasing
for `x ≥ κ / e`. -/
theorem monotoneOn_prop5rpow {κ : ℝ} (hκ : 0 < κ) :
    AntitoneOn (fun x : ℝ => prop5rpow κ x) (Set.Ici (κ / Real.exp 1)) := by
  have hbase : (0 : ℝ) < κ / Real.exp 1 := div_pos hκ (Real.exp_pos 1)
  have hf : AntitoneOn (fun x : ℝ => prop5f κ x) (Set.Ici (κ / Real.exp 1)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) (prop5f_continuousOn κ hκ)
      (fun x hx => (hasDerivAt_prop5f hκ (by simpa using hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    have hx' : κ / Real.exp 1 < x := by simpa using hx
    exact deriv_prop5f_nonpos hκ hx'
  refine hf.congr (fun x hx => ?_)
  exact prop5f_eq_rpow (lt_of_lt_of_le hbase hx) hκ

/-- The threshold `e κ + 4 log(1/η) / log(e + κ⁻¹ log(1/η))` of Eq. (58). -/
def prop5Threshold (κ η : ℝ) : ℝ :=
  Real.exp 1 * κ + 4 * Real.log (1 / η) /
    Real.log (Real.exp 1 + κ⁻¹ * Real.log (1 / η))

/-- **Proposition 5 (part 2)**: for `κ > 0`, `0 < η < 1`, and every
`x ≥ prop5Threshold κ η`, `(κ / x)^x ≤ η`. -/
theorem tail_bound {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∀ x : ℝ, prop5Threshold κ η ≤ x → prop5rpow κ x ≤ η := by
  intro x hx
  let L := Real.log (1 / η)
  let u := κ⁻¹ * L
  let B := Real.log (Real.exp 1 + u)
  let z := Real.exp 1 + 4 * u / B
  let X := prop5Threshold κ η
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hη0).2 (by simpa using hη1))
  have hu : 0 < u := mul_pos (inv_pos.mpr hκ) hL
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hB1 : 1 < B := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < B := Real.log_lt_log he (lt_add_of_pos_right _ hu)
  have hB : 0 < B := by linarith
  have hBexp : Real.exp B = Real.exp 1 + u := Real.exp_log (by positivity)
  have hze : Real.exp 1 < z := lt_add_of_pos_right _ (div_pos (by positivity) hB)
  have hz : 0 < z := he.trans hze
  have hX : X = κ * z := by
    change Real.exp 1 * κ + 4 * L / B = κ * (Real.exp 1 + 4 * (κ⁻¹ * L) / B)
    field_simp
  have hXpos : 0 < X := by rw [hX]; exact mul_pos hκ hz
  have hbase : κ / Real.exp 1 ≤ X := by
    rw [hX]
    have hdiv : κ / Real.exp 1 ≤ κ := (div_le_iff₀ he).2 (by nlinarith)
    exact hdiv.trans (by nlinarith)
  have hlog : B / 4 ≤ Real.log z := by
    rcases le_total B 4 with hsmall | hlarge
    · have huz : Real.exp 1 + u ≤ z := by
        have hquot : u ≤ 4 * u / B := (le_div_iff₀ hB).2 (by nlinarith)
        dsimp [z]
        linarith
      have hBlog : B ≤ Real.log z := by
        simpa only [B] using Real.log_le_log (by positivity : 0 < Real.exp 1 + u) huz
      linarith
    · have hetwo : 2 * Real.exp 1 ≤ Real.exp B := by
        have htwo : (2 : ℝ) ≤ Real.exp (B - 1) := by
          linarith [Real.add_one_le_exp (B - 1)]
        calc
          2 * Real.exp 1 ≤ Real.exp 1 * Real.exp (B - 1) := by nlinarith
          _ = Real.exp B := by rw [← Real.exp_add]; congr 1; ring
      have huB : Real.exp B / 2 ≤ u := by rw [hBexp] at hetwo ⊢; linarith
      have hexp : Real.exp (B / 4) ≤ 2 * Real.exp B / B := by
        apply (le_div_iff₀ hB).2
        have hlinear : B ≤ 2 * Real.exp (3 * B / 4) := by
          linarith [Real.add_one_le_exp (3 * B / 4)]
        calc
          Real.exp (B / 4) * B ≤
              2 * (Real.exp (B / 4) * Real.exp (3 * B / 4)) := by
            nlinarith [mul_le_mul_of_nonneg_left hlinear (Real.exp_pos (B / 4)).le]
          _ = 2 * Real.exp B := by rw [← Real.exp_add]; congr 1; ring
      apply (Real.le_log_iff_exp_le hz).2
      calc
        Real.exp (B / 4) ≤ 2 * Real.exp B / B := hexp
        _ ≤ 4 * u / B := div_le_div_of_nonneg_right (by linarith) hB.le
        _ ≤ z := by dsimp [z]; linarith
  have hprod : u ≤ z * Real.log z := by
    calc
      u = (4 * u / B) * (B / 4) := by field_simp
      _ ≤ z * Real.log z := mul_le_mul (by dsimp [z]; linarith) hlog
        (by positivity) hz.le
  have hXL : L ≤ X * Real.log (X / κ) := by
    rw [hX, mul_div_cancel_left₀ z hκ.ne']
    have hκu : κ * u = L := by dsimp [u]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hprod hκ.le]
  have hthreshold : prop5rpow κ X ≤ η := by
    rw [← prop5f_eq_rpow hXpos hκ, prop5f]
    have hlogs : Real.log (κ / X) = -Real.log (X / κ) := by
      rw [Real.log_div hκ.ne' hXpos.ne', Real.log_div hXpos.ne' hκ.ne']
      ring
    have hLη : L = -Real.log η := by
      dsimp [L]
      rw [Real.log_div one_ne_zero hη0.ne', Real.log_one]
      ring
    rw [hlogs, ← Real.exp_log hη0]
    apply Real.exp_le_exp.mpr
    rw [hLη] at hXL
    nlinarith
  exact ((monotoneOn_prop5rpow hκ) hbase (hbase.trans hx) hx).trans hthreshold

/-- **Proposition 5**: monotonicity on `[κ / e, ∞)` and the truncation tail bound
Eq. (58) for `κ > 0` and `0 < η < 1`. -/
theorem proposition5 {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    AntitoneOn (fun x : ℝ => prop5rpow κ x) (Set.Ici (κ / Real.exp 1)) ∧
      ∀ x : ℝ, prop5Threshold κ η ≤ x → prop5rpow κ x ≤ η :=
  ⟨monotoneOn_prop5rpow hκ, tail_bound hκ hη0 hη1⟩

end Qatlib.Papers.TimePeriodic22.MainResults
