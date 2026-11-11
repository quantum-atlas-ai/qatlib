/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Angle representatives and trigonometric identities

Relates reduction modulo `2π` to equality in `Real.Angle`, and controls subtraction of real
angle representatives under sign hypotheses. Further lemmas recover integer shifts from matching
sine and cosine values.

These identities support the crossing-angle calculations used in the contour framework
associated with [WangEtAl2026].

## Main statements

* `Angle.toIcoMod_eq_toIcoMod_iff_coe_eq`: Two real numbers have the same representative in `[0,
  2π)` exactly when they determine the same element of `Real.Angle`.
* `Real.exists_int_eq_add_of_cos_sin_eq`: Equality of both sine and cosine at `2πa` and `2πb`
  implies that `a` differs from `b` by an integer.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

namespace TauCeti

/-- Two real numbers have the same representative in `[0, 2π)` exactly when they determine the
same element of `Real.Angle`. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq {x y : ℝ} :
    toIcoMod Real.two_pi_pos 0 x = toIcoMod Real.two_pi_pos 0 y ↔
      (x : Real.Angle) = (y : Real.Angle) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Real.Angle.coe_toIcoMod x 0, ← Real.Angle.coe_toIcoMod y 0, h]
  · obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    have hshift : x = y + k • (2 * Real.pi) := by rw [zsmul_eq_mul]; linarith
    rw [hshift, toIcoMod_add_zsmul]

/-- For angles with equal sign and `ψ ≠ π`, taking the real representative commutes with
subtracting `ψ`. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Real.Angle.toReal_sub_of_sign_eq {θ ψ : Real.Angle} (hψ : ψ ≠ ↑Real.pi)
    (hs : θ.sign = ψ.sign) : (θ - ψ).toReal = θ.toReal - ψ.toReal := by
  have hψ' : -ψ ≠ ↑Real.pi := fun h ↦ hψ (by rw [← neg_neg ψ, h, Real.Angle.neg_coe_pi])
  rw [sub_eq_add_neg, Real.Angle.toReal_add_of_sign_eq_neg_sign (.inr hψ')
    (by rw [Real.Angle.sign_neg, neg_neg, hs]), Real.Angle.toReal_neg_eq_neg_toReal_iff.2 hψ,
    ← sub_eq_add_neg]

/-- For angles with the same nonzero sign, the difference `ψ - θ` has positive sign exactly when
`θ.toReal < ψ.toReal`. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Real.Angle.sign_sub_pos_iff_toReal_lt_of_sign_eq {θ ψ : Real.Angle}
    (hs : θ.sign = ψ.sign) (h0 : θ.sign ≠ 0) : (ψ - θ).sign = 1 ↔ θ.toReal < ψ.toReal := by
  rw [← Real.Angle.sign_toReal (Real.Angle.sub_ne_pi_of_sign_eq_of_sign_ne_zero ψ θ hs.symm h0),
    Real.Angle.toReal_sub_of_sign_eq (Real.Angle.sign_ne_zero_iff.1 h0).2 hs.symm, sign_eq_one_iff,
    sub_pos]

/-- Equality of both sine and cosine at `2πa` and `2πb` implies that `a` differs from `b` by an
integer. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Real.exists_int_eq_add_of_cos_sin_eq {a b : ℝ}
    (hc : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b))
    (hs : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b)) : ∃ n : ℤ, a = b + n := by
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi (by linarith)

/-- If `|θ.toReal| = α` and `θ + α = β` with `0 < β < π`, then `β = 2α`. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Real.Angle.eq_two_mul_of_abs_toReal_eq {θ : Real.Angle} {α β : ℝ}
    (hθ : |θ.toReal| = α) (hβ : θ + α = β) (hβ₀ : 0 < β) (hβπ : β < Real.pi) :
    β = 2 * α := by
  have hα₀ : 0 ≤ α := hθ ▸ abs_nonneg _
  have hαπ : α ≤ Real.pi := hθ ▸ θ.abs_toReal_le_pi
  have hπ := Real.pi_pos
  have hβrep : (β : Real.Angle).toReal = β :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, hβπ.le⟩
  have hsum : ((θ.toReal + α : ℝ) : Real.Angle) = β := by
    rw [Real.Angle.coe_add, θ.coe_toReal, hβ]
  rcases (abs_eq hα₀).1 hθ with hpos | hneg
  · rw [hpos] at hsum
    by_cases hα : α = 0
    · have h := congrArg Real.Angle.toReal hsum
      rw [hα, zero_add, Real.Angle.coe_zero, Real.Angle.toReal_zero, hβrep] at h
      linarith
    · have hαpos : 0 < α := lt_of_le_of_ne hα₀ (Ne.symm hα)
      let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
      have h := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := 2 * Real.pi) (a := 0)
        (x := α + α) (y := β) ⟨by linarith, by linarith⟩ ⟨hβ₀, by linarith⟩).1 hsum
      linarith
  · have hzero : θ.toReal + α = 0 := by linarith
    have h := congrArg Real.Angle.toReal hsum
    rw [hzero, Real.Angle.coe_zero, Real.Angle.toReal_zero, hβrep] at h
    linarith

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
