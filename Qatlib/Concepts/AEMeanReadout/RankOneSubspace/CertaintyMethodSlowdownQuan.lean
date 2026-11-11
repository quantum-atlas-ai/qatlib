/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.CertaintyMethodSlowdownStat
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan

/-!
# A final phase adjustment for certain success

`certaintyMethodSlowdown` proves the phase-adjustment method for exact amplification described
in [BrassardHoyerTapp1998Counting]. After the integer number of ordinary iterations below the
ideal stopping point, suitable unit-modulus phases give marked mass one.

## Main statements

* `certaintyMethodSlowdown`: existence of a final phase adjustment yielding certain marked
  output.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open scoped BigOperators

/-- For positive amplitudes satisfying the stated normalization and size bound, constructs two
unit-modulus phases solving the cancellation equations and giving final marked mass one. -/
private lemma slowdown_phases (a k l : ℝ) (ha : 0 < a)
    (hk : 0 < k) (hl : 0 < l) (hbound : l ^ 2 ≤ 4 * a)
    (hstate : a * k ^ 2 + (1 - a) * l ^ 2 = 1) :
    ∃ φ ϕ : ℂ, ‖φ‖ = 1 ∧ ‖ϕ‖ = 1 ∧
      l ^ 2 = 2 * a * (1 - φ.re) ∧
      ϕ * (1 - φ) * (a : ℂ) * (k : ℂ) =
        ((1 - φ) * (a : ℂ) + φ) * (l : ℂ) ∧
      Complex.normSq ((l : ℂ) - ϕ * (k : ℂ)) * a = 1 := by
  let c : ℝ := 1 - l ^ 2 / (2 * a)
  have hc0 : -1 ≤ c := by
    have h : l ^ 2 / (2 * a) ≤ 2 :=
      (div_le_iff₀ (show 0 < 2 * a by positivity)).2 (by linarith)
    dsimp [c]
    linarith
  have hc1 : c < 1 := by
    have h : 0 < l ^ 2 / (2 * a) := by positivity
    dsimp [c]
    linarith
  let φ : ℂ := (c : ℂ) + Complex.I * (Real.sqrt (1 - c ^ 2) : ℂ)
  have hφsq : Complex.normSq φ = 1 :=
    Complex.normSq_ofReal_add_I_mul_sqrt_one_sub (abs_le.mpr ⟨hc0, hc1.le⟩)
  have hφ : ‖φ‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hφsq
    nlinarith [norm_nonneg φ]
  have hfirst : l ^ 2 = 2 * a * (1 - φ.re) := by
    simp only [φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_self, add_zero]
    dsimp [c]
    field_simp
    ring
  have hsub : Complex.normSq (1 - φ) = 2 * (1 - φ.re) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im] at *
    nlinarith
  have hφne : 1 - φ ≠ 0 := by
    intro h
    have hp : φ = 1 := sub_eq_zero.mp h |>.symm
    rw [hp, Complex.one_re] at hfirst
    nlinarith
  let D : ℂ := (1 - φ) * (a : ℂ) * (k : ℂ)
  let C : ℂ := (1 - φ) * (a : ℂ) + φ
  have hD : D ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hφne (Complex.ofReal_ne_zero.mpr ha.ne'))
      (Complex.ofReal_ne_zero.mpr hk.ne')
  have hDs : Complex.normSq D = l ^ 2 * a * k ^ 2 := by
    simp only [D, Complex.normSq_mul, Complex.normSq_ofReal, hsub]
    linear_combination -a * k ^ 2 * hfirst
  have hCs : Complex.normSq C = 1 - (1 - a) * l ^ 2 := by
    simp only [C, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_sub] at *
    linear_combination (1 - a) ^ 2 * hφsq + (1 - a) * hfirst
  let ϕ : ℂ := C * (l : ℂ) / D
  have hϕsq : Complex.normSq ϕ = 1 := by
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal,
      hCs, hDs]
    apply (div_eq_one_iff_eq (by positivity : l ^ 2 * a * k ^ 2 ≠ 0)).2
    linear_combination -l ^ 2 * hstate
  have hϕ : ‖ϕ‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hϕsq
    nlinarith [norm_nonneg ϕ]
  have hsecond : ϕ * (1 - φ) * (a : ℂ) * (k : ℂ) = C * (l : ℂ) := by
    change (C * (l : ℂ) / D) * (1 - φ) * (a : ℂ) * (k : ℂ) = _
    calc
      _ = (C * (l : ℂ) / D) * D := by dsimp [D]; ring
      _ = _ := div_mul_cancel₀ _ hD
  have hcancel : ((l : ℂ) - ϕ * (k : ℂ)) * ((1 - φ) * (a : ℂ)) =
      -(l : ℂ) * φ := by
    dsimp [C] at hsecond
    linear_combination -hsecond
  have hmass := congrArg Complex.normSq hcancel
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal,
    hφsq, mul_one, hsub] at hmass
  have hscale : (2 * (1 - φ.re)) * (a * a) = l ^ 2 * a := by
    linear_combination -a * hfirst
  rw [hscale] at hmass
  have hfinal : Complex.normSq ((l : ℂ) - ϕ * (k : ℂ)) * a = 1 := by
    apply (mul_right_inj' (ne_of_gt (sq_pos_of_pos hl))).mp
    convert hmass using 1 <;> ring
  exact ⟨φ, ϕ, hφ, hϕ, hfirst, hsecond, hfinal⟩

/-- For `0 < θ < π/2` and a strict floor inequality, the angle after the floored number of
ordinary iterations lies in `(0, π/2)` and satisfies the stated cosine bound. -/
private lemma slowdown_angle (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hfloor : (Nat.floor (Real.pi / (4 * θ) - 1 / 2) : ℝ) <
      Real.pi / (4 * θ) - 1 / 2) :
    let x := (2 * (Nat.floor (Real.pi / (4 * θ) - 1 / 2) : ℝ) + 1) * θ
    0 < x ∧ x < Real.pi / 2 ∧
      Real.cos x ^ 2 ≤ 4 * Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2) := by
  let m : ℕ := Nat.floor (Real.pi / (4 * θ) - 1 / 2)
  let x : ℝ := (2 * (m : ℝ) + 1) * θ
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hxθ : θ ≤ x := by dsimp [x]; nlinarith
  have hx0 : 0 < x := hθ0.trans_le hxθ
  have hupper : (m : ℝ) + 1 / 2 < Real.pi / (4 * θ) := by
    change (m : ℝ) < _ at hfloor
    linarith
  have hu := (lt_div_iff₀ (show 0 < 4 * θ by positivity)).mp hupper
  have hx1 : x < Real.pi / 2 := by dsimp [x]; nlinarith
  have hfl := Nat.lt_floor_add_one (Real.pi / (4 * θ) - 1 / 2)
  have hlower : Real.pi / (4 * θ) < (m : ℝ) + 3 / 2 := by
    change _ < (m : ℝ) + 1 at hfl
    linarith
  have hd := (div_lt_iff₀ (show 0 < 4 * θ by positivity)).mp hlower
  have hxl : Real.pi / 2 - 2 * θ < x := by dsimp [x]; nlinarith
  have hcx : 0 ≤ Real.cos x :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩).le
  have hct : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).le
  have htrig := Real.sin_sq_add_cos_sq θ
  refine ⟨hx0, hx1, ?_⟩
  by_cases hlarge : Real.pi / 6 ≤ θ
  · have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.pi / 6 by linarith [Real.pi_pos]) hθ1.le hlarge
    rw [Real.sin_pi_div_six] at hs
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hθ0.le
      (show x ≤ Real.pi by linarith [Real.pi_pos]) hxθ
    have hc2 := pow_le_pow_left₀ hcx hc 2
    have hprod := mul_nonneg (show 0 ≤ 4 * Real.sin θ ^ 2 - 1 by nlinarith)
      (sq_nonneg (Real.cos θ))
    nlinarith
  · have hy : 0 ≤ Real.pi / 2 - 2 * θ := by
      have := lt_of_not_ge hlarge
      linarith [Real.pi_pos]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hy
      (show x ≤ Real.pi by linarith [Real.pi_pos]) hxl.le
    rw [Real.cos_pi_div_two_sub] at hc
    have hc2 := pow_le_pow_left₀ hcx hc 2
    rw [Real.sin_two_mul] at hc2
    nlinarith

/-- Constructs a final pair of unit-modulus phases that yields marked mass one after the floored
number of ordinary amplification iterations, under the strict floor condition [Brassard et
al., Section 2][BrassardHoyerTapp1998Counting]. -/
theorem certaintyMethodSlowdown : CertaintyMethodSlowdown := by
  intro n A g hA a θ hθ0 hθ1 hmass m hfloor
  let x : ℝ := (2 * (m : ℝ) + 1) * θ
  let k : ℝ := Real.sin x / Real.sqrt a
  let l : ℝ := Real.cos x / Real.sqrt (1 - a)
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ1⟩
  have ha : 0 < a := by change Real.sin θ ^ 2 = a at hmass; nlinarith
  have ha1 : a < 1 := by
    have ht := Real.sin_sq_add_cos_sq θ
    change Real.sin θ ^ 2 = a at hmass
    nlinarith
  obtain ⟨hx0, hx1, hxb⟩ := slowdown_angle θ hθ0 hθ1 hfloor
  change 0 < x at hx0
  change x < Real.pi / 2 at hx1
  change Real.cos x ^ 2 ≤ _ at hxb
  rw [hmass] at hxb
  have hk : 0 < k := div_pos
    (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos]))
    (Real.sqrt_pos.mpr ha)
  have hl : 0 < l := div_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩)
    (Real.sqrt_pos.mpr (sub_pos.mpr ha1))
  have hks : k ^ 2 * a = Real.sin x ^ 2 := by
    dsimp [k]
    rw [div_pow, Real.sq_sqrt ha.le, div_mul_cancel₀ _ ha.ne']
  have hls : l ^ 2 * (1 - a) = Real.cos x ^ 2 := by
    dsimp [l]
    rw [div_pow, Real.sq_sqrt (sub_nonneg.mpr ha1.le),
      div_mul_cancel₀ _ (sub_pos.mpr ha1).ne']
  have hbound : l ^ 2 ≤ 4 * a := by
    apply (mul_le_mul_iff_left₀ (sub_pos.mpr ha1)).mp
    rw [hls]
    exact hxb
  have hstate : a * k ^ 2 + (1 - a) * l ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  obtain ⟨φ, ϕ, hφ, hϕ, hfirst, hsecond, hfinal⟩ :=
    slowdown_phases a k l ha hk hl hbound hstate
  refine ⟨φ, ϕ, hφ, hϕ, hfirst, ?_, ?_⟩
  · simpa only [k, l, x, Complex.ofReal_div] using hsecond
  have hrotation := zoo_counting_rankone_known_success_amplification_rotation
    A g hA θ hθ0.le hθ1.le hmass ha ha1 m
  obtain ⟨hgood, hbad⟩ := zoo_counting_two_dimensional_phase_action n A g φ ϕ hA hφ hϕ
  have houtput :
      (RankOneReflection.iterate A g φ ϕ).mulVec
          (((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec (fun i => A i 0)) =
        ((l : ℂ) - ϕ * (k : ℂ)) • RankOneReflection.goodPart g (fun i => A i 0) +
          (0 : ℂ) • RankOneReflection.badPart g (fun i => A i 0) := by
    rw [hrotation, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hgood, hbad]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change (k : ℂ) *
          (ϕ * ((1 - φ) * (a : ℂ) - 1) * RankOneReflection.goodPart g (fun i => A i 0) i +
            ϕ * (1 - φ) * (a : ℂ) * RankOneReflection.badPart g (fun i => A i 0) i) +
        (l : ℂ) *
          (-((1 - φ) * (a : ℂ) + φ) * RankOneReflection.badPart g (fun i => A i 0) i +
            (1 - φ) * (1 - (a : ℂ)) * RankOneReflection.goodPart g (fun i => A i 0) i) =
        ((l : ℂ) - ϕ * (k : ℂ)) * RankOneReflection.goodPart g (fun i => A i 0) i +
          0 * RankOneReflection.badPart g (fun i => A i 0) i
    linear_combination
      (RankOneReflection.goodPart g (fun i => A i 0) i +
        RankOneReflection.badPart g (fun i => A i 0) i) * hsecond
  rw [houtput, zoo_counting_rankone_known_success_amplification_goodPart_combination,
    zoo_counting_rankone_known_success_amplification_normSq_sum_smul]
  exact hfinal

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
