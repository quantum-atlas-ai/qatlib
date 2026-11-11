/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.HittingSpectrum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Integer hitting times and spectral quantiles

This module defines `HittingLaw.hittingInt` as the least natural time at which the cosine
survival sum is at most a prescribed positive error. Trigonometric and exponential bounds
compare this time with spectral quantiles, giving the two estimates associated with Theorem 2.2
of [MagniezEtAl2008].

## Main statements

* `tendsto_survival`: proves that survival tends to zero when all phases are at most `π / 2`.
* `theorem_2_2_first`: bounds integer hitting time by a rounded logarithmic multiple of a
  quantile.
* `theorem_2_2_second`: bounds a quantile by integer hitting time at a smaller error.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

namespace HittingLaw

variable {J : Type*} [Fintype J]

/-- The half-angle identity `2 * sin (θ / 2) ^ 2 = 1 - cos θ`. -/
theorem two_mul_sin_sq (θ : ℝ) : 2 * Real.sin (θ / 2) ^ 2 = 1 - Real.cos θ := by
  have h := Real.cos_two_mul_eq_one_sub (x := θ / 2)
  have harg : 2 * (θ / 2) = θ := by ring
  rw [harg] at h
  linarith

/-- For `0 ≤ θ ≤ π / 2`, the quantity `1 - cos θ` is at least `θ ^ 2 / 4`. -/
theorem one_sub_cos_ge (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    θ ^ 2 / 4 ≤ 1 - Real.cos θ := by
  rcases eq_or_lt_of_le h0 with rfl | hθ
  · simp
  set y := θ / 2 with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    have h1' : y ≤ Real.pi / 4 := by rw [hy]; linarith
    have h2' : Real.pi / 4 ≤ 1 := by nlinarith [Real.pi_lt_four]
    linarith
  have hsin : (3 / 4) * y ≤ Real.sin y := by
    have hcube : y - y ^ 3 / 4 < Real.sin y := by
      linarith [Real.sin_gt_sub_cube hy0, pow_nonneg hy0.le 3]
    have hsq_le : y ^ 2 ≤ 1 := pow_le_one₀ hy0.le hy1
    have hle : y ^ 3 / 4 ≤ y / 4 := by
      have h3 : y ^ 3 ≤ y := by
        have hmul := mul_le_mul_of_nonneg_left hsq_le hy0.le
        nlinarith [hmul]
      linarith
    linarith
  have hnn : 0 ≤ Real.sin y :=
    Real.sin_nonneg_of_nonneg_of_le_pi hy0.le (by nlinarith [hy, Real.pi_pos])
  have hsq : (1 / 2) * y ^ 2 ≤ Real.sin y ^ 2 := by nlinarith [hsin, hnn, hy0.le]
  have hmain : 2 * Real.sin y ^ 2 = 1 - Real.cos θ := by
    rw [hy]; exact two_mul_sin_sq θ
  nlinarith [hmain, hsq, hy]

/-- For every real `θ`, the quantity `1 - cos θ` is at most `θ ^ 2 / 2`. -/
theorem one_sub_cos_le (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

/-- Every phase `L.theta j` associated with a positive hitting-law value is positive. -/
theorem theta_pos (L : HittingLaw J) (j : J) : 0 < L.theta j := by
  rw [theta]
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (L.val_pos j))

/-- If `L.theta j ≤ π / 2`, its cosine belongs to `[0, 1)`. -/
theorem cos_nonneg_lt_one (L : HittingLaw J) (j : J) (hθ1 : L.theta j ≤ Real.pi / 2) :
    0 ≤ Real.cos (L.theta j) ∧ Real.cos (L.theta j) < 1 := by
  have hθ0 : 0 < L.theta j := L.theta_pos j
  refine ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hθ1, ?_⟩
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 0) (y := L.theta j)
    le_rfl hθ1 hθ0
  simpa using h

/-- The square of the phase `L.theta j` is the reciprocal of `L.val j`. -/
theorem theta_sq (L : HittingLaw J) (j : J) :
    L.theta j ^ 2 = 1 / L.val j := by
  have hv : 0 < L.val j := L.val_pos j
  rw [theta, div_pow, one_pow, Real.sq_sqrt hv.le]

/-- A hitting-law value whose phase is at most `π / 2` is strictly greater than `1 / 4`. -/
theorem val_ge_of_theta_le (L : HittingLaw J) (j : J) (hθ1 : L.theta j ≤ Real.pi / 2) :
    (1 : ℝ) / 4 < L.val j := by
  have hv : 0 < L.val j := L.val_pos j
  have hθ0 : 0 < L.theta j := L.theta_pos j
  have hprod : L.theta j ^ 2 * L.val j = 1 := by
    rw [L.theta_sq j, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hv)]
  have hle : L.theta j ^ 2 ≤ Real.pi ^ 2 / 4 := by nlinarith
  have hπ2 : 0 < Real.pi ^ 2 := by positivity
  have hge : (4 : ℝ) / Real.pi ^ 2 ≤ L.val j := by
    rw [div_le_iff₀ hπ2]
    have hmul : L.theta j ^ 2 * L.val j ≤ (Real.pi ^ 2 / 4) * L.val j :=
      mul_le_mul_of_nonneg_right hle hv.le
    nlinarith [hmul, hprod]
  have hpi2 : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hquarter : (1 : ℝ) / 4 < (4 : ℝ) / Real.pi ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    nlinarith
  linarith

/-- If all phases are at most `π / 2`, the survival sum tends to zero as the natural time tends
to infinity. -/
theorem tendsto_survival (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2) :
    Filter.Tendsto (fun k : ℕ => L.survival k) Filter.atTop (nhds 0) := by
  have hterm : ∀ j : J,
      Filter.Tendsto (fun k : ℕ => Real.cos (L.theta j) ^ k) Filter.atTop (nhds 0) := by
    intro j
    refine tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
    obtain ⟨h0, h1⟩ := L.cos_nonneg_lt_one j (hθ1 j)
    rw [Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith, h1⟩
  have hsum : Filter.Tendsto (fun k : ℕ => ∑ j, L.mass j * Real.cos (L.theta j) ^ k)
      Filter.atTop (nhds (∑ j, L.mass j * 0)) :=
    tendsto_finsetSum _ fun j _ => (hterm j).const_mul (L.mass j)
  simpa [survival] using hsum

/-- If all phases are at most `π / 2`, some natural time has survival at most any prescribed
positive `ε`. -/
theorem exists_survival_le (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) : ∃ k, L.survival k ≤ ε := by
  have h := (L.tendsto_survival hθ1).eventually (isOpen_Iio.mem_nhds hε)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp h
  exact ⟨k, (hk k le_rfl).le⟩

/-- The least natural time at which survival is at most the positive tolerance `ε`, assuming all
phases are at most `π / 2`. -/
def hittingInt (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) : ℕ :=
  Nat.find (L.exists_survival_le hθ1 hε)

/-- Survival at `hittingInt` is at most the prescribed tolerance `ε`. -/
theorem hittingInt_spec (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) : L.survival (L.hittingInt hθ1 hε) ≤ ε :=
  Nat.find_spec (L.exists_survival_le hθ1 hε)

/-- Any natural time with survival at most `ε` is at least `hittingInt`. -/
theorem hittingInt_min (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : L.survival k ≤ ε) :
    L.hittingInt hθ1 hε ≤ k :=
  Nat.find_min' (L.exists_survival_le hθ1 hε) hk

/-- When all phases are at most `π / 2`, survival is nonincreasing in natural time. -/
theorem survival_antitone (L : HittingLaw J) (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    {k k' : ℕ} (h : k ≤ k') : L.survival k' ≤ L.survival k := by
  unfold survival
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h0, h1⟩ := L.cos_nonneg_lt_one j (hθ1 j)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1.le h) (L.mass_nonneg j)

/-- For `0 ≤ x ≤ 1`, the power `(1 - x) ^ n` is at most `exp (-n * x)`. -/
theorem one_sub_pow_le_exp (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 - x) ^ n ≤ Real.exp (-(n : ℝ) * x) := by
  have hbase : 0 ≤ 1 - x := by linarith
  have hstep : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hp : (1 - x) ^ n ≤ Real.exp (-x) ^ n := pow_le_pow_left₀ hbase hstep n
  have he : Real.exp (-x) ^ n = Real.exp (-(n : ℝ) * x) := by
    rw [← Real.exp_nat_mul]
    exact congrArg Real.exp (by ring)
  linarith [hp, he]

/-- For `0 ≤ x ≤ 1` and `n * x ≤ 1 / 2`, the power `(1 - x) ^ n` is at least `1 / 2`. -/
theorem one_sub_pow_ge_half (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ)
    (hx : (n : ℝ) * x ≤ 1 / 2) : (1 / 2 : ℝ) ≤ (1 - x) ^ n := by
  have hbern := one_add_mul_le_pow (a := -x) (by linarith) n
  have harg : (1 : ℝ) + (n : ℝ) * (-x) = 1 - (n : ℝ) * x := by ring
  rw [harg] at hbern
  have hbase : (1 : ℝ) + -x = 1 - x := by ring
  rw [hbase] at hbern
  linarith

/-- With phases at most `π / 2`, total mass at most one, and `ε > 0`, integer hitting time is at
most the natural ceiling of `4 * log (2 / ε) * L.quantile (ε / 2)`. This is the first
comparison in [Magniez et al., Theorem 2.2][MagniezEtAl2008]. -/
theorem theorem_2_2_first (L : HittingLaw J)
    (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2)
    (hTot : L.totalMass ≤ 1) {ε : ℝ} (hε0 : 0 < ε) :
    L.hittingInt hθ1 hε0 ≤ ⌈4 * Real.log (2 / ε) * L.quantile (ε / 2)⌉₊ := by
  refine L.hittingInt_min hθ1 hε0 ?_
  set T := L.quantile (ε / 2) with hTdef
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have htailT : L.tail T ≤ ε / 2 := L.tail_quantile_le hε2.le
  set m := ⌈4 * Real.log (2 / ε) * T⌉₊ with hmdef
  have hmK : 4 * Real.log (2 / ε) * T ≤ (m : ℝ) := Nat.le_ceil _
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset J)
    (fun j => T < L.val j) (fun j => L.mass j * Real.cos (L.theta j) ^ m)
  unfold survival
  rw [← hsplit]

  have hA : ∑ j ∈ Finset.univ.filter (fun j => T < L.val j),
      L.mass j * Real.cos (L.theta j) ^ m ≤ ε / 2 := by
    calc ∑ j ∈ Finset.univ.filter (fun j => T < L.val j),
            L.mass j * Real.cos (L.theta j) ^ m
        ≤ ∑ j ∈ Finset.univ.filter (fun j => T < L.val j), L.mass j := by
          refine Finset.sum_le_sum fun j _ => ?_
          obtain ⟨hc0, hc1⟩ := L.cos_nonneg_lt_one j (hθ1 j)
          simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hc0 hc1.le) (L.mass_nonneg j)
      _ = L.tail T := rfl
      _ ≤ ε / 2 := htailT

  have hB : ∑ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j),
      L.mass j * Real.cos (L.theta j) ^ m ≤ ε / 2 := by
    by_cases hsmall : T < 1 / 4
    · have hemp : Finset.univ.filter (fun j => ¬ T < L.val j) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro j _ hmem
        have hval : L.val j ≤ T := le_of_not_gt hmem
        have hquarter := L.val_ge_of_theta_le j (hθ1 j)
        linarith
      rw [hemp, Finset.sum_empty]
      linarith
    · push Not at hsmall
      have hTpos : 0 < T := by linarith
      have hc0T : (0 : ℝ) ≤ 1 / (4 * T) :=
        le_of_lt (one_div_pos.mpr (by linarith))

      have hstep : ∀ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j),
          L.mass j * Real.cos (L.theta j) ^ m ≤ L.mass j * (ε / 2) := by
        intro j hj
        have hval : L.val j ≤ T := le_of_not_gt (Finset.mem_filter.mp hj).2
        have hv : 0 < L.val j := L.val_pos j

        have hge : 1 / (4 * T) ≤ 1 - Real.cos (L.theta j) := by
          have h1 : (1 : ℝ) / (4 * T) ≤ 1 / (4 * L.val j) :=
            one_div_le_one_div_of_le (by linarith) (by linarith)
          have h2 : (1 : ℝ) / (4 * L.val j) = L.theta j ^ 2 / 4 := by
            rw [L.theta_sq j]
            ring
          have h3 : L.theta j ^ 2 / 4 ≤ 1 - Real.cos (L.theta j) :=
            one_sub_cos_ge (L.theta j) (L.theta_pos j).le (hθ1 j)
          linarith
        obtain ⟨hc0, _hc1'⟩ := L.cos_nonneg_lt_one j (hθ1 j)
        have hx1 : (1 : ℝ) / (4 * T) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have hc1 : Real.cos (L.theta j) ≤ 1 - 1 / (4 * T) := by linarith
        have hmono : Real.cos (L.theta j) ^ m ≤ (1 - 1 / (4 * T)) ^ m :=
          pow_le_pow_left₀ hc0 hc1 m
        have hexp := one_sub_pow_le_exp (1 / (4 * T)) hc0T hx1 m
        have hmain : (1 - 1 / (4 * T)) ^ m ≤ ε / 2 := by
          refine hexp.trans ?_
          have harg : -(m : ℝ) * (1 / (4 * T))
              ≤ -(4 * Real.log (2 / ε) * T) * (1 / (4 * T)) := by
            have hK : (4 * Real.log (2 / ε) * T) * (1 / (4 * T))
                ≤ (m : ℝ) * (1 / (4 * T)) :=
              mul_le_mul_of_nonneg_right hmK hc0T
            linarith
          refine (Real.exp_le_exp.mpr harg).trans_eq ?_
          have hc : -(4 * Real.log (2 / ε) * T) * (1 / (4 * T))
              = -Real.log (2 / ε) := by
            have h4T : (4 : ℝ) * T ≠ 0 := ne_of_gt (by positivity)
            field_simp
          rw [hc, Real.exp_neg, Real.exp_log (div_pos (by norm_num) hε0), inv_div]
        exact mul_le_mul_of_nonneg_left (hmono.trans hmain) (L.mass_nonneg j)
      have hmass : ∑ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j), L.mass j ≤ 1 := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans hTot
        intro i _ _; exact L.mass_nonneg i
      calc ∑ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j),
              L.mass j * Real.cos (L.theta j) ^ m
          ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j), L.mass j * (ε / 2) :=
            Finset.sum_le_sum hstep
        _ = (∑ j ∈ Finset.univ.filter (fun j => ¬ T < L.val j), L.mass j) * (ε / 2) := by
            rw [Finset.sum_mul]
        _ ≤ 1 * (ε / 2) :=
            mul_le_mul_of_nonneg_right hmass (by linarith)
        _ = ε / 2 := one_mul _
  linarith [hA, hB]

/-- With phases at most `π / 2` and `ε > 0`, the `ε`-quantile is at most the integer hitting
time for tolerance `ε / 3`. This is the second comparison in [Magniez et al., Theorem
2.2][MagniezEtAl2008]. -/
theorem theorem_2_2_second (L : HittingLaw J)
    (hθ1 : ∀ j, L.theta j ≤ Real.pi / 2) {ε : ℝ} (hε0 : 0 < ε) :
    L.quantile ε ≤ (L.hittingInt hθ1 (by linarith : (0 : ℝ) < ε / 3) : ℝ) := by
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have htail : L.tail ((L.hittingInt hθ1 hε3 : ℕ) : ℝ) ≤ ε := by
    let n := L.hittingInt hθ1 hε3
    change L.tail ((n : ℕ) : ℝ) ≤ ε
    have hsn : L.survival n ≤ ε / 3 := L.hittingInt_spec hθ1 hε3
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn] at hsn ⊢
      have h0 : L.survival 0 = L.totalMass := by
        unfold survival totalMass
        simp
      have ht0 : L.tail (0 : ℝ) = L.totalMass := by
        unfold tail totalMass
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j
        simp [L.val_pos j]
      rw [Nat.cast_zero, ht0]
      nlinarith [h0, hsn, hε0]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hhalf : (1 / 2 : ℝ) * L.tail (n : ℝ) ≤ L.survival n := by
        have hstep : ∀ j ∈ Finset.univ.filter (fun j => (n : ℝ) < L.val j),
            L.mass j * (1 / 2) ≤ L.mass j * Real.cos (L.theta j) ^ n := by
          intro j hj
          have hval : (n : ℝ) < L.val j := (Finset.mem_filter.mp hj).2
          have hv : 0 < L.val j := L.val_pos j
          have hprod : L.theta j ^ 2 * L.val j = 1 := by
            rw [L.theta_sq j, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hv)]
          have hθ2pos : 0 < L.theta j ^ 2 := pow_pos (L.theta_pos j) 2

          have hθ2lt : L.theta j ^ 2 < 1 / (n : ℝ) := by
            rw [lt_div_iff₀ hn0]
            have hmul := mul_lt_mul_of_pos_left hval hθ2pos
            nlinarith [hmul, hprod]
          have hθ2le : L.theta j ^ 2 ≤ 1 := by
            have hle1 : 1 / (n : ℝ) ≤ 1 := by
              rw [div_le_one hn0]; exact_mod_cast hn
            linarith

          have hx : (n : ℝ) * (L.theta j ^ 2 / 2) ≤ 1 / 2 := by
            have htmp : (n : ℝ) * L.theta j ^ 2 < (n : ℝ) * (1 / (n : ℝ)) :=
              mul_lt_mul_of_pos_left hθ2lt hn0
            have hnn : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
              rw [mul_one_div, div_self (ne_of_gt hn0)]
            nlinarith [htmp, hnn]
          have hx0 : (0 : ℝ) ≤ L.theta j ^ 2 / 2 := by positivity
          have hx1 : L.theta j ^ 2 / 2 ≤ 1 := by linarith

          have hbern : (1 / 2 : ℝ) ≤ (1 - L.theta j ^ 2 / 2) ^ n :=
            one_sub_pow_ge_half (L.theta j ^ 2 / 2) hx0 hx1 n hx
          have hbase : (0 : ℝ) ≤ 1 - L.theta j ^ 2 / 2 := by linarith
          have hcos : 1 - L.theta j ^ 2 / 2 ≤ Real.cos (L.theta j) := by
            have h := one_sub_cos_le (L.theta j)
            linarith
          have hpow : (1 / 2 : ℝ) ≤ Real.cos (L.theta j) ^ n :=
            hbern.trans (pow_le_pow_left₀ hbase hcos n)
          calc L.mass j * (1 / 2) = (1 / 2) * L.mass j := by ring
            _ ≤ Real.cos (L.theta j) ^ n * L.mass j :=
                mul_le_mul_of_nonneg_right hpow (L.mass_nonneg j)
            _ = L.mass j * Real.cos (L.theta j) ^ n := by ring
        have hsum : (1 / 2 : ℝ) * L.tail (n : ℝ)
            = ∑ j ∈ Finset.univ.filter (fun j => (n : ℝ) < L.val j), L.mass j * (1 / 2) := by
          rw [tail, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hsum]
        unfold survival
        refine (Finset.sum_le_sum hstep).trans ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro i _ _
        exact mul_nonneg (L.mass_nonneg i)
          (pow_nonneg (L.cos_nonneg_lt_one i (hθ1 i)).1 n)
      nlinarith [hhalf, hsn, hε0]
  have hmain : L.quantile ε ≤ (L.hittingInt hθ1 hε3 : ℝ) := by
    unfold HittingLaw.quantile
    exact csInf_le ⟨0, fun y hy => hy.1⟩ ⟨by positivity, htail⟩
  simpa using hmain

end HittingLaw

end Qatlib.Papers.HittingTimes08.MainResults
