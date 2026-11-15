/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.DeflatedFourierRootFactorFormStat
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Complex Polynomial MeasureTheory Filter
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator Polynomial Topology

/-- The normalized contour integral extracting coefficient `n` equals the circle average
weighted by the negative power `n`. -/
private theorem contour_coeff_eq_circleAverage (f : ℂ → ℂ) (n : ℕ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z : ℂ in C(0, 1), z ^ (-((n + 1 : ℕ) : ℤ)) * f z) =
    Real.circleAverage (fun z => z ^ (-(n : ℤ)) * f z) 0 1 := by
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0), smul_eq_mul]
  congr 1
  apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using! hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz1]; norm_num)
  simp only [sub_zero, smul_eq_mul]
  rw [← zpow_neg_one, ← mul_assoc, ← zpow_add₀ hz0]
  congr 2
  push_cast
  ring

/-- A polynomial with no closed unit disk zeros has a holomorphic logarithm on a strictly larger
closed disk. -/
private theorem boundary_polynomial_disk_log_exists_radius (A : Polynomial ℂ)
    (ha : ∀ z : ℂ, ‖z‖ ≤ 1 → A.eval z ≠ 0) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∃ H : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → DifferentiableAt ℂ H z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → Complex.exp (H z) = A.eval z) := by
  generalize hd : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    have ha0 : A ≠ 0 := by intro h; have := ha 0 (by simp); simp [h] at this
    by_cases hdeg : A.natDegree = 0
    · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
      have hane : a ≠ 0 := by simpa using! ha 0 (by simp)
      exact ⟨2, by norm_num, fun _ => Complex.log a,
        fun _ _ => differentiableAt_const _,
        fun _ _ => by simpa using! Complex.exp_log hane⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)))
    have hr' : A.IsRoot r := by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using! hr
    obtain ⟨g, hAg⟩ := Polynomial.dvd_iff_isRoot.mpr hr'
    have hg0 : g ≠ 0 := by intro h; simp [h] at hAg; exact ha0 hAg
    have hdegree : A.natDegree = 1 + g.natDegree := by
      rw [hAg, natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C]
    have hgc : ∀ z : ℂ, ‖z‖ ≤ 1 → g.eval z ≠ 0 := by
      intro z hz hg
      apply ha z hz
      simp [hAg, hg]
    have hrnorm : 1 < ‖r‖ := lt_of_not_ge (fun h => ha r h hr')
    have hr0 : r ≠ 0 := by intro h; norm_num [h] at hrnorm
    obtain ⟨ρ₀, hρ₀, H, hHd, hHe⟩ := ih g.natDegree (by omega) g hgc rfl
    let ρ : ℝ := min ρ₀ ((1 + ‖r‖) / 2)
    have hρ1 : 1 < ρ := lt_min hρ₀ (by linarith)
    have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
    have hρ_lt_r : ρ < ‖r‖ := (min_le_right _ _).trans_lt (by linarith)
    have hslit (z : ℂ) (hz : ‖z‖ ≤ ρ) : 1 - z / r ∈ Complex.slitPlane := by
      have hh : ‖-(z / r)‖ < 1 := by
        rw [norm_neg, norm_div, div_lt_one (by positivity)]
        exact hz.trans_lt hρ_lt_r
      simpa only [sub_eq_add_neg] using! Complex.mem_slitPlane_of_norm_lt_one hh
    refine ⟨ρ, hρ1, fun z => Complex.log (-r) + Complex.log (1 - z / r) + H z, ?_, ?_⟩
    · intro z hz
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => 1 - w / r) z := by fun_prop
      exact ((differentiableAt_const _).add (hd1.clog (hslit z hz))).add (hHd z (hz.trans hρ_le))
    · intro z hz
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hr0),
        Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)), hHe z (hz.trans hρ_le), hAg,
        eval_mul, eval_sub, eval_X, eval_C]
      field_simp
      ring

set_option maxHeartbeats 800000 in

/-- The Schwarz circle average of the real part recovers a holomorphic disk function whose value
at zero is real. -/
private theorem profile_schwarz_circle_average (H : ℂ → ℂ)
    (hH : DiffContOnCl ℂ H (Metric.ball 0 1)) (hH0 : (H 0).im = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Real.circleAverage (fun u : ℂ => (u + z) / (u - z) * (H u).re) 0 1 = H z := by
  let K : ℂ → ℂ := fun u => (u + z) / (u - z)
  let C : ℂ → ℂ := fun u => u / (u - z)
  have hzs : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_eq_norm] using! hz
  have hden (u : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1) : u - z ≠ 0 := by
    intro he
    have he' : u = z := sub_eq_zero.mp he
    have hu' : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using! hu
    rw [he'] at hu'
    linarith
  have hHc : ContinuousOn H (Metric.sphere (0 : ℂ) 1) := by
    apply hH.2.mono
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall
  have hKc : ContinuousOn K (Metric.sphere (0 : ℂ) 1) := by
    dsimp [K]
    fun_prop (disch := exact hden _ ‹_›)
  have hCc : ContinuousOn C (Metric.sphere (0 : ℂ) 1) := by
    dsimp [C]
    fun_prop (disch := exact hden _ ‹_›)
  have hiH : CircleIntegrable H 0 1 := hHc.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiC : CircleIntegrable (fun u => C u * H u) 0 1 :=
    (hCc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiK : CircleIntegrable (fun u => K u * H u) 0 1 :=
    (hKc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hKrc : ContinuousOn (fun u => ((K u).re : ℂ)) (Metric.sphere (0 : ℂ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hKc)
  have hiR : CircleIntegrable (fun u => (K u).re * H u) 0 1 :=
    (hKrc.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hiS : CircleIntegrable (fun u => star (K u) * H u) 0 1 :=
    (hKc.star.mul hHc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hHabs : DiffContOnCl ℂ H (Metric.ball 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using! hH
  have hC : Real.circleAverage (fun u => C u * H u) 0 1 = H z := by
    simpa only [C, sub_zero, smul_eq_mul] using! hHabs.circleAverage_smul_div
      (by simpa only [abs_one] using! hzs)
  have hA : Real.circleAverage H 0 1 = H 0 := hHabs.circleAverage
  have hR : Real.circleAverage (fun u => (K u).re * H u) 0 1 = H z := by
    simpa [K, smul_eq_mul] using! hH.circleAverage_re_herglotzRieszKernel_smul' hzs
  have hK : Real.circleAverage (fun u => K u * H u) 0 1 = 2 * H z - H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • (C u * H u) - H u) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro u hu
        have hu' : u ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [abs_one] using! hu
        dsimp [K, C]
        change (u + z) / (u - z) * H u = 2 * (u / (u - z) * H u) - H u
        field_simp [hden u hu']
        ring
      _ = 2 * H z - H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • (C u * H u)) hiC.const_smul hiH,
          Real.circleAverage_fun_smul, hC, hA, smul_eq_mul]
  have hS : Real.circleAverage (fun u => star (K u) * H u) 0 1 = H 0 := by
    calc
      _ = Real.circleAverage (fun u => (2 : ℂ) • ((K u).re * H u) - K u * H u) 0 1 := by
        congr 1
        funext u
        simp only [smul_eq_mul]
        have hr : star (K u) = 2 * (K u).re - K u := by
          apply Complex.ext <;> simp
          ring
        rw [hr]
        ring
      _ = H 0 := by
        rw [Real.circleAverage_fun_sub (f₁ := fun u => (2 : ℂ) • ((K u).re * H u)) hiR.const_smul hiK,
          Real.circleAverage_fun_smul, hR, hK, smul_eq_mul]
        ring
  have hT : Real.circleAverage (fun u => K u * star (H u)) 0 1 = H 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hiS
    have h0 : star (H 0) = H 0 := by
      apply Complex.ext <;> simp [hH0]
    change Real.circleAverage (fun u => star (star (K u) * H u)) 0 1 =
      star (Real.circleAverage (fun u => star (K u) * H u) 0 1) at hh
    rw [hS, h0] at hh
    simpa only [star_mul, star_star, mul_comm] using! hh
  calc
    _ = Real.circleAverage (fun u => (2 : ℂ)⁻¹ • (K u * H u + K u * star (H u))) 0 1 := by
      congr 1
      funext u
      change K u * (H u).re = (2 : ℂ)⁻¹ * (K u * H u + K u * star (H u))
      have hr : ((H u).re : ℂ) = (2 : ℂ)⁻¹ * (H u + star (H u)) := by
        apply Complex.ext <;> simp
        ring
      rw [hr]
      ring
    _ = H z := by
      have hiT : CircleIntegrable (fun u => K u * star (H u)) 0 1 :=
        (hKc.mul hHc.star).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.circleAverage_fun_smul, Real.circleAverage_fun_add hiK hiT, hK, hT,
        smul_eq_mul]
      ring

/-- The positive profile logarithm series sums to its Cauchy circle average inside the unit
disk. -/
private theorem profile_positive_series_cauchy
    (Q : Polynomial ℂ)
    (hi : CircleIntegrable (fun u => (Real.log (boundaryComplementProfile Q u) : ℂ)) 0 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => profileLogCoeff Q n * z ^ n)
      (Real.circleAverage
        (fun u : ℂ => u / (u - z) * (Real.log (boundaryComplementProfile Q u) : ℂ)) 0 1) := by
  have hs := hasSum_cauchyPowerSeries_integral hi hz
  have hterm (n : ℕ) :
      profileLogCoeff Q n * z ^ n =
        cauchyPowerSeries (fun u => (Real.log (boundaryComplementProfile Q u) : ℂ)) 0 1 n (fun _ => z) := by
    rw [cauchyPowerSeries_apply, profileLogCoeff]
    simp only [smul_eq_mul, sub_zero]
    calc
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (z ^ n * ∮ u in C(0, 1), u ^ (-((n + 1 : ℕ) : ℤ)) *
            (Real.log (boundaryComplementProfile Q u) : ℂ)) := by ring
      _ = _ := by
        rw [← circleIntegral.integral_const_mul]
        congr 1
        apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
        intro u _
        simp only [zpow_neg, zpow_natCast, div_pow, pow_succ, mul_inv_rev]
        ring
  have hvalue : Real.circleAverage
      (fun u : ℂ => u / (u - z) * (Real.log (boundaryComplementProfile Q u) : ℂ)) 0 1 =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ u in C(0, 1), (u - (0 + z))⁻¹ • (Real.log (boundaryComplementProfile Q u) : ℂ) := by
    rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
    simp only [sub_zero, zero_add, smul_eq_mul]
    congr 1
    apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using! hu
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu1]; norm_num)
    simp only [div_eq_mul_inv]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  rw [hvalue]
  simpa only [← hterm] using! hs

/-- Every strictly positive Fourier coefficient of the conjugate of a holomorphic disk function
vanishes. -/
private theorem circleAverage_neg_zpow_star_eq_zero (L : ℂ → ℂ)
    (hLd : DiffContOnCl ℂ L (Metric.ball 0 1)) (n : ℕ) (hn : n ≠ 0) :
    Real.circleAverage (fun u : ℂ => u ^ (-(n : ℤ)) * star (L u)) 0 1 = 0 := by
  have hLc : ContinuousOn L (Metric.sphere (0 : ℂ) 1) := by
    apply hLd.2.mono
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall
  have hpow_c : ContinuousOn (fun u : ℂ => u ^ n) (Metric.sphere (0 : ℂ) 1) :=
    (continuous_pow n).continuousOn
  have hi : CircleIntegrable (fun u : ℂ => u ^ n * L u) 0 1 :=
    (hpow_c.mul hLc).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hcongr : Real.circleAverage (fun u : ℂ => u ^ (-(n : ℤ)) * star (L u)) 0 1 =
      Real.circleAverage (fun u : ℂ => star (u ^ n * L u)) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using! hu
    have hustar : star u = u⁻¹ := by
      symm
      apply inv_eq_of_mul_eq_one_left
      calc
        star u * u = (‖u‖ : ℂ) ^ 2 := Complex.conj_mul' u
        _ = 1 := by simp [hu1]
    (try dsimp only)
    rw [zpow_neg, zpow_natCast, star_mul, star_pow, hustar, inv_pow, mul_comm]
  rw [hcongr]
  have hcomm := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm hi
  change Real.circleAverage (fun u : ℂ => star (u ^ n * L u)) 0 1 =
    star (Real.circleAverage (fun u : ℂ => u ^ n * L u) 0 1) at hcomm
  rw [hcomm]
  have hdiff : DiffContOnCl ℂ (fun u : ℂ => u ^ n * L u) (Metric.ball 0 |(1 : ℝ)|) :=
    ⟨((differentiable_id.pow n).differentiableOn).mul (by simpa only [abs_one] using! hLd.1),
     ((continuous_pow n).continuousOn).mul (by simpa only [abs_one] using! hLd.2)⟩
  rw [hdiff.circleAverage]
  simp [zero_pow hn]

set_option maxHeartbeats 800000 in

/-- A nonzero boundary canonical complement equals its phase times its boundary root factor
times the exponential of its profile logarithm series on the closed unit disk. -/
theorem deflatedFourierRootFactorForm : DeflatedFourierRootFactorForm := by
  intro P Q d hc hQ
  (try dsimp only)
  let Q₀ := boundaryComplementFactor Q
  let R := boundaryComplementQuotient Q
  let S := boundaryComplementNormalizedQuotient Q
  let ζ := boundaryComplementQuotientPhase Q
  have hRn : ∀ z : ℂ, ‖z‖ ≤ 1 → R.eval z ≠ 0 :=
    boundaryComplementQuotient_closed_disk P Q d hc hQ
  have hR0 : R.eval 0 ≠ 0 := hRn 0 (by simp)
  have hR0_norm : (‖R.eval 0‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hR0)
  have hS0 : S.eval 0 = (‖R.eval 0‖ : ℂ) := by
    dsimp [S, boundaryComplementNormalizedQuotient, R]
    rw [Polynomial.eval_mul, Polynomial.eval_C, div_mul_cancel₀ _ hR0]
  have hSr : 0 < (S.eval 0).re := by
    rw [hS0, Complex.ofReal_re]
    exact norm_pos_iff.mpr hR0
  have hSi : (S.eval 0).im = 0 := by
    rw [hS0, Complex.ofReal_im]
  have hSn (z : ℂ) (hz : ‖z‖ ≤ 1) : S.eval z ≠ 0 := by
    dsimp [S, boundaryComplementNormalizedQuotient, R]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero (div_ne_zero hR0_norm hR0) (hRn z hz)
  obtain ⟨ρ, hρ1, H, hHd, hHe⟩ := boundary_polynomial_disk_log_exists_radius S hSn
  let c : ℂ := (Real.log (S.eval 0).re : ℝ)
  have hS0_ne : S.eval 0 ≠ 0 := hSn 0 (by simp)
  have hc_exp : Complex.exp c = S.eval 0 := by
    simp only [c, ← Complex.ofReal_exp, Real.exp_log hSr]
    apply Complex.ext <;> simp [hSi]
  let L : ℂ → ℂ := fun z => H z + c - H 0
  have hLd_at (z : ℂ) (hz : ‖z‖ ≤ ρ) : DifferentiableAt ℂ L z :=
    ((hHd z hz).add (differentiableAt_const _)).sub (differentiableAt_const _)
  have hLd : DiffContOnCl ℂ L (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using! hz
    exact (hLd_at z (hz1.trans hρ1.le)).differentiableWithinAt
  have hLe (z : ℂ) (hz : ‖z‖ ≤ ρ) : Complex.exp (L z) = S.eval z := by
    dsimp [L]
    rw [Complex.exp_sub, Complex.exp_add, hHe z hz, hc_exp, hHe 0 (by rw [norm_zero]; linarith)]
    exact mul_div_cancel_right₀ _ hS0_ne
  have hL0 : L 0 = c := by simp [L]
  have hL0im : (L 0).im = 0 := by rw [hL0]; simp [c]
  let F : ℂ → ℂ := fun u => (Real.log (boundaryComplementProfile Q u) : ℂ)
  have hFre (u : ℂ) (hu : ‖u‖ ≤ 1) :
      F u = L u + star (L u) := by
    have hl : Real.log ‖S.eval u‖ = (L u).re := by
      rw [← hLe u (hu.trans hρ1.le), Complex.norm_exp, Real.log_exp]
    dsimp [F, boundaryComplementProfile]
    rw [Real.log_pow, hl]
    apply Complex.ext <;> simp
    ring
  have hLre (u : ℂ) (hu : ‖u‖ = 1) : ((L u).re : ℂ) = F u / 2 := by
    rw [hFre u hu.le]
    apply Complex.ext <;> simp
  have hLc_sphere : ContinuousOn L (Metric.sphere 0 1) := by
    apply hLd.2.mono
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall
  have hFc : ContinuousOn F (Metric.sphere 0 1) := by
    refine (hLc_sphere.add hLc_sphere.star).congr ?_
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using! hu
    exact hFre u hu1.le
  have hiF : CircleIntegrable F 0 1 := hFc.circleIntegrable (by norm_num)
  have hid (w : ℂ) (hw : ‖w‖ < 1) : profileLogSeries Q w = L w := by
    let C : ℂ → ℂ := fun u => u / (u - w)
    have hden (u : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1) : u - w ≠ 0 := by
      intro he
      have he' : u = w := sub_eq_zero.mp he
      have hu' : ‖u‖ = 1 := by simpa using! hu
      rw [he'] at hu'
      linarith
    have hCc : ContinuousOn C (Metric.sphere (0 : ℂ) 1) := by
      dsimp [C]
      fun_prop (disch := exact hden _ ‹_›)
    have hiCF : CircleIntegrable (fun u => C u * F u) 0 1 :=
      (hCc.mul hFc).circleIntegrable (by norm_num)
    have hzero : profileLogCoeff Q 0 = Real.circleAverage F 0 1 := by
      simpa [profileLogCoeff, F] using! contour_coeff_eq_circleAverage F 0
    have hsum : (∑' n : ℕ, profileLogCoeff Q n * w ^ n) =
        Real.circleAverage (fun u => C u * F u) 0 1 :=
      (profile_positive_series_cauchy Q hiF w hw).tsum_eq
    have hsch := profile_schwarz_circle_average L hLd hL0im w hw
    calc
      profileLogSeries Q w =
          Real.circleAverage (fun u => C u * F u) 0 1 -
            Real.circleAverage F 0 1 / 2 := by
        rw [profileLogSeries, hsum, hzero]
      _ = Real.circleAverage (fun u : ℂ => (u + w) / (u - w) * (L u).re) 0 1 := by
        calc
          _ = Real.circleAverage (fun u =>
              (C u * F u) - (2 : ℂ)⁻¹ • F u) 0 1 := by
            have hsub := Real.circleAverage_fun_sub
              (f₁ := fun u => C u * F u)
              (f₂ := fun u => (2 : ℂ)⁻¹ • F u)
              hiCF hiF.const_smul
            have hmul : Real.circleAverage (fun u => (2 : ℂ)⁻¹ • F u) 0 1 =
                (2 : ℂ)⁻¹ • Real.circleAverage F 0 1 :=
              Real.circleAverage_fun_smul
            rw [hmul] at hsub
            simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using! hsub.symm
          _ = _ := by
            apply Real.circleAverage_congr_sphere
            intro u hu
            have hu1 : ‖u‖ = 1 := by simpa using! hu
            (try dsimp only)
            rw [hLre u hu1]
            dsimp [C]
            field_simp [hden u (by simpa using! hu)]
            ring
      _ = L w := hsch
  have hLc_rho : ContinuousOn L (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    have hzr : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_zero_right] using! hz
    exact (hLd_at z hzr.le).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn hLc_rho
  let M : ℝ := max ‖profileLogCoeff Q 0‖ (max 0 M₀)
  have hM_nonneg : 0 ≤ M := le_max_of_le_right (le_max_left 0 M₀)
  have hcoeff_bound (n : ℕ) : ‖profileLogCoeff Q n‖ ≤ M / ρ ^ n := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [pow_zero, div_one]
      exact le_max_left _ _
    · have hcoeff_L : profileLogCoeff Q n =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ z : ℂ in C(0, 1), z ^ (-((n + 1 : ℕ) : ℤ)) * L z := by
        rw [profileLogCoeff, contour_coeff_eq_circleAverage F n, smul_eq_mul,
          contour_coeff_eq_circleAverage L n]
        have hpow_c : ContinuousOn (fun u : ℂ => u ^ (-(n : ℤ))) (Metric.sphere (0 : ℂ) 1) := by
          have hinv_c : ContinuousOn (fun u : ℂ => (u ^ n)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
            apply ((continuous_pow n).continuousOn).inv₀
            intro u hu
            have hu1 : ‖u‖ = 1 := by simpa using! hu
            exact pow_ne_zero n (norm_ne_zero_iff.mp (by rw [hu1]; norm_num))
          simpa only [zpow_neg, zpow_natCast] using! hinv_c
        have hi1 : CircleIntegrable (fun u : ℂ => u ^ (-(n : ℤ)) * L u) 0 1 :=
          (hpow_c.mul hLc_sphere).circleIntegrable (by norm_num)
        have hi2 : CircleIntegrable (fun u : ℂ => u ^ (-(n : ℤ)) * star (L u)) 0 1 :=
          (hpow_c.mul hLc_sphere.star).circleIntegrable (by norm_num)
        have hcongr : Real.circleAverage (fun z => z ^ (-(n : ℤ)) * F z) 0 1 =
            Real.circleAverage (fun z => z ^ (-(n : ℤ)) * L z + z ^ (-(n : ℤ)) * star (L z)) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          have hz1 : ‖z‖ = 1 := by simpa using! hz
          (try dsimp only)
          rw [hFre z hz1.le, mul_add]
        rw [hcongr, Real.circleAverage_fun_add hi1 hi2,
          circleAverage_neg_zpow_star_eq_zero L hLd n hn0, add_zero]
      rw [hcoeff_L]
      let f : ℂ → ℂ := fun z => z ^ (-((n + 1 : ℕ) : ℤ)) * L z
      have hdf (z : ℂ) (hz1 : 1 ≤ ‖z‖) (hzr : ‖z‖ ≤ ρ) : DifferentiableAt ℂ f z := by
        have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
        have hdp : DifferentiableAt ℂ (fun u : ℂ => u ^ (-((n + 1 : ℕ) : ℤ))) z := by
          simpa only [zpow_neg, zpow_natCast] using!
            (differentiableAt_id.pow (n + 1)).inv (pow_ne_zero _ hz0)
        exact hdp.mul (hLd_at z hzr)
      have hcf : ContinuousOn f (Metric.closedBall 0 ρ \ Metric.ball 0 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ ρ ∧ 1 ≤ ‖z‖ := by
          simpa only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
              not_lt] using! hz
        exact (hdf z hz'.2 hz'.1).continuousAt.continuousWithinAt
      have he : (∮ z in C(0, ρ), f z) = ∮ z in C(0, 1), f z := by
        apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
          (by norm_num : (0 : ℝ) < 1) hρ1.le Set.countable_empty hcf
        intro z hz
        have hz' : ‖z‖ < ρ ∧ 1 < ‖z‖ := by
          simpa only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
            Set.mem_empty_iff_false, not_false_eq_true, and_true, not_le] using! hz
        exact hdf z hz'.2.le hz'.1.le
      change ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), f z‖ ≤ M / ρ ^ n
      rw [← he]
      have hρ0 : 0 < ρ := by linarith
      have hb : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖f z‖ ≤ (ρ ^ (n + 1))⁻¹ * M := by
        intro z hz
        have hzr : ‖z‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using! hz
        dsimp only [f]
        rw [norm_mul, norm_zpow, hzr, zpow_neg, zpow_natCast]
        have hLM : ‖L z‖ ≤ M := (hM₀ z hz).trans (le_max_of_le_right (le_max_right 0 M₀))
        exact mul_le_mul_of_nonneg_left hLM (by positivity)
      apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0.le hb).trans
      have hpow : ρ ^ n ≠ 0 := pow_ne_zero _ hρ0.ne'
      rw [pow_succ]
      field_simp
      exact le_rfl
  have hρ0 : 0 < ρ := by linarith
  have hgeom := (summable_geometric_of_lt_one (inv_nonneg.mpr hρ0.le)
    ((inv_lt_one₀ hρ0).mpr hρ1)).mul_left M
  have hseries : ContinuousOn (profileLogSeries Q) (Metric.closedBall 0 1) := by
    apply ContinuousOn.sub ?_ continuousOn_const
    apply continuousOn_tsum (fun _ => by fun_prop) hgeom
    intro n w hw
    have hwn : ‖w‖ ≤ 1 := by simpa using! hw
    have hpow : ‖w ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hwn
    calc
      ‖profileLogCoeff Q n * w ^ n‖ ≤ ‖profileLogCoeff Q n‖ := by
        rw [norm_mul]
        simpa using! mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ ≤ M / ρ ^ n := hcoeff_bound n
      _ = M * (ρ⁻¹) ^ n := by rw [div_eq_mul_inv, inv_pow]
  have heq : Set.EqOn (fun w => Complex.exp (profileLogSeries Q w))
      (fun w => S.eval w) (Metric.ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa using! hw
    (try dsimp only)
    rw [hid w hwn]
    exact hLe w (hwn.le.trans hρ1.le)
  have hclosed := heq.of_subset_closure hseries.cexp (by fun_prop)
    Metric.ball_subset_closedBall (by rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)])
  intro z hz
  have hexp_S : Complex.exp (profileLogSeries Q z) = S.eval z :=
    hclosed (by simpa using! hz)
  rw [hexp_S]
  have hfac := boundaryComplementFactor_mul_quotient Q
  have hQ_eval : Q.eval z = Q₀.eval z * R.eval z := by
    dsimp [Q₀, R]
    rw [← Polynomial.eval_mul, hfac]
  have hS_eval : S.eval z = ((‖R.eval 0‖ : ℂ) / R.eval 0) * R.eval z := by
    dsimp [S, boundaryComplementNormalizedQuotient, R]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hQ_eval, hS_eval]
  dsimp [ζ, boundaryComplementQuotientPhase, R]
  calc
    Q₀.eval z * R.eval z =
        (R.eval 0 / (‖R.eval 0‖ : ℂ) * ((‖R.eval 0‖ : ℂ) / R.eval 0)) * (Q₀.eval z * R.eval z) := by
      rw [div_mul_div_cancel₀ hR0_norm, div_self hR0, one_mul]
    _ = R.eval 0 / (‖R.eval 0‖ : ℂ) * Q₀.eval z * (((‖R.eval 0‖ : ℂ) / R.eval 0) * R.eval z) := by
      ring

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
