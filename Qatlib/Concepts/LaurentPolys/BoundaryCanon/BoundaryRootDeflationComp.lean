/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryRootDeflationStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

noncomputable section

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon

open Polynomial
open scoped Classical BigOperators

/-- A nonzero boundary canonical complement factors into a unit phase, its monic boundary root
factor, and a normalized factor without closed disk zeros, with the stated multiplicity and
positive profile properties. -/
theorem boundaryRootDeflation : BoundaryRootDeflation := by
  intro P Q d hc hQ Q₀ R ζ
  let q := boundaryComplementQuotient Q
  have hq : ∀ z : ℂ, ‖z‖ ≤ 1 → q.eval z ≠ 0 :=
    boundaryComplementQuotient_closed_disk P Q d hc hQ
  have hq0 : q.eval 0 ≠ 0 := hq 0 (by simp)
  have hqn : q ≠ 0 := by intro h; exact hq0 (by simp [h])
  let c : ℂ := (‖q.eval 0‖ : ℂ) / q.eval 0
  have hc0 : c * q.eval 0 = (‖q.eval 0‖ : ℂ) := div_mul_cancel₀ _ hq0
  have hcn : ‖c‖ = 1 := by
    simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hq0)
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcn]; norm_num)
  have hR : R = C c * q := rfl
  have hζ : ‖ζ‖ = 1 := by
    change ‖q.eval 0 / (‖q.eval 0‖ : ℂ)‖ = 1
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hq0)
  have hζc : ζ * c = 1 := by
    change (q.eval 0 / (‖q.eval 0‖ : ℂ)) * ((‖q.eval 0‖ : ℂ) / q.eval 0) = 1
    have hn : (‖q.eval 0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq0)
    field_simp
  have hmul : Q₀ * q = Q := boundaryComplementFactor_mul_quotient Q
  have hfactor : Q = C ζ * Q₀ * R := by
    calc
      Q = Q₀ * q := hmul.symm
      _ = C (ζ * c) * Q₀ * q := by rw [hζc, C_1, one_mul]
      _ = C ζ * Q₀ * R := by rw [hR, C_mul]; ring
  have hdegree : Q₀.natDegree + R.natDegree = Q.natDegree := by
    rw [hR, Polynomial.natDegree_C_mul hcne, ← hmul,
      Polynomial.natDegree_mul (boundaryComplementFactor_monic Q).ne_zero hqn]
  have hr0 : 0 < (R.eval 0).re := by
    rw [hR, eval_mul, eval_C, hc0, Complex.ofReal_re]
    exact norm_pos_iff.mpr hq0
  have hi0 : (R.eval 0).im = 0 := by
    rw [hR, eval_mul, eval_C, hc0, Complex.ofReal_im]
  have hRn : ∀ z : ℂ, ‖z‖ ≤ 1 → R.eval z ≠ 0 := by
    intro z hz
    rw [hR, eval_mul, eval_C]
    exact mul_ne_zero hcne (hq z hz)
  have hsupport (z : ℂ) (hz : ‖z‖ = 1) : Q₀.eval z = 0 ↔ ‖P.eval z‖ = 1 := by
    have heval : Q₀.eval z * q.eval z = Q.eval z := by
      rw [← eval_mul, hmul]
    have hzero : Q₀.eval z = 0 ↔ Q.eval z = 0 := by
      rw [← heval]
      exact (mul_eq_zero_iff_right (hq z hz.le)).symm
    rw [hzero]
    have hm := hc.2.1 z hz
    constructor
    · intro h
      rw [h, norm_zero] at hm
      nlinarith [norm_nonneg (P.eval z)]
    · intro h
      apply norm_eq_zero.mp
      rw [h] at hm
      nlinarith [norm_nonneg (Q.eval z)]
  have hres (z : ℂ) (hz : ‖z‖ = 1) :
      ‖P.eval z‖ ^ 2 + ‖Q₀.eval z‖ ^ 2 * boundaryComplementProfile Q z = 1 := by
    have hm := hc.2.1 z hz
    rw [hfactor, eval_mul, eval_mul, eval_C, norm_mul, norm_mul, hζ, one_mul,
      mul_pow] at hm
    exact hm
  have hratio (z : ℂ) (hz : ‖z‖ = 1) (h0 : Q₀.eval z ≠ 0) :
      boundaryComplementProfile Q z = (1 - ‖P.eval z‖ ^ 2) / ‖Q₀.eval z‖ ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))).2
    nlinarith [hres z hz]
  refine ⟨boundaryComplementFactor_monic Q, boundaryComplementFactor_dvd Q,
    hfactor, hζ, hdegree, hr0, hi0, hRn,
    boundaryComplementFactor_rootMultiplicity Q, hsupport, hres, hratio, ?_⟩
  have hcont : Continuous (boundaryComplementProfile Q) := R.continuous.norm.pow 2
  have hs : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hnonempty : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  obtain ⟨lo, hlo, hmin⟩ := hs.exists_isMinOn hnonempty hcont.continuousOn
  obtain ⟨hi, hhi, hmax⟩ := hs.exists_isMaxOn hnonempty hcont.continuousOn
  have hlo' : ‖lo‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hlo
  have hpositive : 0 < boundaryComplementProfile Q lo := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (hRn lo hlo'.le))
  refine ⟨boundaryComplementProfile Q lo, boundaryComplementProfile Q hi,
    hpositive, hmin hhi, ?_⟩
  intro z hz
  have hz' : z ∈ Metric.sphere (0 : ℂ) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  exact ⟨hmin hz', hmax hz'⟩

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
