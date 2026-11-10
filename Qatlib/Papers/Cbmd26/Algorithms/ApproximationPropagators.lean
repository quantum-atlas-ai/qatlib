/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationEntire
import Qatlib.Foundations.CbmdAnalysis.Core.PropagatorGrowth
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Complex Polynomial Metric Set

theorem wave_scalar_real (x t : ℝ) :
    ((_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator (x : ℂ) (t : ℂ)).re : ℂ) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator (x : ℂ) (t : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator, smul_eq_mul, Complex.conj_tsum,
    map_mul, map_inv₀, map_natCast, map_pow, map_neg, Complex.conj_ofReal]

theorem bessel_scalar_real (x t : ℝ) :
    ((_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator (x : ℂ) (t : ℂ)).re : ℂ) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator (x : ℂ) (t : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator, smul_eq_mul, Complex.conj_tsum,
    map_mul, map_inv₀, map_natCast, map_pow, map_neg, map_div₀, map_ofNat, Complex.conj_ofReal]

theorem wave_scalar_circle_bound (b t : ℝ) (hb : 0 ≤ b)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 2) :
    ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator ((b : ℂ) * z) (t : ℂ)‖ ≤
      Real.exp (|t| * Real.sqrt (2 * b)) := by
  have hn : ‖z‖ = 2 := by simpa using mem_sphere_iff_norm.mp hz
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb, hn, mul_comm b 2]
    using _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator_norm_le_exp ((b : ℂ) * z) (t : ℂ)

theorem bessel_scalar_circle_bound (b t : ℝ) (hb : 0 ≤ b)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 2) :
    ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator ((b : ℂ) * z) (t : ℂ)‖ ≤
      Real.exp (|t| * Real.sqrt (2 * b)) := by
  have hn : ‖z‖ = 2 := by simpa using mem_sphere_iff_norm.mp hz
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb, hn, mul_comm b 2]
    using _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator_norm_le_exp ((b : ℂ) * z) (t : ℂ)

theorem wave_bounded_polynomial_exists (b t g ε : ℝ)
    (hb : 0 ≤ b) (hg : 0 < g) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.natDegree ≤ dyadicOrder (ε / (4 * Real.exp (|t| * Real.sqrt (2 * b)))) *
        (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1,
        ‖P.eval (x : ℂ) - _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator ((b * x : ℝ) : ℂ) (t : ℂ)‖ ≤ ε) := by
  simp only [Complex.ofReal_mul]
  apply bounded_real_holomorphic_complex_polynomial_exists
    (fun z => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator ((b : ℂ) * z) (t : ℂ)) g
    (Real.exp (|t| * Real.sqrt (2 * b))) ε hg
    (Real.one_le_exp (by positivity)) hε
  · intro z _
    have h :=
        (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
    simpa only [zero_add, smul_eq_mul, mul_comm,
        _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator] using
        h.differentiableWithinAt
  · exact wave_scalar_circle_bound b t hb
  · intro x hx
    simpa only [← Complex.ofReal_mul] using
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator_scalar_nonneg_norm_le_one (b * x) t (mul_nonneg hb hx.1)
  · intro x _
    simpa only [← Complex.ofReal_mul] using wave_scalar_real (b * x) t

theorem bessel_bounded_polynomial_exists (b t g ε : ℝ)
    (hb : 0 ≤ b) (hg : 0 < g) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.natDegree ≤ dyadicOrder (ε / (4 * Real.exp (|t| * Real.sqrt (2 * b)))) *
        (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1,
        ‖P.eval (x : ℂ) - _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator ((b * x : ℝ) : ℂ) (t : ℂ)‖ ≤ ε) := by
  simp only [Complex.ofReal_mul]
  apply bounded_real_holomorphic_complex_polynomial_exists
    (fun z => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator ((b : ℂ) * z) (t : ℂ)) g
    (Real.exp (|t| * Real.sqrt (2 * b))) ε hg
    (Real.one_le_exp (by positivity)) hε
  · intro z _
    have h :=
        (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.bessel_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
    simpa only [zero_add, smul_eq_mul, mul_comm,
        _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator] using
        h.differentiableWithinAt
  · exact bessel_scalar_circle_bound b t hb
  · intro x hx
    simpa only [← Complex.ofReal_mul] using
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator_scalar_nonneg_norm_le_one (b * x) t (mul_nonneg hb hx.1)
  · intro x _
    simpa only [← Complex.ofReal_mul] using bessel_scalar_real (b * x) t

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
