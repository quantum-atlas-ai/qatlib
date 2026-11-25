/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Qatlib.Papers.KnottedLight08.NullLinking.ComplexPhaseFibers

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Determinant winding of distinct Hopf fibers

[IrvineBouwmeester2008KnottedLight], Figs. 1–2,
[DOI](https://doi.org/10.1038/nphys1056).
The complex determinant with a representative of the first fiber is a
nonvanishing meridian coordinate on its complement in the unit three-sphere.
On any distinct phase fiber, this coordinate is a nonzero constant times the
unit phase. Its logarithmic winding integral is exactly one in the positive
phase orientation.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

/-- The determinant vanishes exactly on pairs projectively proportional
to the reference pair. -/
def fiberDeterminant (p q : ℂ × ℂ) : ℂ := q.1 * p.2 - q.2 * p.1

/-- On the unit sphere, the determinant is nonzero on the complement of
the reference Hopf fiber. -/
theorem fiberDeterminant_ne_zero_iff (p q : ℂ × ℂ)
    (hq : Complex.normSq q.1 + Complex.normSq q.2 = 1) :
    fiberDeterminant p q ≠ 0 ↔ q ∉ unitHopfFiber p := by
  change _ ↔ ¬ (_ ∧ _)
  simp only [hq, true_and, fiberDeterminant]
  exact sub_ne_zero

/-- The determinant in its second argument transforms by the simultaneous
phase multiplier of the second pair. -/
theorem fiberDeterminant_phaseOrbit (p q : ℂ × ℂ) (u : ℂ) :
    fiberDeterminant p (phaseOrbit q u) = u * fiberDeterminant p q := by
  simp only [fiberDeterminant, phaseOrbit]
  ring

/-- The complementary determinant coordinate traced as the second fiber
traverses its positive phase circle. -/
noncomputable def fiberDeterminantLoop (p q : ℂ × ℂ) (θ : ℝ) : ℂ :=
  fiberDeterminant p (phaseOrbit q (Complex.exp ((θ : ℂ) * Complex.I)))

/-- The trace avoids zero for distinct Hopf fibers. -/
theorem fiberDeterminantLoop_ne_zero (p q : ℂ × ℂ)
    (hq : Complex.normSq q.1 + Complex.normSq q.2 = 1) (h : q ∉ unitHopfFiber p)
    (θ : ℝ) : fiberDeterminantLoop p q θ ≠ 0 := by
  rw [fiberDeterminantLoop, fiberDeterminant_phaseOrbit]
  exact mul_ne_zero (Complex.exp_ne_zero _) ((fiberDeterminant_ne_zero_iff p q hq).2 h)

/-- The determinant trace has unit angular velocity for distinct fibers. -/
theorem fiberDeterminantLoop_angular_velocity (p q : ℂ × ℂ)
    (hq : Complex.normSq q.1 + Complex.normSq q.2 = 1) (h : q ∉ unitHopfFiber p)
    (θ : ℝ) : (deriv (fiberDeterminantLoop p q) θ / fiberDeterminantLoop p q θ).im = 1 := by
  have hpre : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
  have hd :
      HasDerivAt (fiberDeterminantLoop p q) (Complex.I * fiberDeterminantLoop p q θ) θ := by
    have hderiv := hpre.cexp.mul_const (fiberDeterminant p q)
    have hfun : (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * fiberDeterminant p q) =
        fiberDeterminantLoop p q := by
      funext t
      exact (fiberDeterminant_phaseOrbit p q _).symm
    rw [hfun] at hderiv
    apply hderiv.congr_deriv
    rw [fiberDeterminantLoop, fiberDeterminant_phaseOrbit]
    ring
  rw [hd.deriv, mul_div_cancel_right₀ _ (fiberDeterminantLoop_ne_zero p q hq h θ)]
  exact Complex.I_im

/-- Logarithmic winding about the reference fiber, computed in the
complementary determinant coordinate. -/
noncomputable def hopfDeterminantWinding (p q : ℂ × ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (deriv (fiberDeterminantLoop p q) θ / fiberDeterminantLoop p q θ).im

/-- The positive phase circle of any distinct Hopf fiber winds once in
the meridian coordinate of the reference fiber. -/
theorem hopf_determinant_winding_eq_one (p q : ℂ × ℂ)
    (hq : Complex.normSq q.1 + Complex.normSq q.2 = 1) (h : q ∉ unitHopfFiber p) :
    hopfDeterminantWinding p q = 1 := by
  simp only [hopfDeterminantWinding, fiberDeterminantLoop_angular_velocity p q hq h,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
    inv_mul_cancel₀ Real.two_pi_pos.ne']

end Qatlib.Papers.KnottedLight08.NullLinking
