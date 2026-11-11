/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.GaussianPrimitives
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskInclusion

set_option backward.isDefEq.respectTransparency false

/-! Exact source cross-multiplication, then the established root-disk theorem.
Evaluation identities and actual polynomial degree remain explicit obligations;
this does not yet claim that a decoded Python checker establishes them. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- The actual integer comparison, before dividing either Horner value. -/
def rootIntegerCoordinateBound (n : ℕ) (v w : GaussianIntegerFraction) (r : ℚ) : Prop :=
  (n : ℤ)*(|v.numerator.1|+|v.numerator.2|)*(w.denominator : ℤ)*(r.den : ℤ)≤
    r.num*max |w.numerator.1| |w.numerator.2| *(v.denominator : ℤ)

/-- The finite construction in `NativeRootIntegerCoordinate` satisfies `rootIntegerValue_l1` under the displayed hypotheses. -/
theorem rootIntegerValue_l1 (v : GaussianIntegerFraction) (hD : 0<v.denominator) :
    |(gaussianPointValue v).re|+|(gaussianPointValue v).im|=
      (|(v.numerator.1 : ℝ)|+|(v.numerator.2 : ℝ)|)/(v.denominator : ℝ) := by
  have hp : (0 : ℝ)<v.denominator := by exact_mod_cast hD
  simp [gaussianPointValue,abs_div,abs_of_pos hp,add_div]

/-- The finite construction in `NativeRootIntegerCoordinate` satisfies `rootIntegerValue_linf` under the displayed hypotheses. -/
theorem rootIntegerValue_linf (v : GaussianIntegerFraction) (hD : 0<v.denominator) :
    max |(gaussianPointValue v).re| |(gaussianPointValue v).im|=
      max |(v.numerator.1 : ℝ)| |(v.numerator.2 : ℝ)|/(v.denominator : ℝ) := by
  have hp : (0 : ℝ)<v.denominator := by exact_mod_cast hD
  simpa [gaussianPointValue,abs_div,abs_of_pos hp] using
    max_div_div_right hp.le |(v.numerator.1 : ℝ)| |(v.numerator.2 : ℝ)|

/-- No positive derivative premise is needed for this transport. In the
nonconstant root consumer, a zero derivative numerator forces the value
numerator to vanish through the integer comparison. -/
theorem rootIntegerCoordinateBound_sound (n : ℕ) (v w : GaussianIntegerFraction) (r : ℚ)
    (hE : 0<v.denominator) (hF : 0<w.denominator)
    (h : rootIntegerCoordinateBound n v w r) :
    (n : ℝ)*(|(gaussianPointValue v).re|+|(gaussianPointValue v).im|)≤
      (r : ℝ)*max |(gaussianPointValue w).re| |(gaussianPointValue w).im| := by
  have he : (0 : ℝ)<v.denominator := by exact_mod_cast hE
  have hf : (0 : ℝ)<w.denominator := by exact_mod_cast hF
  have hd : (0 : ℝ)<r.den := by exact_mod_cast r.den_pos
  have hr : (r.num : ℝ)/(r.den : ℝ)=(r : ℝ) := by exact_mod_cast r.num_div_den
  have hraw : (n : ℝ)*(|(v.numerator.1 : ℝ)|+|(v.numerator.2 : ℝ)|)*
      (w.denominator : ℝ)*(r.den : ℝ)≤
      (r.num : ℝ)*max |(w.numerator.1 : ℝ)| |(w.numerator.2 : ℝ)| *(v.denominator : ℝ) := by
    dsimp only [rootIntegerCoordinateBound] at h
    exact_mod_cast h
  rw [rootIntegerValue_l1 v hE,rootIntegerValue_linf w hF,← hr]
  calc
    _ = ((n : ℝ)*(|(v.numerator.1 : ℝ)|+|(v.numerator.2 : ℝ)|))/(v.denominator : ℝ) := by ring
    _ ≤ ((r.num : ℝ)*max |(w.numerator.1 : ℝ)| |(w.numerator.2 : ℝ)|)/
        ((r.den : ℝ)*(w.denominator : ℝ)) := by
      apply (div_le_div_iff₀ he (mul_pos hd hf)).mpr
      nlinarith [hraw]
    _ = _ := by ring

/-- Arithmetic transport to the existing mathematical root theorem. The two
value identities must still be derived from the SAME actual coefficient data. -/
theorem polynomial_root_disk_of_integer_coordinate_test (f : Polynomial ℂ)
    (hf : 0<f.natDegree) (c : ℂ) (r : ℚ) (hr : 0<r)
    (v w : GaussianIntegerFraction) (hE : 0<v.denominator) (hF : 0<w.denominator)
    (heval : gaussianPointValue v=f.eval c)
    (hprime : gaussianPointValue w=f.derivative.eval c)
    (htest : rootIntegerCoordinateBound f.natDegree v w r) :
    ∃ z : ℂ, f.eval z=0 ∧ ‖z-c‖≤(r : ℝ) := by
  apply polynomial_root_disk_of_coordinate_test f hf c r (by exact_mod_cast hr)
  rw [← heval,← hprime]
  exact rootIntegerCoordinateBound_sound f.natDegree v w r hE hF htest

/-- Exact-zero shortcut does not evaluate or assume a nonzero derivative. -/
theorem polynomial_root_disk_of_integer_zero (f : Polynomial ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (v : GaussianIntegerFraction) (hz : v.numerator=(0,0))
    (heval : gaussianPointValue v=f.eval c) :
    ∃ z : ℂ, f.eval z=0 ∧ ‖z-c‖≤r := by
  have hc : f.eval c=0 := by rw [← heval]; simp [gaussianPointValue,hz]
  exact ⟨c,hc,by simpa using hr⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
