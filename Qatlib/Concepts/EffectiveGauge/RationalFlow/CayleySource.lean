/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleyError
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.MixedTime

/-!
# Integer Cayley execution approximates the constructed source line

The exact endpoint below is the existing sourceLiftExtension, with one fixed
initial chart point and physical endpoint. It does not depend on D or p.
The callback accuracy and regularity contracts are stated explicitly.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of normalized Source Line in the Rational Flow construction. -/
def normalizedSourceLine (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (x t : ℝ) : ℍ :=
  sourceLiftExtension v hv q₀ h₀ (p,x*t)

/-- Definition of normalized Source Generator in the Rational Flow construction. -/
def normalizedSourceGenerator (v : SpatialPoint → SpatialPoint) (p : TransversePoint) (x t : ℝ) : ℍ :=
  x • sourceHorizontalQuaternion v (sourcePosition (p,x*t))

/-- Original `normalizedTime_maps` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
private theorem normalizedTime_maps (x : ℝ) (hx : 0 ≤ x ∧ x ≤ physicalPeriod) :
    MapsTo (fun t : ℝ => x*t) (Icc 0 1) (Icc 0 physicalPeriod) := by
  intro t ht
  exact ⟨mul_nonneg hx.1 ht.1,(mul_le_mul_of_nonneg_left ht.2 hx.1).trans (by simpa using hx.2)⟩

/-- Original `normalizedSourceLine_initial` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
theorem normalizedSourceLine_initial (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (x : ℝ) :
    normalizedSourceLine v hv q₀ h₀ p x 0=q₀ := by
  change sourceLiftExtension v hv q₀ h₀ (p,x*0)=q₀
  rw [mul_zero]
  change sourceLiftExtension v hv q₀ h₀ (p,(transportStart : TransportTime))=q₀
  rw [sourceLiftExtension_eq v hv hu q₀ h₀ p transportStart]
  exact pathTransport_start q₀ h₀ _

/-- Original `normalizedSourceLine_unit` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
theorem normalizedSourceLine_unit (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (x t : ℝ) :
    ‖normalizedSourceLine v hv q₀ h₀ p x t‖=1 := pathTransport_unit q₀ h₀ _ transportFinish

/-- Original `continuous_normalizedSourceGenerator` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
theorem continuous_normalizedSourceGenerator (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (p : TransversePoint) (x : ℝ) : Continuous (normalizedSourceGenerator v p x) :=
  ((contDiff_sourceHorizontalQuaternion hv).continuous.comp
    (sourcePosition.continuous.comp (continuous_const.prodMk (continuous_const.mul continuous_id)))).const_smul x

/-- Original `normalizedSourceGenerator_re` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
theorem normalizedSourceGenerator_re (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (p : TransversePoint) (x t : ℝ) : (normalizedSourceGenerator v p x t).re=0 := by
  have h := horizontal_re _ _ (source_tangent (sourceCurve_hasDerivAt hv p) (fun _ => rfl)
    (fun u => (spinOfVector_norm (v (sourcePosition (p,u)))).trans (hu _)) (x*t))
  change x • (sourceHorizontalQuaternion v (sourcePosition (p,x*t))).re=0
  rw [show (sourceHorizontalQuaternion v (sourcePosition (p,x*t))).re=0 from h]
  exact smul_zero x

/-- Original `normalizedSourceLine_hasDerivWithinAt` guarantee for the `CayleySource` construction; the complete source hypotheses are retained. -/
theorem normalizedSourceLine_hasDerivWithinAt (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ physicalPeriod) (t : ℝ) (ht : t ∈ Icc 0 1) :
    HasDerivWithinAt (normalizedSourceLine v hv q₀ h₀ p x)
      (normalizedSourceLine v hv q₀ h₀ p x t*normalizedSourceGenerator v p x t) (Icc 0 1) t := by
  have hxder : HasDerivAt (fun u : ℝ => x*u) x t := by simpa using (hasDerivAt_id t).const_mul x
  have hd := ((contDiff_sourceLiftExtension v hv q₀ h₀).differentiable (by simp) (p,x*t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t p).prodMk hxder)
  have hvec : (0,x)=(x : ℝ) • ((0,1) : TransversePoint × ℝ) := by simp
  have he : fderiv ℝ (sourceLiftExtension v hv q₀ h₀) (p,x*t) (0,x) =
      normalizedSourceLine v hv q₀ h₀ p x t*normalizedSourceGenerator v p x t := by
    rw [hvec,map_smul,sourceLiftExtension_timeDerivative v hv hu q₀ h₀ p (x*t) (normalizedTime_maps x hx ht)]
    exact (mul_smul_comm _ _ _).symm
  rw [he] at hd
  exact hd.hasDerivWithinAt

/-- Actual rational query labels and decoded integer execution, with a target
that is constructed from the same spin and fixed chart point at every precision. -/
theorem cayleySourceLine_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ physicalPeriod) (D b : ℕ) (hD : 0<D)
    (oracle : ℚ × ℕ → Fin 3 → ℤ) (K M : ℝ)
    (hK : ∀ t ∈ Icc 0 1, ‖normalizedSourceGenerator v p x t‖ ≤ K)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      ‖normalizedSourceGenerator v p x t-normalizedSourceGenerator v p x s‖ ≤ M*|t-s|)
    (horacle : ∀ j < D, ‖dyadicCoefficient b (oracle ((j : ℚ)/(D : ℚ),b))-
      normalizedSourceGenerator v p x ((j : ℝ)/D)‖ ≤ (2^b : ℝ)⁻¹)
    (initial : ℍ) (delta0 : ℝ) (hinitial : ‖initial-q₀‖ ≤ delta0) :
    ‖initial*decodeCayleyState (cayleyOracleExecution D b oracle)-sourceLiftExtension v hv q₀ h₀ (p,x)‖ ≤
      delta0+M/(2*(D : ℝ))+(2^b : ℝ)⁻¹+(K+(2^b : ℝ)⁻¹)^3/(12*(D : ℝ)^2) := by
  have hi : ‖initial-normalizedSourceLine v hv q₀ h₀ p x 0‖ ≤ delta0 := by
    rw [normalizedSourceLine_initial v hv hu q₀ h₀ p x]
    exact hinitial
  have h := cayleyOracleExecution_error D b hD oracle
    (continuous_normalizedSourceGenerator v hv p x).continuousOn
    (fun t _ => normalizedSourceGenerator_re v hv hu p x t)
    (fun t ht => normalizedSourceLine_hasDerivWithinAt v hv hu q₀ h₀ p x hx t ht)
    (fun t _ => normalizedSourceLine_unit v hv q₀ h₀ p x t) K M hK hlip horacle initial delta0 hi
  simpa only [normalizedSourceLine,mul_one] using h

end Qatlib.Concepts.EffectiveGauge.RationalFlow
