/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.FinitePoissonPlan

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Spectral Plan

Rational Flow constructions for Effective Gauge.
Defines `finiteGaugeOutputCutoff`, `finiteGaugeCoefficientAccuracy`, `finiteGaugeCoefficientMesh`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of finite Gauge Output Cutoff in the Rational Flow construction. -/
def finiteGaugeOutputCutoff (M3 tolerance : ℚ) : ℕ := max 1 (Nat.ceil (16*|M3|/tolerance))

/-- Definition of finite Gauge Coefficient Accuracy in the Rational Flow construction. -/
def finiteGaugeCoefficientAccuracy (N : ℕ) (tolerance : ℚ) : ℚ :=
  tolerance/(512*(finitePoissonFrequencyCount N : ℚ)*((N : ℚ)+1))

/-- Definition of finite Gauge Coefficient Mesh in the Rational Flow construction. -/
def finiteGaugeCoefficientMesh (P1 : ℚ) (N : ℕ) (accuracy : ℚ) : ℕ :=
  max 1 (Nat.ceil (12*(P1+7*(N : ℚ))/accuracy))

/-- Definition of finite Gauge Sample Accuracy in the Rational Flow construction. -/
def finiteGaugeSampleAccuracy (accuracy : ℚ) : ℚ := accuracy/4

/-- Definition of finite Gauge Mode Accuracy in the Rational Flow construction. -/
def finiteGaugeModeAccuracy (accuracy : ℚ) : ℚ := accuracy/(4*(1+finiteGaugeSampleAccuracy accuracy))

/-- Definition of finite Gauge Mode Period Accuracy in the Rational Flow construction. -/
def finiteGaugeModePeriodAccuracy (N : ℕ) (accuracy : ℚ) : ℚ :=
  finiteGaugeModeAccuracy accuracy/(12*((N : ℚ)+1))

end Qatlib.Concepts.EffectiveGauge.RationalFlow
