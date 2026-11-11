/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientQuadrature

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficient Sampling

Rational Flow constructions for Effective Gauge.
Defines `sampledFourierCoefficientGrid`.
Proves `sampledFourierCoefficientGrid_error`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of sampled Fourier Coefficient Grid in the Rational Flow construction. -/
def sampledFourierCoefficientGrid (M : ℕ) (samples modes : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  complexGridAverage M (fun a b c => modes a b c*samples a b c)

/-- The approximation hypotheses concern only executed node values. The
Fourier coefficient is still the true integral of the original function. -/
theorem sampledFourierCoefficientGrid_error (M : ℕ) (hM : 0<M) (f : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f)
    (k : SpatialFrequency) (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (C0 C1 : ℝ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hb0 : ∀ x, InUnitCube x → ‖f x‖ ≤ C0)
    (hb1 : ∀ x, InUnitCube x → ∀ i, ‖spatialWordPartial f [i] x‖ ≤ C1)
    (samples modes : ℕ → ℕ → ℕ → ℂ) (s d : ℝ)
    (hs : ∀ a, a<M → ∀ b, b<M → ∀ c, c<M →
      ‖samples a b c-f (meanTensorSpatial ((a : ℝ)/(M : ℝ),(b : ℝ)/(M : ℝ),(c : ℝ)/(M : ℝ)))‖ ≤ s)
    (hd : ∀ a, a<M → ∀ b, b<M → ∀ c, c<M →
      ‖modes a b c-unitFourierMode (-k)
        (meanTensorSpatial ((a : ℝ)/(M : ℝ),(b : ℝ)/(M : ℝ),(c : ℝ)/(M : ℝ)))‖ ≤ d) :
    ‖unitFourierCoefficient f hf.continuous hp k-sampledFourierCoefficientGrid M samples modes‖ ≤
      3*(C1+7*(N : ℝ)*C0)/(M : ℝ)+(s+(C0+s)*d) := by
  let exactNode : ℕ → ℕ → ℕ → ℂ := fun a b c =>
    let u := meanTensorSpatial ((a : ℝ)/(M : ℝ),(b : ℝ)/(M : ℝ),(c : ℝ)/(M : ℝ))
    unitFourierMode (-k) u*f u
  have hprod (a : ℕ) (ha : a<M) (b : ℕ) (hb : b<M) (c : ℕ) (hc : c<M) :
      ‖modes a b c*samples a b c-exactNode a b c‖ ≤ s+(C0+s)*d := by
    let u := meanTensorSpatial ((a : ℝ)/(M : ℝ),(b : ℝ)/(M : ℝ),(c : ℝ)/(M : ℝ))
    have hu : InUnitCube u := meanTensorSpatial_inCube _
      ⟨meanLeftNode_mem M hM a ha,meanLeftNode_mem M hM b hb,meanLeftNode_mem M hM c hc⟩
    exact complexProduct_sample_mode_error (unitFourierMode (-k) u) (modes a b c) (f u)
      (samples a b c) C0 s d (unitFourierMode_norm _ _) (hb0 u hu) (hs a ha b hb c hc) (hd a ha b hb c hc)
  have hgrid := complexGridAverage_sub_bound M hM (fun a b c => modes a b c*samples a b c)
    exactNode (s+(C0+s)*d) hprod
  have hquad := unitFourierCoefficient_grid_error M hM f hf hp k N hk C0 C1 hC0 hC1 hb0 hb1
  have htri := dist_triangle (unitFourierCoefficient f hf.continuous hp k)
    (exactFourierCoefficientGrid f k M) (sampledFourierCoefficientGrid M samples modes)
  simp only [dist_eq_norm] at htri
  have hrev : ‖exactFourierCoefficientGrid f k M-sampledFourierCoefficientGrid M samples modes‖ ≤
      s+(C0+s)*d := by
    change ‖complexGridAverage M exactNode-complexGridAverage M (fun a b c => modes a b c*samples a b c)‖ ≤ _
    rw [norm_sub_rev]
    exact hgrid
  exact htri.trans (add_le_add hquad hrev)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
