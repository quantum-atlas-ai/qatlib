/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceFourierCoefficient
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonBounds
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierMean
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonTruncation

set_option backward.isDefEq.respectTransparency false

/-!
# Connection Poisson

Torus Fourier constructions for Effective Gauge.
Defines `normalizedConnectionPoisson`.
Proves `normalizedConnectionPoisson_mean_zero`, `normalizedConnectionPoisson_spec`, `normalizedConnectionPoisson_c6_decay`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Analytic Poisson phase of the same physical connection, normalized
 exactly as C(u)=L*A(Lu). This definition makes no finite-program claim. -/
def normalizedConnectionPoisson (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : SpatialPoint → ℝ :=
  unitRealPoisson (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp)

/-- Original `normalizedConnectionPoisson_mean_zero` guarantee for the `ConnectionPoisson` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionPoisson_mean_zero (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) :
    (∫ u : Fin 3 → ℝ in Set.Icc 0 1, normalizedConnectionPoisson q hq hp (WithLp.toLp 2 u))=0 :=
  unitRealPoisson_mean_zero (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp)

/-- Original `normalizedConnectionPoisson_spec` guarantee for the `ConnectionPoisson` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionPoisson_spec (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) :
    ContDiff ℝ ∞ (normalizedConnectionPoisson q hq hp) ∧
      IsUnitPeriodicField (normalizedConnectionPoisson q hq hp) ∧
      ∀ x, (∑ j : Fin 3, spatialWordPartial (normalizedConnectionPoisson q hq hp) [j,j] x)=
        -∑ j : Fin 3, spatialWordPartial (normalizedConnectionReal q j) [j] x := by
  refine ⟨unitRealPoisson_contDiff _ _ _,unitRealPoisson_periodic _ _ _,?_⟩
  intro x
  have h := unitRealPoisson_equation (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp) x
  have heq (j : Fin 3) : (fun y => Complex.reCLM (normalizedConnectionComplex q j y))=
      normalizedConnectionReal q j := rfl
  simpa only [normalizedConnectionPoisson,heq] using h

/-- Original `normalizedConnectionPoisson_c6_decay` guarantee for the `ConnectionPoisson` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionPoisson_c6_decay (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ M)
    (k : SpatialFrequency) (hk : k≠0) :
    ‖unitPoissonCoefficient (normalizedConnectionFourierCoefficient q hq hp) k‖ ≤
      3*M/(physicalPeriod^7*(frequencyRadius k : ℝ)^7) := by
  apply unitPoissonCoefficient_sixthOrder_decay (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp) M _ k hk
  intro j i x hx
  change ‖spatialWordPartial (fun y => Complex.ofRealCLM (normalizedConnectionReal q j y))
    (List.replicate 6 i) x‖ ≤ M
  rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
    (contDiff_normalizedConnectionReal q hq j)]
  change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real]
  exact hb j i x hx

/-- Original `normalizedConnectionPoisson_word_bound` guarantee for the `ConnectionPoisson` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionPoisson_word_bound (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ M)
    (w : List (Fin 3)) (hw : w.length≤2) (x : SpatialPoint) :
    ‖spatialWordPartial (normalizedConnectionPoisson q hq hp) w x‖ ≤ 156*M := by
  apply unitRealPoisson_word_bound (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp) M _ w hw x
  intro j i y hy
  change ‖spatialWordPartial (fun z => Complex.ofRealCLM (normalizedConnectionReal q j z))
    (List.replicate 6 i) y‖ ≤ M
  rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
    (contDiff_normalizedConnectionReal q hq j)]
  change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) y : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real]
  exact hb j i y hy

/-- Exact Fourier truncation of the same source connection. Numerical
 coefficient and trig errors remain separate obligations. -/
theorem normalizedConnectionPoisson_truncation_bound (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ M)
    (N : ℕ) (hN : 0<N) (x : SpatialPoint) :
    ‖normalizedConnectionPoisson q hq hp x-Complex.reCLM
      (unitFourierTruncation (unitPoissonCoefficient (normalizedConnectionFourierCoefficient q hq hp)) N x)‖ ≤
      156*M/(N : ℝ)^3 := by
  apply unitRealPoisson_truncation_bound (normalizedConnectionComplex q)
    (contDiff_normalizedConnectionComplex q hq) (unitPeriodic_normalizedConnectionComplex q hq hp) M _ N hN x
  intro j i y hy
  change ‖spatialWordPartial (fun z => Complex.ofRealCLM (normalizedConnectionReal q j z))
    (List.replicate 6 i) y‖ ≤ M
  rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
    (contDiff_normalizedConnectionReal q hq j)]
  change ‖((spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) y : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real]
  exact hb j i y hy

end Qatlib.Concepts.EffectiveGauge.TorusFourier
