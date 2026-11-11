/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleShadows

/-!
# Finite POVMs and measurement reconstruction

Defines `FinitePOVM` using effects with nonnegative weighted Gram factorizations and proves that
the Born probabilities form `povmRecordLaw`. It also defines the linear frame map
`povmMeasurementMap`, its inverse when bijective, and the associated snapshots and real
observable statistics.

These finite-dimensional measurement constructions use the standard POVM framework of
[Watrous2018].

## Main statements

* `povmBorn_sum_one`: normalization of the Born probabilities.
* `povmSnapshot`: reconstruction snapshot from the inverse measurement map.
* `povmMeasurementMap_trace_adjoint`: symmetry of the measurement map under the trace pairing.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementStatisticsExt

open Matrix
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {O : Type} [Fintype O] {D : ℕ}

/-- A finite POVM whose effects sum to the identity and possess nonnegative weighted Gram
factorizations. -/
structure FinitePOVM (O : Type) [Fintype O] (D : ℕ) where

  effect : O → Operator D

  effect_sum : ∑ o, effect o = 1

  weight : O → ℝ

  weight_nonneg : ∀ o, 0 ≤ weight o

  factor : O → Operator D

  effect_eq_factor : ∀ o, effect o = (weight o : ℂ) • ((factor o)ᴴ * (factor o))

namespace FinitePOVM

/-- Each effect of a finite POVM is Hermitian. -/
theorem effect_isHermitian (E : FinitePOVM O D) (o : O) : (E.effect o).IsHermitian := by
  show (E.effect o)ᴴ = E.effect o
  rw [E.effect_eq_factor, Matrix.conjTranspose_smul]
  have hconj : star (E.weight o : ℂ) = (E.weight o : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hconj]
  have hF : ((E.factor o)ᴴ * (E.factor o))ᴴ = (E.factor o)ᴴ * (E.factor o) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hF]

/-- Each effect of a finite POVM is positive semidefinite. -/
theorem effect_posSemidef (E : FinitePOVM O D) (o : O) : (E.effect o).PosSemidef := by
  have hsqrt : (Real.sqrt (E.weight o) : ℂ) ^ 2 = (E.weight o : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (E.weight_nonneg o)]
  have hcc : (Real.sqrt (E.weight o) : ℂ) * (Real.sqrt (E.weight o) : ℂ)
      = (Real.sqrt (E.weight o) : ℂ) ^ 2 := by ring
  have hconj : star (Real.sqrt (E.weight o) : ℂ) = (Real.sqrt (E.weight o) : ℂ) := by
    simp [Complex.conj_ofReal]
  have key : (E.effect o) =
      ((Real.sqrt (E.weight o) : ℂ) • (E.factor o))ᴴ *
        ((Real.sqrt (E.weight o) : ℂ) • (E.factor o)) := by
    rw [E.effect_eq_factor, Matrix.conjTranspose_smul, hconj,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc, hsqrt]
  rw [key]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end FinitePOVM

/-- For positive semidefinite `ρ`, the trace of `F * ρ * Fᴴ` equals the complex embedding of its
real part. -/
theorem factor_trace_re {E : ℕ} (F ρ : Operator E) (hρ : ρ.PosSemidef) :
    Matrix.trace (F * ρ * Fᴴ) = (((Matrix.trace (F * ρ * Fᴴ)).re : ℝ) : ℂ) := by
  have hpsd : (F * ρ * Fᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hρ.conjTranspose_mul_mul_same Fᴴ
  have himag : (Matrix.trace (F * ρ * Fᴴ)).im = 0 :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
  refine Complex.ext ?_ ?_
  · rfl
  · rw [himag, Complex.ofReal_im]

/-- The Born trace equals the nonnegative weighted real trace of the factored state. -/
theorem povmBorn_trace (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o : O) :
    Matrix.trace (E.effect o * ρ)
        = ((E.weight o * (Matrix.trace ((E.factor o) * ρ * (E.factor o)ᴴ)).re : ℝ) : ℂ) ∧
      0 ≤ E.weight o * (Matrix.trace ((E.factor o) * ρ * (E.factor o)ᴴ)).re := by
  have hpsd : ((E.factor o) * ρ * (E.factor o)ᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hρ.1.conjTranspose_mul_mul_same (E.factor o)ᴴ
  have hnonneg : 0 ≤ (Matrix.trace ((E.factor o) * ρ * (E.factor o)ᴴ)).re :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
  have hF : Matrix.trace ((E.factor o)ᴴ * (E.factor o) * ρ)
      = Matrix.trace ((E.factor o) * ρ * (E.factor o)ᴴ) :=
    (Matrix.trace_mul_cycle (A := E.factor o) (B := ρ) (C := (E.factor o)ᴴ)).symm
  have htr : Matrix.trace (E.effect o * ρ)
      = (E.weight o : ℂ) * Matrix.trace ((E.factor o) * ρ * (E.factor o)ᴴ) := by
    rw [E.effect_eq_factor, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hF]
  constructor
  · rw [htr, factor_trace_re (E.factor o) ρ hρ.1, ← Complex.ofReal_mul]
    rfl
  · exact mul_nonneg (E.weight_nonneg o) hnonneg

/-- The Born trace of a finite POVM effect against a density operator is real. -/
theorem povmBorn_trace_real (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o : O) :
    Matrix.trace (E.effect o * ρ) = (((Matrix.trace (E.effect o * ρ)).re : ℝ) : ℂ) := by
  have h := povmBorn_trace E ρ hρ o
  rw [h.1, Complex.ofReal_re]

/-- The real part of each Born trace is nonnegative. -/
theorem povmBorn_nonneg (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o : O) : 0 ≤ (Matrix.trace (E.effect o * ρ)).re := by
  have h := povmBorn_trace E ρ hρ o
  rw [h.1, Complex.ofReal_re]
  exact h.2

/-- The real Born probabilities of a finite POVM sum to one on a density operator. -/
theorem povmBorn_sum_one (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : ∑ o : O, (Matrix.trace (E.effect o * ρ)).re = 1 := by
  have htr : ∑ o : O, Matrix.trace (E.effect o * ρ) = Matrix.trace ρ := by
    calc ∑ o : O, Matrix.trace (E.effect o * ρ)
        = Matrix.trace (∑ o : O, (E.effect o * ρ)) := by
            rw [Finset.sum_congr rfl fun o _ => rfl, Matrix.trace_sum]
      _ = Matrix.trace ((∑ o : O, E.effect o) * ρ) := by
            rw [Finset.sum_mul]
      _ = Matrix.trace (1 * ρ) := by rw [E.effect_sum]
      _ = Matrix.trace ρ := by rw [Matrix.one_mul]
  have hre : (∑ o : O, Matrix.trace (E.effect o * ρ)).re = 1 := by
    rw [htr, hρ.2]
    simp
  rw [← Complex.re_sum, hre]

/-- The finite outcome distribution given by the real Born traces of a POVM on a density
operator. -/
noncomputable def povmRecordLaw (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : FinDist O where
  prob o := (Matrix.trace (E.effect o * ρ)).re
  nonneg o := povmBorn_nonneg E ρ hρ o
  sum_one := povmBorn_sum_one E ρ hρ

/-- The probability of an outcome in `povmRecordLaw` equals the real part of its Born trace. -/
theorem povmRecordLaw_prob (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o : O) :
    (povmRecordLaw E ρ hρ).prob o = (Matrix.trace (E.effect o * ρ)).re := rfl

/-- The complex embedding of an outcome probability equals its Born trace. -/
theorem povmRecordLaw_prob_complex (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o : O) :
    (((povmRecordLaw E ρ hρ).prob o : ℝ) : ℂ) = Matrix.trace (E.effect o * ρ) := by
  rw [povmBorn_trace_real E ρ hρ o, povmRecordLaw_prob E ρ hρ o]

/-- For a finite distribution, the second centered moment equals the second moment minus the
square of the mean. -/
theorem FinDist.expect_centered_sq {X : Type} [Fintype X] (p : FinDist X) (f : X → ℝ) :
    p.expect (fun x => (f x - p.expect f) ^ 2)
      = p.expect (fun x => (f x) ^ 2) - (p.expect f) ^ 2 := by
  have hkey : ∀ x : X, p.prob x * (f x - p.expect f) ^ 2
      = p.prob x * (f x) ^ 2 - p.prob x * (2 * p.expect f * f x)
        + p.prob x * (p.expect f) ^ 2 := by
    intro x
    ring
  have h2 : (∑ x : X, p.prob x * (2 * p.expect f * f x))
      = 2 * p.expect f * (∑ x : X, p.prob x * f x) := by
    calc (∑ x : X, p.prob x * (2 * p.expect f * f x))
        = ∑ x : X, 2 * p.expect f * (p.prob x * f x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = 2 * p.expect f * (∑ x : X, p.prob x * f x) := by
          rw [Finset.mul_sum]
  have h3 : (∑ x : X, p.prob x * (p.expect f) ^ 2)
      = (p.expect f) ^ 2 * (∑ x : X, p.prob x) := by
    calc (∑ x : X, p.prob x * (p.expect f) ^ 2)
        = ∑ x : X, (p.expect f) ^ 2 * (p.prob x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = (p.expect f) ^ 2 * (∑ x : X, p.prob x) := by
          rw [Finset.mul_sum]
  show ∑ x : X, p.prob x * (f x - p.expect f) ^ 2 = _
  calc (∑ x : X, p.prob x * (f x - p.expect f) ^ 2)
      = ∑ x : X, (p.prob x * (f x) ^ 2 - p.prob x * (2 * p.expect f * f x)
          + p.prob x * (p.expect f) ^ 2) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hkey]
      _ = (∑ x : X, p.prob x * (f x) ^ 2) - (∑ x : X, p.prob x * (2 * p.expect f * f x))
          + (∑ x : X, p.prob x * (p.expect f) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ x : X, p.prob x * (f x) ^ 2)
          - 2 * p.expect f * (∑ x : X, p.prob x * f x)
          + (p.expect f) ^ 2 * (∑ x : X, p.prob x) := by
        rw [h2, h3]
      _ = p.expect (fun x => (f x) ^ 2) - 2 * p.expect f * p.expect f
          + (p.expect f) ^ 2 * 1 := by
        rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,
            Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, p.sum_one]
      _ = p.expect (fun x => (f x) ^ 2) - (p.expect f) ^ 2 := by ring

/-- The complex linear frame map sending `A` to the sum of `trace (E.effect o * A)` times
`E.effect o`. -/
noncomputable def povmMeasurementMap (E : FinitePOVM O D) : Operator D →ₗ[ℂ] Operator D where
  toFun A := ∑ o : O, (Matrix.trace (E.effect o * A)) • E.effect o
  map_add' A B := by
    have h : ∀ o : O,
        (Matrix.trace (E.effect o * (A + B))) • E.effect o
          = (Matrix.trace (E.effect o * A)) • E.effect o
            + (Matrix.trace (E.effect o * B)) • E.effect o := by
      intro o
      rw [Matrix.mul_add, Matrix.trace_add, add_smul]
    rw [Finset.sum_congr rfl fun o _ => h o, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [smul_smul]

/-- Expands the measurement frame map as a sum over POVM effects. -/
theorem povmMeasurementMap_apply (E : FinitePOVM O D) (A : Operator D) :
    povmMeasurementMap E A = ∑ o : O, (Matrix.trace (E.effect o * A)) • E.effect o := rfl

/-- The measurement frame map is symmetric with respect to the bilinear trace pairing. -/
theorem povmMeasurementMap_trace_adjoint (E : FinitePOVM O D) (A B : Operator D) :
    Matrix.trace (A * povmMeasurementMap E B) = Matrix.trace (povmMeasurementMap E A * B) := by
  rw [povmMeasurementMap_apply, povmMeasurementMap_apply, Matrix.mul_sum,
    Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm A (E.effect o)]
  ring

/-- The linear equivalence induced by a bijective measurement frame map. -/
noncomputable def povmMeasurementEquiv (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) : Operator D ≃ₗ[ℂ] Operator D :=
  LinearEquiv.ofBijective (povmMeasurementMap E) hM

/-- The inverse measurement frame map applied to an outcome effect. -/
noncomputable def povmSnapshot (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (o : O) : Operator D :=
  (povmMeasurementEquiv E hM).symm (E.effect o)

/-- The real trace pairing of an observable with the reconstruction snapshot of an outcome. -/
noncomputable def povmStatistic (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (A : Operator D) (o : O) : ℝ :=
  (Matrix.trace (A * povmSnapshot E hM o)).re

end MeasurementStatisticsExt
end Qatlib.Concepts.MbqcFlow.FlowDecision
