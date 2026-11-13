/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Contractive matrix evolution and Duhamel bounds

The evolution `evolution A t` is the matrix exponential `exp (-t • A)`. Positivity of the
Hermitian part of the generator gives contraction and exponential decay estimates; the Duhamel
identity then bounds perturbations using the integrated damping factor `damping`. For
background, see [ReedSimon1980I].

## Main statements

* `evolution_sub_eq_integral`: Duhamel formula for two constant generators.
* `norm_evolution_sub_le_damping`: a perturbation bound with exponential damping.

## References

* [Reed and Simon, 1980][ReedSimon1980I]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix evolution `exp ((-t) • A)` for a constant generator `A`. -/
def evolution (A : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-t) • A)

/-- The constant-generator evolution at time zero is the identity matrix. -/
@[simp] theorem evolution_zero (A : Matrix I I ℂ) : Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A 0 = 1 := by
  simp [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution]

/-- The exponential evolution equals the time-ordered evolution of the constant generator
starting at zero. -/
theorem evolution_eq_ordered (A : Matrix I I ℂ) (t : ℝ) :
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t = Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution (fun _ => A) 0 t := by
  have hd (u : ℝ) : HasDerivAt (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A) (-(A * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A u)) u := by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (-u)).scomp u
      (hasDerivAt_id u).neg
    simpa [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution] using! h
  exact congrFun (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_matrix_ode_unique (fun _ => A) continuous_const
    (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A) (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution (fun _ => A) 0) 0 (by simp)
    hd (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_hasDerivAt _ continuous_const 0)) t

/-- If `A + Aᴴ` is positive semidefinite, the evolution has norm at most one at every
nonnegative time. -/
theorem norm_evolution_le_one (A : Matrix I I ℂ)
    (hA : (A + Aᴴ).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t‖ ≤ 1 := by
  rw [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution_eq_ordered]
  exact Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_psd_contraction I
      (fun _ => A) continuous_const (fun _ => hA) 0 t ht

/-- Adding `γ • 1` to the generator multiplies the evolution by the scalar `exp (-γ * t)`. -/
theorem evolution_scalar_shift (A : Matrix I I ℂ) (γ t : ℝ) :
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution (A + γ • (1 : Matrix I I ℂ)) t =
      Real.exp (-γ * t) • Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t := by
  have hc : Commute ((-t) • A) ((-t * γ) • (1 : Matrix I I ℂ)) :=
    ((Commute.one_right A).smul_left (-t)).smul_right (-t * γ)
  have he : NormedSpace.exp ((-t * γ) • (1 : Matrix I I ℂ)) =
      Real.exp (-t * γ) • (1 : Matrix I I ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using!
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix I I ℂ) (-t * γ)).symm
  unfold Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
  rw [smul_add, smul_smul, Matrix.exp_add_of_commute _ _ hc, he, mul_smul_comm,
    mul_one]
  congr 2
  ring

/-- If the Hermitian part of `A - γ • 1` is positive semidefinite, the evolution norm is at most
`exp (-γ * t)` for nonnegative time. -/
theorem norm_evolution_le_exp (A : Matrix I I ℂ) (γ : ℝ)
    (hA : ((A - γ • (1 : Matrix I I ℂ)) +
      (A - γ • (1 : Matrix I I ℂ))ᴴ).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t‖ ≤ Real.exp (-γ * t) := by
  have he : A = (A - γ • (1 : Matrix I I ℂ)) + γ • (1 : Matrix I I ℂ) := by abel
  conv_lhs => rw [he, Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution_scalar_shift]
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_one _ hA ht)
    (Real.exp_pos _).le).trans_eq (mul_one _)

/-- The difference of two constant-generator evolutions equals the integral of `evolution A s *
(B - A) * evolution B (t - s)`. -/
theorem evolution_sub_eq_integral (A B : Matrix I I ℂ) (t : ℝ) :
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t =
      ∫ s in 0..t, Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A s * (B - A) * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s) := by
  have hdA (s : ℝ) : HasDerivAt (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A)
      (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A s * (-A)) s := by
    simpa [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution] using!
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (-s)).scomp s (hasDerivAt_id s).neg
  have hdB (s : ℝ) : HasDerivAt (fun u => Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - u))
      (B * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s)) s := by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (s - t)).scomp s
      ((hasDerivAt_id s).sub_const t)
    simpa [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution,
        neg_sub] using! h
  have hd (s : ℝ) : HasDerivAt (fun u => Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A u * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - u))
      (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A s * (B - A) * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s)) s := by
    convert! (hdA s).mul (hdB s) using 1
    noncomm_ring
  have hcA : Continuous (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A) :=
    continuous_iff_continuousAt.mpr fun s => (hdA s).continuousAt
  have hcB : Continuous (fun s => Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s)) :=
    continuous_iff_continuousAt.mpr fun s => (hdB s).continuousAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((hcA.mul continuous_const).mul hcB).intervalIntegrable 0 t)
  simpa using! hi.symm

/-- The integrated exponential damping factor, equal to `t` when `γ = 0` and to `(1 - exp (-γ *
t)) / γ` otherwise. -/
def damping (γ t : ℝ) : ℝ :=
  if γ = 0 then t else (1 - Real.exp (-γ * t)) / γ

/-- The integral of `exp (-γ * s)` from zero to `t` equals `damping γ t`. -/
theorem integral_exp_neg_mul (γ t : ℝ) :
    (∫ s in 0..t, Real.exp (-γ * s)) = Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping γ t := by
  by_cases hγ : γ = 0
  · subst γ
    simp [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping]
  · have hd (s : ℝ) : HasDerivAt (fun u => -Real.exp (-γ * u) / γ)
        (Real.exp (-γ * s)) s := by
      have h := ((((hasDerivAt_id s).const_mul (-γ)).exp).neg.div_const γ)
      simp only [id_eq] at h
      convert! h using 1
      field_simp
    have hc : Continuous (fun s : ℝ => Real.exp (-γ * s)) := by fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable 0 t)
    rw [hi]
    simp only [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping,
        if_neg hγ, mul_zero, Real.exp_zero]
    ring

/-- If `A - γ • 1` and `B` have positive semidefinite Hermitian parts, their evolution
difference is bounded by `damping γ t * ‖A - B‖` for nonnegative time. -/
theorem norm_evolution_sub_le_damping (A B : Matrix I I ℂ) (γ : ℝ)
    (hA : ((A - γ • (1 : Matrix I I ℂ)) +
      (A - γ • (1 : Matrix I I ℂ))ᴴ).PosSemidef)
    (hB : (B + Bᴴ).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t‖ ≤ Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping γ t * ‖A - B‖ := by
  have hb (s : ℝ) (hs : s ∈ Set.Ioc 0 t) :
      ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A s * (B - A) * Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s)‖ ≤
        Real.exp (-γ * s) * ‖A - B‖ := by
    calc
      _ ≤ ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A s‖ * ‖B - A‖ * ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B (t - s)‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (-γ * s) * ‖B - A‖ * 1 := by
        gcongr
        · exact Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_exp A γ hA hs.1.le
        · exact Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_one B hB (sub_nonneg.mpr hs.2)
      _ = Real.exp (-γ * s) * ‖A - B‖ := by rw [mul_one, norm_sub_rev]
  have hc : Continuous (fun s : ℝ => Real.exp (-γ * s) * ‖A - B‖) := by fun_prop
  rw [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution_sub_eq_integral]
  calc
    _ ≤ ∫ s in 0..t, Real.exp (-γ * s) * ‖A - B‖ :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (Filter.Eventually.of_forall hb) (hc.intervalIntegrable 0 t)
    _ = Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping γ t * ‖A - B‖ := by
      rw [intervalIntegral.integral_mul_const,
          Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.integral_exp_neg_mul]

/-- For generators with positive semidefinite Hermitian parts, the evolution difference at
nonnegative time is at most `t * ‖A - B‖`. -/
theorem norm_evolution_sub_le (A B : Matrix I I ℂ)
    (hA : (A + Aᴴ).PosSemidef) (hB : (B + Bᴴ).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t‖ ≤ t * ‖A - B‖ := by
  simpa [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping] using!
      Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_sub_le_damping A B 0 (by simpa using! hA) hB ht

/-- If `A - γ • 1` and `B` are positive semidefinite, their evolution difference is bounded by
`damping γ t * ‖A - B‖` for nonnegative time. -/
theorem norm_evolution_sub_le_of_posSemidef (A B : Matrix I I ℂ) (γ : ℝ)
    (hA : (A - γ • (1 : Matrix I I ℂ)).PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t‖ ≤ Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping γ t * ‖A - B‖ := by
  exact Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_sub_le_damping A B γ
    (by simpa only [hA.isHermitian.eq] using! hA.add hA)
    (by simpa only [hB.isHermitian.eq] using! hB.add hB) ht

/-- Under the positive semidefiniteness assumptions, the Euclidean norm of the evolved-vector
difference is at most `damping γ t * ‖A - B‖` times the input norm. -/
theorem norm_evolution_mulVec_sub_le (A B : Matrix I I ℂ) (γ : ℝ)
    (hA : (A - γ • (1 : Matrix I I ℂ)).PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (v : Qatlib.Foundations.PureStateMath.QState I) :
    ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t *ᵥ v - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t *ᵥ v)‖ ≤
      (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.damping γ t * ‖A - B‖) * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ := by
  rw [← Matrix.sub_mulVec]
  exact (Matrix.l2_opNorm_mulVec (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution A t - Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution B t)
    (Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v)).trans
      (mul_le_mul_of_nonneg_right (Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_sub_le_of_posSemidef A B γ hA hB ht)
        (norm_nonneg _))

end Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
