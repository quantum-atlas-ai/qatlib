/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Exact evolution of fixed Hamiltonian eigenvectors

This module defines vector overlap, fidelity, a time-ordered evolution operator, and the linear
schedule `scheduled`. It proves exact phase evolution for a normalized vector that is an
eigenvector of every Hamiltonian in the family, and derives unit fidelity in
`static_eigenvector_fidelity` and `proportional_schedule_fidelity`; it also records
nonnegativity of `minGap`. The mathematical context is [FarhiEtAl2000].

## Main statements

* `orderedEvolution_static_eigenvector`: A normalized common eigenvector of a continuous
  Hamiltonian family evolves exactly by the dynamical phase associated with its continuous
  eigenvalue function.
* `proportional_schedule_fidelity`: A normalized eigenvector retains fidelity one under the
  linear schedule from `HB` to a real scalar multiple of `HB`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.MainTheorem

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

/-- The complex inner product `∑ i, star (φ i) * ψ i` of two finite coordinate vectors. -/
def overlap {D : ℕ} (φ ψ : Fin D → ℂ) : ℂ := ∑ i, star (φ i) * ψ i

/-- The squared complex norm of the overlap of `φ` and `ψ`. -/
def fidelity {D : ℕ} (φ ψ : Fin D → ℂ) : ℝ := Complex.normSq (overlap φ ψ)

/-- The sum of the squared complex norms of the coordinates of `ψ`. -/
def vecNormSq {D : ℕ} (ψ : Fin D → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)

/-- The condition that the sum of squared coordinate norms of a vector equals one. -/
def IsUnitVec {D : ℕ} (ψ : Fin D → ℂ) : Prop := vecNormSq ψ = 1

/-- The time-ordered Hamiltonian evolution associated with `H` from time zero to time `T`. -/
def evolutionOperator {D : ℕ} (H : ℝ → Operator D) (T : ℝ) : Operator D :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
    (fun t => Complex.I • H t) 0 T

/-- The Hamiltonian family obtained by evaluating `interpolate HB HP` at the time fraction `t /
T`. -/
def scheduled {D : ℕ} (HB HP : Operator D) (T : ℝ) : ℝ → Operator D :=
  fun t => interpolate HB HP (t / T)

/-- The linear interpolation starts at the initial Hamiltonian `HB`. -/
theorem start_hamiltonian {D : ℕ} (HB HP : Operator D) :
    interpolate HB HP 0 = HB := interpolate_zero HB HP

/-- The linear interpolation ends at the problem Hamiltonian `HP`. -/
theorem end_hamiltonian {D : ℕ} (HB HP : Operator D) :
    interpolate HB HP 1 = HP := interpolate_one HB HP

/-- The interpolated operator is Hermitian at every real parameter when both endpoint
Hamiltonians are Hermitian. -/
theorem scheduled_isHermitian {D : ℕ} (HB HP : Operator D)
    (hB : HB.IsHermitian) (hP : HP.IsHermitian) (s : ℝ) :
    (interpolate HB HP s).IsHermitian :=
  interpolate_isHermitian HB HP hB hP s

/-- The infimum of the instantaneous lowest-eigenvalue gaps along a Hermitian interpolation is
nonnegative in dimension at least two [FarhiEtAl2000]. -/
theorem zero_le_minGap {D : ℕ} (hD : 2 ≤ D) (HB HP : Operator D)
    (hB : HB.IsHermitian) (hP : HP.IsHermitian) :
    0 ≤ minGap hD HB HP hB hP := by
  unfold minGap
  refine le_csInf ?_ ?_
  · exact ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  · rintro _ ⟨s, -, rfl⟩
    exact instantaneousGap_nonneg hD _ _

/-- The outer-product matrix with entries `ψ i * star (ψ j)`, which is an orthogonal projection
when `ψ` is a unit vector. -/
def rankOneProj {D : ℕ} (ψ : Fin D → ℂ) : Operator D :=
  Matrix.of fun i j => ψ i * star (ψ j)

/-- The outer-product matrix `rankOneProj ψ` sends `v` to the vector with coordinates `ψ i *
overlap ψ v`. -/
theorem rankOneProj_mulVec {D : ℕ} (ψ v : Fin D → ℂ) :
    rankOneProj ψ *ᵥ v = fun i => ψ i * overlap ψ v := by
  funext i
  simp only [rankOneProj, Matrix.mulVec, dotProduct, Matrix.of_apply, overlap, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The outer-product matrix of a unit vector fixes that vector. -/
theorem rankOneProj_mulVec_self {D : ℕ} (ψ : Fin D → ℂ) (hψ : IsUnitVec ψ) :
    rankOneProj ψ *ᵥ ψ = ψ := by
  rw [rankOneProj_mulVec]
  funext i
  have hov : overlap ψ ψ = (vecNormSq ψ : ℂ) := by
    unfold overlap vecNormSq
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun j _ => by
      simpa [Complex.star_def] using! (Complex.normSq_eq_conj_mul_self (z := ψ j)).symm)
  rw [hov, hψ]
  simp

/-- If `ψ` satisfies the eigenvector equation for `H` with real eigenvalue `E`, then left
multiplication of its outer-product matrix by `H` equals multiplication by `E`. -/
theorem mul_rankOneProj_of_eigen {D : ℕ} (H : Operator D) (ψ : Fin D → ℂ) (E : ℝ)
    (hψ : H *ᵥ ψ = fun i => (E : ℂ) * ψ i) :
    H * rankOneProj ψ = (E : ℂ) • rankOneProj ψ := by
  ext i j
  have h := congrFun hψ i
  simp only [Matrix.mulVec, dotProduct] at h
  simp only [rankOneProj, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ k, H i k * (ψ k * star (ψ j))
      = (∑ k, H i k * ψ k) * star (ψ j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = ((E : ℂ) * ψ i) * star (ψ j) := by rw [h]
    _ = (E : ℂ) * (ψ i * star (ψ j)) := by ring

/-- The dynamical phase `exp (-i * ∫ E)` accumulated from time zero to `t`. -/
def phaseExp (E : ℝ → ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I) * ∫ u in (0)..t, (E u : ℂ))

/-- For a continuous real energy function, the derivative of its dynamical phase is `-i * E t *
phaseExp E t`. -/
theorem phaseExp_hasDerivAt {E : ℝ → ℝ} (hE : Continuous fun t => (E t : ℂ)) (t : ℝ) :
    HasDerivAt (phaseExp E) (-(Complex.I) * (E t : ℂ) * phaseExp E t) t := by
  have hInt : HasDerivAt (fun t => ∫ u in (0)..t, (E u : ℂ)) ((E t : ℂ)) t :=
    intervalIntegral.integral_hasDerivAt_right (hE.intervalIntegrable _ _)
      hE.aestronglyMeasurable.stronglyMeasurableAtFilter hE.continuousAt
  have harg : HasDerivAt (fun t => -(Complex.I) * ∫ u in (0)..t, (E u : ℂ))
      (-(Complex.I) * (E t : ℂ)) t := hInt.const_mul _
  have h := harg.cexp
  simpa only [phaseExp, mul_assoc, mul_comm, mul_left_comm] using! h

/-- The sum of time-ordered evolution multiplied by `1 - rankOneProj ψ` and the phase `phaseExp
E t` times `rankOneProj ψ`. -/
def trackedProp {D : ℕ} (H : ℝ → Operator D) (ψ : Fin D → ℂ) (E : ℝ → ℝ)
    (t : ℝ) : Operator D :=
  orderedEvolution (fun t => Complex.I • H t) 0 t * (1 - rankOneProj ψ) +
    phaseExp E t • rankOneProj ψ

/-- For continuous Hamiltonian and energy families with a fixed common eigenvector `ψ`,
`trackedProp` satisfies the differential equation with derivative `-(Complex.I • H t *
trackedProp H ψ E t)`. -/
theorem trackedProp_hasDerivAt {D : ℕ} {H : ℝ → Operator D} {ψ : Fin D → ℂ}
    {E : ℝ → ℝ} (hH : Continuous H) (hE : Continuous fun t => (E t : ℂ))
    (hψ : ∀ t, H t *ᵥ ψ = fun i => (E t : ℂ) * ψ i) (t : ℝ) :
    HasDerivAt (trackedProp H ψ E) (-(Complex.I • H t * trackedProp H ψ E t)) t := by
  have hA : Continuous (fun t => Complex.I • H t) := hH.const_smul Complex.I
  have hU := orderedEvolution_hasDerivAt (fun t => Complex.I • H t) hA 0 t
  have hPh := phaseExp_hasDerivAt (E := E) hE t
  have hder : HasDerivAt (trackedProp H ψ E)
      ((-(Complex.I • H t * orderedEvolution (fun t => Complex.I • H t) 0 t)) *
          (1 - rankOneProj ψ) +
        (-(Complex.I) * (E t : ℂ) * phaseExp E t) • rankOneProj ψ) t := by
    simpa only [trackedProp] using!
      (hU.mul_const (1 - rankOneProj ψ)).add (hPh.smul_const (rankOneProj ψ))
  have hAP : Complex.I • H t * rankOneProj ψ = ((E t : ℂ) * Complex.I) • rankOneProj ψ := by
    rw [Matrix.smul_mul, mul_rankOneProj_of_eigen (H t) ψ (E t) (hψ t), smul_smul]
    congr 1
    ring
  have hrhs : -(Complex.I • H t * trackedProp H ψ E t) =
      (-(Complex.I • H t * orderedEvolution (fun t => Complex.I • H t) 0 t)) *
          (1 - rankOneProj ψ) +
        (-(Complex.I) * (E t : ℂ) * phaseExp E t) • rankOneProj ψ := by
    unfold trackedProp
    rw [Matrix.mul_add, Matrix.mul_smul, hAP, smul_smul, neg_add, ← Matrix.mul_assoc,
      ← Matrix.neg_mul, ← neg_smul]
    have hscalar : -(phaseExp E t * ((E t : ℂ) * Complex.I)) =
        -(Complex.I) * (E t : ℂ) * phaseExp E t := by ring
    rw [hscalar]
  rw [hrhs]
  exact hder

/-- A normalized common eigenvector of a continuous Hamiltonian family evolves exactly by the
dynamical phase associated with its continuous eigenvalue function [FarhiEtAl2000]. -/
theorem orderedEvolution_static_eigenvector {D : ℕ} {H : ℝ → Operator D} {ψ : Fin D → ℂ}
    {E : ℝ → ℝ} (hH : Continuous H) (hE : Continuous fun t => (E t : ℂ))
    (hunit : IsUnitVec ψ) (hψ : ∀ t, H t *ᵥ ψ = fun i => (E t : ℂ) * ψ i) (T : ℝ) :
    orderedEvolution (fun t => Complex.I • H t) 0 T *ᵥ ψ = phaseExp E T • ψ := by
  have hA : Continuous (fun t => Complex.I • H t) := hH.const_smul Complex.I
  have huniq := ordered_matrix_ode_unique (fun t => Complex.I • H t) hA
    (trackedProp H ψ E) (orderedEvolution (fun t => Complex.I • H t) 0) 0 ?_ ?_ ?_
  · have hT : trackedProp H ψ E T = orderedEvolution (fun t => Complex.I • H t) 0 T :=
      congrFun huniq T
    rw [← hT]
    unfold trackedProp
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      rankOneProj_mulVec_self ψ hunit, sub_self, Matrix.mulVec_zero, zero_add,
      Matrix.smul_mulVec, rankOneProj_mulVec_self ψ hunit]
  · unfold trackedProp phaseExp
    rw [orderedEvolution_self, intervalIntegral.integral_same, mul_zero,
      Complex.exp_zero, Matrix.one_mul, one_smul, sub_add_cancel]
  · exact trackedProp_hasDerivAt hH hE hψ
  · exact orderedEvolution_hasDerivAt _ hA 0

/-- The fidelity of a normalized common eigenvector with its time-ordered evolution under the
continuous Hamiltonian family is one [FarhiEtAl2000]. -/
theorem static_eigenvector_fidelity {D : ℕ} {H : ℝ → Operator D} {ψ : Fin D → ℂ}
    {E : ℝ → ℝ} (hH : Continuous H) (hE : Continuous fun t => (E t : ℂ))
    (hunit : IsUnitVec ψ) (hψ : ∀ t, H t *ᵥ ψ = fun i => (E t : ℂ) * ψ i) (T : ℝ) :
    fidelity ψ (orderedEvolution (fun t => Complex.I • H t) 0 T *ᵥ ψ) = 1 := by
  rw [orderedEvolution_static_eigenvector hH hE hunit hψ T]
  have hov : overlap ψ (phaseExp E T • ψ) = phaseExp E T * (vecNormSq ψ : ℂ) := by
    unfold overlap vecNormSq
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hnorm : Complex.normSq (phaseExp E T) = 1 := by
    unfold phaseExp
    have him : (-(Complex.I) * ∫ u in (0)..T, (E u : ℂ)).re = 0 := by
      rw [intervalIntegral.integral_ofReal]
      simp [Complex.mul_re]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, him, Real.exp_zero, one_pow]
  unfold fidelity
  rw [hov, hunit]
  simp only [Complex.ofReal_one, mul_one]
  exact hnorm

/-- A normalized eigenvector retains fidelity one under the linear schedule from `HB` to a real
scalar multiple of `HB` [FarhiEtAl2000]. -/
theorem proportional_schedule_fidelity {D : ℕ} (HB : Operator D) (c : ℝ)
    (ψ : Fin D → ℂ) (E : ℝ) (hunit : IsUnitVec ψ)
    (hψ : HB *ᵥ ψ = fun i => (E : ℂ) * ψ i) (T : ℝ) :
    fidelity ψ
      (orderedEvolution (fun t => Complex.I • interpolate HB (c • HB) (t / T)) 0 T *ᵥ ψ) = 1 := by
  have hH : Continuous (fun t : ℝ => interpolate HB (c • HB) (t / T)) := by
    unfold interpolate
    fun_prop
  have hE : Continuous (fun t : ℝ => ((((1 - t / T) + t / T * c) * E : ℝ) : ℂ)) := by
    fun_prop
  have hψ' : ∀ t : ℝ,
      interpolate HB (c • HB) (t / T) *ᵥ ψ =
        fun i => ((((1 - t / T) + t / T * c) * E : ℝ) : ℂ) * ψ i := by
    intro t
    have hmat : interpolate HB (c • HB) (t / T) *ᵥ ψ =
        (1 - t / T) • (HB *ᵥ ψ) + (t / T) • (c • (HB *ᵥ ψ)) := by
      unfold interpolate
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [hmat, hψ]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    push_cast
    ring
  exact static_eigenvector_fidelity hH hE hunit hψ' T

/-- For positive `g`, the runtime inequality `E / g ^ 2 ≤ T` yields `TimeSufficient T E g`. -/
theorem time_sufficient_of_gap {T E g : ℝ} (hg : 0 < g)
    (h : E / g ^ 2 ≤ T) : TimeSufficient T E g :=
  timeSufficient_of_gap T E g hg h

end Qatlib.Papers.AdiabaticEvol00.MainResults.MainTheorem
