/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.OperatorDefs
set_option warningAsError false

noncomputable section

open scoped ComplexOrder
open InnerProductSpace

namespace Qatlib.Papers.LocalHam06.MainResults.AdiabaticTheorem

open Qatlib.Papers.LocalHam06.MainResults.OperatorDefs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

def IsEigenvalue {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : M →ₗ[ℂ] M) (μ : ℝ) : Prop :=
  ∃ v : M, v ≠ 0 ∧ T v = (μ : ℂ) • v

def eigenMultiplicity (T : E →L[ℂ] E) (μ : ℝ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (((μ : ℂ) • (1 : E →L[ℂ] E) - T).toLinearMap))

def operatorRank (T : E →L[ℂ] E) : ℕ :=
  Module.finrank ℂ (LinearMap.range T.toLinearMap)

def SpectralGap (H : E →L[ℂ] E) (lamstar Δ : ℝ) : Prop :=
  ∀ v : E, ‖v‖ = 1 → rayleigh H v ≤ lamstar - Δ / 2 ∨ lamstar + Δ / 2 ≤ rayleigh H v

theorem symmetric_eigenvalue_real (T : E →L[ℂ] E)
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric)
    {z : ℂ} {v : E} (hv : v ≠ 0) (hTv : T v = z • v) :
    ∃ r : ℝ, z = (r : ℂ) := by
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have h1 : inner ℂ (T v) v = inner ℂ v (T v) := hT v v
  rw [hTv] at h1
  simp only [inner_smul_left, inner_smul_right] at h1
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hvv h1
  exact Complex.conj_eq_iff_real.mp h2

theorem symmetric_eigenvectors_orthogonal (T : E →L[ℂ] E)
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric)
    {μ ν : ℝ} (hμν : μ ≠ ν) {v w : E}
    (hTv : T v = (μ : ℂ) • v) (hTw : T w = (ν : ℂ) • w) :
    inner ℂ v w = 0 := by
  have h1 : inner ℂ (T v) w = inner ℂ v (T w) := hT v w
  rw [hTv, hTw] at h1
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have hne : ((μ : ℂ) - (ν : ℂ)) ≠ 0 := by
    have hcast : (μ : ℂ) ≠ (ν : ℂ) := by exact_mod_cast hμν
    exact sub_ne_zero.mpr hcast
  have hzero : ((μ : ℂ) - (ν : ℂ)) * inner ℂ v w = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

theorem rayleigh_eigenvector (T : E →L[ℂ] E) {μ : ℝ} {v : E}
    (hTv : T v = (μ : ℂ) • v) (hv : ‖v‖ = 1) :
    rayleigh T v = μ := by
  unfold rayleigh
  rw [hTv, inner_smul_right]
  have hvv : inner ℂ v v = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  rw [hvv, mul_one, Complex.ofReal_re]

theorem resolvent_mul_cancel (T : E →L[ℂ] E) (z : ℂ)
    (h : IsUnit (z • (1 : E →L[ℂ] E) - T)) :
    resolventOperator T z * (z • (1 : E →L[ℂ] E) - T) = 1 := by
  unfold resolventOperator
  exact Ring.inverse_mul_cancel _ h

theorem mul_resolvent_cancel (T : E →L[ℂ] E) (z : ℂ)
    (h : IsUnit (z • (1 : E →L[ℂ] E) - T)) :
    (z • (1 : E →L[ℂ] E) - T) * resolventOperator T z = 1 := by
  unfold resolventOperator
  exact Ring.mul_inverse_cancel _ h

theorem operatorRank_zero : operatorRank (0 : E →L[ℂ] E) = 0 := by
  unfold operatorRank
  simp

end Qatlib.Papers.LocalHam06.MainResults.AdiabaticTheorem
