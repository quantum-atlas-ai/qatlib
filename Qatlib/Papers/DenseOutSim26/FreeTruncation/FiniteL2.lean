/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section

open Matrix
open MeasureTheory intervalIntegral
open Set
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.FiniteL2

/-!
# Finite-dimensional Euclidean dense-output integral

[Yang–Liu–Wang–Zhang–Liu](https://arxiv.org/abs/2609.40094v1) define dense
output in Eq. (4). In the Heisenberg picture this is
`J_H(O) = ∫₀^T ⟨ψ₀|O(t)|ψ₀⟩ dt`, with Eq. (B4) giving the truncated
counterpart. Appendix B (B12) then uses a normalised state to pass from a
pointwise Euclidean operator-norm bound on the Heisenberg observables to the
integrated comparison

`|J_H(O) − J_{H_R}(O)| ≤ ∫₀^T ‖O(t) − O_R(t)‖ dt ≤ T² / R^{α − D/2}`.

This file proves that integration step on a nonempty finite index set. A
matrix acts on `EuclideanSpace ℂ I` through `Matrix.toEuclideanCLM`, and every
matrix norm below is the induced `ℓ²` operator norm. The constant `C`, the
horizon `T`, the radius `R`, and the exponent `β` are fixed before the
quantifiers over time and over unit states. The fermionic tail estimates
(B8)–(B11), the identification `β = α − D/2`, and the radius asymptotics of
Theorem 3 are not proved here. The factor `1/2` coming from `∫₀^T t dt = T²/2`
is loosened to the factor `1` written in (B12) and Eq. (29).
-/

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Euclidean quadratic forms -/

/-- The expectation of a matrix observable in a Euclidean-space vector. -/
def denseOutputForm (ψ : EuclideanSpace ℂ I) (M : Matrix I I ℂ) : ℂ :=
  inner ℂ ψ ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) M) ψ)

/-- Quadratic-form subtraction is the quadratic form of the matrix difference. -/
theorem denseOutputForm_sub (ψ : EuclideanSpace ℂ I) (M N : Matrix I I ℂ) :
    denseOutputForm ψ M - denseOutputForm ψ N = denseOutputForm ψ (M - N) := by
  simp [denseOutputForm, map_sub, _root_.sub_apply, inner_sub_right]

/-- A unit Euclidean vector turns an `ℓ²` operator norm into the same
quadratic-form bound. The constant `1` does not depend on the vector or the
matrix. -/
theorem denseOutputForm_norm_le (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1)
    (M : Matrix I I ℂ) : ‖denseOutputForm ψ M‖ ≤ ‖M‖ := by
  unfold denseOutputForm
  calc
    ‖inner ℂ ψ ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) M) ψ)‖
        ≤ ‖ψ‖ * ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) M) ψ‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖M‖ * ‖ψ‖) := by
      gcongr
      have h := ContinuousLinearMap.le_opNorm
        (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) M) ψ
      rwa [Matrix.l2_opNorm_toEuclideanCLM] at h
    _ = ‖M‖ := by rw [hψ]; ring

set_option backward.isDefEq.respectTransparency true in
/-- The map sending a matrix to its Euclidean quadratic form is continuous, so
a continuous observable curve has a Bochner-integrable dense-output signal. -/
theorem continuous_denseOutputForm (ψ : EuclideanSpace ℂ I) :
    Continuous (denseOutputForm ψ) := by
  have huncurry : Continuous (fun p : Matrix I I ℂ × EuclideanSpace ℂ I =>
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) p.1 p.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM (n := I) (𝕜 := ℂ)
  have hpair : Continuous (fun M : Matrix I I ℂ => (M, ψ)) :=
    continuous_id.prodMk continuous_const
  have happly : Continuous fun M : Matrix I I ℂ =>
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) M ψ :=
    Continuous.comp' (f := fun M : Matrix I I ℂ => (M, ψ))
      (g := fun p : Matrix I I ℂ × EuclideanSpace ℂ I =>
        Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) p.1 p.2) huncurry hpair
  exact continuous_const.inner happly

/-- A positive finite cardinality supplies a genuine unit Euclidean vector, so
the later state quantifier is not taken over an empty sphere. -/
theorem euclidean_unit_sphere_nonempty (hcard : 0 < Fintype.card I) :
    ∃ ψ : EuclideanSpace ℂ I, ‖ψ‖ = 1 := by
  have : Nonempty I := Fintype.card_pos_iff.mp hcard
  refine ⟨PiLp.single 2 (Classical.choice ‹Nonempty I›) (1 : ℂ), ?_⟩
  rw [PiLp.norm_single, norm_one]

/-! ## The integrated dense-output step -/

/-- Appendix B (B12) on a nonempty finite Euclidean space. If the `ℓ²` operator
norm of the Heisenberg difference satisfies `‖F(t) − G(t)‖ ≤ C t / R^β` on the
real segment `[0, T]`, then every unit state has integrated quadratic-form
error at most `C T² / R^β`. The parameters `C`, `T`, `R`, and `β` are fixed
before both the time quantifier and the state quantifier. The time segment is
`[0, T]` with `T ≥ 0`. At `T = 0`, the integral and the upper bound both
vanish. -/
theorem dense_output_l2_light_cone
    (hcard : 0 < Fintype.card I)
    (F G : ℝ → Matrix I I ℂ)
    (T R β C : ℝ)
    (hT : 0 ≤ T) (hR : 0 < R) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun t => F t - G t) (Icc (0 : ℝ) T))
    (hpt : ∀ t ∈ Icc (0 : ℝ) T, ‖F t - G t‖ ≤ C * t / R ^ β) :
    (∃ ψ : EuclideanSpace ℂ I, ‖ψ‖ = 1) ∧
      ∀ ψ : EuclideanSpace ℂ I, ‖ψ‖ = 1 →
        ‖∫ t in (0 : ℝ)..T,
            denseOutputForm ψ (F t) - denseOutputForm ψ (G t)‖ ≤
          C * T ^ 2 / R ^ β := by
  refine ⟨euclidean_unit_sphere_nonempty hcard, ?_⟩
  intro ψ hψ
  have hrewrite :
      (∫ t in (0 : ℝ)..T, denseOutputForm ψ (F t) - denseOutputForm ψ (G t)) =
        ∫ t in (0 : ℝ)..T, denseOutputForm ψ (F t - G t) := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact denseOutputForm_sub ψ (F t) (G t)
  rw [hrewrite]
  have hf_cont : ContinuousOn (fun t => denseOutputForm ψ (F t - G t)) (Icc (0 : ℝ) T) :=
    (continuous_denseOutputForm ψ).comp_continuousOn hcont
  have hnorm_cont : ContinuousOn (fun t => ‖denseOutputForm ψ (F t - G t)‖) (Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn hf_cont
  have hnorm_int : IntervalIntegrable (fun t => ‖denseOutputForm ψ (F t - G t)‖) volume 0 T :=
    hnorm_cont.intervalIntegrable_of_Icc hT
  have hg_cont : Continuous fun t : ℝ => C * t / R ^ β :=
    (continuous_const.mul continuous_id).div_const _
  have hg_int : IntervalIntegrable (fun t : ℝ => C * t / R ^ β) volume 0 T :=
    hg_cont.intervalIntegrable 0 T
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      ‖denseOutputForm ψ (F t - G t)‖ ≤ C * t / R ^ β := by
    intro t ht
    exact (denseOutputForm_norm_le ψ hψ (F t - G t)).trans (hpt t ht)
  have hmono :
      ∫ t in (0 : ℝ)..T, ‖denseOutputForm ψ (F t - G t)‖ ≤
        ∫ t in (0 : ℝ)..T, C * t / R ^ β :=
    intervalIntegral.integral_mono_on hT hnorm_int hg_int hpoint
  have hbochner :
      ‖∫ t in (0 : ℝ)..T, denseOutputForm ψ (F t - G t)‖ ≤
        ∫ t in (0 : ℝ)..T, ‖denseOutputForm ψ (F t - G t)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hT
  have hcalc : (∫ t in (0 : ℝ)..T, C * t / R ^ β) = C * T ^ 2 / (2 * R ^ β) := by
    rw [show (fun t : ℝ => C * t / R ^ β) = fun t => (C / R ^ β) * t by
      funext t; ring]
    rw [intervalIntegral.integral_const_mul, integral_id]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
    ring
  have hRβ : 0 < R ^ β := Real.rpow_pos_of_pos hR β
  have hhalf : C * T ^ 2 / (2 * R ^ β) ≤ C * T ^ 2 / R ^ β := by
    exact div_le_div_of_nonneg_left (mul_nonneg hC (sq_nonneg T)) hRβ (by linarith)
  calc
    ‖∫ t in (0 : ℝ)..T, denseOutputForm ψ (F t - G t)‖
        ≤ ∫ t in (0 : ℝ)..T, ‖denseOutputForm ψ (F t - G t)‖ := hbochner
    _ ≤ ∫ t in (0 : ℝ)..T, C * t / R ^ β := hmono
    _ = C * T ^ 2 / (2 * R ^ β) := hcalc
    _ ≤ C * T ^ 2 / R ^ β := hhalf

/-! ## A concrete nonempty two-site domain -/

/-- The two-site one-particle space used by the consumer smoke test. -/
abbrev TwoSite := Fin 2

/-- A normalized one-particle basis state at site `q`. -/
def siteState (q : TwoSite) : EuclideanSpace ℂ TwoSite :=
  PiLp.single 2 q (1 : ℂ)

/-- Every two-site basis state is a genuine unit Euclidean vector. -/
theorem siteState_norm (q : TwoSite) : ‖siteState q‖ = 1 := by
  rw [siteState, PiLp.norm_single, norm_one]

/-- The identity scaled by a real time. Its `ℓ²` operator norm is the absolute
value of that time, so on `[0, T]` it realises the linear light-cone majorant. -/
def scaledIdentity (t : ℝ) : Matrix TwoSite TwoSite ℂ :=
  (t : ℂ) • (1 : Matrix TwoSite TwoSite ℂ)

/-- On the nonnegative ray the scaled identity obeys the unit-constant linear
bound `‖t I‖ ≤ t`. -/
theorem scaledIdentity_l2_le {t : ℝ} (ht : 0 ≤ t) : ‖scaledIdentity t‖ ≤ t := by
  unfold scaledIdentity
  have hnorm : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht
  have hone : ‖(1 : Matrix TwoSite TwoSite ℂ)‖ = 1 := CStarRing.norm_one
  calc
    ‖(t : ℂ) • (1 : Matrix TwoSite TwoSite ℂ)‖
        ≤ ‖(t : ℂ)‖ * ‖(1 : Matrix TwoSite TwoSite ℂ)‖ := norm_smul_le _ _
    _ = t * 1 := by rw [hnorm, hone]
    _ = t := by ring

/-- The scaled identity contributes the real signal `t` on a unit basis state. -/
theorem scaledIdentity_form (t : ℝ) :
    denseOutputForm (siteState 0) (scaledIdentity t) = (t : ℂ) := by
  unfold denseOutputForm scaledIdentity siteState
  rw [map_smul, map_one]
  simp only [_root_.smul_apply, one_apply_eq_self,
    inner_smul_right, inner_self_eq_norm_sq_to_K, PiLp.norm_single, norm_one]
  simp

end Qatlib.Papers.DenseOutSim26.FreeTruncation.FiniteL2
