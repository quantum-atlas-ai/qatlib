/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Exact Dyson source series

The recursively integrated terms `dysonSourceTerm` define the inhomogeneous Dyson series
`dysonSourceSeries`. For continuous matrix coefficients and driving terms, this module proves
convergence, differentiability, and the variation of constants representation of solutions to
`x' = A x + b`. It also records dissipative contraction estimates and scalar expressions used in
resource bounds.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `dysonSourceSeries_hasDerivAt`: the source series solves the inhomogeneous equation.
* `solution_eq_initial_add_dyson`: decomposition into homogeneous evolution and source series.
* `dissipative_contraction`: contraction under the nonpositive logarithmic norm condition.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.DysonSeries22.ExactSource

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator ComplexOrder Topology
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- For a continuous state valued function, conversion to Euclidean space commutes with interval
integration. -/
theorem toEuclidean_intervalIntegral (f : ℝ → QState I) (hf : Continuous f) (s t : ℝ) :
    toEuclidean_fromVec (∫ u in s..t, f u) = ∫ u in s..t, toEuclidean_fromVec (f u) := by
  let e : QState I ≃L[ℂ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm
  have he : ⇑e = toEuclidean_fromVec := rfl
  have h := (e : QState I →L[ℂ] EuclideanSpace ℂ I).intervalIntegral_comp_comm
    (μ := MeasureTheory.volume) (hf.intervalIntegrable s t)
  simpa [he] using! h.symm

omit [Fintype I] [DecidableEq I] in

/-- Converting a continuous state valued function to Euclidean space preserves continuity. -/
theorem continuous_toEuclidean {f : ℝ → QState I} (hf : Continuous f) :
    Continuous (fun u => toEuclidean_fromVec (f u)) := by
  let e : QState I ≃L[ℂ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm
  have he : ⇑e = toEuclidean_fromVec := rfl
  simpa [he] using! (e : QState I →L[ℂ] EuclideanSpace ℂ I).continuous.comp hf

/-- The Euclidean norm of a matrix applied to a state is bounded by the operator norm times the
Euclidean norm of the state. -/
theorem norm_mulVec_le (A : Matrix I I ℂ) (v : QState I) :
    ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec v‖ := by
  simpa using! Matrix.l2_opNorm_mulVec A (toEuclidean_fromVec v)

omit [DecidableEq I] in

/-- The function space norm of a state is at most its Euclidean norm. -/
theorem pi_norm_le_toEuclidean (v : QState I) : ‖v‖ ≤ ‖toEuclidean_fromVec v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  have h := PiLp.norm_apply_le (p := 2) (toEuclidean_fromVec v) i
  simpa [toEuclidean_fromVec] using! h

omit [DecidableEq I] in

/-- Matrix multiplication commutes with the sum of a summable state valued series. -/
theorem mulVec_tsum (A : Matrix I I ℂ) (f : ℕ → QState I) (h : Summable f) :
    (∑' n, A *ᵥ f n) = A *ᵥ (∑' n, f n) := by
  let L : QState I →L[ℂ] QState I := (Matrix.mulVecLin A).toContinuousLinearMap
  have hL : ∀ v, L v = A *ᵥ v := fun v => rfl
  have := L.map_tsum h
  simpa [hL] using! this.symm

/-- The recursively integrated source term, starting with the integral of `b` and then
repeatedly integrating multiplication by `A`. -/
noncomputable def dysonSourceTerm (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s : ℝ) : ℕ → ℝ → QState I
  | 0, t => ∫ u in s..t, b u
  | n + 1, t => ∫ u in s..t, A u *ᵥ dysonSourceTerm A b s n u

/-- The infinite sum of the recursively integrated Dyson source terms. -/
noncomputable def dysonSourceSeries (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) : QState I :=
  ∑' n, dysonSourceTerm A b s n t

omit [DecidableEq I] in

/-- Every successor indexed source term vanishes when its endpoint equals its initial time. -/
@[simp]
theorem dysonSourceTerm_succ_self (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s : ℝ) (n : ℕ) : dysonSourceTerm A b s (n + 1) s = 0 := by
  simp [dysonSourceTerm]

omit [DecidableEq I] in

/-- The zeroth source term vanishes when its endpoint equals its initial time. -/
@[simp]
theorem dysonSourceTerm_zero_self (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s : ℝ) : dysonSourceTerm A b s 0 s = 0 := by
  simp [dysonSourceTerm]

omit [DecidableEq I] in

/-- The Dyson source series vanishes when the initial and final times coincide. -/
@[simp] theorem dysonSourceSeries_self (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s : ℝ) : dysonSourceSeries A b s s = 0 := by
  unfold dysonSourceSeries
  have h : ∀ n, dysonSourceTerm A b s n s = 0 := by
    intro n
    cases n with
    | zero => simp
    | succ n => simp
  simp [h]

omit [DecidableEq I] in

/-- Each Dyson source term is continuous in its final time when `A` and `b` are continuous. -/
theorem dysonSourceTerm_continuous (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s : ℝ) (n : ℕ) :
    Continuous (dysonSourceTerm A b s n) := by
  induction n with
  | zero =>
    exact (intervalIntegral.differentiable_integral_of_continuous hb).continuous
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous
      (hA.matrix_mulVec ih)).continuous

omit [DecidableEq I] in

/-- The derivative of the successor source term at `t` is `A t` applied to the preceding source
term at `t`, for continuous `A` and `b`. -/
theorem dysonSourceTerm_hasDerivAt_succ (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (dysonSourceTerm A b s (n + 1)) (A t *ᵥ dysonSourceTerm A b s n t) t := by
  have hc : Continuous (fun u => A u *ᵥ dysonSourceTerm A b s n u) :=
    hA.matrix_mulVec (dysonSourceTerm_continuous A b hA hb s n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Bounds `M` on the matrix norm and `C` on the Euclidean driving norm give the source term
bound `C * |t - s| * (M * |t - s|)^n / (n + 1)!`. -/
theorem dysonSourceTerm_norm_le (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t M C : ℝ)
    (hM : 0 ≤ M) (_hC : 0 ≤ C)
    (hboundA : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ uIcc s t, ‖toEuclidean_fromVec (b u)‖ ≤ C) (n : ℕ) :
    ‖toEuclidean_fromVec (dysonSourceTerm A b s n t)‖ ≤
      C * |t - s| * (M * |t - s|) ^ n / ((n + 1).factorial : ℝ) := by
  induction n generalizing t with
  | zero =>
    have hcont : Continuous (fun u => toEuclidean_fromVec (b u)) := continuous_toEuclidean hb
    have hfinal : (∫ u in uIoc s t, (C : ℝ)) =
        C * |t - s| * (M * |t - s|) ^ 0 / ((0 + 1).factorial : ℝ) := by
      rw [MeasureTheory.setIntegral_const]
      rw [show volume.real (uIoc s t) = |t - s| from by
        rw [MeasureTheory.measureReal_def, Real.volume_uIoc,
          ENNReal.toReal_ofReal (abs_nonneg _)]]
      have hone : ((0 + 1).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
      rw [hone, pow_zero]
      simp [smul_eq_mul, mul_comm]
    have h2 : ‖∫ u in s..t, toEuclidean_fromVec (b u)‖ ≤
        ∫ u in uIoc s t, ‖toEuclidean_fromVec (b u)‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    have h3 : (∫ u in uIoc s t, ‖toEuclidean_fromVec (b u)‖) ≤
        ∫ u in uIoc s t, (C : ℝ) := by
      apply MeasureTheory.integral_mono_ae
      · exact ((hcont.norm).intervalIntegrable s t).def'
      · exact (intervalIntegrable_const).def'
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
          (fun u hu => hboundb u (uIoc_subset_uIcc hu))
    rw [dysonSourceTerm, toEuclidean_intervalIntegral b hb s t]
    exact h2.trans (h3.trans (le_of_eq hfinal))
  | succ n ih =>
    let g : ℝ → ℝ := fun u => M * (C * |u - s| * (M * |u - s|) ^ n / ((n + 1).factorial : ℝ))
    have hg : Continuous g := by fun_prop
    have hbnd (u : ℝ) (hu : u ∈ uIoc s t) :
        ‖toEuclidean_fromVec (A u *ᵥ dysonSourceTerm A b s n u)‖ ≤ g u := by
      have hu' : u ∈ uIcc s t := uIoc_subset_uIcc hu
      have hAu : ‖A u‖ ≤ M := hboundA u hu'
      have hn : ‖toEuclidean_fromVec (dysonSourceTerm A b s n u)‖ ≤
          C * |u - s| * (M * |u - s|) ^ n / ((n + 1).factorial : ℝ) :=
        ih u (fun x hx => hboundA x (uIcc_subset_uIcc_left hu' hx))
          (fun x hx => hboundb x (uIcc_subset_uIcc_left hu' hx))
      calc
        _ ≤ ‖A u‖ * ‖toEuclidean_fromVec (dysonSourceTerm A b s n u)‖ :=
              norm_mulVec_le (A u) (dysonSourceTerm A b s n u)
        _ ≤ M * (C * |u - s| * (M * |u - s|) ^ n / ((n + 1).factorial : ℝ)) :=
              mul_le_mul hAu hn (norm_nonneg _) hM
        _ = g u := rfl
    calc
      ‖toEuclidean_fromVec (dysonSourceTerm A b s (n + 1) t)‖
          = ‖∫ u in s..t, toEuclidean_fromVec (A u *ᵥ dysonSourceTerm A b s n u)‖ := by
            rw [dysonSourceTerm,
              toEuclidean_intervalIntegral (fun u => A u *ᵥ dysonSourceTerm A b s n u)
                (hA.matrix_mulVec (dysonSourceTerm_continuous A b hA hb s n)) s t]
      _ ≤ ∫ u in uIoc s t, ‖toEuclidean_fromVec (A u *ᵥ dysonSourceTerm A b s n u)‖ :=
            intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ u in uIoc s t, g u := by
            apply MeasureTheory.integral_mono_ae
            · exact ((continuous_toEuclidean
                (hA.matrix_mulVec (dysonSourceTerm_continuous A b hA hb s n))).norm
                  |>.intervalIntegrable s t).def'
            · exact (hg.intervalIntegrable s t).def'
            · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hbnd
      _ ≤ C * |t - s| * (M * |t - s|) ^ (n + 1) / ((n + 1 + 1).factorial : ℝ) := by
            have halg : (∫ u in uIoc s t, g u) =
                C * |t - s| * (M * |t - s|) ^ (n + 1) / ((n + 1 + 1).factorial : ℝ) := by
              have hg_eq : g = fun u =>
                  C * M ^ (n + 1) / ((n + 1).factorial : ℝ) * |u - s| ^ (n + 1) := by
                funext u
                dsimp [g]
                rw [mul_pow, pow_succ]
                ring
              rw [hg_eq, MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
              have hfac : ((n + 1 + 1).factorial : ℝ) =
                  ((n : ℝ) + 1 + 1) * ((n + 1).factorial : ℝ) := by
                rw [show n + 1 + 1 = (n + 1).succ from rfl, Nat.factorial_succ]
                push_cast
                ring
              rw [mul_pow, pow_succ, hfac]
              have hden1 : ((n + 1).factorial : ℝ) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero (n + 1)
              have hden2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
              field_simp
              push_cast
              ring
            exact le_of_eq halg

/-- For continuous `A` and `b`, the Dyson source terms form a summable series at any fixed pair
of times. -/
theorem dysonSourceTerm_summable (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t : ℝ) :
    Summable (fun n => dysonSourceTerm A b s n t) := by
  obtain ⟨CA, hCA⟩ := (isCompact_uIcc.image hA).isBounded.exists_norm_le
  obtain ⟨Cb, hCb⟩ :=
    (isCompact_uIcc.image (continuous_toEuclidean hb)).isBounded.exists_norm_le
  let M := max 0 CA
  let C := max 0 Cb
  have hM : 0 ≤ M := le_max_left _ _
  have hC : 0 ≤ C := le_max_left _ _
  have hboundA : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M := fun u hu =>
    (hCA (A u) ⟨u, hu, rfl⟩).trans (le_max_right (0 : ℝ) CA)
  have hboundb : ∀ u ∈ uIcc s t, ‖toEuclidean_fromVec (b u)‖ ≤ C := fun u hu =>
    (hCb (toEuclidean_fromVec (b u)) ⟨u, hu, rfl⟩).trans (le_max_right (0 : ℝ) Cb)
  have hfac : Summable (fun n : ℕ => (M * |t - s|) ^ n / ((n + 1).factorial : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (Real.summable_pow_div_factorial (M * |t - s|))
    intro n
    have hle : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    have hpow : 0 ≤ (M * |t - s|) ^ n := by positivity
    exact div_le_div_of_nonneg_left hpow (by positivity) hle
  apply Summable.of_norm_bounded (hfac.mul_left (C * |t - s|))
  intro n
  calc
    ‖dysonSourceTerm A b s n t‖
        ≤ ‖toEuclidean_fromVec (dysonSourceTerm A b s n t)‖ :=
              pi_norm_le_toEuclidean (dysonSourceTerm A b s n t)
    _ ≤ C * |t - s| * (M * |t - s|) ^ n / ((n + 1).factorial : ℝ) :=
          dysonSourceTerm_norm_le A b hA hb s t M C hM hC hboundA hboundb n
    _ = (C * |t - s|) * ((M * |t - s|) ^ n / ((n + 1).factorial : ℝ)) := by ring

/-- The factorial majorant for source term derivatives is summable for nonnegative `M` and `R`. -/
theorem summable_factorial_majorant (M C R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => M * ((C * R) * ((M * R) ^ n / ((n + 1).factorial : ℝ)))) := by
  have hfac : Summable (fun n : ℕ => (M * R) ^ n / ((n + 1).factorial : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (Real.summable_pow_div_factorial (M * R))
    intro n
    have hle : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hle
  simpa [mul_assoc] using! ((hfac.mul_left (C * R)).mul_left M)

/-- Uniform bounds on the matrix and driving terms in an interval give the stated factorial
majorant for the norm of `A u` applied to a source term at an interior point. -/
theorem dysonSourceTerm_deriv_norm_le (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s M C R : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 < R)
    (hboundA : ∀ u ∈ Icc (s - R) (s + R), ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ Icc (s - R) (s + R), ‖toEuclidean_fromVec (b u)‖ ≤ C)
    (n : ℕ) (u : ℝ) (hu : u ∈ Ioo (s - R) (s + R)) :
    ‖A u *ᵥ dysonSourceTerm A b s n u‖ ≤
      M * ((C * R) * ((M * R) ^ n / ((n + 1).factorial : ℝ))) := by
  have hs' : s ∈ Icc (s - R) (s + R) := ⟨by linarith, by linarith⟩
  have hsub : uIcc s u ⊆ Icc (s - R) (s + R) :=
    (convex_Icc (s - R) (s + R)).ordConnected.uIcc_subset hs' ⟨hu.1.le, hu.2.le⟩
  have hb' := dysonSourceTerm_norm_le A b hA hb s u M C hM hC
    (fun x hx => hboundA x (hsub hx)) (fun x hx => hboundb x (hsub hx)) n
  have huR : |u - s| ≤ R := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hAu : ‖A u‖ ≤ M := hboundA u ⟨hu.1.le, hu.2.le⟩
  have hfirst : ‖A u *ᵥ dysonSourceTerm A b s n u‖ ≤
      ‖A u‖ * ‖toEuclidean_fromVec (dysonSourceTerm A b s n u)‖ := by
    have h1 : ‖A u *ᵥ dysonSourceTerm A b s n u‖ ≤
        ‖toEuclidean_fromVec (A u *ᵥ dysonSourceTerm A b s n u)‖ :=
      pi_norm_le_toEuclidean (A u *ᵥ dysonSourceTerm A b s n u)
    have h2 : ‖toEuclidean_fromVec (A u *ᵥ dysonSourceTerm A b s n u)‖ ≤
        ‖A u‖ * ‖toEuclidean_fromVec (dysonSourceTerm A b s n u)‖ :=
      norm_mulVec_le (A u) (dysonSourceTerm A b s n u)
    exact h1.trans h2
  have hP : (0 : ℝ) ≤ (M * |u - s|) ^ n := pow_nonneg (mul_nonneg hM (abs_nonneg _)) n
  have hQ : (0 : ℝ) ≤ (M * R) ^ n := pow_nonneg (mul_nonneg hM hR.le) n
  have hpow : (M * |u - s|) ^ n ≤ (M * R) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hM (abs_nonneg _)) (mul_le_mul_of_nonneg_left huR hM) n
  have hbracket : C * |u - s| * (M * |u - s|) ^ n / ((n + 1).factorial : ℝ)
      ≤ C * R * (M * R) ^ n / ((n + 1).factorial : ℝ) := by
    have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hnum : C * |u - s| * (M * |u - s|) ^ n ≤ C * R * (M * R) ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left huR hC) hpow hP (mul_nonneg hC hR.le)
    exact div_le_div_of_nonneg_right hnum hf.le
  have hmul : M * (C * |u - s| * (M * |u - s|) ^ n / ((n + 1).factorial : ℝ))
      ≤ M * ((C * R) * ((M * R) ^ n / ((n + 1).factorial : ℝ))) := by
    have hrhs : (C * R) * ((M * R) ^ n / ((n + 1).factorial : ℝ))
        = C * R * (M * R) ^ n / ((n + 1).factorial : ℝ) := by ring
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left hbracket hM
  exact hfirst.trans ((mul_le_mul hAu hb' (norm_nonneg _) hM).trans hmul)

/-- For continuous `A` and `b`, the source series has derivative `A t` applied to the series
plus `b t`. See [Berry and Costa, 2024, Section 1.1–1.2; Eqs. (2)–(11),
(91)][BerryCosta2024]. -/
theorem dysonSourceSeries_hasDerivAt (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t : ℝ) :
    HasDerivAt (dysonSourceSeries A b s) (A t *ᵥ dysonSourceSeries A b s t + b t) t := by
  let R : ℝ := |t - s| + 1
  let a : ℝ := s - R
  let c : ℝ := s + R
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨CA, hCA⟩ :=
    (isCompact_Icc (a := a) (b := c)).image hA |>.isBounded.exists_norm_le
  obtain ⟨Cb, hCb⟩ :=
    (isCompact_Icc (a := a) (b := c)).image (continuous_toEuclidean hb)
      |>.isBounded.exists_norm_le
  let M := max 0 CA
  let C := max 0 Cb
  have hM : 0 ≤ M := le_max_left _ _
  have hC : 0 ≤ C := le_max_left _ _
  have hboundA : ∀ u ∈ Icc a c, ‖A u‖ ≤ M := fun u hu =>
    (hCA (A u) ⟨u, hu, rfl⟩).trans (le_max_right (0 : ℝ) CA)
  have hboundb : ∀ u ∈ Icc a c, ‖toEuclidean_fromVec (b u)‖ ≤ C := fun u hu =>
    (hCb (toEuclidean_fromVec (b u)) ⟨u, hu, rfl⟩).trans (le_max_right (0 : ℝ) Cb)
  have hs : s ∈ Ioo a c := by dsimp [a, c]; constructor <;> linarith
  have ht : t ∈ Ioo a c := by
    dsimp [a, c, R]
    constructor <;> linarith [le_abs_self (t - s), neg_le_abs (t - s)]
  let u : ℕ → ℝ := fun n => M * ((C * R) * ((M * R) ^ n / ((n + 1).factorial : ℝ)))
  have hfacSum : Summable u := summable_factorial_majorant M C R hM hR.le
  have hder : HasDerivAt (fun z => ∑' n, dysonSourceTerm A b s (n + 1) z)
      (∑' n, A t *ᵥ dysonSourceTerm A b s n t) t := by
    refine hasDerivAt_tsum_of_isPreconnected (u := u) (t := Ioo a c) (y₀ := s)
      (g := fun n z => dysonSourceTerm A b s (n + 1) z)
      (g' := fun n z => A z *ᵥ dysonSourceTerm A b s n z)
      hfacSum isOpen_Ioo isPreconnected_Ioo ?_ ?_ hs ?_ ht
    · exact fun n y _ => dysonSourceTerm_hasDerivAt_succ A b hA hb s n y
    · exact fun n y hy =>
        dysonSourceTerm_deriv_norm_le A b hA hb s M C R hM hC hR hboundA hboundb n y hy
    · simp

  have hzero : HasDerivAt (dysonSourceTerm A b s 0) (b t) t := by
    exact intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable _ _)
      hb.aestronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt
  have hsum : HasDerivAt (fun z => dysonSourceTerm A b s 0 z
      + ∑' n, dysonSourceTerm A b s (n + 1) z)
      (b t + ∑' n, A t *ᵥ dysonSourceTerm A b s n t) t :=
    hzero.add hder
  have he : (fun z => dysonSourceTerm A b s 0 z + ∑' n, dysonSourceTerm A b s (n + 1) z)
      = dysonSourceSeries A b s := by
    funext z
    exact ((dysonSourceTerm_summable A b hA hb s z).tsum_eq_zero_add).symm
  have hsum' : (∑' n, A t *ᵥ dysonSourceTerm A b s n t)
      = A t *ᵥ dysonSourceSeries A b s t := by
    unfold dysonSourceSeries
    exact mulVec_tsum (A t) (fun n => dysonSourceTerm A b s n t)
      (dysonSourceTerm_summable A b hA hb s t)
  rw [he] at hsum
  rw [hsum'] at hsum
  simpa [add_comm] using! hsum

/-- For continuous `A` and `b`, the Dyson source series equals the integral of the driving term
propagated from each integration time to the endpoint. -/
theorem dysonSourceSeries_eq_sourceIntegral (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t : ℝ) :
    dysonSourceSeries A b s t =
      ∫ u in s..t, orderedEvolution (fun u => -A u) u t *ᵥ b u := by
  have hneg : Continuous (fun u => -A u) := hA.neg
  have huniq := orderedForcedSolution_unique (fun u => -A u) b hneg hb s 0
    (dysonSourceSeries A b s) (by simp)
    (fun t => by
      have h := dysonSourceSeries_hasDerivAt A b hA hb s t
      simpa [Matrix.neg_mulVec] using! h)
  have hval := congrFun huniq t
  rw [hval]
  simp [orderedForcedSolution]

/-- Any solution of `x' = A x + b` with continuous coefficients equals its propagated initial
value plus the Dyson source series. See [Berry and Costa, 2024, Section 1.1–1.2; Eqs.
(2)–(11), (91)][BerryCosta2024]. -/
theorem solution_eq_initial_add_dyson (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (x : ℝ → QState I) (hA : Continuous A) (hb : Continuous b) (s : ℝ)
    (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + b t) t) :
    x = fun t => orderedEvolution (fun u => -A u) s t *ᵥ x s + dysonSourceSeries A b s t := by
  have hneg : Continuous (fun u => -A u) := hA.neg
  have huniq := orderedForcedSolution_unique (fun u => -A u) b hneg hb s (x s) x
    (by simp) (fun t => by simpa [Matrix.neg_mulVec] using! hx t)
  funext t
  rw [congrFun huniq t]
  simp only [orderedForcedSolution]
  rw [dysonSourceSeries_eq_sourceIntegral A b hA hb s t]

/-- The condition that `-A u - (A u)ᴴ` is positive semidefinite at every time. -/
def HasNonpositiveLogNorm (A : ℝ → Matrix I I ℂ) : Prop :=
  ∀ u, ((-A u) + (-A u)ᴴ).PosSemidef

/-- Continuous coefficients with nonpositive logarithmic norm have forward ordered evolution of
operator norm at most one. See [Berry and Costa, 2024, Eq. (27) and stability
discussion][BerryCosta2024]. -/
theorem dissipative_contraction (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (hlog : HasNonpositiveLogNorm A) {s t : ℝ} (hst : s ≤ t) :
    ‖orderedEvolution (fun u => -A u) s t‖ ≤ 1 :=
  ordered_evolution_psd_contraction I (fun u => -A u) hA.neg hlog s t hst

/-- A uniform upper bound `xMax` on the norm of a trajectory throughout the interval `[0, T]`. -/
def SolutionMaxBound (x : ℝ → EuclideanSpace ℂ I) (T xMax : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ ≤ xMax

/-- A uniform upper bound `bMax` on the norm of the driving term throughout the interval `[0,
T]`. -/
def DrivingMaxBound (b : ℝ → EuclideanSpace ℂ I) (T bMax : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ‖b t‖ ≤ bMax

/-- The maximum of the matrix scale `lamA` and the ratio `bMax / xMax`. -/
def lambdaAx (lamA bMax xMax : ℝ) : ℝ := max lamA (bMax / xMax)

/-- The time step `T / nSteps` for a uniform subdivision. -/
def deltaT (T : ℝ) (nSteps : ℕ) : ℝ := T / (nSteps : ℝ)

/-- The scalar expression `(xMax / xT) * (lamB / lamA) / (vMin - eps * xMax / (lamA * T))` used
in the variable coefficient resource bound. -/
def RBound41 (xMax xT lamB lamA T eps vMin : ℝ) : ℝ :=
  (xMax / xT) * (lamB / lamA) / (vMin - eps * xMax / (lamA * T))

/-- The derivative scale expression `(1 + T * bMax / (lamA * xMax)) * dA + db / xMax`. -/
def DBound (T bMax lamA xMax dA db : ℝ) : ℝ :=
  (1 + T * bMax / (lamA * xMax)) * dA + db / xMax

/-- The ratio `xMax / xT` used in the constant coefficient resource bound. -/
def RBound42 (xMax xT : ℝ) : ℝ := xMax / xT

/-- The combined scale `lambdaAx` is at least the matrix scale `lamA`. -/
theorem le_lambdaAx (lamA bMax xMax : ℝ) : lamA ≤ lambdaAx lamA bMax xMax :=
  le_max_left _ _

/-- The combined scale `lambdaAx` is at least the driving to solution ratio `bMax / xMax`. -/
theorem div_bMax_le_lambdaAx (lamA bMax xMax : ℝ) :
    bMax / xMax ≤ lambdaAx lamA bMax xMax :=
  le_max_right _ _

/-- A positive number of steps satisfying `lamA * T ≤ nSteps` gives the bound `lamA * deltaT T
nSteps ≤ 1`. See [Berry and Costa, 2024, Eqs. (71)–(77), (88), (92)][BerryCosta2024]. -/
theorem lamA_mul_deltaT_le_one (lamA T : ℝ) (nSteps : ℕ)
    (_hlam : 0 < lamA) (hn : 0 < nSteps) (hstep : lamA * T ≤ (nSteps : ℝ)) :
    lamA * deltaT T nSteps ≤ 1 := by
  unfold deltaT
  have hnpos : (0 : ℝ) < (nSteps : ℝ) := by exact_mod_cast hn
  have hmul : lamA * (T / (nSteps : ℝ)) = (lamA * T) / (nSteps : ℝ) := by
    rw [mul_div_assoc']
  rw [hmul, div_le_one hnpos]
  exact hstep

/-- If `0 < xT ≤ xMax`, the ratio `RBound42 xMax xT` is at least one. -/
theorem one_le_RBound42 (xMax xT : ℝ) (hxT : 0 < xT) (hx : xT ≤ xMax) :
    1 ≤ RBound42 xMax xT := by
  unfold RBound42
  rw [le_div_iff₀ hxT]
  simpa using! hx

/-- For positive `xT`, the ratio `RBound42` is monotone in its numerator `xMax`. -/
theorem RBound42_mono (xMax xMax' xT : ℝ) (hxT : 0 < xT) (h : xMax ≤ xMax') :
    RBound42 xMax xT ≤ RBound42 xMax' xT := by
  unfold RBound42
  exact div_le_div_of_nonneg_right h hxT.le

/-- A solution with constant matrix and driving term equals its propagated value at `s` plus the
constant coefficient Dyson source series. -/
theorem constant_solution_representation
    (A₀ : Matrix I I ℂ) (b₀ : QState I) (x : ℝ → QState I) (s : ℝ)
    (hx : ∀ t, HasDerivAt x (A₀ *ᵥ x t + b₀) t) :
    x = fun t => orderedEvolution (fun _ => -A₀) s t *ᵥ x s +
      dysonSourceSeries (fun _ => A₀) (fun _ => b₀) s t := by
  exact solution_eq_initial_add_dyson (fun _ => A₀) (fun _ => b₀) x
    continuous_const continuous_const s hx

/-- For constant `A`, ordered evolution from zero to `t` with coefficient `-A` equals the matrix
exponential of `t • A`. See [Berry and Costa, 2024, Section 1.1–1.2; Eqs. (2)–(11),
(91)][BerryCosta2024]. -/
theorem constant_ordered_eq_exp (A : Matrix I I ℂ) (t : ℝ) :
    orderedEvolution (fun _ => -A) 0 t = NormedSpace.exp (t • A) := by
  rw [← Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution_eq_ordered]
  simp [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution]

/-- If `-A - Aᴴ` is positive semidefinite, the matrix exponential of `t • A` has operator norm
at most one for nonnegative `t`. -/
theorem constant_exp_contraction (A : Matrix I I ℂ)
    (hA : ((-A)+(-A)ᴴ).PosSemidef) {t : ℝ} (ht : 0≤t) :
    ‖NormedSpace.exp (t • A)‖≤1 := by
  simpa only [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution,
    smul_neg,neg_smul,neg_neg] using!
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_one (-A) hA ht

/-- A solution of the constant coefficient inhomogeneous equation equals the matrix exponential
applied to its initial value plus the Dyson source series. See [Berry and Costa, 2024,
Section 1.3; Eqs. (15)–(18)][BerryCosta2024]. -/
theorem constant_solution_exp (A : Matrix I I ℂ) (b : QState I) (x : ℝ → QState I)
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + b) t) (t : ℝ) :
    x t = NormedSpace.exp (t • A) *ᵥ x 0 + dysonSourceSeries (fun _ => A) (fun _ => b) 0 t := by
  have h := congrFun (constant_solution_representation A b x 0 hx) t
  rwa [constant_ordered_eq_exp] at h
end Qatlib.Papers.DysonSeries22.ExactSource
