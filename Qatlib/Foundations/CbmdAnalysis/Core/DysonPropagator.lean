/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.DysonConstruction
import Qatlib.Foundations.CbmdAnalysis.Core.DysonEnergy
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.Module

/-!
# Dyson propagators with a complex parameter

`dysonPropagator` is the time-ordered matrix evolution with generator `i (H + z L)`. Polynomial
dependence of each Dyson term yields complex differentiability of the full propagator in `z`.

For continuous Hermitian `H` and positive semidefinite `L`, the module proves exponential growth
in the upper half-plane and contractivity in the lower half-plane. Real parameters give unitary
evolution when both fields are Hermitian, providing analytic families for [WangEtAl2026].

## Main statements

* `dysonPropagator_differentiable`: proves complex differentiability in the parameter.
* `dysonPropagator_norm_le`: gives the half-plane growth bound.
* `dysonPropagator_real_unitary`: establishes unitarity at real parameters.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Each Dyson term for the field `z L + i H` is a finite sum of powers of `z` with continuous
time-dependent matrix coefficients. -/
private theorem parameterDyson_polynomial {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H) (s : ℝ) (n : ℕ) :
    ∃ (J : Type) (_inst : Fintype J) (p : J → ℕ) (C : J → ℝ → Matrix I I ℂ),
      (∀ j, Continuous (C j)) ∧
      ∀ (z : ℂ) (t : ℝ), orderedDysonTerm (fun u => z • L u + Complex.I • H u) s n t =
        ∑ j : J, z ^ p j • C j t := by
  induction n with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => 0, fun _ _ => 1, fun _ => continuous_const, ?_⟩
    intro z t
    simp [orderedDysonTerm]
  | succ n ih =>
    obtain ⟨J, inst, p, C, hC, he⟩ := ih
    letI := inst
    let D : Sum J J → ℝ → Matrix I I ℂ := Sum.elim
      (fun j t => ∫ u in s..t, -(Complex.I • H u * C j u))
      (fun j t => ∫ u in s..t, -(L u * C j u))
    refine ⟨Sum J J, inferInstance, Sum.elim p (fun j => p j + 1), D, ?_, ?_⟩
    · intro j
      cases j with
      | inl j =>
        dsimp only [D, Sum.elim_inl]
        have hc : Continuous (fun u => -(Complex.I • H u * C j u)) := by fun_prop
        exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous
      | inr j =>
        dsimp only [D, Sum.elim_inr]
        have hc : Continuous (fun u => -(L u * C j u)) := by fun_prop
        exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous
    · intro z t
      simp only [orderedDysonTerm, he, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      have hi (j : J) : IntervalIntegrable
          (fun u => z ^ p j • -(Complex.I • H u * C j u)) volume s t := by
        have hc : Continuous (fun u => z ^ p j • -(Complex.I • H u * C j u)) := by fun_prop
        exact hc.intervalIntegrable s t
      have hl (j : J) : IntervalIntegrable
          (fun u => z ^ (p j + 1) • -(L u * C j u)) volume s t := by
        have hc : Continuous (fun u => z ^ (p j + 1) • -(L u * C j u)) := by fun_prop
        exact hc.intervalIntegrable s t
      have hx (u : ℝ) :
          -((z • L u + Complex.I • H u) * ∑ j, z ^ p j • C j u) =
          (∑ j, z ^ p j • -(Complex.I • H u * C j u)) +
          ∑ j, z ^ (p j + 1) • -(L u * C j u) := by
        rw [Matrix.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [add_mul, mul_smul_comm, smul_mul_assoc, smul_neg, pow_succ]
        module
      simp_rw [hx]
      have his : IntervalIntegrable (fun u => ∑ j, z ^ p j • -(Complex.I • H u * C j u)) volume s t := by
        have hc : Continuous (fun u => ∑ j, z ^ p j • -(Complex.I • H u * C j u)) := by fun_prop
        exact hc.intervalIntegrable s t
      have hls : IntervalIntegrable (fun u => ∑ j, z ^ (p j + 1) • -(L u * C j u)) volume s t := by
        have hc : Continuous (fun u => ∑ j, z ^ (p j + 1) • -(L u * C j u)) := by fun_prop
        exact hc.intervalIntegrable s t
      rw [intervalIntegral.integral_add his hls,
        intervalIntegral.integral_finsetSum (fun j _ => hi j),
        intervalIntegral.integral_finsetSum (fun j _ => hl j)]
      simp only [intervalIntegral.integral_smul, D, Sum.elim_inl, Sum.elim_inr]

/-- For continuous fields, each parameter-dependent Dyson term is complex differentiable in `z`
at fixed start and end times. -/
private theorem parameterDyson_differentiable {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H) (s t : ℝ) (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => orderedDysonTerm (fun u => z • L u + Complex.I • H u) s n t) := by
  obtain ⟨J, inst, p, C, _, he⟩ := parameterDyson_polynomial L H hL hH s n
  letI := inst
  have hf : (fun z : ℂ => orderedDysonTerm (fun u => z • L u + Complex.I • H u) s n t) =
      fun z => ∑ j : J, z ^ p j • C j t := funext (fun z => he z t)
  rw [hf]
  exact Differentiable.fun_sum
      (fun j _ => ((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).pow (p j)).smul_const (C j t))

/-- For continuous `L` and `H`, the ordered evolution for `z L + i H` is complex differentiable
on the whole parameter plane. -/
theorem ordered_evolution_entire_parameter {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H) (s t : ℝ) :
    Differentiable ℂ (fun z : ℂ => orderedEvolution (fun u => z • L u + Complex.I • H u) s t) := by
  intro z₀
  obtain ⟨CL, hCL⟩ := (isCompact_uIcc.image hL).isBounded.exists_norm_le
  obtain ⟨CH, hCH⟩ := (isCompact_uIcc.image hH).isBounded.exists_norm_le
  let R := ‖z₀‖ + 1
  let M := R * max 0 CL + max 0 CH
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) (u : ℝ) (hu : u ∈ uIcc s t) :
      ‖z • L u + Complex.I • H u‖ ≤ M := by
    have hzR : ‖z‖ ≤ R := by
      have hh := norm_le_norm_sub_add z z₀
      rw [← dist_eq_norm] at hh
      dsimp [R]
      linarith [Metric.mem_ball.mp hz]
    calc
      _ ≤ ‖z • L u‖ + ‖Complex.I • H u‖ := norm_add_le _ _
      _ = ‖z‖ * ‖L u‖ + ‖H u‖ := by rw [norm_smul, norm_smul, Complex.norm_I, one_mul]
      _ ≤ R * max 0 CL + max 0 CH := by
        gcongr
        · exact (hCL (L u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)
        · exact (hCH (H u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)
      _ = M := rfl
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (Real.summable_pow_div_factorial (M * |t-s|))
    (fun n => (parameterDyson_differentiable L H hL hH s t n).differentiableOn)
    Metric.isOpen_ball
    (fun n z hz => orderedDysonTerm_norm_le _
      ((hL.const_smul z).add (hH.const_smul Complex.I)) s t M hM (hb z hz) n)
  exact hd.differentiableAt (Metric.ball_mem_nhds z₀ zero_lt_one)

/-- The ordered matrix evolution generated by `i (H + z L)` between the times `s` and `t`. -/
noncomputable def dysonPropagator {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (s t : ℝ) (z : ℂ) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (H u + z • L u)) s t

/-- The Dyson propagator equals the ordered evolution for the field `(i z) L + i H`. -/
theorem dysonPropagator_parameter {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (s t : ℝ) (z : ℂ) :
    dysonPropagator H L s t z =
      orderedEvolution (fun u => (Complex.I * z) • L u + Complex.I • H u) s t := by
  unfold dysonPropagator
  congr 1
  funext u
  simp only [smul_add, smul_smul]
  exact add_comm _ _

/-- For continuous `H` and `L`, the Dyson propagator is complex differentiable in its parameter. -/
theorem dysonPropagator_differentiable {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L) (s t : ℝ) :
    Differentiable ℂ (dysonPropagator H L s t) := by
  change Differentiable ℂ (fun z => dysonPropagator H L s t z)
  simp_rw [dysonPropagator_parameter]
  exact (ordered_evolution_entire_parameter L H hL hH s t).comp
    (differentiable_id.const_mul Complex.I)

/-- At parameter `-i`, the Dyson propagator equals the ordered evolution generated by `L + i H`. -/
theorem dysonPropagator_at_neg_I {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (s t : ℝ) :
    dysonPropagator H L s t (-Complex.I) =
      orderedEvolution (fun u => L u + Complex.I • H u) s t := by
  rw [dysonPropagator_parameter]
  simp

/-- The continuous complex-linear map sending a matrix to its action as an operator on Euclidean
space. -/
private noncomputable def dysonMatrixToOperator {I : Type} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℂ] (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)).toAlgEquiv.toLinearMap.toContinuousLinearMap

/-- For continuous fields, the action of the Dyson propagator on a fixed vector satisfies the
vector evolution equation with generator `i (H + z L)`. -/
private theorem dysonPropagator_action_deriv {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (s : ℝ) (z : ℂ) (v : EuclideanSpace ℂ I) (t : ℝ) :
    HasDerivAt (fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s u z) v)
      ((-Complex.I) •
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (H t) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s t z) v) +
          z • (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (L t) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s t z) v))) t := by
  have hd := orderedEvolution_hasDerivAt
    (fun u => Complex.I • (H u + z • L u))
    ((hH.add (hL.const_smul z)).const_smul Complex.I) s t
  have hOp := (dysonMatrixToOperator (I := I)).restrictScalars ℝ
    |>.hasFDerivAt.comp_hasDerivAt t hd
  have hVec := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ I) v).restrictScalars ℝ)
    |>.hasFDerivAt.comp_hasDerivAt t hOp
  change HasDerivAt (fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s u z) v)
    (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (-(Complex.I • (H t + z • L t) * dysonPropagator H L s t z))) v) t at hVec
  simpa only [map_neg, map_mul, map_smul, map_add,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    neg_smul] using hVec

/-- For forward time, continuous Hermitian `H` and positive semidefinite `L` give the norm bound
`exp (max z.im 0 * ∫ u in s..t, ‖L u‖)`. -/
theorem dysonPropagator_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (hHherm : ∀ u, (H u).IsHermitian) (hLpos : ∀ u, (L u).PosSemidef)
    (s t : ℝ) (hst : s ≤ t) (z : ℂ) :
    ‖dysonPropagator H L s t z‖ ≤
      Real.exp (max z.im 0 * ∫ u in s..t, ‖L u‖) := by
  let HH := fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (H u)
  let LL := fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (L u)
  have hc : Continuous LL := (dysonMatrixToOperator (I := I)).continuous.comp hL
  have hHs (u : ℝ) : (HH u).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hHherm u)
  have hLp (u : ℝ) : (LL u).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (hLpos u)
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s t z)‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  have h := dyson_trajectory_norm_le HH LL hc hHs hLp z
    (fun u => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (dysonPropagator H L s u z) v)
    (dysonPropagator_action_deriv H L hH hL s z v) s t hst
  simpa only [dysonPropagator, orderedEvolution_self, map_one,
    ContinuousLinearMap.one_apply] using! h

/-- For continuous fields, the derivative in the final time is left multiplication of the
propagator by `-i (H t + z L t)`. -/
theorem dysonPropagator_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (s t : ℝ) (z : ℂ) :
    HasDerivAt (fun u => dysonPropagator H L s u z)
      (-(Complex.I • (H t + z • L t) * dysonPropagator H L s t z)) t :=
  orderedEvolution_hasDerivAt _ ((hH.add (hL.const_smul z)).const_smul Complex.I) s t

/-- The Dyson propagator between identical start and end times is the identity matrix. -/
@[simp] theorem dysonPropagator_self {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (s : ℝ) (z : ℂ) : dysonPropagator H L s s z = 1 :=
  orderedEvolution_self _ s

/-- For continuous Hermitian `H` and `L`, the Dyson propagator is unitary at real parameters. -/
theorem dysonPropagator_real_unitary {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (hHherm : ∀ u, (H u).IsHermitian) (hLherm : ∀ u, (L u).IsHermitian)
    (s t x : ℝ) : dysonPropagator H L s t (x : ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  let A := fun u => Complex.I • (H u + (x : ℂ) • L u)
  have hA : Continuous A := (hH.add (hL.const_smul (x : ℂ))).const_smul Complex.I
  have hskew (u : ℝ) : star (A u) = -A u := by
    dsimp [A]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      (hHherm u).eq, (hLherm u).eq]
    simp [RCLike.star_def]
    abel
  let U := orderedEvolution A s
  have hd (u : ℝ) : HasDerivAt (fun r => star (U r) * U r) 0 u := by
    have hf := orderedEvolution_hasDerivAt A hA s u
    convert! hf.star.mul hf using 1
    (try simp only [star_neg, star_mul, hskew, mul_neg, neg_neg])
    noncomm_ring
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  have hu : star (U t) * U t = 1 := by simpa [U] using he
  exact Matrix.mem_unitaryGroup_iff'.mpr hu

/-- In the upper half-plane and for forward time, the norm is at most `exp (z.im * ∫ u in s..t,
‖L u‖)` for continuous Hermitian `H` and positive semidefinite `L`. -/
theorem dysonPropagator_norm_le_upper {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (hHherm : ∀ u, (H u).IsHermitian) (hLpos : ∀ u, (L u).PosSemidef)
    (s t : ℝ) (hst : s ≤ t) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖dysonPropagator H L s t z‖ ≤ Real.exp (z.im * ∫ u in s..t, ‖L u‖) := by
  simpa only [max_eq_left hz] using dysonPropagator_norm_le H L hH hL hHherm hLpos s t hst z

/-- In the lower half-plane and for forward time, the Dyson propagator is contractive for
continuous Hermitian `H` and positive semidefinite `L`. -/
theorem dysonPropagator_norm_le_lower {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (hHherm : ∀ u, (H u).IsHermitian) (hLpos : ∀ u, (L u).PosSemidef)
    (s t : ℝ) (hst : s ≤ t) (z : ℂ) (hz : z.im ≤ 0) :
    ‖dysonPropagator H L s t z‖ ≤ 1 := by
  simpa only [max_eq_right hz, zero_mul, Real.exp_zero] using
    dysonPropagator_norm_le H L hH hL hHherm hLpos s t hst z

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
