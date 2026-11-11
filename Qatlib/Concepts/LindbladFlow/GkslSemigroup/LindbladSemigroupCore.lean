/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import QuantumInfo.Channels.Unbundled
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.Entropy.DPI

/-!
# Lindblad semigroups from completely positive Euler maps

This module proves the semigroup law, trace preservation, norm growth, and a quadratic
first-order remainder estimate for `lindbladSemigroup`. Completely positive Kraus-form Euler
maps converge to the exponential evolution, yielding complete positivity, a finite Kraus
representation, and preservation of density operators for nonnegative time.

It also relates Kraus representations to Choi positivity and derives stationarity from
`KMSNormalForm`. These results formalize the finite-dimensional dynamical-semigroup framework of
[Lindblad1976] and the complete-positivity criterion of [Choi1975].

## Main statements

* `gkslEulerMap_tendsto`: converge from iterated completely positive steps to the semigroup.
* `lindbladSemigroup_cptp`: obtain Kraus, trace, and density-preservation guarantees.
* `hasKrausFamily_iff_choi_posSemidef`: characterize Kraus form by Choi positivity.
* `g1`: collect the semigroup, error, channel, norm, and KMS properties.

## References

* [Lindblad, 1976][Lindblad1976]
* [Choi, 1975][Choi1975]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

/-- The Lindblad exponential evolution at time `s + t` is the composition of the evolutions at
times `t` and `s`. -/
theorem lindbladSemigroup_add {D : ℕ} (G : GKSL D) (s t : ℝ) (ρ : Operator D) :
    lindbladSemigroup G (s + t) ρ =
      lindbladSemigroup G s (lindbladSemigroup G t ρ) := by
  letI : NormedAddCommGroup (Operator D) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (Operator D) := Matrix.instL2OpNormedSpace
  letI : TopologicalSpace (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toUniformSpace.toTopologicalSpace
  letI : Module ℂ (Operator D) := (inferInstance : NormedSpace ℂ (Operator D)).toModule
  let L : Operator D →L[ℂ] Operator D := LinearMap.toContinuousLinearMap (lindbladMap G)
  have heq (u : ℝ) (σ : Operator D) :
      lindbladSemigroup G u σ = (NormedSpace.exp ((u : ℂ) • L)) σ := by
    have hh := (ContinuousLinearMap.apply ℂ (Operator D) σ).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((u : ℂ) • L))
    have ht (k : ℕ) :
        (ContinuousLinearMap.apply ℂ (Operator D) σ)
            (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) =
          ((u : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) σ := by
      change (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) σ = _
      rw [ContinuousLinearMap.smul_apply]
      have hpow (k : ℕ) : ((u : ℂ) • L) ^ k = (u : ℂ) ^ k • L ^ k := by
        induction k with
        | zero => simp only [pow_zero, one_smul]
        | succ k ih =>
          rw [pow_succ, ih]
          ext τ
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            map_smul, smul_smul, pow_succ, mul_comm]
      rw [hpow k, ContinuousLinearMap.smul_apply, smul_smul,
        ContinuousLinearMap.coe_pow']
      change ((k.factorial : ℂ)⁻¹ * (u : ℂ) ^ k) • ((lindbladMap G)^[k]) σ = _
      rw [div_eq_mul_inv, mul_comm]
    simp only [ht] at hh
    exact hh.tsum_eq
  rw [heq, heq, heq, Complex.ofReal_add]
  have hadd : ((s : ℂ) + (t : ℂ)) • L = (s : ℂ) • L + (t : ℂ) • L := by
    ext σ
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, add_smul]
  have hcomm : Commute ((s : ℂ) • L) ((t : ℂ) • L) := by
    show ((s : ℂ) • L) * ((t : ℂ) • L) = ((t : ℂ) • L) * ((s : ℂ) • L)
    ext τ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      map_smul, smul_smul, mul_comm]
  have hexp := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  rw [hadd, hexp]
  rfl

/-- The exponential series of iterated generator applications sums to the Lindblad evolution. -/
theorem lindbladSemigroup_hasSum {D : ℕ} (G : GKSL D) (u : ℝ) (σ : Operator D) :
    HasSum (fun k : ℕ => ((u : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) σ)
      (lindbladSemigroup G u σ) := by
  letI : NormedAddCommGroup (Operator D) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (Operator D) := Matrix.instL2OpNormedSpace
  letI : TopologicalSpace (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toUniformSpace.toTopologicalSpace
  letI : Module ℂ (Operator D) := (inferInstance : NormedSpace ℂ (Operator D)).toModule
  let L : Operator D →L[ℂ] Operator D := LinearMap.toContinuousLinearMap (lindbladMap G)
  have hh := (ContinuousLinearMap.apply ℂ (Operator D) σ).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((u : ℂ) • L))
  have ht (k : ℕ) :
      (ContinuousLinearMap.apply ℂ (Operator D) σ)
          (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) =
        ((u : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) σ := by
    change (((k.factorial : ℂ)⁻¹) • ((u : ℂ) • L) ^ k) σ = _
    rw [ContinuousLinearMap.smul_apply]
    have hpow (k : ℕ) : ((u : ℂ) • L) ^ k = (u : ℂ) ^ k • L ^ k := by
      induction k with
      | zero => simp only [pow_zero, one_smul]
      | succ k ih =>
        rw [pow_succ, ih]
        ext τ
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
          map_smul, smul_smul, pow_succ, mul_comm]
    rw [hpow k, ContinuousLinearMap.smul_apply, smul_smul,
      ContinuousLinearMap.coe_pow']
    change ((k.factorial : ℂ)⁻¹ * (u : ℂ) ^ k) • ((lindbladMap G)^[k]) σ = _
    rw [div_eq_mul_inv, mul_comm]
  simp only [ht] at hh
  simpa only [lindbladSemigroup] using! hh.summable.hasSum

/-- The trace of the Lindblad generator applied to any operator is zero. -/
theorem trace_lindbladApply {D : ℕ} (G : GKSL D) (ρ : Operator D) :
    Matrix.trace (lindbladApply G ρ) = 0 := by
  have hc : Matrix.trace (G.ham * ρ - ρ * G.ham) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm G.ham ρ, sub_self]
  have hj (j : Fin (D * D)) :
      Matrix.trace (G.jumps j * ρ * (G.jumps j)ᴴ -
        (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ + ρ * (G.jumps j)ᴴ * G.jumps j)) = 0 := by
    have ha := Matrix.trace_mul_cycle (G.jumps j) ρ (G.jumps j)ᴴ
    have hb := (Matrix.trace_mul_cycle ρ (G.jumps j)ᴴ (G.jumps j)).trans ha
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, ha, hb]
    change _ - (1 / 2 : ℂ) * (_ + _) = 0
    ring
  simp only [lindbladApply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    hc, hj, smul_zero, Finset.sum_const_zero, add_zero]

/-- Lindblad evolution preserves the trace of every operator at every real time. -/
theorem trace_lindbladSemigroup {D : ℕ} (G : GKSL D) (t : ℝ) (ρ : Operator D) :
    Matrix.trace (lindbladSemigroup G t ρ) = Matrix.trace ρ := by
  letI : NormedAddCommGroup (Operator D) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (Operator D) := Matrix.instL2OpNormedSpace
  letI : TopologicalSpace (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toUniformSpace.toTopologicalSpace
  letI : Module ℂ (Operator D) := (inferInstance : NormedSpace ℂ (Operator D)).toModule
  let f : Operator D →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D) ℂ ℂ)
  have hs := f.hasSum (lindbladSemigroup_hasSum G t ρ)
  have hiter (k : ℕ) (hk : k ≠ 0) : Matrix.trace (((lindbladMap G)^[k]) ρ) = 0 := by
    rcases k with _ | k
    · exact (hk rfl).elim
    · rw [Function.iterate_succ_apply']
      exact trace_lindbladApply G _
  have hterm (k : ℕ) (hk : k ≠ 0) :
      f (((t : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) ρ) = 0 := by
    change Matrix.trace (((t : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) ρ) = 0
    rw [Matrix.trace_smul, hiter k hk, smul_zero]
  calc
    Matrix.trace (lindbladSemigroup G t ρ) =
        ∑' k : ℕ, f (((t : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) ρ) :=
      hs.tsum_eq.symm
    _ = f (((t : ℂ) ^ 0 / Nat.factorial 0) • ((lindbladMap G)^[0]) ρ) :=
      tsum_eq_single 0 hterm
    _ = Matrix.trace ρ := by simp [f, Matrix.traceLinearMap]

/-- Bounds the generator action by `(2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖^2) * ‖ρ‖`. -/
theorem norm_lindbladApply_le {D : ℕ} (G : GKSL D) (ρ : Operator D) :
    ‖lindbladApply G ρ‖ ≤ (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) * ‖ρ‖ := by
  have hp (A B C : Operator D) : ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  have hH : ‖(-Complex.I) • (G.ham * ρ - ρ * G.ham)‖ ≤ 2 * ‖G.ham‖ * ‖ρ‖ := by
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    calc
      _ ≤ ‖G.ham * ρ‖ + ‖ρ * G.ham‖ := norm_sub_le _ _
      _ ≤ ‖G.ham‖ * ‖ρ‖ + ‖ρ‖ * ‖G.ham‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ = _ := by ring
  have hJ (L : Operator D) :
      ‖L * ρ * Lᴴ - (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * Lᴴ * L)‖ ≤
        2 * ‖L‖ ^ 2 * ‖ρ‖ := by
    have ha : ‖L * ρ * Lᴴ‖ ≤ ‖L‖ ^ 2 * ‖ρ‖ := by
      have h := hp L ρ Lᴴ
      rw [Matrix.l2_opNorm_conjTranspose] at h
      nlinarith
    have hb : ‖Lᴴ * L * ρ‖ ≤ ‖L‖ ^ 2 * ‖ρ‖ := by
      have h := hp Lᴴ L ρ
      rw [Matrix.l2_opNorm_conjTranspose] at h
      nlinarith
    have hc : ‖ρ * Lᴴ * L‖ ≤ ‖L‖ ^ 2 * ‖ρ‖ := by
      have h := hp ρ Lᴴ L
      rw [Matrix.l2_opNorm_conjTranspose] at h
      nlinarith
    have hd : ‖(1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * Lᴴ * L)‖ ≤ ‖L‖ ^ 2 * ‖ρ‖ := by
      calc
        _ = (1 / 2 : ℝ) * ‖Lᴴ * L * ρ + ρ * Lᴴ * L‖ := by
          rw [norm_smul]
          norm_num
        _ ≤ (1 / 2 : ℝ) * (‖Lᴴ * L * ρ‖ + ‖ρ * Lᴴ * L‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ (1 / 2 : ℝ) * (‖L‖ ^ 2 * ‖ρ‖ + ‖L‖ ^ 2 * ‖ρ‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hb hc) (by norm_num)
        _ = _ := by ring
    exact (norm_sub_le _ _).trans ((add_le_add ha hd).trans_eq (by ring))
  unfold lindbladApply
  calc
    _ ≤ ‖(-Complex.I) • (G.ham * ρ - ρ * G.ham)‖ +
        ∑ j, ‖G.jumps j * ρ * (G.jumps j)ᴴ -
          (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ + ρ * (G.jumps j)ᴴ * G.jumps j)‖ :=
      (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ 2 * ‖G.ham‖ * ‖ρ‖ + ∑ j, 2 * ‖G.jumps j‖ ^ 2 * ‖ρ‖ :=
      add_le_add hH (Finset.sum_le_sum fun j _ => hJ (G.jumps j))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring

/-- For nonnegative time, bounds the evolution norm by the exponential of the generator bound
times the initial norm. -/
theorem norm_lindbladSemigroup_le {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t)
    (ρ : Operator D) :
    ‖lindbladSemigroup G t ρ‖ ≤
      Real.exp ((2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) * t) * ‖ρ‖ := by
  let β : ℝ := 2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hiter (k : ℕ) : ‖((lindbladMap G)^[k]) ρ‖ ≤ β ^ k * ‖ρ‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ β * ‖((lindbladMap G)^[k]) ρ‖ := norm_lindbladApply_le G _
        _ ≤ β * (β ^ k * ‖ρ‖) := mul_le_mul_of_nonneg_left ih hβ
        _ = _ := by ring
  have hs : HasSum (fun k : ℕ => (β * t) ^ k / (k.factorial : ℝ)) (Real.exp (β * t)) := by
    simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul, div_eq_mul_inv, mul_comm] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (β * t))
  apply (lindbladSemigroup_hasSum G t ρ).norm_le_of_bounded (hs.mul_right ‖ρ‖)
  intro k
  rw [norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, Complex.norm_natCast]
  calc
    _ ≤ (t ^ k / (k.factorial : ℝ)) * (β ^ k * ‖ρ‖) :=
      mul_le_mul_of_nonneg_left (hiter k) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- For `0 ≤ t ≤ 1`, bounds the first-order Taylor remainder by the squared generator bound
times its exponential, `t^2`, and the initial norm. -/
theorem lindbladSemigroup_taylor_one_le {D : ℕ} (G : GKSL D) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ρ : Operator D) :
    ‖lindbladSemigroup G t ρ - ρ - t • lindbladApply G ρ‖ ≤
      (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) ^ 2 *
        Real.exp (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) * t ^ 2 * ‖ρ‖ := by
  let β : ℝ := 2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hiter (k : ℕ) : ‖((lindbladMap G)^[k]) ρ‖ ≤ β ^ k * ‖ρ‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ β * ‖((lindbladMap G)^[k]) ρ‖ := norm_lindbladApply_le G _
        _ ≤ β * (β ^ k * ‖ρ‖) := mul_le_mul_of_nonneg_left ih hβ
        _ = _ := by ring
  have hs : HasSum (fun k : ℕ => (β * t) ^ k / (k.factorial : ℝ)) (Real.exp (β * t)) := by
    simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul, div_eq_mul_inv, mul_comm] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (β * t))
  have ht' : HasSum (fun k : ℕ => ((t : ℂ) ^ (k + 2) / (k + 2).factorial) •
      ((lindbladMap G)^[k + 2]) ρ)
      (lindbladSemigroup G t ρ - ρ - t • lindbladApply G ρ) := by
    have hh := (hasSum_nat_add_iff' 2).mpr (lindbladSemigroup_hasSum G t ρ)
    simpa [Finset.sum_range_succ, sub_add_eq_sub_sub, lindbladMap] using! hh
  have hb : ‖lindbladSemigroup G t ρ - ρ - t • lindbladApply G ρ‖ ≤
      (β ^ 2 * t ^ 2 * ‖ρ‖) * Real.exp (β * t) := by
    apply ht'.norm_le_of_bounded (hs.mul_left (β ^ 2 * t ^ 2 * ‖ρ‖))
    intro k
    rw [norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht, Complex.norm_natCast]
    have hfac : (k.factorial : ℝ) ≤ ((k + 2).factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_le (Nat.le_add_right k 2)
    calc
      _ ≤ (t ^ (k + 2) / ((k + 2).factorial : ℝ)) * (β ^ (k + 2) * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left (hiter (k + 2)) (by positivity)
      _ = (β ^ 2 * t ^ 2 * ‖ρ‖) * (β * t) ^ k / ((k + 2).factorial : ℝ) := by
        rw [pow_add, pow_add, mul_pow]
        ring
      _ ≤ (β ^ 2 * t ^ 2 * ‖ρ‖) * (β * t) ^ k / (k.factorial : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by ring
  calc
    _ ≤ (β ^ 2 * t ^ 2 * ‖ρ‖) * Real.exp (β * t) := hb
    _ ≤ (β ^ 2 * t ^ 2 * ‖ρ‖) * Real.exp β :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_of_le_one_right hβ ht1)) (by positivity)
    _ = _ := by ring

/-- The index equivalence converting the local flattened Choi indexing to the output-input
product indexing. -/
private noncomputable def choiIndexEquiv (D E : ℕ) :
    Fin (D * E) ≃ Fin E × Fin D :=
  finProdFinEquiv.symm.trans (Equiv.prodComm (Fin D) (Fin E))

/-- The local Choi matrix is the Physlib Choi matrix reindexed along `choiIndexEquiv`. -/
private theorem choiMatrix_reindex {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    ChoiMatrix T = (MatrixMap.choi_matrix T).submatrix
      (choiIndexEquiv D E) (choiIndexEquiv D E) := by
  ext p q
  change T (matrixUnit (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 =
    T (Matrix.single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 1)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2
  have hu : matrixUnit (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 =
      Matrix.single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 (1 : ℂ) := by
    ext a b
    simp [matrixUnit, Matrix.single, Prod.mk.injEq, eq_comm, ite_and]
  rw [hu]

/-- A Physlib Kraus-form map possesses a Kraus family with the local fixed-size indexing. -/
private theorem krausFamily_of_physlib {D E : ℕ}
    (K : (Fin E × Fin D) → Matrix (Fin E) (Fin D) ℂ) :
    HasKrausFamily (MatrixMap.of_kraus K K) := by
  classical
  let e : Fin (D * D * E * E) ≃ (Fin E × Fin D) × (Fin E × Fin D) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_prod]; ring)
  let K' : Fin (D * D * E * E) → Matrix (Fin E) (Fin D) ℂ :=
    fun j => if (e j).1 = (e j).2 then K (e j).1 else 0
  refine ⟨K', fun ρ => ?_⟩
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  symm
  calc
    _ = ∑ j : (Fin E × Fin D) × (Fin E × Fin D),
        (if j.1 = j.2 then K j.1 else 0) * ρ *
          (if j.1 = j.2 then K j.1 else 0)ᴴ :=
      e.sum_comp _
    _ = _ := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj
        simp [Ne.symm hbj]
      · simp

/-- A complex-linear matrix map possesses a finite Kraus family exactly when its Choi matrix is
positive semidefinite [Choi1975]. -/
theorem hasKrausFamily_iff_choi_posSemidef {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) :
    HasKrausFamily T ↔ (ChoiMatrix T).PosSemidef := by
  constructor
  · rintro ⟨K, hK⟩
    have heq : T = MatrixMap.of_kraus K K := by
      ext ρ a b
      simpa [MatrixMap.of_kraus] using! congrFun (congrFun (hK ρ) a) b
    rw [choiMatrix_reindex, heq]
    exact ((MatrixMap.choi_PSD_iff_CP_map _).mp
      (MatrixMap.of_kraus_CP K)).submatrix _
  · intro h
    have hphys : (MatrixMap.choi_matrix T).PosSemidef := by
      have hs := h.submatrix (choiIndexEquiv D E).symm
      rw [choiMatrix_reindex] at hs
      simpa [Matrix.submatrix_submatrix] using! hs
    obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus T
      ((MatrixMap.choi_PSD_iff_CP_map T).mpr hphys)
    rw [hK]
    exact krausFamily_of_physlib K

/-- The drift operator `-i * G.ham - (1 / 2) * ∑ j, (G.jumps j)ᴴ * G.jumps j`. -/
noncomputable def gkslDrift {D : ℕ} (G : GKSL D) : Operator D :=
  (-Complex.I) • G.ham - (1 / 2 : ℂ) • ∑ j, (G.jumps j)ᴴ * G.jumps j

/-- The Euler Kraus family with drift step `1 + h * gkslDrift G` and jump steps `√h * G.jumps
j`. -/
noncomputable def gkslEulerKraus {D : ℕ} (G : GKSL D) (h : ℝ) :
    Option (Fin (D * D)) → Operator D
  | none => 1 + (h : ℂ) • gkslDrift G
  | some j => (Real.sqrt h : ℂ) • G.jumps j

/-- The completely positive Euler map defined by `gkslEulerKraus`. -/
noncomputable def gkslEulerMap {D : ℕ} (G : GKSL D) (h : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  MatrixMap.of_kraus (gkslEulerKraus G h) (gkslEulerKraus G h)

/-- The Kraus-form Euler map is completely positive for every real step parameter. -/
theorem gkslEulerMap_cp {D : ℕ} (G : GKSL D) (h : ℝ) :
    MatrixMap.IsCompletelyPositive (gkslEulerMap G h) :=
  MatrixMap.of_kraus_CP _

/-- Computes the conjugate transpose of the GKSL drift using Hermiticity of the Hamiltonian. -/
private theorem gkslDrift_conjTranspose {D : ℕ} (G : GKSL D) :
    (gkslDrift G)ᴴ = Complex.I • G.ham - (1 / 2 : ℂ) •
      ∑ j, (G.jumps j)ᴴ * G.jumps j := by
  simp [gkslDrift, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, G.hamHermitian.eq]

/-- Expresses the Lindblad generator as left drift, right adjoint drift, and the jump Kraus sum. -/
private theorem lindbladApply_drift {D : ℕ} (G : GKSL D) (ρ : Operator D) :
    lindbladApply G ρ = gkslDrift G * ρ + ρ * (gkslDrift G)ᴴ +
      ∑ j, G.jumps j * ρ * (G.jumps j)ᴴ := by
  rw [gkslDrift_conjTranspose]
  simp only [gkslDrift, lindbladApply, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_mul, Matrix.mul_sum,
    Finset.sum_sub_distrib, smul_add, Finset.sum_add_distrib, ← Finset.smul_sum, Matrix.mul_assoc]
  module

/-- For nonnegative step size, the Euler map equals identity plus the linear generator step and
the explicit quadratic drift term. -/
theorem gkslEulerMap_taylor {D : ℕ} (G : GKSL D) (h : ℝ) (hh : 0 ≤ h)
    (ρ : Operator D) :
    gkslEulerMap G h ρ = ρ + (h : ℂ) • lindbladApply G ρ +
      ((h : ℂ) ^ 2) • (gkslDrift G * ρ * (gkslDrift G)ᴴ) := by
  have hroot : (Real.sqrt h : ℂ) * (Real.sqrt h : ℂ) = (h : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hh
  have hmain (K : Operator D) :
      (1 + (h : ℂ) • K) * ρ * (1 + (h : ℂ) • K)ᴴ =
        ρ + (h : ℂ) • (K * ρ + ρ * Kᴴ) +
          ((h : ℂ) ^ 2) • (K * ρ * Kᴴ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  change (MatrixMap.of_kraus _ _) ρ = _
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_option, gkslEulerKraus]
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hroot]
  rw [hmain, lindbladApply_drift, smul_add, ← Finset.smul_sum]
  module

/-- Bounds the Euler map's first-order remainder by `h^2 * ‖gkslDrift G‖^2 * ‖ρ‖`. -/
theorem norm_gkslEulerMap_sub_linear {D : ℕ} (G : GKSL D) (h : ℝ) (hh : 0 ≤ h)
    (ρ : Operator D) :
    ‖gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ‖ ≤
      h ^ 2 * ‖gkslDrift G‖ ^ 2 * ‖ρ‖ := by
  have heq : gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ =
      ((h : ℂ) ^ 2) • (gkslDrift G * ρ * (gkslDrift G)ᴴ) := by
    rw [gkslEulerMap_taylor G h hh ρ]
    have hs : (h : ℂ) • lindbladApply G ρ = h • lindbladApply G ρ := by
      ext i j
      simp
    rw [hs]
    abel
  rw [heq, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hh]
  have hp : ‖gkslDrift G * ρ * (gkslDrift G)ᴴ‖ ≤ ‖gkslDrift G‖ ^ 2 * ‖ρ‖ := by
    calc
      _ ≤ ‖gkslDrift G * ρ‖ * ‖(gkslDrift G)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖gkslDrift G‖ * ‖ρ‖) * ‖gkslDrift G‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)

/-- For `0 ≤ h ≤ 1`, bounds the difference between one Euler step and exact evolution by the
stated quadratic local-error constant. -/
theorem norm_gkslEulerMap_sub_semigroup {D : ℕ} (G : GKSL D) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ρ : Operator D) :
    ‖gkslEulerMap G h ρ - lindbladSemigroup G h ρ‖ ≤
      (‖gkslDrift G‖ ^ 2 +
        (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) ^ 2 *
          Real.exp (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2)) * h ^ 2 * ‖ρ‖ := by
  have heq : gkslEulerMap G h ρ - lindbladSemigroup G h ρ =
      (gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ) -
        (lindbladSemigroup G h ρ - ρ - h • lindbladApply G ρ) := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans
    ((add_le_add (norm_gkslEulerMap_sub_linear G h hh ρ)
      (lindbladSemigroup_taylor_one_le G h hh hh1 ρ)).trans_eq (by ring))

/-- For `0 ≤ h ≤ 1`, bounds Euler-map norm growth by the exponential of the generator bound plus
the squared drift norm. -/
theorem norm_gkslEulerMap_le {D : ℕ} (G : GKSL D) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ρ : Operator D) :
    ‖gkslEulerMap G h ρ‖ ≤
      Real.exp ((2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2 + ‖gkslDrift G‖ ^ 2) * h) * ‖ρ‖ := by
  let β : ℝ := 2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have heq : gkslEulerMap G h ρ = (ρ + h • lindbladApply G ρ) +
      (gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ) := by abel
  have hl : ‖h • lindbladApply G ρ‖ ≤ h * β * ‖ρ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (norm_lindbladApply_le G ρ) hh).trans_eq (by ring)
  have hsq : h ^ 2 ≤ h := by nlinarith
  calc
    _ = ‖(ρ + h • lindbladApply G ρ) +
        (gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ)‖ := congrArg norm heq
    _ ≤ (‖ρ‖ + ‖h • lindbladApply G ρ‖) +
        ‖gkslEulerMap G h ρ - ρ - h • lindbladApply G ρ‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (‖ρ‖ + h * β * ‖ρ‖) + h ^ 2 * ‖gkslDrift G‖ ^ 2 * ‖ρ‖ :=
      add_le_add (add_le_add (le_refl _) hl) (norm_gkslEulerMap_sub_linear G h hh ρ)
    _ ≤ (‖ρ‖ + h * β * ‖ρ‖) + h * ‖gkslDrift G‖ ^ 2 * ‖ρ‖ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (norm_nonneg _))
    _ = (1 + (β + ‖gkslDrift G‖ ^ 2) * h) * ‖ρ‖ := by ring
    _ ≤ Real.exp ((β + ‖gkslDrift G‖ ^ 2) * h) * ‖ρ‖ :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp ((β + ‖gkslDrift G‖ ^ 2) * h)]) (norm_nonneg _)

/-- The Lindblad evolution at time zero is the identity on operators. -/
theorem lindbladSemigroup_zero_apply {D : ℕ} (G : GKSL D) (ρ : Operator D) :
    lindbladSemigroup G 0 ρ = ρ := by
  rw [lindbladSemigroup, tsum_eq_single 0]
  · simp
  · intro k hk
    rcases k with _ | k
    · exact (hk rfl).elim
    · simp

/-- Bounds the error of `n` Euler steps against evolution at time `n * h` by the stated
accumulated quadratic local error and exponential growth factor. -/
theorem gkslEulerMap_iterate_error {D : ℕ} (G : GKSL D) (h : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (n : ℕ) (ρ : Operator D) :
    ‖((gkslEulerMap G h)^[n]) ρ - lindbladSemigroup G ((n : ℝ) * h) ρ‖ ≤
      (n : ℝ) * (‖gkslDrift G‖ ^ 2 +
        (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2) ^ 2 *
          Real.exp (2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2)) * h ^ 2 *
        Real.exp ((2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2 + ‖gkslDrift G‖ ^ 2) *
          ((n : ℝ) * h)) * ‖ρ‖ := by
  let β : ℝ := 2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2
  let c : ℝ := β + ‖gkslDrift G‖ ^ 2
  let C : ℝ := ‖gkslDrift G‖ ^ 2 + β ^ 2 * Real.exp β
  have hc : 0 ≤ c := by dsimp [c, β]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbc : β ≤ c := le_add_of_nonneg_right (sq_nonneg _)
  have hsN (n : ℕ) :
      ‖lindbladSemigroup G ((n : ℝ) * h) ρ‖ ≤ Real.exp (c * ((n : ℝ) * h)) * ‖ρ‖ := by
    apply (norm_lindbladSemigroup_le G ((n : ℝ) * h) (by positivity) ρ).trans
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbc (by positivity))) (norm_nonneg _)
  change ‖((gkslEulerMap G h)^[n]) ρ - lindbladSemigroup G ((n : ℝ) * h) ρ‖ ≤
    (n : ℝ) * C * h ^ 2 * Real.exp (c * ((n : ℝ) * h)) * ‖ρ‖
  induction n with
  | zero => simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
    have htime : ((n + 1 : ℕ) : ℝ) * h = h + (n : ℝ) * h := by push_cast; ring
    have hE : Real.exp (c * ((n : ℝ) * h)) ≤ Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hc
      apply mul_le_mul_of_nonneg_right _ hh
      exact_mod_cast Nat.le_succ n
    have hprod : Real.exp (c * h) * Real.exp (c * ((n : ℝ) * h)) =
        Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hfirst : Real.exp (c * h) *
        ((n : ℝ) * C * h ^ 2 * Real.exp (c * ((n : ℝ) * h)) * ‖ρ‖) =
        (n : ℝ) * C * h ^ 2 * Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) * ‖ρ‖ := by
      calc
        _ = (n : ℝ) * C * h ^ 2 *
            (Real.exp (c * h) * Real.exp (c * ((n : ℝ) * h))) * ‖ρ‖ := by ring
        _ = _ := by rw [hprod]
    have hlocal : ‖gkslEulerMap G h (lindbladSemigroup G ((n : ℝ) * h) ρ) -
        lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) ρ)‖ ≤
        C * h ^ 2 * Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) * ‖ρ‖ := by
      apply (norm_gkslEulerMap_sub_semigroup G h hh hh1 _).trans
      calc
        _ ≤ C * h ^ 2 * (Real.exp (c * ((n : ℝ) * h)) * ‖ρ‖) :=
          mul_le_mul_of_nonneg_left (hsN n) (by positivity)
        _ ≤ C * h ^ 2 * (Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) * ‖ρ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) (by positivity)
        _ = _ := by ring
    rw [Function.iterate_succ_apply', htime, lindbladSemigroup_add]
    have hd : gkslEulerMap G h (((gkslEulerMap G h)^[n]) ρ) -
        lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) ρ) =
        gkslEulerMap G h (((gkslEulerMap G h)^[n]) ρ - lindbladSemigroup G ((n : ℝ) * h) ρ) +
          (gkslEulerMap G h (lindbladSemigroup G ((n : ℝ) * h) ρ) -
            lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) ρ)) := by
      rw [map_sub]
      abel
    rw [hd]
    calc
      _ ≤ Real.exp (c * h) *
          ‖((gkslEulerMap G h)^[n]) ρ - lindbladSemigroup G ((n : ℝ) * h) ρ‖ +
          C * h ^ 2 * Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) * ‖ρ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_gkslEulerMap_le G h hh hh1 _) hlocal)
      _ ≤ Real.exp (c * h) *
          ((n : ℝ) * C * h ^ 2 * Real.exp (c * ((n : ℝ) * h)) * ‖ρ‖) +
          C * h ^ 2 * Real.exp (c * (((n + 1 : ℕ) : ℝ) * h)) * ‖ρ‖ :=
        add_le_add (mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)) (le_refl _)
      _ = _ := by rw [hfirst]; push_cast; ring_nf

open Filter
open scoped Topology

/-- For nonnegative `t`, Euler iteration with `n + ⌈t⌉ + 1` steps of size `t / (n + ⌈t⌉ + 1)`
converges to evolution at time `t`. -/
theorem gkslEulerMap_tendsto {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t)
    (ρ : Operator D) :
    Tendsto (fun n : ℕ => ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) ρ)
      atTop (𝓝 (lindbladSemigroup G t ρ)) := by
  let β : ℝ := 2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2
  let C : ℝ := ‖gkslDrift G‖ ^ 2 + β ^ 2 * Real.exp β
  let c : ℝ := β + ‖gkslDrift G‖ ^ 2
  let K : ℝ := C * t ^ 2 * Real.exp (c * t) * ‖ρ‖
  have hbound (n : ℕ) :
      ‖((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) ρ -
        lindbladSemigroup G t ρ‖ ≤ K / (n + Nat.ceil t + 1 : ℕ) := by
    let m : ℕ := n + Nat.ceil t + 1
    have hm : (0 : ℝ) < m := by dsimp [m]; positivity
    have htm : t ≤ (m : ℝ) := by
      calc
        t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
        _ ≤ m := by exact_mod_cast (show Nat.ceil t ≤ m by dsimp [m]; omega)
    have hh : 0 ≤ t / (m : ℝ) := div_nonneg ht hm.le
    have hh1 : t / (m : ℝ) ≤ 1 := (div_le_one hm).mpr htm
    have htime : (m : ℝ) * (t / (m : ℝ)) = t := mul_div_cancel₀ t (ne_of_gt hm)
    have he := gkslEulerMap_iterate_error G (t / (m : ℝ)) hh hh1 m ρ
    rw [htime] at he
    apply he.trans_eq
    change (m : ℝ) * C * (t / (m : ℝ)) ^ 2 * Real.exp (c * t) * ‖ρ‖ = K / m
    dsimp [K]
    field_simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  have hlim := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) K).comp
    (tendsto_add_atTop_nat (Nat.ceil t + 1))
  simpa only [Nat.add_assoc] using! hlim

/-- The complex-linear map underlying Lindblad evolution at a nonnegative time. -/
noncomputable def lindbladSemigroupMap {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t) :
    Operator D →ₗ[ℂ] Operator D where
  toFun := lindbladSemigroup G t
  map_add' ρ σ := by
    have h := (gkslEulerMap_tendsto G t ht ρ).add (gkslEulerMap_tendsto G t ht σ)
    have heq (n : ℕ) :
        ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) (ρ + σ) =
          ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) ρ +
            ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) σ := by
      simp only [← Module.End.pow_apply, map_add]
    exact tendsto_nhds_unique (gkslEulerMap_tendsto G t ht (ρ + σ)) (by simpa only [heq] using! h)
  map_smul' z ρ := by
    have h := (gkslEulerMap_tendsto G t ht ρ).const_smul z
    have heq (n : ℕ) :
        ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) (z • ρ) =
          z • ((gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ)))^[n + Nat.ceil t + 1]) ρ := by
      simp only [← Module.End.pow_apply, map_smul]
    exact tendsto_nhds_unique (gkslEulerMap_tendsto G t ht (z • ρ)) (by simpa only [heq] using! h)

/-- Every natural power of a Kraus-form Euler map is completely positive. -/
theorem gkslEulerMap_pow_cp {D : ℕ} (G : GKSL D) (h : ℝ) (n : ℕ) :
    MatrixMap.IsCompletelyPositive ((gkslEulerMap G h) ^ n) := by
  induction n with
  | zero => exact MatrixMap.IsCompletelyPositive.id
  | succ n ih =>
    rw [pow_succ]
    exact (gkslEulerMap_cp G h).comp ih

/-- The Lindblad evolution map is completely positive for nonnegative time [Lindblad1976]. -/
theorem lindbladSemigroupMap_cp {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t) :
    MatrixMap.IsCompletelyPositive (lindbladSemigroupMap G t ht) := by
  rw [MatrixMap.choi_PSD_iff_CP_map]
  let T (n : ℕ) := (gkslEulerMap G (t / (n + Nat.ceil t + 1 : ℕ))) ^ (n + Nat.ceil t + 1)
  have hpos (n : ℕ) : (MatrixMap.choi_matrix (T n)).PosSemidef :=
    (MatrixMap.choi_PSD_iff_CP_map _).mp (gkslEulerMap_pow_cp G _ _)
  have hlim : Tendsto (fun n => MatrixMap.choi_matrix (T n)) atTop
      (𝓝 (MatrixMap.choi_matrix (lindbladSemigroupMap G t ht))) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    have h := gkslEulerMap_tendsto G t ht (Matrix.single a.2 b.2 1)
    have he := ((continuous_apply b.1).comp (continuous_apply a.1)).tendsto
      (lindbladSemigroup G t (Matrix.single a.2 b.2 1))
    simpa only [T, MatrixMap.choi_matrix, Matrix.of_apply, Module.End.pow_apply,
      lindbladSemigroupMap, LinearMap.coe_mk, AddHom.coe_mk] using! he.comp h
  exact HermitianMat.Matrix.PosSemiDef_isClosed.mem_of_tendsto hlim (Eventually.of_forall hpos)

/-- At every nonnegative time, the Lindblad evolution possesses a finite Kraus family. -/
theorem lindbladSemigroup_hasKrausFamily {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t) :
    HasKrausFamily (lindbladSemigroupMap G t ht) := by
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus
    (lindbladSemigroupMap G t ht) (lindbladSemigroupMap_cp G t ht)
  rw [hK]
  exact krausFamily_of_physlib K

/-- Lindblad evolution at nonnegative time preserves density operators. -/
theorem lindbladSemigroup_isDensityOperator {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    IsDensityOperator (lindbladSemigroup G t ρ) := by
  exact ⟨(lindbladSemigroupMap_cp G t ht).IsPositive hρ.1,
    (trace_lindbladSemigroup G t ρ).trans hρ.2⟩

/-- The KMS pairing is additive in its first operator argument. -/
private theorem inner_add_left {D : ℕ} (ρ X Y Z : Operator D) :
    kmsInner ρ (X + Y) Z = kmsInner ρ X Z + kmsInner ρ Y Z := by
  rw [kmsInner_conjSym, kmsInner_add_right]
  simp only [star_add]
  rw [← kmsInner_conjSym, ← kmsInner_conjSym]

/-- The KMS pairing is complex-linear in its second operator argument. -/
private theorem inner_smul_right {D : ℕ} (ρ X Y : Operator D) (z : ℂ) :
    kmsInner ρ X (z • Y) = z * kmsInner ρ X Y := by
  simp only [kmsInner, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The KMS pairing is conjugate-linear in its first operator argument. -/
private theorem inner_smul_left {D : ℕ} (ρ X Y : Operator D) (z : ℂ) :
    kmsInner ρ (z • X) Y = star z * kmsInner ρ X Y := by
  rw [kmsInner_conjSym, inner_smul_right]
  simp only [star_mul]
  rw [← kmsInner_conjSym, mul_comm]

/-- For a positive-definite reference, a KMS-self-adjoint map with zero real diagonal pairing is
the zero map. -/
private theorem kms_selfAdjoint_eq_zero_of_diagonal {D : ℕ} {ρ : Operator D}
    (hρ : ρ.PosDef) (N : Operator D →ₗ[ℂ] Operator D)
    (hN : KmsSelfAdjoint ρ N) (hdiag : ∀ X, (kmsInner ρ X (N X)).re = 0) : N = 0 := by
  have hzero (X : Operator D) : kmsInner ρ X (N X) = 0 := by
    have hs := (hN X X).trans (kmsInner_conjSym ρ (N X) X)
    apply Complex.ext
    · exact hdiag X
    · have hi := congrArg Complex.im hs
      simp only [Complex.star_def, Complex.conj_im] at hi
      change (kmsInner ρ X (N X)).im = 0
      linarith
  have hall (X Y : Operator D) : kmsInner ρ X (N Y) = 0 := by
    have hp := hzero (X + Y)
    simp only [map_add, kmsInner_add_right, inner_add_left, hzero, zero_add, add_zero] at hp
    have hI := hzero (X + Complex.I • Y)
    simp only [map_add, map_smul, kmsInner_add_right, inner_add_left,
      inner_smul_left, inner_smul_right, hzero, mul_zero, add_zero, zero_add,
      Complex.star_def, Complex.conj_I] at hI
    have hs : kmsInner ρ X (N Y) = kmsInner ρ Y (N X) := by
      have hh : Complex.I * (kmsInner ρ X (N Y) - kmsInner ρ Y (N X)) = 0 := by
        linear_combination hI
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left Complex.I_ne_zero)
    rw [← hs] at hp
    have hh : (2 : ℂ) * kmsInner ρ X (N Y) = 0 := by linear_combination hp
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  ext Y a b
  have hh := hall (N Y) Y
  have hz : kmsNorm ρ (N Y) = 0 := by simp only [kmsNorm, hh, Complex.zero_re, Real.sqrt_zero]
  have heq := (kmsNorm_eq_zero_iff hρ _).mp hz
  exact congrFun (congrFun heq a) b

/-- For a positive-definite reference, the jump-family KMS generator is KMS-self-adjoint. -/
private theorem family_selfadjoint {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (A : Fin (D * D) → Operator D) : KmsSelfAdjoint ρ (kmsGeneratorFam ρ A) := by
  intro X Y
  simp only [kmsGeneratorFam, LinearMap.sum_apply]
  rw [kmsInner_sum_right, kmsInner_conjSym, kmsInner_sum_right, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← kmsInner_conjSym]
  exact kmsGenerator_selfAdjoint hρ (A i) X Y

/-- The Lindblad map of a KMS normal form equals its jump-family KMS generator. -/
private theorem normal_form_map_eq {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (h : KMSNormalForm G ρ) : lindbladMap G = kmsGeneratorFam ρ G.jumps := by
  obtain ⟨_hden, hρ, H, β, _heq, hself, hdir⟩ := h
  have hK := family_selfadjoint hρ G.jumps
  have hN : KmsSelfAdjoint ρ (lindbladMap G - kmsGeneratorFam ρ G.jumps) := by
    intro X Y
    change kmsInner ρ X (lindbladMap G Y - kmsGeneratorFam ρ G.jumps Y) =
      kmsInner ρ (lindbladMap G X - kmsGeneratorFam ρ G.jumps X) Y
    rw [kmsInner_sub_right, kmsInner_conjSym ρ (_ - _) Y, kmsInner_sub_right, star_sub,
      ← kmsInner_conjSym ρ _ Y, ← kmsInner_conjSym ρ _ Y]
    rw [hself, hK]
  have hz : lindbladMap G - kmsGeneratorFam ρ G.jumps = 0 := by
    apply kms_selfAdjoint_eq_zero_of_diagonal hρ _ hN
    intro X
    have hd := hdir X
    simp only [kmsDirichlet, kmsInner_neg_right, Complex.neg_re] at hd
    change (kmsInner ρ X (lindbladMap G X - kmsGeneratorFam ρ G.jumps X)).re = 0
    rw [kmsInner_sub_right, Complex.sub_re]
    linarith
  exact sub_eq_zero.mp hz

/-- For a positive-definite reference, pairing its inverse with an operator in the KMS inner
product gives the operator's trace. -/
private theorem inner_inv_left {D : ℕ} {ρ : Operator D} (hρ : ρ.PosDef) (Y : Operator D) :
    kmsInner ρ ρ⁻¹ Y = Matrix.trace Y := by
  have hunit : IsUnit ρ.det := IsUnit.mk0 _ (Matrix.PosDef.det_pos hρ).ne'
  have hL : ρ⁻¹ * ρ = 1 := Matrix.nonsing_inv_mul _ hunit
  have hR : ρ * ρ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  let S : Operator D := CFC.sqrt ρ
  have hS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have hcom : S * ρ = ρ * S := by rw [← hS, Matrix.mul_assoc]
  have hcomI : S * ρ⁻¹ = ρ⁻¹ * S := by
    calc
      _ = (ρ⁻¹ * ρ) * S * ρ⁻¹ := by rw [hL, Matrix.one_mul]
      _ = ρ⁻¹ * (ρ * S) * ρ⁻¹ := by noncomm_ring
      _ = ρ⁻¹ * (S * ρ) * ρ⁻¹ := by rw [hcom]
      _ = ρ⁻¹ * S := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hSI : S * ρ⁻¹ * S = 1 := by rw [hcomI, Matrix.mul_assoc, hS, hL]
  change Matrix.trace ((ρ⁻¹)ᴴ * S * Y * S) = _
  rw [hρ.isHermitian.inv.eq, Matrix.trace_mul_comm _ S]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSI, Matrix.one_mul]

/-- A reference in KMS normal form is annihilated by the Lindblad generator. -/
private theorem normal_form_generator_zero {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (h : KMSNormalForm G ρ) : lindbladApply G ρ = 0 := by
  have hρ := h.2.1
  have heq := normal_form_map_eq G ρ h
  have hdir0 : kmsDirichlet ρ (kmsGeneratorFam ρ G.jumps) ρ⁻¹ = 0 := by
    rw [← heq]
    unfold kmsDirichlet
    rw [inner_inv_left hρ, Matrix.trace_neg]
    change (-Matrix.trace (lindbladApply G ρ⁻¹)).re = 0
    rw [trace_lindbladApply]
    simp only [neg_zero, Complex.zero_re]
  have hsum := (kmsGeneratorFam_dirichlet_self hρ G.jumps ρ⁻¹).symm.trans hdir0
  have hinv (j : Fin (D * D)) : G.jumps j * ρ⁻¹ = ρ⁻¹ * G.jumps j := by
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (kmsNorm ρ (G.jumps i * ρ⁻¹ - ρ⁻¹ * G.jumps i)))).mp hsum j
      (Finset.mem_univ j)
    have hz : kmsNorm ρ (G.jumps j * ρ⁻¹ - ρ⁻¹ * G.jumps j) = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp hterm
    exact sub_eq_zero.mp ((kmsNorm_eq_zero_iff hρ _).mp hz)
  have hunit : IsUnit ρ.det := IsUnit.mk0 _ (Matrix.PosDef.det_pos hρ).ne'
  have hL : ρ⁻¹ * ρ = 1 := Matrix.nonsing_inv_mul _ hunit
  have hR : ρ * ρ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcomm (j : Fin (D * D)) : G.jumps j * ρ = ρ * G.jumps j := by
    calc
      _ = (ρ * ρ⁻¹) * G.jumps j * ρ := by rw [hR, Matrix.one_mul]
      _ = ρ * (ρ⁻¹ * G.jumps j) * ρ := by noncomm_ring
      _ = ρ * (G.jumps j * ρ⁻¹) * ρ := by rw [hinv]
      _ = ρ * G.jumps j := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one]
  change lindbladMap G ρ = 0
  rw [heq]
  exact (kmsGeneratorFam_kernel hρ G.jumps ρ).mpr hcomm

/-- An operator annihilated by the generator is stationary under all nonnegative-time Lindblad
evolution. -/
theorem stationary_of_generator_zero {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (hρ : lindbladApply G ρ = 0) : IsStationary G ρ := by
  intro t _ht
  rw [lindbladSemigroup, tsum_eq_single 0]
  · simp
  · intro k hk
    rcases k with _ | k
    · exact (hk rfl).elim
    · have hz : ((lindbladMap G)^[k + 1]) ρ = 0 := by
        rw [Function.iterate_succ_apply]
        change ((lindbladMap G)^[k]) (lindbladApply G ρ) = 0
        rw [hρ, ← Module.End.pow_apply]
        exact map_zero _
      rw [hz, smul_zero]

/-- A reference in KMS normal form is stationary. -/
theorem stationary_of_kmsNormalForm {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (h : KMSNormalForm G ρ) : IsStationary G ρ :=
  stationary_of_generator_zero G ρ (normal_form_generator_zero G ρ h)

/-- The generator norm bound `2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖^2`. -/
private noncomputable def lindbladGeneratorBound {D : ℕ} (G : GKSL D) : ℝ :=
  2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2

/-- The complex-linear Kraus-sum map associated with the family `K`. -/
private noncomputable def krausMap {D : ℕ} (K : Fin (D * D * D * D) → Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun ρ := ∑ j, K j * ρ * (K j)ᴴ
  map_add' := by
    intro ρ σ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c ρ
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- For nonnegative time, provides a finite Kraus representation of Lindblad evolution together
with trace preservation and density-operator preservation [Lindblad1976]. -/
theorem lindbladSemigroup_cptp {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t) :
    ∃ K : Fin (D * D * D * D) → Operator D,
      (∀ ρ : Operator D, lindbladSemigroup G t ρ = ∑ j, K j * ρ * (K j)ᴴ) ∧
        HasKrausFamily (krausMap K) ∧
        (∀ ρ : Operator D, Matrix.trace (lindbladSemigroup G t ρ) = Matrix.trace ρ) ∧
        (∀ ρ : Operator D, IsDensityOperator ρ → IsDensityOperator (lindbladSemigroup G t ρ)) := by
  obtain ⟨K, hK⟩ := lindbladSemigroup_hasKrausFamily G t ht
  refine ⟨K, hK, ⟨K, fun _ => rfl⟩, trace_lindbladSemigroup G t, ?_⟩
  exact lindbladSemigroup_isDensityOperator G t ht

/-- Collects the nonnegative-time semigroup law, first-order error and norm bounds, Kraus and
density-preservation properties, KMS-normal-form stationarity, and the Kraus-Choi
equivalence [Lindblad1976]. -/
theorem g1 :
(∀ (D : ℕ) (G : GKSL D),

    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ ρ : Operator D,
        lindbladSemigroup G (s + t) ρ = lindbladSemigroup G s (lindbladSemigroup G t ρ)) ∧

    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ρ : Operator D,
        ‖lindbladSemigroup G t ρ - ρ - t • lindbladApply G ρ‖
          ≤ (lindbladGeneratorBound G) ^ 2 * Real.exp (lindbladGeneratorBound G)
              * t ^ 2 * ‖ρ‖) ∧

    (∀ t : ℝ, 0 ≤ t →
        ∃ K : Fin (D * D * D * D) → Operator D,
          (∀ ρ : Operator D, lindbladSemigroup G t ρ = ∑ j, K j * ρ * (K j)ᴴ) ∧
            HasKrausFamily (krausMap K) ∧
            (∀ ρ : Operator D, Matrix.trace (lindbladSemigroup G t ρ) = Matrix.trace ρ) ∧
            (∀ ρ : Operator D, IsDensityOperator ρ →
                IsDensityOperator (lindbladSemigroup G t ρ))) ∧

    (∀ t : ℝ, 0 ≤ t → ∀ ρ : Operator D,
        ‖lindbladSemigroup G t ρ‖
          ≤ Real.exp (lindbladGeneratorBound G * t) * ‖ρ‖) ∧

    (∀ ρ : Operator D, KMSNormalForm G ρ →
        IsStationary G ρ ∧ KmsSelfAdjoint ρ (lindbladMap G) ∧
          ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
            = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O)) ∧

  (∀ (D E : ℕ) (T : Operator D →ₗ[ℂ] Operator E),
      HasKrausFamily T ↔ (ChoiMatrix T).PosSemidef) := by
  constructor
  · intro D G
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u v _hu _hv ρ
      exact lindbladSemigroup_add G u v ρ
    · intro u hu hu1 ρ
      exact lindbladSemigroup_taylor_one_le G u hu hu1 ρ
    · intro u hu
      exact lindbladSemigroup_cptp G u hu
    · intro u hu ρ
      exact norm_lindbladSemigroup_le G u hu ρ
    · intro ρ h
      refine ⟨stationary_of_kmsNormalForm G ρ h, ?_⟩
      obtain ⟨_hdensity, _hpos, H, β, _heq, hself, hdir⟩ := h
      exact ⟨hself, hdir⟩
  · intro D E T
    exact hasKrausFamily_iff_choi_posSemidef T
open Filter
open scoped Topology

/-- The dissipative Lindblad sum built from the thermal Kraus family. -/
private noncomputable def ckLindbladApply (D : ℕ) (E : Fin D → ℝ) (β : ℝ)
    (ρ : Operator D) : Operator D :=
  ∑ p : Fin D × Fin D × Bool,
    (thermalKraus D E β p * ρ * (thermalKraus D E β p)ᴴ -
      (1 / 2 : ℂ) • ((thermalKraus D E β p)ᴴ * thermalKraus D E β p * ρ +
          ρ * (thermalKraus D E β p)ᴴ * thermalKraus D E β p))

/-- Specifies a positive-dimensional GKSL generator with diagonal energy Hamiltonian whose
action equals the thermal-Kraus dissipative sum. -/
private def IsCKGenerator {D : ℕ} (G : GKSL D) (E : Fin D → ℝ) (β : ℝ) : Prop :=
  0 < D ∧ (∀ i j : Fin D, G.ham i j = if i = j then ((E i : ℝ) : ℂ) else 0) ∧
    ∀ ρ : Operator D, lindbladApply G ρ = ckLindbladApply D E β ρ

/-- The time average of Lindblad evolution over `[0, T]`, multiplied by `T⁻¹`. -/
private noncomputable def boxFilteredState {D : ℕ} (G : GKSL D) (T : ℝ)
    (ρ : Operator D) : Operator D :=
  (T⁻¹ : ℝ) • ∫ s in (0 : ℝ)..T, lindbladSemigroup G s ρ
end Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
