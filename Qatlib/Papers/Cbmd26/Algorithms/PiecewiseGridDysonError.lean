/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.PiecewiseGridFreeze
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid

/-!
# Dyson Error on Supplied Piecewise Grids

This module compares a discrete Dyson expansion with sampled Hamiltonian evolution for bounded
Hermitian fields, allowing discontinuities. `dyson_grid_euler_error_discontinuous` controls the
finite-grid Euler error, and `dyson_grid_truncation_sample_error_discontinuous` adds the
factorial truncation tail when the norm-time product is at most `Real.log 2`.

For a monotone supplied breakpoint grid, the sampled evolution is identified with the frozen
table from `suppliedFrozenTable`. `suppliedGrid_dyson_error_budget` combines the freezing and
Euler errors into `suppliedGridErrorConstant / M` and retains the explicit truncation tail. See
[WangEtAl2026].

## Main statements

* `dyson_grid_euler_error_discontinuous` gives an error bounded by `exp (Λ*t) * Λ^2 * t^2 /
  (2*M)`.
* `suppliedGrid_dyson_truncation_error` combines freezing, Euler discretization, and Dyson
  truncation errors.
* `suppliedGrid_dyson_error_budget` packages the grid-dependent terms using
  `suppliedGridErrorConstant`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Bounds the error between one Euler factor for `B` and its exact Hamiltonian evolution by
`exp (Λ * h) * (Λ * h)^2 / 2`, for nonnegative step and norm bound. -/
private theorem dyson_euler_factor_error
    (B : Matrix I I ℂ) (h Λ : ℝ) (hh : 0 ≤ h) (hΛ : 0 ≤ Λ) (hB : ‖B‖ ≤ Λ) :
    ‖(1 - (h : ℂ) • (Complex.I • B)) - HamiltonianEvolution B h‖ ≤
      Real.exp (Λ * h) * (Λ * h) ^ 2 / 2 := by
  have hb : ∀ u ∈ Set.uIcc (0 : ℝ) h, ‖(fun _ => Complex.I • B) u‖ ≤ Λ := by
    intro u _
    simpa [norm_smul] using! hB
  have ht := dyson_finite_prefix_explicit_factorial_tail I (fun _ => Complex.I • B)
    0 h Λ 1 continuous_const hΛ hb
  have hp : dysonPrefix (fun _ => Complex.I • B) 0 h 1 =
      1 - (h : ℂ) • (Complex.I • B) := by
    simp [dysonPrefix, Finset.sum_range_succ, orderedDysonTerm,
      intervalIntegral.integral_const, sub_eq_add_neg]
    rw [smul_comm]
  rw [hp, orderedEvolution_constant_hamiltonian, sub_zero, norm_sub_rev] at ht
  simpa [abs_of_nonneg hh, Nat.factorial] using! ht

/-- Bounds the norm of the Euler factor for `B` by `exp (Λ * h)` when the step is nonnegative
and `‖B‖ ≤ Λ`. -/
private theorem dyson_euler_factor_norm
    (B : Matrix I I ℂ) (h Λ : ℝ) (hh : 0 ≤ h) (hB : ‖B‖ ≤ Λ) :
    ‖1 - (h : ℂ) • (Complex.I • B)‖ ≤ Real.exp (Λ * h) := by
  calc
    _ ≤ ‖(1 : Matrix I I ℂ)‖ + ‖(h : ℂ) • (Complex.I • B)‖ := norm_sub_le _ _
    _ ≤ 1 + h * Λ := by
      rw [norm_smul, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh, Complex.norm_I,
        one_mul]
      exact add_le_add l2_norm_one_le (mul_le_mul_of_nonneg_left hB hh)
    _ ≤ _ := by simpa [add_comm, mul_comm] using! Real.add_one_le_exp (Λ * h)

/-- The chronological matrix product defined by starting at the identity and multiplying each
new factor on the left. -/
private noncomputable def dysonLeftProduct
    (f : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | n + 1 => f n * dysonLeftProduct f n

/-- Expresses the chronological product as the product of the reversed finite list of its first
`n` factors. -/
private theorem dysonLeftProduct_eq_reverse_prod
    (f : ℕ → Matrix I I ℂ) (n : ℕ) :
    dysonLeftProduct f n = ((List.ofFn (fun j : Fin n => f j.val)).reverse).prod := by
  induction n with
  | zero => simp [dysonLeftProduct]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.prod_cons]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [dysonLeftProduct, ih]

/-- Bounds the difference of two chronological products by `M * B^M * d` when one factor family
is bounded by `B ≥ 1`, the other by one, and each factor error is at most `B * d`. -/
private theorem dysonLeftProduct_perturbation
    (f g : ℕ → Matrix I I ℂ) (B d : ℝ) (M : ℕ) (hB : 1 ≤ B) (hd : 0 ≤ d)
    (hf : ∀ j < M, ‖f j‖ ≤ B) (hg : ∀ j < M, ‖g j‖ ≤ 1)
    (hfg : ∀ j < M, ‖f j - g j‖ ≤ B * d) :
    ‖dysonLeftProduct f M - dysonLeftProduct g M‖ ≤ (M : ℝ) * B ^ M * d := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hgn (n : ℕ) (hn : n ≤ M) : ‖dysonLeftProduct g n‖ ≤ 1 := by
    induction n with
    | zero => exact l2_norm_one_le
    | succ n ih =>
      have hnM : n < M := by omega
      calc
        _ ≤ ‖g n‖ * ‖dysonLeftProduct g n‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hg n hnM) (ih (by omega)) (norm_nonneg _)
          (by norm_num)
        _ = 1 := one_mul _
  have herr (n : ℕ) (hn : n ≤ M) :
      ‖dysonLeftProduct f n - dysonLeftProduct g n‖ ≤ (n : ℝ) * B ^ n * d := by
    induction n with
    | zero => simp [dysonLeftProduct]
    | succ n ih =>
      have hnM : n < M := by omega
      have he : dysonLeftProduct f (n + 1) - dysonLeftProduct g (n + 1) =
          f n * (dysonLeftProduct f n - dysonLeftProduct g n) +
            (f n - g n) * dysonLeftProduct g n := by
        simp only [dysonLeftProduct]
        noncomm_ring
      have hpow : B ≤ B ^ (n + 1) := by
        rw [pow_succ]
        have hpn : 1 ≤ B ^ n := one_le_pow₀ hB
        nlinarith
      rw [he]
      calc
        _ ≤ ‖f n * (dysonLeftProduct f n - dysonLeftProduct g n)‖ +
            ‖(f n - g n) * dysonLeftProduct g n‖ := norm_add_le _ _
        _ ≤ B * ((n : ℝ) * B ^ n * d) + B * d := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              (mul_le_mul (hf n hnM) (ih (by omega)) (norm_nonneg _) hB0)
          · exact (norm_mul_le _ _).trans
              ((mul_le_mul (hfg n hnM) (hgn n (by omega)) (norm_nonneg _)
                (by positivity)).trans_eq (mul_one _))
        _ = (n : ℝ) * B ^ (n + 1) * d + B * d := by rw [pow_succ]; ring
        _ ≤ (n : ℝ) * B ^ (n + 1) * d + B ^ (n + 1) * d := by
          gcongr
        _ = ((n + 1 : ℕ) : ℝ) * B ^ (n + 1) * d := by push_cast; ring
  exact herr M le_rfl

/-- For a bounded Hermitian field on `[0,t]`, bounds the difference between the grid Dyson run
and the sampled exact evolution product by `exp (Λ*t) * Λ^2 * t^2 / (2*M)`. No continuity
assumption on the field is required. -/
theorem dyson_grid_euler_error_discontinuous (H : ℝ → Matrix I I ℂ)
    (t Λ : ℝ) (M : ℕ) (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M)
    (hbound : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) :
    ‖dysonGridRun H t M - sampledEvolutionProduct H t M‖ ≤
      Real.exp (Λ*t)*Λ^2*t^2/(2*M) := by
  let h : ℝ := t/M
  let c := Λ*h
  let d := c^2/2
  let B := Real.exp c
  let f := fun j : ℕ => 1-(h : ℂ) • (Complex.I • H ((j : ℝ)*h))
  let g := fun j : ℕ => HamiltonianEvolution (H ((j : ℝ)*h)) h
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh : 0 ≤ h := div_nonneg ht (Nat.cast_nonneg M)
  have hc : 0 ≤ c := mul_nonneg hΛ hh
  have hmem (j : ℕ) (hj : j < M) : (j : ℝ)*h ∈ Set.Icc 0 t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg j) hh, ?_⟩
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj.le
    calc
      (j : ℝ)*h ≤ (M : ℝ)*h := mul_le_mul_of_nonneg_right hj' hh
      _ = t := by dsimp [h]; field_simp
  have hrun : dysonGridRun H t M = dysonLeftProduct f M := by
    rw [dysonLeftProduct_eq_reverse_prod]
    unfold dysonGridRun
    congr 3
    funext j
    simp only [dysonGridStep, f, h]
    rw [mul_comm t (j.val : ℝ), mul_div_assoc]
  have hp := dysonLeftProduct_perturbation f g B d M (Real.one_le_exp hc)
    (by positivity) (fun j hj => dyson_euler_factor_norm _ h Λ hh (hbound _ (hmem j hj)).2)
    (fun j hj => l2_norm_unitary_le_one (hamiltonianEvolution_unitary
      (hbound _ (hmem j hj)).1 h))
    (fun j hj => by simpa [B, d, c, mul_div_assoc] using!
      dyson_euler_factor_error (H ((j : ℝ)*h)) h Λ hh hΛ (hbound _ (hmem j hj)).2)
  have hsample : sampledEvolutionProduct H t M = dysonLeftProduct g M := by
    rw [dysonLeftProduct_eq_reverse_prod]
    unfold sampledEvolutionProduct
    congr 3
    funext j
    dsimp only [g, h]
    rw [mul_comm t (j.val : ℝ), mul_div_assoc]
  have hBpow : B^M = Real.exp (Λ*t) := by
    dsimp [B]
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [c, h]
    field_simp
  have hpoly : (M : ℝ)*B^M*d = Real.exp (Λ*t)*Λ^2*t^2/(2*M) := by
    rw [hBpow]
    dsimp [d, c, h]
    field_simp
  rw [hrun, hsample]
  exact hp.trans_eq hpoly

/-- Bounds the truncated grid Dyson sum's error against the sampled exact evolution by the Euler
grid error plus `2 * (Λ*t)^(K+1) / (K+1)!`. The field is bounded Hermitian and the norm-time
product is at most `Real.log 2`. -/
theorem dyson_grid_truncation_sample_error_discontinuous (H : ℝ → Matrix I I ℂ)
    (t Λ : ℝ) (M K : ℕ) (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M)
    (hbound : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ)
    (hlog : Λ*t ≤ Real.log 2) :
    ‖dysonGridTruncatedSum H t M K - sampledEvolutionProduct H t M‖ ≤
      Real.exp (Λ*t)*Λ^2*t^2/(2*M) + 2*(Λ*t)^(K+1)/((K+1).factorial:ℝ) := by
  have he := dyson_grid_euler_error_discontinuous H t Λ M ht hΛ hM hbound
  have ht' := dyson_grid_truncation_factorial_tail I H t Λ M K ht hΛ hM
    (fun u hu => (hbound u hu).2) hlog
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (by linarith : ‖dysonGridTruncatedSum H t M K-dysonGridRun H t M‖ +
      ‖dysonGridRun H t M-sampledEvolutionProduct H t M‖ ≤ _)

/-- Identifies the uniform sampled evolution product of the supplied piecewise field with the
reversed product of exact evolutions of its frozen table entries. -/
theorem suppliedGrid_sampledEvolutionProduct {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (B : ℕ → Matrix I I ℂ) (N M : ℕ) {T : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) :
    sampledEvolutionProduct (suppliedGridField τ B N) T M =
      (((suppliedFrozenTable τ B (T/M) N).map
        (fun X => HamiltonianEvolution X (T/M))).reverse).prod := by
  unfold sampledEvolutionProduct
  have hs := suppliedGridField_sample_list hτ hτ0 B N M hτN hT hM
  rw [← hs, List.map_ofFn]
  rfl

/-- For a monotone supplied grid with bounded Hermitian interval matrices, the uniform sampled
evolution differs from the supplied-grid evolution by at most `2 * Λ * N * (T/M)`. -/
theorem suppliedGrid_sampled_freezing_error {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (B : ℕ → Matrix I I ℂ) (N M : ℕ) {T Λ : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) :
    ‖suppliedGridEvolution τ B N - sampledEvolutionProduct (suppliedGridField τ B N) T M‖ ≤
      2*Λ*N*(T/M) := by
  rw [suppliedGrid_sampledEvolutionProduct hτ hτ0 B N M hτN hT hM]
  exact suppliedGridEvolution_freezing_error hτ hτ0 B N
    (div_pos hT (by exact_mod_cast hM)) hΛ hB

/-- Bounds the error between supplied-grid evolution and its truncated uniform-grid Dyson sum by
the sum of the freezing error, Euler discretization error, and factorial truncation tail.
The estimate assumes bounded Hermitian interval matrices and `Λ*T ≤ Real.log 2`. -/
theorem suppliedGrid_dyson_truncation_error {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (B : ℕ → Matrix I I ℂ) (N M K : ℕ) {T Λ : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) (hlog : Λ*T ≤ Real.log 2) :
    ‖suppliedGridEvolution τ B N - dysonGridTruncatedSum (suppliedGridField τ B N) T M K‖ ≤
      2*Λ*N*(T/M) + Real.exp (Λ*T)*Λ^2*T^2/(2*M) +
        2*(Λ*T)^(K+1)/((K+1).factorial:ℝ) := by
  let H := suppliedGridField τ B N
  have hf := suppliedGrid_sampled_freezing_error hτ hτ0 B N M hτN hT hM hΛ hB
  have he := dyson_grid_euler_error_discontinuous H T Λ M hT.le hΛ hM
    (fun u _ => suppliedGridField_bound τ B N hΛ hB u)
  have ht := dyson_grid_truncation_factorial_tail I H T Λ M K hT.le hΛ hM
    (fun u _ => (suppliedGridField_bound τ B N hΛ hB u).2) hlog
  rw [norm_sub_rev] at he ht
  calc
    _ ≤ ‖suppliedGridEvolution τ B N-sampledEvolutionProduct H T M‖ +
        ‖sampledEvolutionProduct H T M-dysonGridTruncatedSum H T M K‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖suppliedGridEvolution τ B N-sampledEvolutionProduct H T M‖ +
        (‖sampledEvolutionProduct H T M-dysonGridRun H T M‖ +
          ‖dysonGridRun H T M-dysonGridTruncatedSum H T M K‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ _ := by linarith

/-- Collects the freezing and Euler error coefficients as `2*Λ*N*T + exp (Λ*T)*Λ^2*T^2/2`, so
both grid errors are bounded by this constant divided by the grid size. -/
def suppliedGridErrorConstant (Λ T : ℝ) (N : ℕ) : ℝ :=
  2*Λ*N*T + Real.exp (Λ*T)*Λ^2*T^2/2

/-- The supplied-grid error constant is nonnegative when the Hamiltonian norm bound and time
horizon are nonnegative. -/
theorem suppliedGridErrorConstant_nonneg {Λ T : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ T)
    (N : ℕ) : 0 ≤ suppliedGridErrorConstant Λ T N := by
  unfold suppliedGridErrorConstant
  positivity

/-- Packages the supplied-grid Dyson error as `suppliedGridErrorConstant Λ T N / M` plus the
factorial truncation tail, under the monotone-grid, bounded-Hermitian, and norm-time
assumptions. -/
theorem suppliedGrid_dyson_error_budget {τ : ℕ → ℝ} (hτ : Monotone τ)
    (hτ0 : τ 0 = 0) (B : ℕ → Matrix I I ℂ) (N M K : ℕ) {T Λ : ℝ}
    (hτN : τ N = T) (hT : 0 < T) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) (hlog : Λ*T ≤ Real.log 2) :
    ‖suppliedGridEvolution τ B N - dysonGridTruncatedSum (suppliedGridField τ B N) T M K‖ ≤
      suppliedGridErrorConstant Λ T N / M + 2*(Λ*T)^(K+1)/((K+1).factorial:ℝ) := by
  convert! suppliedGrid_dyson_truncation_error hτ hτ0 B N M K hτN hT hM hΛ hB hlog using 1
  unfold suppliedGridErrorConstant
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
