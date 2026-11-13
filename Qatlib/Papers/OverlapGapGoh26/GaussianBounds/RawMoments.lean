/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Tail

/-!
# Uniform Gaussian moments of raw dynamics

`budgetCoefficient` gives polynomial control of the raw energy gradient in terms of `normScale`.
Gaussian tensor moments then bound its integrated squared norm and yield variance and centered
tail estimates with explicit `1/N` scaling through `rawVarianceConstant`. These estimates
quantify fluctuations of the raw dynamics in the analysis associated with [GohMuller2026].

## Main statements

* `actual_raw_variance_uniform`: For positive `r` and `N` and a schedule in `[0,1]`, the
  Gaussian variance of the raw energy is at most `rawVarianceConstant r T / N`.
* `actual_raw_centered_tail_uniform`: For positive `r` and `N`, a schedule in `[0,1]`, and `ε >
  0`, the probability of a centered raw energy deviation of at least `ε` is at most
  `rawVarianceConstant r T / (N * ε²)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators NNReal
open MeasureTheory ProbabilityTheory
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments

/-- The dimension independent coefficient `2 * (1 + 2(r+1)√T(2+2r√T)^T)` used to bound the raw
energy gradient. -/
def budgetCoefficient (r T : ℕ) : ℝ :=
  2*(1+2*((r+1:ℕ):ℝ)*Real.sqrt (T:ℝ)*(2+2*(r:ℝ)*Real.sqrt (T:ℝ))^T)

/-- For `K ≥ 0`, `energyBudget r N T K` is at most `budgetCoefficient r T * (1+K)^(T+1) / √N`. -/
theorem energyBudget_polynomial (r N T : ℕ) (K : ℝ) (hK : 0≤K) :
    energyBudget r N T K≤(budgetCoefficient r T/Real.sqrt (N:ℝ))*(1+K)^(T+1) := by
  let A := 2+2*(r:ℝ)*Real.sqrt (T:ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  have hbase : 2+2*K*(r:ℝ)*Real.sqrt (T:ℝ)≤A*(1+K) := by
    calc
      _ ≤ (2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))+(2*K+2*(r:ℝ)*Real.sqrt (T:ℝ)) := le_add_of_nonneg_right (by positivity)
      _ = _ := by dsimp [A]; ring
  have hp := pow_le_pow_left₀ (by positivity : 0≤2+2*K*(r:ℝ)*Real.sqrt (T:ℝ)) hbase T
  rw [mul_pow] at hp
  have h1 : 1≤(1+K)^(T+1) := one_le_pow₀ (by linarith : 1≤1+K)
  have hk : K*(1+K)^T≤(1+K)^(T+1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by linarith : 0≤1+K) T]
  have hcoef : 0≤2*((r+1:ℕ):ℝ)*Real.sqrt (T:ℝ)*A^T := by positivity
  have hpoly : 1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T)≤
      (1+2*((r+1:ℕ):ℝ)*Real.sqrt (T:ℝ)*A^T)*(1+K)^(T+1) := by
    calc
      _ ≤ 1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(A^T*(1+K)^T)) := by gcongr
      _ = 1+(2*((r+1:ℕ):ℝ)*Real.sqrt (T:ℝ)*A^T)*(K*(1+K)^T) := by ring
      _ ≤ 1+(2*((r+1:ℕ):ℝ)*Real.sqrt (T:ℝ)*A^T)*(1+K)^(T+1) := by gcongr
      _ ≤ _ := by nlinarith
  unfold energyBudget budgetCoefficient
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ)≤2))
    (Real.sqrt_nonneg (N:ℝ))
  exact hh.trans_eq (by dsimp [A]; ring)

/-- For positive `r` and `N` and a schedule in `[0,1]`, the squared raw energy derivative norm
is at most `(budgetCoefficient r T)^2 * (1+normScale x)^(2T+2) / N`. -/
theorem actual_gradient_polynomial {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (x : Input r N) :
    ‖fderiv ℝ (energy (r:=r) (N:=N) s T) x‖^2≤
      ((budgetCoefficient r T)^2/(N:ℝ))*(1+normScale x)^(2*T+2) := by
  have hK : 0≤normScale x := by dsimp [normScale]; positivity
  have h :=
      (energy_fderiv_bound hr hN s hs x).trans (energyBudget_polynomial r N T (normScale x) hK)
  have hn : 0≤budgetCoefficient r T/Real.sqrt (N:ℝ)*(1+normScale x)^(T+1) := by
    dsimp [budgetCoefficient]
    positivity
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine hh.trans_eq ?_
  rw [mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg N),← pow_mul (1+normScale x) (T+1) 2,
    show (T+1)*2=2*T+2 by omega]

/-- For positive `r` and `N` and a schedule in `[0,1]`, the raw energy belongs to `L²` of the
standard Gaussian input law. -/
theorem energy_memLp_two {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    MemLp (energy (r:=r) (N:=N) s T) 2 (stdGaussian (Input r N)) := by
  have hz : sourceTensor (tensorCoords (0 : Input r N)).ofLp=0 := by
    funext k
    change Real.sqrt (((N:ℝ)^r)⁻¹)*(0:ℝ)=0
    exact mul_zero _
  have h0 : normScale (0 : Input r N)=0 := by
    unfold normScale
    rw [hz]
    simp [tensorForm]
  have he0 : energy (r:=r) (N:=N) s T 0=0 := by
    change tensorEnergy (sourceTensor (tensorCoords (0 : Input r N)).ofLp) _/(N:ℝ)=0
    rw [hz]
    simp [tensorEnergy]
  have hb : ∀ x : Input r N,|energy s T x|≤(2/Real.sqrt (N:ℝ))*‖x‖ := by
    intro x
    simpa [he0,energyBudget] using! energy_difference hr hN s hs x 0 0 h0.le
  have hn :=
      ((IsGaussian.memLp_id (stdGaussian (Input r N)) 2 (by simp)).norm).const_mul
      (2/Real.sqrt (N:ℝ))
  apply hn.mono' (contDiff_energy s T).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using! hb x)

/-- For positive `r` and `N` and a schedule in `[0,1]`, the squared raw energy derivative norm
is Gaussian integrable. -/
theorem gradient_square_integrable {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    Integrable (fun x : Input r N => ‖fderiv ℝ (energy s T) x‖^2) (stdGaussian (Input r N)) := by
  have hp := (actual_tensor_preserving r N).integrable_comp_of_integrable
    (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.actual_gradient_budget_moment hr hN T).1
  change Integrable (fun x : Input r N => (1+normScale x)^(2*T+2)) (stdGaussian (Input r N)) at hp
  have hpoly := hp.const_mul ((budgetCoefficient r T)^2/(N:ℝ))
  have hcont : Continuous (fun x : Input r N => ‖fderiv ℝ (energy s T) x‖^2) := by
    have := (contDiff_energy (r:=r) (N:=N) s T).continuous_fderiv (by simp)
    fun_prop
  apply hpoly.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖fderiv ℝ (energy s T) x‖)] using!
        actual_gradient_polynomial hr hN s hs x)

/-- Under the positivity and schedule assumptions, the Gaussian variance of the raw energy is at
most `π²/8` times its integrated squared derivative norm. -/
theorem actual_raw_variance {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    variance (energy (r:=r) (N:=N) s T) (stdGaussian (Input r N))≤
      (Real.pi^2/8)*(∫ x : Input r N,‖fderiv ℝ (energy s T) x‖^2 ∂stdGaussian (Input r N)) := by
  exact Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare.c1_gaussian_poincare_gradient
    (energy s T) ((contDiff_energy s T).of_le (by simp)) (energy_memLp_two hr hN s hs)
    (gradient_square_integrable hr hN s hs)

/-- Under the positivity and schedule assumptions, a centered raw energy deviation of size `ε >
0` has probability at most `π²/(8ε²)` times the integrated squared derivative norm. -/
theorem actual_raw_centered_tail {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    (stdGaussian (Input r N)).real {x | ε≤|energy s T x-(∫ y,energy s T y ∂stdGaussian (Input r N))|}≤
      (Real.pi^2/8)*(∫ x : Input r N,‖fderiv ℝ (energy s T) x‖^2 ∂stdGaussian (Input r N))/ε^2 := by
  exact Qatlib.Foundations.ProbabilityCore.GaussPoincare.Tail.centered_tail
    (energy s T) ((contDiff_energy s T).of_le (by simp)) (energy_memLp_two hr hN s hs)
    (gradient_square_integrable hr hN s hs) ε hε

/-- For positive `r` and `N`, `(1+normScale x)^p` is Gaussian integrable and its integral is at
most `uniformMomentConstant r p`. -/
theorem input_moment_bound {r N : ℕ} (hr : 0<r) (hN : 0<N) (p : ℕ) :
    Integrable (fun x : Input r N => (1+normScale x)^p) (stdGaussian (Input r N)) ∧
      (∫ x : Input r N,(1+normScale x)^p ∂stdGaussian (Input r N))≤
        Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.uniformMomentConstant r p := by
  let f := fun A : Tensor (r+1) N =>
    (1+Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.normalizedNorm A)^p
  have hp :=
      Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.actual_shifted_moment hr hN p
  have hmp := actual_tensor_preserving r N
  have hmeas : AEStronglyMeasurable f ((stdGaussian (Input r N)).map (fun x => sourceTensor (tensorCoords x).ofLp)) := by
    rw [hmp.map_eq]
    exact hp.1.aestronglyMeasurable
  have he := (integral_map hmp.measurable.aemeasurable hmeas).symm
  rw [hmp.map_eq] at he
  refine ⟨hmp.integrable_comp_of_integrable hp.1,?_⟩
  exact he.trans_le hp.2

/-- Under the positivity and schedule assumptions, the integrated squared raw energy derivative
norm is at most `(budgetCoefficient r T)^2 * uniformMomentConstant r (2*T+2) / N`. -/
theorem actual_gradient_integral_bound {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    (∫ x : Input r N,‖fderiv ℝ (energy s T) x‖^2 ∂stdGaussian (Input r N))≤
      ((budgetCoefficient r T)^2/(N:ℝ))*
        Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.uniformMomentConstant r (2*T+2) := by
  have hp := input_moment_bound hr hN (2*T+2)
  have hcoef : 0≤(budgetCoefficient r T)^2/(N:ℝ) := by positivity
  calc
    _ ≤ ∫ x : Input r N,((budgetCoefficient r T)^2/(N:ℝ))*(1+normScale x)^(2*T+2) ∂stdGaussian (Input r N) :=
      integral_mono (gradient_square_integrable hr hN s hs) (hp.1.const_mul _)
        (fun x => actual_gradient_polynomial hr hN s hs x)
    _ = ((budgetCoefficient r T)^2/(N:ℝ))*(∫ x : Input r N,(1+normScale x)^(2*T+2) ∂stdGaussian (Input r N)) := by
      rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp.2 hcoef

/-- The dimension independent raw energy variance coefficient `(π²/8) * (budgetCoefficient r
T)^2 * uniformMomentConstant r (2*T+2)`. -/
def rawVarianceConstant (r T : ℕ) : ℝ :=
  (Real.pi^2/8)*(budgetCoefficient r T)^2*
    Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments.uniformMomentConstant r (2*T+2)

/-- For positive `r` and `N` and a schedule in `[0,1]`, the Gaussian variance of the raw energy
is at most `rawVarianceConstant r T / N`. See [GohMuller2026]. -/
theorem actual_raw_variance_uniform {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) :
    variance (energy (r:=r) (N:=N) s T) (stdGaussian (Input r N))≤rawVarianceConstant r T/(N:ℝ) := by
  refine (actual_raw_variance hr hN s hs).trans ?_
  exact (mul_le_mul_of_nonneg_left (actual_gradient_integral_bound hr hN s hs)
    (by positivity : (0:ℝ)≤Real.pi^2/8)).trans_eq (by unfold rawVarianceConstant; ring)

/-- For positive `r` and `N`, a schedule in `[0,1]`, and `ε > 0`, the probability of a centered
raw energy deviation of at least `ε` is at most `rawVarianceConstant r T / (N * ε²)`. See
[GohMuller2026]. -/
theorem actual_raw_centered_tail_uniform {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    (stdGaussian (Input r N)).real {x | ε≤|energy s T x-(∫ y,energy s T y ∂stdGaussian (Input r N))|}≤
      rawVarianceConstant r T/((N:ℝ)*ε^2) := by
  refine (actual_raw_centered_tail hr hN s hs ε hε).trans ?_
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_gradient_integral_bound hr hN s hs) (by positivity : (0:ℝ)≤Real.pi^2/8))
    (sq_nonneg ε)).trans_eq (by unfold rawVarianceConstant; ring)

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
