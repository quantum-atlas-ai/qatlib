/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround

/-!
# Standard Gaussian inputs for raw spin dynamics

`Input` combines tensor and seed coordinates in one Euclidean space, and `energy` evaluates the
raw dynamics on these coordinates. The module proves smoothness, local difference and derivative
bounds, and Lipschitz extensions on bounded norm regions; `actual_tensor_seed_preserving`
identifies the induced independent tensor and seed laws. This representation supports the
Gaussian analysis associated with [GohMuller2026].

## Main statements

* `actual_energy_extension`: For positive `r` and `N`, a schedule in `[0,1]`, and `K ≥ 0`, the
  raw energy on `normScale ≤ K` has a global Lipschitz extension with constant `energyBudget r N
  T K` belonging to every finite Gaussian `Lᵖ` space.
* `contDiff_energy`: The raw energy density is infinitely differentiable in the combined
  Gaussian input.
* `actual_tensor_seed_preserving`: Extracting the scaled tensor and seed from a standard
  Gaussian input preserves measure, with target the product of `gaussianTensorLaw` and
  independent standard real Gaussian seed coordinates.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput

/-- The Euclidean space with coordinates indexed by the disjoint union of tensor indices and
seed indices. -/
abbrev Input (r N : ℕ) := EuclideanSpace ℝ ((Fin (r+1)→Fin N)⊕Fin N)

/-- The Euclidean tensor coordinate block of a combined Gaussian input. -/
def tensorCoords {r N : ℕ} (x : Input r N) : EuclideanSpace ℝ (Fin (r+1)→Fin N) :=
  WithLp.toLp 2 (fun k => x (Sum.inl k))

/-- The seed coordinate block of a combined Gaussian input. -/
def seedCoords {r N : ℕ} (x : Input r N) : Fin N→ℝ := fun i => x (Sum.inr i)

/-- The raw energy density evaluated at the tensor and seed coordinates of the combined input. -/
def energy {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x : Input r N) : ℝ :=
  rawEnergyDensity s T (tensorCoords x) (seedCoords x)

/-- The squared input distance is the sum of the squared distances of its tensor and seed
coordinate blocks. -/
theorem input_split_sq {r N : ℕ} (x y : Input r N) :
    ‖tensorCoords x-tensorCoords y‖^2+
      ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y)‖^2=‖x-y‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,tensorCoords,seedCoords,PiLp.sub_apply,Fintype.sum_sum_type]

/-- The sum of the tensor and seed block distances is at most twice the combined input distance. -/
theorem input_split_le {r N : ℕ} (x y : Input r N) :
    ‖tensorCoords x-tensorCoords y‖+
      ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y)‖≤2*‖x-y‖ := by
  have h := input_split_sq x y
  have ha := norm_nonneg (tensorCoords x-tensorCoords y)
  have hb :=
      norm_nonneg ((WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y))
  have hc := norm_nonneg (x-y)
  have h1 : ‖tensorCoords x-tensorCoords y‖≤‖x-y‖ := by
    nlinarith [sq_nonneg ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 (seedCoords y)‖]
  have h2 :
      ‖(WithLp.toLp 2 (seedCoords x) : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2
      (seedCoords y)‖≤‖x-y‖ := by nlinarith [sq_nonneg ‖tensorCoords x-tensorCoords y‖]
  linarith

/-- The operator norm of the scaled input tensor form, multiplied by `(√N)^(r-1)`. -/
def normScale {r N : ℕ} (x : Input r N) : ℝ :=
  ‖tensorForm (sourceTensor (tensorCoords x).ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)

/-- The coefficient `2 * (1 + K(r+1)2√T(2+2Kr√T)^T) / √N` used in raw energy difference and
derivative bounds. -/
def energyBudget (r N T : ℕ) (K : ℝ) : ℝ :=
  2*(1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T))/Real.sqrt (N:ℝ)

/-- For positive `r` and `N` and a schedule in `[0,1]`, if `normScale y ≤ K`, then the raw
energy difference is at most `energyBudget r N T K * ‖x-y‖`. -/
theorem energy_difference {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (x y : Input r N) (K : ℝ)
    (hK : normScale y≤K) : |energy s T x-energy s T y|≤energyBudget r N T K*‖x-y‖ := by
  have hK0 : 0≤K := le_trans (by dsimp [normScale]; positivity) hK
  have h :=
      actual_raw_energy_difference hr hN s hs (tensorCoords x) (tensorCoords y) (seedCoords x)
      (seedCoords y) K hK
  refine h.trans ?_
  have hh := mul_le_mul_of_nonneg_left (input_split_le x y)
    (by positivity : 0≤(1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T))/Real.sqrt (N:ℝ))
  exact hh.trans_eq (by dsimp [energyBudget]; ring)

/-- For positive `r` and `N` and a schedule in `[0,1]`, the raw energy derivative norm at `x` is
at most `energyBudget r N T (normScale x)`. -/
theorem energy_fderiv_bound {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (x : Input r N) :
    ‖fderiv ℝ (energy (r:=r) (N:=N) s T) x‖≤energyBudget r N T (normScale x) := by
  apply norm_fderiv_le_of_lip' ℝ (by dsimp [energyBudget,normScale]; positivity)
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using! energy_difference hr hN s hs y x (normScale x) le_rfl)

/-- For positive `r` and `N`, a schedule in `[0,1]`, and `K ≥ 0`, the raw energy on `normScale ≤
K` has a global Lipschitz extension with constant `energyBudget r N T K` belonging to every
finite Gaussian `Lᵖ` space. -/
theorem actual_energy_extension {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (K : ℝ≥0) :
    ∃ g : Input r N→ℝ,LipschitzWith (⟨energyBudget r N T K,by dsimp [energyBudget]; positivity⟩ : ℝ≥0) g ∧
      Set.EqOn (energy s T) g {x | normScale x≤K} ∧
      ∀ p : ENNReal,p≠⊤→MemLp g p (stdGaussian (Input r N)) := by
  apply Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments.same_constant_gaussian_extension
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y hy
  simpa only [Real.dist_eq,dist_eq_norm] using! energy_difference hr hN s hs x y K hy

/-- Each coordinate of the raw feedback state is infinitely differentiable in the combined
tensor and seed input. -/
theorem contDiff_feedback {r N : ℕ} (s : ℕ→ℝ) (t : ℕ) :
    ∀ i j,ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Input r N =>
      feedbackState id (rowTensor (sourceTensor (tensorCoords x).ofLp)) (seedCoords x) s t i j) := by
  induction t with
  | zero => intro i j; simp only [feedbackState]; fun_prop
  | succ t ih =>
    intro i j
    let h : Input r N→ℝ := fun x => feedbackField id (rowTensor (sourceTensor (tensorCoords x).ofLp))
      (seedCoords x) s t (feedbackState id (rowTensor (sourceTensor (tensorCoords x).ofLp)) (seedCoords x) s t) i
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) h := by
      dsimp only [h,feedbackField,id_eq,interaction,rowTensor,sourceTensor,tensorCoords,seedCoords]
      fun_prop
    have hm (a b : Fin 3) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Input r N => rotationStep (s (t+1)) (h x) a b) := by
      fin_cases a <;> fin_cases b <;>
        simp [rotationStep,driverAngle,problemAngle,Matrix.mul_apply,Fin.sum_univ_three] <;> fun_prop
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Input r N => ∑ a,
      rotationStep (s (t+1)) (h x) j a*
      feedbackState id (rowTensor (sourceTensor (tensorCoords x).ofLp)) (seedCoords x) s t i a)
    fun_prop

/-- The raw energy density is infinitely differentiable in the combined Gaussian input. -/
theorem contDiff_energy {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (energy (r:=r) (N:=N) s T) := by
  have hs := contDiff_feedback (r:=r) (N:=N) s T
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Input r N =>
    (∑ k : Fin (r+1)→Fin N,Real.sqrt (((N:ℝ)^r)⁻¹)*x (Sum.inl k)*
      ∏ a,feedbackState id (rowTensor (sourceTensor (tensorCoords x).ofLp)) (seedCoords x) s T (k a) 2)/(N:ℝ))
  fun_prop

/-- Extracting the scaled tensor and seed from a standard Gaussian input preserves measure, with
target the product of `gaussianTensorLaw` and independent standard real Gaussian seed
coordinates. See [GohMuller2026]. -/
theorem actual_tensor_seed_preserving (r N : ℕ) :
    MeasurePreserving (fun x : Input r N => (sourceTensor (tensorCoords x).ofLp,seedCoords x))
      (stdGaussian (Input r N)) ((gaussianTensorLaw r N).prod (Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  have ht : MeasurePreserving (sourceTensor : Tensor (r+1) N→Tensor (r+1) N)
      (Measure.pi (fun _ : Fin (r+1)→Fin N => gaussianReal 0 1)) (gaussianTensorLaw r N) :=
    ⟨by unfold sourceTensor; fun_prop,Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround.sourceTensor_map_standard r N⟩
  have hs :=
      measurePreserving_sumPiEquivProdPi (fun _ : (Fin (r+1)→Fin N)⊕Fin N => gaussianReal 0 1)
  have hp :=
      (ht.prod (MeasurePreserving.id (Measure.pi (fun _ : Fin N => gaussianReal 0 1)))).comp hs
  have hm : Measurable (fun x : Input r N => (sourceTensor (tensorCoords x).ofLp,seedCoords x)) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro k
      change Measurable (fun x : Input r N => Real.sqrt (((N:ℝ)^r)⁻¹)*x (Sum.inl k))
      fun_prop
    · apply measurable_pi_lambda
      intro i
      change Measurable (fun x : Input r N => x (Sum.inr i))
      fun_prop
  refine ⟨hm,?_⟩
  rw [← map_pi_eq_stdGaussian,Measure.map_map hm (by fun_prop)]
  exact hp.map_eq

/-- Extracting the scaled tensor from a standard Gaussian input preserves measure with target
`gaussianTensorLaw`. -/
theorem actual_tensor_preserving (r N : ℕ) :
    MeasurePreserving (fun x : Input r N => sourceTensor (tensorCoords x).ofLp)
      (stdGaussian (Input r N)) (gaussianTensorLaw r N) :=
  (measurePreserving_fst (μ:=gaussianTensorLaw r N) (ν:=Measure.pi (fun _ : Fin N => gaussianReal 0 1))).comp
    (actual_tensor_seed_preserving r N)

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
