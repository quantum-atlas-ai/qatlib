/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Parameter Encoding

Parameter Encoding constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding

/-- Data and invariants for Scalar Interval Q in the parameter encoding model. -/
structure ScalarIntervalQ where
  lo : ℚ
  hi : ℚ
  deriving Repr

/-- Data and invariants for Physical Box Q in the parameter encoding model. -/
structure PhysicalBoxQ where
  kappa : ScalarIntervalQ
  lambda : ScalarIntervalQ
  deriving Repr

/-- Construction for kappa Approx Q in the parameter encoding model. -/
def kappaApproxQ (box : PhysicalBoxQ) : ℚ := box.kappa.lo
/-- Construction for lambda Approx Q in the parameter encoding model. -/
def lambdaApproxQ (box : PhysicalBoxQ) : ℚ := max 0 box.lambda.lo
/-- Construction for lambda Upper Q in the parameter encoding model. -/
def lambdaUpperQ (box : PhysicalBoxQ) : ℚ := max 0 box.lambda.hi
/-- Construction for inverse Radius Q in the parameter encoding model. -/
def inverseRadiusQ (box : PhysicalBoxQ) : ℚ := 1/box.kappa.lo-1/box.kappa.hi
/-- Construction for gamma Radius Q in the parameter encoding model. -/
def gammaRadiusQ (r : ℕ) (box : PhysicalBoxQ) : ℚ :=
  ((lambdaUpperQ box)^2-(lambdaApproxQ box)^2)*((2^r : ℕ) : ℚ)^2/72
/-- Construction for parameter Bias Q in the parameter encoding model. -/
def parameterBiasQ (d r : ℕ) (U : ℚ) (box : PhysicalBoxQ) : ℚ :=
  let C := ((2^r : ℕ) : ℚ)/6+U/box.kappa.lo
  let E := inverseRadiusQ box*U
  (d : ℚ)*(2*C*E+E^2)+2*(d : ℚ)*gammaRadiusQ r box

noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
/-- Complete original `implemented_target_absorb` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem implemented_target_absorb {d : ℕ} (mv u : Fin d → S → ℝ) (ms : Fin 3 → S → ℝ)
    (e : Fin d → S ≃ S) (α β γ : ℝ) :
    implementedResidualLoss mv u ms e α β γ =
      implementedResidualLoss mv (fun j x => β*u j x) ms e α 1 γ := by
  simp only [implementedResidualLoss, one_mul]

/-- Complete original `scalar_parameter_loss_bias` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem scalar_parameter_loss_bias {d : ℕ} (a b c k : S → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (u : Fin d → S → ℝ) (e : Fin d → S ≃ S)
    (h κ0 κ1 κmin lam0 lam1 U C eβ eγ : ℝ)
    (hh : 0 < h) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1) (hmin : 0 < κmin) (hmin0 : κmin ≤ κ0)
    (hU : 0 ≤ U) (hu : ∀ j x, |u j x| ≤ U)
    (hβ : |1/κ1-1/κ0| ≤ eβ) (hγ : |lam1^2/(2*h^2)-lam0^2/(2*h^2)| ≤ eγ)
    (hC : 1/h+U/κmin ≤ C) :
    |spinorDiscreteLoss a b c k u e h κ1 lam1-spinorDiscreteLoss a b c k u e h κ0 lam0| ≤
      (d : ℝ)*(2*C*(eβ*U)+(eβ*U)^2)+2*(d : ℝ)*eγ := by
  have hi : 1/κ0 ≤ 1/κmin := one_div_le_one_div_of_le hmin hmin0
  have heβ : 0 ≤ eβ := (abs_nonneg _).trans hβ
  have hu0 (j : Fin d) (x : S) : |(1/κ0)*u j x| ≤ U/κmin := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/κ0)]
    calc
      _ ≤ (1/κ0)*U := mul_le_mul_of_nonneg_left (hu j x) (by positivity)
      _ ≤ (1/κmin)*U := mul_le_mul_of_nonneg_right hi hU
      _ = _ := by ring
  have ht (j : Fin d) (x : S) : |(1/κ1)*u j x-(1/κ0)*u j x| ≤ eβ*U := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul hβ (hu j x) (abs_nonneg _) heβ
  rw [spinor_discrete_loss_eq a b c k hz u e h κ1 lam1 hh.ne' hκ1.ne',
    spinor_discrete_loss_eq a b c k hz u e h κ0 lam0 hh.ne' hκ0.ne']
  rw [implemented_target_absorb (spinorCurrentMean a b c k e) u (pauliField a b c k)
      (fun j => (e j).trans (e j)) (1/h) (1/κ1) (lam1^2/(2*h^2)),
    implemented_target_absorb (spinorCurrentMean a b c k e) u (pauliField a b c k)
      (fun j => (e j).trans (e j)) (1/h) (1/κ0) (lam0^2/(2*h^2))]
  have hb := implemented_loss_bias_bound (spinorCurrentMean a b c k e)
    (fun j x => (1/κ0)*u j x) (fun j x => (1/κ1)*u j x)
    (1/h) (1/h) 1 (lam0^2/(2*h^2)) (lam1^2/(2*h^2)) (U/κmin) C 0 (eβ*U) eγ
    (spinor_current_mean_bound a b c k hz e) hu0 ht (pauliField a b c k)
    (pauli_field_unit a b c k hz) (fun j => (e j).trans (e j))
    (by positivity) (by norm_num) (by simp) hγ (by simpa only [one_mul] using hC)
  simpa only [zero_add, one_mul] using hb

/-- Complete original `reciprocal_interval_error` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem reciprocal_interval_error (lo hi κ : ℝ) (hlo : 0 < lo) (hlκ : lo ≤ κ) (hκu : κ ≤ hi) :
    |1/lo-1/κ| ≤ 1/lo-1/hi := by
  have hu : 1/κ ≤ 1/lo := one_div_le_one_div_of_le hlo hlκ
  have hl : 1/hi ≤ 1/κ := one_div_le_one_div_of_le (lt_of_lt_of_le hlo hlκ) hκu
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith

/-- Complete original `lambda_interval_error` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem lambda_interval_error (lo hi lam h : ℝ) (h0 : 0 ≤ lam)
    (hl : lo ≤ lam) (hu : lam ≤ hi) (hh : 0 < h) :
    |(max 0 lo)^2/(2*h^2)-lam^2/(2*h^2)| ≤
      ((max 0 hi)^2-(max 0 lo)^2)/(2*h^2) := by
  have hlow : 0 ≤ max 0 lo := le_max_left _ _
  have hlower : max 0 lo ≤ lam := max_le h0 hl
  have hupper : lam ≤ max 0 hi := hu.trans (le_max_right _ _)
  have hs0 : (max 0 lo)^2 ≤ lam^2 := (sq_le_sq₀ hlow h0).mpr hlower
  have hs1 : lam^2 ≤ (max 0 hi)^2 := (sq_le_sq₀ h0 (le_max_left _ _)).mpr hupper
  have hden : 0 < 2*h^2 := by positivity
  rw [← sub_div, abs_div, abs_of_nonpos (sub_nonpos.mpr hs0), abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  linarith

/-- Complete original `periodic_grid_scale_bounds` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem periodic_grid_scale_bounds (r : ℕ) :
    let N : ℝ := ((2^r : ℕ) : ℝ)
    let h := 2*Real.pi/N
    0 < h ∧ 1/h ≤ N/6 ∧ 1/(2*h^2) ≤ N^2/72 := by
  let N : ℝ := ((2^r : ℕ) : ℝ)
  let h := 2*Real.pi/N
  have hN : 0 < N := by dsimp [N]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hmul : h*N=2*Real.pi := div_mul_cancel₀ _ hN.ne'
  have hs : 6 ≤ h*N := by rw [hmul]; linarith [Real.pi_gt_three]
  have hi : 1/h ≤ N/6 := (div_le_iff₀ hh).mpr (by nlinarith [hs])
  have hs2 : 36 ≤ h^2*N^2 := by
    have ht := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6) (by positivity : (0 : ℝ) ≤ h*N)).mpr hs
    nlinarith
  have hg : 1/(2*h^2) ≤ N^2/72 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2*h^2)).mpr (by nlinarith [hs2])
  exact ⟨hh,hi,hg⟩

/-- Complete original `rat_max_zero_cast` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem rat_max_zero_cast (q : ℚ) : ((max 0 q : ℚ) : ℝ)=max 0 (q : ℝ) := by
  by_cases hq : q ≤ 0
  · have hr : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    rw [max_eq_left hq, max_eq_left hr]
    norm_num
  · have hq0 : 0 ≤ q := (lt_of_not_ge hq).le
    have hr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [max_eq_right hq0, max_eq_right hr]

/-- Complete original `physical_box_loss_bias` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem physical_box_loss_bias {d r : ℕ} (box : PhysicalBoxQ) (U : ℚ)
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → S → ℝ) (e : Fin d → S ≃ S) (κ lam : ℝ)
    (hklo : 0 < box.kappa.lo) (hU : 0 ≤ U) (hκlo : (box.kappa.lo : ℝ) ≤ κ)
    (hκhi : κ ≤ (box.kappa.hi : ℝ)) (hlam0 : 0 ≤ lam)
    (hlamlo : (box.lambda.lo : ℝ) ≤ lam) (hlamhi : lam ≤ (box.lambda.hi : ℝ))
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) :
    |spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ))
        (kappaApproxQ box : ℝ) (lambdaApproxQ box : ℝ)-
      spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam| ≤
        (parameterBiasQ d r U box : ℝ) := by
  let N : ℝ := ((2^r : ℕ) : ℝ)
  let h := 2*Real.pi/N
  let C : ℝ := N/6+(U : ℝ)/(box.kappa.lo : ℝ)
  have hscale := periodic_grid_scale_bounds r
  have hh : 0 < h := hscale.1
  have hkloR : (0 : ℝ) < (box.kappa.lo : ℝ) := by exact_mod_cast hklo
  have hκ : 0 < κ := lt_of_lt_of_le hkloR hκlo
  have hUR : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hb : |1/(box.kappa.lo : ℝ)-1/κ| ≤ (inverseRadiusQ box : ℝ) := by
    simpa [inverseRadiusQ] using reciprocal_interval_error (box.kappa.lo : ℝ)
      (box.kappa.hi : ℝ) κ hkloR hκlo hκhi
  have hlcast : (lambdaApproxQ box : ℝ)=max 0 (box.lambda.lo : ℝ) := rat_max_zero_cast _
  have hucast : (lambdaUpperQ box : ℝ)=max 0 (box.lambda.hi : ℝ) := rat_max_zero_cast _
  have hg0 : |(lambdaApproxQ box : ℝ)^2/(2*h^2)-lam^2/(2*h^2)| ≤
      ((lambdaUpperQ box : ℝ)^2-(lambdaApproxQ box : ℝ)^2)/(2*h^2) := by
    rw [hlcast,hucast]
    exact lambda_interval_error _ _ _ _ hlam0 hlamlo hlamhi hh
  let span : ℝ := (lambdaUpperQ box : ℝ)^2-(lambdaApproxQ box : ℝ)^2
  have hden : 0 < 2*h^2 := by positivity
  have hspan : 0 ≤ span := by
    have hnonneg : 0 ≤ span/(2*h^2) := (abs_nonneg _).trans hg0
    have ht := mul_nonneg hnonneg hden.le
    rwa [div_mul_cancel₀ _ hden.ne'] at ht
  have hrad : (gammaRadiusQ r box : ℝ)=span*N^2/72 := by
    dsimp [gammaRadiusQ,span,N]
    push_cast
    rfl
  have hg : |(lambdaApproxQ box : ℝ)^2/(2*h^2)-lam^2/(2*h^2)| ≤ (gammaRadiusQ r box : ℝ) := by
    apply hg0.trans
    have ht := mul_le_mul_of_nonneg_left hscale.2.2 hspan
    rw [hrad]
    convert ht using 1 <;> ring
  have hC : 1/h+(U : ℝ)/(box.kappa.lo : ℝ) ≤ C := by
    dsimp [C,h,N]
    linarith [hscale.2.1]
  have hbias := scalar_parameter_loss_bias a b c k hz u e h κ (box.kappa.lo : ℝ)
    (box.kappa.lo : ℝ) lam (lambdaApproxQ box : ℝ) (U : ℝ) C
    (inverseRadiusQ box : ℝ) (gammaRadiusQ r box : ℝ)
    hh hκ hkloR hkloR hκlo hUR hu hb hg hC
  change |spinorDiscreteLoss a b c k u e h (box.kappa.lo : ℝ) (lambdaApproxQ box : ℝ)-
    spinorDiscreteLoss a b c k u e h κ lam| ≤ _
  apply hbias.trans_eq
  dsimp [parameterBiasQ,C,N]
  push_cast
  rfl

/-- Complete original `physical_box_accuracy_transfer` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem physical_box_accuracy_transfer {d r : ℕ} {X : Type*} [Fintype X]
    (box : PhysicalBoxQ) (U η0 δ0 : ℚ) (a b c k : S → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (u : Fin d → S → ℝ) (e : Fin d → S ≃ S)
    (κ lam η δ : ℝ) (law : FinDist X) (F : X → ℝ)
    (hklo : 0 < box.kappa.lo) (hU : 0 ≤ U)
    (hκlo : (box.kappa.lo : ℝ) ≤ κ) (hκhi : κ ≤ (box.kappa.hi : ℝ))
    (hlam0 : 0 ≤ lam) (hlamlo : (box.lambda.lo : ℝ) ≤ lam) (hlamhi : lam ≤ (box.lambda.hi : ℝ))
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (hbudget : parameterBiasQ d r U box ≤ η0/2)
    (hη : (η0 : ℝ) ≤ η) (hδ : (δ0 : ℝ) ≤ δ)
    (haccuracy : finiteBadMass law F
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ))
        (kappaApproxQ box : ℝ) (lambdaApproxQ box : ℝ)) ((η0/2 : ℚ) : ℝ) ≤ (δ0 : ℝ)) :
    finiteBadMass law F
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam) η ≤ δ := by
  have hb := physical_box_loss_bias (r := r) box U a b c k hz u e κ lam hklo hU
    hκlo hκhi hlam0 hlamlo hlamhi hu
  have hbr : (parameterBiasQ d r U box : ℝ) ≤ ((η0/2 : ℚ) : ℝ) := by exact_mod_cast hbudget
  have he : ((η0/2 : ℚ) : ℝ)=(η0 : ℝ)/2 := by push_cast; rfl
  have hdist : |spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ))
        (kappaApproxQ box : ℝ) (lambdaApproxQ box : ℝ)-
      spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam| ≤ η-((η0/2 : ℚ) : ℝ) := by
    apply hb.trans
    apply hbr.trans
    rw [he]
    linarith
  exact (finite_bad_mass_change_center law F _ _ _ _ hdist).trans (haccuracy.trans hδ)

set_option synthInstance.maxSize 1024 in
/-- Complete original `enclosed_native_estimator_accuracy` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem enclosed_native_estimator_accuracy {d r : ℕ} (box : PhysicalBoxQ) (U η0 δ0 eb : ℚ)
    (κ lam η δ : ℝ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) (kappaApproxQ box) (lambdaApproxQ box) U (η0/2)=some coef)
    (hd : 0 < d) (hklo : 0 < box.kappa.lo) (hU : 0 ≤ U) (hη0 : 0 < η0) (hδ0 : 0 < δ0)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : 0 < coef.gamma)
    (hκlo : (box.kappa.lo : ℝ) ≤ κ) (hκhi : κ ≤ (box.kappa.hi : ℝ))
    (hlam0 : 0 ≤ lam) (hlamlo : (box.lambda.lo : ℝ) ≤ lam) (hlamhi : lam ≤ (box.lambda.hi : ℝ))
    (hbudget : parameterBiasQ d r U box ≤ η0/2) (hη : (η0 : ℝ) ≤ η) (hδ : (δ0 : ℝ) ≤ δ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma (η0/2) δ0
    let e := periodicUnitShift d (2^r)
    finiteBadMass (NativeBridge.nativeTotalRecordLaw d r a b c k hz
      p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks)
      (fun z => (totalMedianOutputQ (2^(d*r)) û (fun j => periodicDoubleShift d (2^r) j)
        coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam) η ≤ δ := by
  have hs := NativeBridge.native_estimator_accuracy (kappaApproxQ box) (lambdaApproxQ box)
    U (η0/2) δ0 eb coef hc hd hklo hU (by linarith) hδ0 heb0 heb hγ a b c k hz u û hu htarget
  dsimp only at hs ⊢
  exact physical_box_accuracy_transfer box U η0 δ0 a b c k hz u (periodicUnitShift d (2^r))
    κ lam η δ _ _ hklo hU hκlo hκhi hlam0 hlamlo hlamhi hu hbudget hη hδ hs

set_option synthInstance.maxSize 1024 in
/-- Complete original `enclosed_native_estimator_accuracy_zero_spin` guarantee for `ParameterEncoding`; all source hypotheses and output obligations are retained. -/
theorem enclosed_native_estimator_accuracy_zero_spin {d r : ℕ} (box : PhysicalBoxQ) (U η0 δ0 eb : ℚ)
    (κ lam η δ : ℝ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) (kappaApproxQ box) (lambdaApproxQ box) U (η0/2)=some coef)
    (hd : 0 < d) (hklo : 0 < box.kappa.lo) (hU : 0 ≤ U) (hη0 : 0 < η0) (hδ0 : 0 < δ0)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : coef.gamma=0)
    (hκlo : (box.kappa.lo : ℝ) ≤ κ) (hκhi : κ ≤ (box.kappa.hi : ℝ))
    (hlam0 : 0 ≤ lam) (hlamlo : (box.lambda.lo : ℝ) ≤ lam) (hlamhi : lam ≤ (box.lambda.hi : ℝ))
    (hbudget : parameterBiasQ d r U box ≤ η0/2) (hη : (η0 : ℝ) ≤ η) (hδ : (δ0 : ℝ) ≤ δ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma (η0/2) δ0
    let e := periodicUnitShift d (2^r)
    finiteBadMass (NativeBridge.nativeVelocityRecordLaw d r a b c k hz p.velocityRecords p.velocityBlocks)
      (fun z => (velocityOnlyOutputQ (2^(d*r)) û coef.alpha coef.beta (U+eb) z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam) η ≤ δ := by
  have hs := NativeBridge.native_zero_spin_estimator_accuracy (kappaApproxQ box) (lambdaApproxQ box)
    U (η0/2) δ0 eb coef hc hd hklo hU (by linarith) hδ0 heb0 heb hγ a b c k hz u û hu htarget
  have hδr : (0 : ℝ) < (δ0 : ℝ) := by exact_mod_cast hδ0
  have hs' := hs.trans (by linarith : (δ0 : ℝ)/2 ≤ (δ0 : ℝ))
  dsimp only at hs' ⊢
  exact physical_box_accuracy_transfer box U η0 δ0 a b c k hz u (periodicUnitShift d (2^r))
    κ lam η δ _ _ hklo hU hκlo hκhi hlam0 hlamlo hlamhi hu hbudget hη hδ hs'

end
end Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding

#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.implemented_target_absorb
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.scalar_parameter_loss_bias
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.reciprocal_interval_error
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.lambda_interval_error
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.periodic_grid_scale_bounds
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.rat_max_zero_cast
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.physical_box_loss_bias
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.physical_box_accuracy_transfer
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.enclosed_native_estimator_accuracy
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding.enclosed_native_estimator_accuracy_zero_spin
