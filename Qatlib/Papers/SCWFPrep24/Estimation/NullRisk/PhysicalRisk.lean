/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.SeparablePOVM
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.FiniteRisk

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

/-!
# Physical Risk

The literal probability of each complete hidden fourth-root assignment.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Foundations.FiniteStats.BornEstimator

/-- The literal probability of each complete hidden fourth-root assignment. -/
def phasePriorWeight {A : Type*} [Fintype A] (_ : A → Fin 4) : ℝ := ∏ _ : A, (1/4 : ℝ)

/-- The actual complete phase weights are nonnegative. -/
theorem phasePriorWeight_nonneg {A : Type*} [Fintype A] (ω : A → Fin 4) :
    0 ≤ phasePriorWeight ω := Finset.prod_nonneg fun _ _ => by norm_num

/-- The complete hidden-phase probability weights sum to one, including the empty address set. -/
theorem phasePriorWeight_sum_one {A : Type*} [Fintype A] :
    (∑ ω : A → Fin 4, phasePriorWeight ω) = 1 := by
  simpa only [phaseMeanReal, phasePriorWeight, mul_one] using (@phaseMeanReal_one A _)

/-- The actual normalized finite prior on the six global null frames and one shared complete phase assignment. -/
def nullPriorWeight {A : Type*} [Fintype A]
    (z : (Fin 3 × Bool) × (A → Fin 4)) : ℝ := phasePriorWeight z.2/6

/-- The physical null input prior has nonnegative actual weights. -/
theorem nullPriorWeight_nonneg {A : Type*} [Fintype A]
    (z : (Fin 3 × Bool) × (A → Fin 4)) : 0 ≤ nullPriorWeight z :=
  div_nonneg (phasePriorWeight_nonneg _) (by norm_num)

/-- The physical six-frame shared-phase null input prior is exactly normalized. -/
theorem nullPriorWeight_sum_one {A : Type*} [Fintype A] :
    (∑ z : (Fin 3 × Bool) × (A → Fin 4), nullPriorWeight z) = 1 := by
  simp only [nullPriorWeight, Fintype.sum_prod_type, ← Finset.sum_div, phasePriorWeight_sum_one]
  norm_num

/-- The literal actual finite POVM outcome probabilities on two identical supplied copies of one input. -/
def physicalOutcome {A O : Type*} [Fintype A]  [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (v : A → Fin 2 → ℂ) (ω : A → Fin 4) (o : O) : ℝ :=
  effectWeight (P.mats o) (pairedState (phasedFieldState v ω))

/-- Every physical finite POVM outcome probability is nonnegative. -/
theorem physicalOutcome_nonneg {A O : Type*} [Fintype A]  [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (v : A → Fin 2 → ℂ) (ω : A → Fin 4) (o : O) : 0 ≤ physicalOutcome P v ω o :=
  effectWeight_nonneg _ (P.nonneg o) _

/-- The actual physical finite POVM output law is normalized for every individual point-normalized input and complete hidden-phase assignment. -/
theorem physicalOutcome_sum_one {A O : Type*} [Fintype A]
    [Nonempty A] [Fintype O] (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (v : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (ω : A → Fin 4) : ∑ o, physicalOutcome P v ω o = 1 := by
  have hψ : ∑ i, Complex.normSq (phasedFieldState v ω i) = 1 := by
    simpa only [Qatlib.Foundations.PureStateMath.Normalized,
      Complex.sq_norm] using phasedFieldState_normalized v hv ω
  exact canonical_povm_effectWeight_sum P _ (pairedState_normalized _ hψ)

/-- The physical null output law for one fixed complete input; the prior does not resample its phases between copies. -/
def nullPhysicalOutcome {A O : Type*} [Fintype A]  [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2))) (parity : A → Bool)
    (z : (Fin 3 × Bool) × (A → Fin 4)) : O → ℝ :=
  physicalOutcome P (nullField parity z.1.1 z.1.2) z.2

/-- The finite null-input law is exactly the literal six-frame shared-phase Born prior already bounded for positive separable effects. -/
theorem nullPhysicalOutcome_prior_eq {A O : Type*} [Fintype A]
    [Fintype O] (P : POVM O ((A × Fin 2) × (A × Fin 2))) (parity : A → Bool) (o : O) :
    priorLaw (@nullPriorWeight A _) (nullPhysicalOutcome P parity) o =
      nullSeparablePrior (P.mats o) parity := by
  unfold priorLaw nullPriorWeight nullPhysicalOutcome physicalOutcome nullSeparablePrior
  simp only [Fintype.sum_prod_type, phaseMeanReal, phasePriorWeight,
    ← Finset.sum_div, div_mul_eq_mul_div]

/-- Every actual null frame is pointwise normalized before measurement. -/
theorem nullField_normalized {A : Type*} (parity : A → Bool) (axis : Fin 3) (sign : Bool)
    (x : A) : ∑ i, Complex.normSq (nullField parity axis sign x i) = 1 :=
  sixPauliState_mass axis (sign ^^ parity x)

/-- The derived physical domination holds for the literal finite null input prior and each arbitrary normalized alternative field. No likelihood bound is accepted as an input. -/
theorem physical_prior_domination {A O K : Type*} [Fintype A]
    [Fintype O] [Fintype K] (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (E F : O → K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (parity : A → Bool) (v : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) (o : O) :
    priorLaw (@phasePriorWeight A _) (physicalOutcome P v) o ≤
      24*priorLaw (@nullPriorWeight A _) (nullPhysicalOutcome P parity) o := by
  rw [nullPhysicalOutcome_prior_eq]
  simpa only [priorLaw, phasePriorWeight, physicalOutcome, phaseMeanReal] using
    canonical_separable_povm_prior_domination P E F hE hF hsep v hv parity o

/-- A finite-output estimator with bounded bias on these actual complete-input laws has an attained physical null variance floor. The remaining scientific obligations are to instantiate the alternative full-loss gap and all legal periodic promises. -/
theorem physical_bounded_bias_null_variance {A O K : Type*} [Fintype A]
     [Nonempty A] [Fintype O] [Fintype K]
    (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (E F : O → K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (parity : A → Bool) (v : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (y : O → ℝ) (loss1 : (A → Fin 4) → ℝ) (S beta : ℝ)
    (hbeta : 0 ≤ beta) (hsmall : beta < S)
    (hnull : ∀ z, |mean (nullPhysicalOutcome P parity z) y| ≤ beta)
    (halt : ∀ ω, |mean (physicalOutcome P v ω) y - loss1 ω| ≤ beta)
    (hgap : ∀ ω, S ≤ loss1 ω) :
    ∃ z, (S-beta)^2/24-beta^2 ≤ variance (nullPhysicalOutcome P parity z) y := by
  exact bounded_bias_null_variance_from_priors
    (Z0 := (Fin 3 × Bool) × (A → Fin 4)) (Z1 := A → Fin 4) (O := O)
    (@nullPriorWeight A _) (@phasePriorWeight A _) (nullPhysicalOutcome P parity)
    (physicalOutcome P v) y loss1 S beta
    nullPriorWeight_nonneg phasePriorWeight_nonneg nullPriorWeight_sum_one
    phasePriorWeight_sum_one
    (fun z => physicalOutcome_sum_one P _ (nullField_normalized parity z.1.1 z.1.2) z.2)
    (physicalOutcome_sum_one P v hv) (physicalOutcome_nonneg P v)
    hbeta hsmall hnull halt hgap (physical_prior_domination P E F hE hF hsep parity v hv)

/-- On the actual canonical separable measurement, bounded bias on the physical alternative gives an attained null mean-square-error floor at zero target loss. This conclusion needs no hypothesis of small null bias and no supplied probability domination. -/
theorem physical_bounded_bias_null_second {A O K : Type*} [Fintype A]
    [Nonempty A] [Fintype O] [Fintype K]
    (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (E F : O → K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (parity : A → Bool) (v : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (y : O → ℝ) (loss1 : (A → Fin 4) → ℝ) (S beta : ℝ)
    (hsmall : beta < S)
    (halt : ∀ ω, |mean (physicalOutcome P v ω) y-loss1 ω| ≤ beta)
    (hgap : ∀ ω, S ≤ loss1 ω) :
    ∃ z, (S-beta)^2/24 ≤ second (nullPhysicalOutcome P parity z) y := by
  have hm : S-beta ≤ mean (priorLaw (@phasePriorWeight A _) (physicalOutcome P v)) y := by
    rw [priorLaw_mean]
    calc S-beta = ∑ ω : A → Fin 4, phasePriorWeight ω*(S-beta) := by
           rw [← Finset.sum_mul, phasePriorWeight_sum_one, one_mul]
         _ ≤ ∑ ω, phasePriorWeight ω*mean (physicalOutcome P v ω) y := by
           apply Finset.sum_le_sum
           intro ω _
           apply mul_le_mul_of_nonneg_left _ (phasePriorWeight_nonneg ω)
           have hb := (abs_le.mp (halt ω)).1
           linarith [hgap ω]
  have hp : ∀ o, 0 ≤ priorLaw (@phasePriorWeight A _) (physicalOutcome P v) o := by
    intro o
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (phasePriorWeight_nonneg ω) (physicalOutcome_nonneg P v ω o)
  have hsq : (S-beta)^2 ≤ second (priorLaw (@phasePriorWeight A _) (physicalOutcome P v)) y := by
    calc (S-beta)^2 ≤ (mean (priorLaw (@phasePriorWeight A _) (physicalOutcome P v)) y)^2 :=
           pow_le_pow_left₀ (sub_pos.mpr hsmall).le hm 2
         _ ≤ _ := finite_mean_sq_le_second _ hp
           (priorLaw_sum_one _ _ phasePriorWeight_sum_one (physicalOutcome_sum_one P v hv)) y
  have hd := second_le_of_leaf_domination
    (priorLaw (@nullPriorWeight A _) (nullPhysicalOutcome P parity))
    (priorLaw (@phasePriorWeight A _) (physicalOutcome P v)) y
    (physical_prior_domination P E F hE hF hsep parity v hv)
  have he : second (priorLaw (@nullPriorWeight A _) (nullPhysicalOutcome P parity)) y =
      ∑ z, nullPriorWeight z*second (nullPhysicalOutcome P parity z) y :=
    priorLaw_mean _ _ (fun o => y o^2)
  apply exists_score_ge_prior_mean (@nullPriorWeight A _)
    (fun z => second (nullPhysicalOutcome P parity z) y)
    nullPriorWeight_nonneg nullPriorWeight_sum_one
  rw [← he]
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
