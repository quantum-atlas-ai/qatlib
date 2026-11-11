/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.FullLossNuisance
import Qatlib.Concepts.SpinorSampling.Retained.LowSpinAccounting
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Upper

A fixed public finite rational current coefficient approximates the actual original coefficient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder Kronecker

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

/-- A fixed public finite rational current coefficient approximates the actual original coefficient. -/
theorem velocity_coefficient_error : |(1/36 : ℝ)-1/(4*Real.pi^2)|≤1/200 := by
  have hp : 0<4*Real.pi^2 := by positivity
  have hlo := Real.pi_gt_d2
  have hhi := Real.pi_lt_d2
  have hplo : (3.14 : ℝ)^2<Real.pi^2 := by nlinarith [Real.pi_pos]
  have hphi : Real.pi^2<(3.15 : ℝ)^2 := by nlinarith [Real.pi_pos]
  have hu : 1/(4*Real.pi^2)≤(1/36 : ℝ) := (div_le_iff₀ hp).2 (by nlinarith)
  have hl : (1/36 : ℝ)-1/200≤1/(4*Real.pi^2) := (le_div_iff₀ hp).2 (by nlinarith)
  rw [abs_of_nonneg (by linarith : 0≤(1/36 : ℝ)-1/(4*Real.pi^2))]
  linarith

/-- A fixed rational Bell coefficient approximates the actual original spin coefficient without a state-dependent input. -/
theorem spin_coefficient_error : |(81/1600 : ℝ)-1/(2*Real.pi^2)|≤1/4000 := by
  have hp : 0<2*Real.pi^2 := by positivity
  have hlo := Real.pi_gt_d2
  have hhi := Real.pi_lt_d2
  have hplo : (3.14 : ℝ)^2<Real.pi^2 := by nlinarith [Real.pi_pos]
  have hphi : Real.pi^2<(3.15 : ℝ)^2 := by nlinarith [Real.pi_pos]
  have hu : 1/(2*Real.pi^2)≤(81/1600 : ℝ)+1/4000 := (div_le_iff₀ hp).2 (by nlinarith)
  have hl : (81/1600 : ℝ)-1/4000≤1/(2*Real.pi^2) := (le_div_iff₀ hp).2 (by nlinarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Finite rational coefficients preserve the full physical velocity and Bell loss, with their same actual two bounded statistics. -/
theorem full_loss_coefficient_bias (N D X Y : ℝ) (hN : 0<N) (hD : D≤3)
    (hX0 : 0≤X) (hX : X≤D) (hY0 : 0≤Y) (hY : Y≤256*D/N^2) :
    |(N^2/36*X+81*N^4/1600*Y)-(N^2/(4*Real.pi^2)*X+N^4/(2*Real.pi^2)*Y)|≤N^2/4 := by
  have hdx := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left velocity_coefficient_error (sq_nonneg N)) hX0
  have hdy := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left spin_coefficient_error (pow_nonneg hN.le 4)) hY0
  have he : |(N^2/36*X+81*N^4/1600*Y)-(N^2/(4*Real.pi^2)*X+N^4/(2*Real.pi^2)*Y)|=
      |N^2*((1/36 : ℝ)-1/(4*Real.pi^2))*X+N^4*((81/1600 : ℝ)-1/(2*Real.pi^2))*Y| := by
    congr 1
    ring
  rw [he]
  have hab := abs_add_le (N^2*((1/36 : ℝ)-1/(4*Real.pi^2))*X)
    (N^4*((81/1600 : ℝ)-1/(2*Real.pi^2))*Y)
  simp only [abs_mul,abs_of_nonneg (sq_nonneg N),abs_of_nonneg (pow_nonneg hN.le 4),
    abs_of_nonneg hX0,abs_of_nonneg hY0] at hab
  have hx := mul_le_mul_of_nonneg_left hX (show 0≤N^2*(1/200 : ℝ) by positivity)
  have hy := mul_le_mul_of_nonneg_left hY (show 0≤N^4*(1/4000 : ℝ) by positivity)
  have hyid : N^4*(1/4000 : ℝ)*(256*D/N^2)=(256/4000 : ℝ)*D*N^2 := by
    field_simp [ne_of_gt hN]
  rw [hyid] at hy
  have hd := mul_le_mul_of_nonneg_left hD (sq_nonneg N)
  nlinarith [hdx,hdy,hx,hy,hab]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Matching.Matched

/-- Explicit finite rational coefficients instantiate the existing complete native low-spin schedule. -/
def physicalPlan (D N M : ℕ) (rootM δ : ℚ) : LowSpinPlanQ :=
  lowSpinPlanQ N D M rootM ((N : ℚ)/6) 1 0 (81*(N : ℚ)^4/6400)
    ((N : ℚ)^2) δ (256/(N : ℚ)^2)

/-- In the original physical dimensions the existing velocity plan's actual tolerance legally selects its zero-copy branch. -/
theorem physical_velocity_zero (D N M : ℕ) (rootM δ : ℚ) (hD0 : 0<D) (hD3 : D≤3) (hN : 0<N) :
    (physicalPlan D N M rootM δ).velocity.current.mode=.zero ∧
    (physicalPlan D N M rootM δ).velocity.current.copies=0 ∧
    (physicalPlan D N M rootM δ).velocity.crossRecords=0 ∧
    (physicalPlan D N M rootM δ).velocity.norm.mode=.zero ∧
    (physicalPlan D N M rootM δ).velocity.copies=0 := by
  have hd : (0 : ℚ)<D := by exact_mod_cast hD0
  have hd3 : (D : ℚ)≤3 := by exact_mod_cast hD3
  have hn : (0 : ℚ)<N := by exact_mod_cast hN
  have he : ((N : ℚ)^2/(8*(D : ℚ)))/((N : ℚ)/6)^2=9/(2*(D : ℚ)) := by
    field_simp [ne_of_gt hd,ne_of_gt hn]
    ring
  have ht : (1 : ℚ)≤((N : ℚ)^2/(8*(D : ℚ)))/((N : ℚ)/6)^2 := by
    rw [he]
    apply (le_div_iff₀ (mul_pos (by norm_num) hd)).2
    nlinarith
  simp only [physicalPlan,lowSpinPlanQ,highConfidencePlanQ,correlationPlanQ,ite_eq_left ht,
    linearCountQ,mul_zero,true_or,ite_true,
    targetNormPlanQ,Nat.add_zero,and_self]

/-- The existing Bell branch uses the exact public N-inverse-square tolerance, with no hidden dependence on the physical spinor. -/
theorem physical_bell_fields (D N M : ℕ) (rootM δ : ℚ) (hD : 0<D) (hN : 0<N) :
    (physicalPlan D N M rootM δ).spin=
      some (bellPlanQ N M (256/(N : ℚ)^2) (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ)))) := by
  have hd : (D : ℚ)≠0 := by exact_mod_cast (ne_of_gt hD)
  have hn : (N : ℚ)≠0 := by exact_mod_cast (ne_of_gt hN)
  have hg : 81*(N : ℚ)^4/6400≠0 := by positivity
  have ht : (N : ℚ)^2/(32*(D : ℚ)*(81*(N : ℚ)^4/6400))=200/(81*(D : ℚ)*(N : ℚ)^2) := by
    field_simp [hd,hn]
    ring
  simp only [physicalPlan,lowSpinPlanQ,ite_eq_right hg,ht]

/-- The literal complete plan charges exactly its executed Bell branch in this physical regime; no uncharged quantum preparation or target query is added. -/
theorem physical_copies (D N M : ℕ) (rootM δ : ℚ) (hD0 : 0<D) (hD3 : D≤3) (hN : 0<N) :
    (physicalPlan D N M rootM δ).copies=
      D*(bellPlanQ N M (256/(N : ℚ)^2) (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ)))).copies := by
  have hv := (physical_velocity_zero D N M rootM δ hD0 hD3 hN).2.2.2.2
  have hb := physical_bell_fields D N M rootM δ hD0 hN
  have ha := (low_plan_account_fields N D M rootM ((N : ℚ)/6) 1 0
    (81*(N : ℚ)^4/6400) ((N : ℚ)^2) δ (256/(N : ℚ)^2)).1
  change (physicalPlan D N M rootM δ).copies=_
  change (physicalPlan D N M rootM δ).copies=
    (physicalPlan D N M rootM δ).velocity.copies+
      (match (physicalPlan D N M rootM δ).spin with | none => 0 | some q => D*q.copies) at ha
  rw [ha,hv,hb,zero_add]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
open scoped BigOperators Classical
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Matching.Matched
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The same physical current and Bell statistics give the finite-coefficient approximation error for the literal full loss, on every original promised field. -/
theorem original_physical_bias {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]
    (D N : ℕ) (hD : D≤3) (hN : 0<N)
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin D → Equiv.Perm S)
    (hmean : ∀ j,bellMean a b c k ((e j).trans (e j))≤256/(N : ℝ)^2) :
    |implementedResidualLoss (spinorCurrentMean a b c k e) (fun _ _ => 0) (pauliField a b c k)
      (fun j => (e j).trans (e j)) ((N : ℝ)/6) 1 (81*(N : ℝ)^4/6400)-
      spinorDiscreteLoss a b c k (fun _ _ => 0) e (2*Real.pi/N) 1 N|≤(N : ℝ)^2/4 := by
  let X := ∑ j : Fin D,siteMean (fun x => (spinorCurrentMean a b c k e j x)^2)
  let Y := ∑ j : Fin D,bellMean a b c k ((e j).trans (e j))
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hX0 : 0≤X := Finset.sum_nonneg (fun _ _ => site_mean_nonneg _ (fun _ => sq_nonneg _))
  have hX : X≤(D : ℝ) := by
    have hbound (j : Fin D) : siteMean (fun x => (spinorCurrentMean a b c k e j x)^2)≤1 := by
      have h (x : S) : |(spinorCurrentMean a b c k e j x)^2|≤1 := by
        have hb := abs_le.mp (spinor_current_mean_bound a b c k hz e j x)
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith
      exact (le_abs_self _).trans (site_mean_abs_le_one _ h)
    calc
      _ ≤ ∑ _j : Fin D,(1 : ℝ) := Finset.sum_le_sum (fun j _ => hbound j)
      _ = _ := by simp
  have hY0 : 0≤Y := Finset.sum_nonneg (fun j _ => bell_mean_nonneg a b c k hz ((e j).trans (e j)))
  have hY : Y≤256*(D : ℝ)/(N : ℝ)^2 := by
    calc
      _ ≤ ∑ _j : Fin D,256/(N : ℝ)^2 := Finset.sum_le_sum (fun j _ => hmean j)
      _ = _ := by simp; ring
  have hexpand (α γ : ℝ) :
      implementedResidualLoss (spinorCurrentMean a b c k e) (fun _ _ => 0) (pauliField a b c k)
        (fun j => (e j).trans (e j)) α 1 γ=α^2*X+4*γ*Y := by
    rw [implemented_loss_bell_form _ _ a b c k hz]
    simp only [mul_zero,sub_zero,mul_pow,site_mean_mul,←Finset.mul_sum]
    rfl
  have hmesh : 2*Real.pi/(N : ℝ)≠0 := div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn.ne'
  rw [spinor_discrete_loss_eq a b c k hz (fun _ _ => 0) e _ 1 N hmesh one_ne_zero]
  simp only [div_one]
  rw [hexpand,hexpand]
  have hc := full_loss_coefficient_bias (N : ℝ) D X Y hn (by exact_mod_cast hD) hX0 hX hY0 hY
  convert hc using 1
  congr 1
  field_simp [hn.ne',Real.pi_ne_zero]
  ring

/-- The literal actual native output law estimates the original full physical loss. The plan is an ordinary parameter so its finite observation carrier is elaborated once before a concrete schedule is substituted. -/
def NativeOriginalAccurate (D r : ℕ) (p : LowSpinPlanQ) (α γ : ℚ) (δ : ℝ)
    (a b c k : (Fin D → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) : Prop :=
  finiteBadMass (nativeLowSpinLaw D r p a b c k hz)
    (fun z => (lowSpinOutputQ p (fun _ _ => 0) (periodicDoubleShift D (2^r)) α 1 0 γ z : ℝ))
    (spinorDiscreteLoss a b c k (fun _ _ => 0) (periodicUnitShift D (2^r))
      (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (2^r)) (((2^r : ℕ) : ℝ)^2)≤δ

/-- Transfer the actual native statistic to the full original loss using a coefficient-bias bound; the concrete physical consumer proves this bound internally. -/
theorem native_original_transfer (D r : ℕ) (hD0 : 0<D) (hsize : 256≤(2^r : ℕ))
    (α γ δ : ℚ) (hα : 0<α) (hγ : 0≤γ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b c k : (Fin D → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (hmean : ∀ j,bellMean a b c k (periodicDoubleShift D (2^r) j)≤256/((2^r : ℕ) : ℝ)^2)
    (hbias : |implementedResidualLoss (spinorCurrentMean a b c k (periodicUnitShift D (2^r)))
      (fun _ _ => 0) (pauliField a b c k) (periodicDoubleShift D (2^r)) (α : ℝ) 1 (γ : ℝ)-
      spinorDiscreteLoss a b c k (fun _ _ => 0) (periodicUnitShift D (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (2^r)|≤(((2^r : ℕ) : ℝ)^2)/4) :
    NativeOriginalAccurate D r
      (lowSpinPlanQ (2^r) D (2^(D*r)) ((2^((D*r+1)/2) : ℕ) : ℚ) α 1 0 γ (((2^r : ℕ) : ℚ)^2) δ (256/((2^r : ℕ) : ℚ)^2))
      α γ (δ : ℝ) a b c k hz := by
  have hN : 0<(2^r : ℕ) := by positivity
  have hp : (0 : ℚ)≤256/((2^r : ℕ) : ℚ)^2 := by positivity
  have hp1 : 256/((2^r : ℕ) : ℚ)^2≤1/2 := by
    have hn : (256 : ℚ)≤((2^r : ℕ) : ℚ) := by exact_mod_cast hsize
    apply (div_le_iff₀ (by positivity : (0 : ℚ)<((2^r : ℕ) : ℚ)^2)).2
    nlinarith
  let p := lowSpinPlanQ (2^r) D (2^(D*r)) ((2^((D*r+1)/2) : ℕ) : ℚ) α 1 0 γ (((2^r : ℕ) : ℚ)^2) δ (256/((2^r : ℕ) : ℚ)^2)
  let law := nativeLowSpinLaw D r p a b c k hz
  let F := fun z : LowSpinData (Fin D → Fin (2^r)) D (periodicDoubleShift D (2^r)) p =>
    (lowSpinOutputQ p (fun _ _ => 0) (periodicDoubleShift D (2^r))
      α 1 0 γ z : ℝ)
  let L0 := spinorDiscreteLoss a b c k (fun _ _ => 0) (periodicUnitShift D (2^r))
    (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (2^r)
  let L1 := implementedResidualLoss (spinorCurrentMean a b c k (periodicUnitShift D (2^r)))
    (fun _ _ => 0) (pauliField a b c k) (periodicDoubleShift D (2^r))
    ((α : ℚ) : ℝ) (1 : ℝ)
    ((γ : ℚ) : ℝ)
  have ht := native_low_spin_accuracy hD0 a b c k hz (fun _ _ => 0)
    α 1 0 γ (((2^r : ℕ) : ℚ)^2) δ
    (256/((2^r : ℕ) : ℚ)^2) (by positivity) (by norm_num) (by norm_num) (by positivity)
    (by intro; norm_num) (by positivity) hδ hδ1 hp hp1 (by intro _ j; push_cast; simpa only [Nat.cast_pow,Nat.cast_ofNat] using hmean j)
  simp only [Rat.cast_zero,Rat.cast_one] at ht
  change finiteBadMass law F L1 (((((2^r : ℕ) : ℚ)^2 : ℚ) : ℝ)/2)≤(δ : ℝ) at ht
  have hb' : |L1-L0|≤(((2^r : ℕ) : ℝ)^2)/4 := by
    simpa only [L1,L0,Rat.cast_one] using hbias
  have hη : (((((2^r : ℕ) : ℚ)^2 : ℚ) : ℝ))=(((2^r : ℕ) : ℝ)^2) := by norm_cast
  change finiteBadMass law F L0 (((2^r : ℕ) : ℝ)^2)≤(δ : ℝ)
  apply (finite_bad_mass_change_center law F L0 L1
    (((((2^r : ℕ) : ℚ)^2 : ℚ) : ℝ)/2) (((2^r : ℕ) : ℝ)^2) ?_).trans ht
  rw [hη]
  linarith [hb',sq_nonneg (((2^r : ℕ) : ℝ))]


/-- The same actual complete native estimator, with explicit public finite coefficients, estimates the original full physical loss at its original tolerance and confidence. -/
theorem original_native_accuracy (D r : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hsize : 256≤(2^r : ℕ))
    (δ : ℚ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b c k : (Fin D → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (hmean : ∀ j,bellMean a b c k (periodicDoubleShift D (2^r) j)≤256/((2^r : ℕ) : ℝ)^2) :
    NativeOriginalAccurate D r
      (physicalPlan D (2^r) (2^(D*r)) ((2^((D*r+1)/2) : ℕ) : ℚ) δ)
      (((2^r : ℕ) : ℚ)/6) (81*((2^r : ℕ) : ℚ)^4/6400) (δ : ℝ) a b c k hz := by
  have hb := original_physical_bias D (2^r) hD3 (by positivity) a b c k hz (periodicUnitShift D (2^r))
    (by intro j; simpa only [periodic_unit_shift_square] using hmean j)
  apply native_original_transfer D r hD0 hsize
    (((2^r : ℕ) : ℚ)/6) (81*((2^r : ℕ) : ℚ)^4/6400) δ (by positivity) (by positivity)
    hδ hδ1 a b c k hz hmean
  simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast,
    Nat.cast_pow,Nat.cast_ofNat,periodic_unit_shift_square] using hb

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The literal public binary ceiling log is bounded by the original natural confidence log, uniformly throughout the full original confidence interval. -/
theorem physical_ceiling_log (D : ℕ) (hD0 : 0<D) (hD3 : D≤3) (δ : ℚ)
    (hδ : 0<δ) (hmax : δ≤1/10) :
    (ceilLog2Q (16*(D : ℚ)/δ) : ℝ)≤256*Real.log (1/(δ : ℝ)) := by
  let q : ℚ := 16*(D : ℚ)/δ
  have hd : (1 : ℚ)≤D := by exact_mod_cast hD0
  have hd3 : (D : ℚ)≤3 := by exact_mod_cast hD3
  have hqp : 1≤q := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hpow := ceil_log2_power_upper q
  rw [max_eq_right hqp] at hpow
  have hp : (2 : ℝ)^ceilLog2Q q≤2*(q : ℝ) := by exact_mod_cast hpow
  have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hp
  rw [Real.log_pow] at hl
  have hδr : (0 : ℝ)<δ := by exact_mod_cast hδ
  have hmaxr : (δ : ℝ)≤1/10 := by
    calc (δ : ℝ)≤((1/10 : ℚ) : ℝ) := Rat.cast_le.mpr hmax
         _ = 1/10 := by norm_num
  have hqbound : 2*(q : ℝ)≤96/(δ : ℝ) := by
    have h : 2*q≤96/δ := by
      dsimp [q]
      apply (le_div_iff₀ hδ).2
      field_simp [ne_of_gt hδ]
      nlinarith
    exact_mod_cast h
  have hqpR : (0 : ℝ)<2*(q : ℝ) := by exact_mod_cast (by linarith [hqp] : (0 : ℚ)<2*q)
  have hlogs := Real.log_le_log hqpR hqbound
  have he : Real.log (96/(δ : ℝ))=Real.log 96+Real.log (1/(δ : ℝ)) := by
    rw [Real.log_div (by norm_num : (96 : ℝ)≠0) hδr.ne',one_div,Real.log_inv]
    ring
  rw [he] at hlogs
  have h96 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<96)
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
  have hL := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδr)
  simp only [inv_div,div_one] at hL
  norm_num at h2 h96
  have hk0 : (0 : ℝ)≤ceilLog2Q q := Nat.cast_nonneg _
  have hk := mul_le_mul_of_nonneg_left h2 hk0
  change (ceilLog2Q q : ℝ)≤_
  nlinarith

/-- The strength of the actual executed original Bell schedule is bounded by a fixed multiple of N-squared times the original confidence log. -/
theorem physical_bell_strength (D N : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hN : 0<N)
    (δ : ℚ) (hδ : 0<δ) (hmax : δ≤1/10) :
    (bellStrengthQ (256/(N : ℚ)^2) (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ))) : ℝ)≤
      16777216*(N : ℝ)^2*Real.log (1/(δ : ℝ)) := by
  have hd : (D : ℚ)≠0 := by exact_mod_cast (ne_of_gt hD0)
  have hn : (N : ℚ)≠0 := by exact_mod_cast (ne_of_gt hN)
  have hr : (4 : ℚ)/(δ/(4*(D : ℚ)))=16*(D : ℚ)/δ := by
    field_simp [hd,ne_of_gt hδ]
    norm_num
  have he : bellStrengthQ (256/(N : ℚ)^2) (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ)))=
      ((3359232/625 : ℚ)*(D : ℚ)^2+(1296/25 : ℚ)*(D : ℚ))*(N : ℚ)^2*
        (ceilLog2Q (16*(D : ℚ)/δ) : ℚ) := by
    unfold bellStrengthQ
    rw [hr]
    field_simp [hd,hn]
    ring
  have heR := congrArg (fun x : ℚ => (x : ℝ)) he
  push_cast at heR
  rw [heR]
  have hd0 : (0 : ℝ)≤D := Nat.cast_nonneg _
  have hd3 : (D : ℝ)≤3 := by exact_mod_cast hD3
  have hd2 : (D : ℝ)^2≤9 := by nlinarith
  have hc : (3359232/625 : ℝ)*(D : ℝ)^2+(1296/25 : ℝ)*(D : ℝ)≤65536 := by nlinarith
  have hk := physical_ceiling_log D hD0 hD3 δ hδ hmax
  calc
    _ ≤ 65536*(N : ℝ)^2*(ceilLog2Q (16*(D : ℚ)/δ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ))) (Nat.cast_nonneg _)
    _ ≤ 65536*(N : ℝ)^2*(256*Real.log (1/(δ : ℝ))) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The exact charged complete native plan has the original high-confidence physical copy rate, with one explicit uniform constant. -/
theorem physical_copy_rate (D N M : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hN : 256≤N) (hM : 0<M)
    (rootM δ : ℚ) (hδ : 0<δ) (hmax : δ≤1/10) :
    ((physicalPlan D N M rootM δ).copies : ℝ)≤268435456*
      ((N : ℝ)^2*Real.log (1/(δ : ℝ))+(N : ℝ)*Real.sqrt ((M : ℝ)*Real.log (1/(δ : ℝ)))) := by
  let L := Real.log (1/(δ : ℝ))
  let S : ℝ := bellStrengthQ (256/(N : ℚ)^2) (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ)))
  have hδr : (0 : ℝ)<δ := by exact_mod_cast hδ
  have hmaxr : (δ : ℝ)≤1/10 := by
    calc (δ : ℝ)≤((1/10 : ℚ) : ℝ) := Rat.cast_le.mpr hmax
         _ = 1/10 := by norm_num
  have hlog := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδr)
  simp only [inv_div,div_one] at hlog
  have hL : (9/10 : ℝ)≤L := by dsimp [L]; linarith
  have hS := physical_bell_strength D N hD0 hD3 (by omega) δ hδ hmax
  change S≤16777216*(N : ℝ)^2*L at hS
  have hS0 : 0≤S := by
    apply Rat.cast_nonneg.mpr
    unfold bellStrengthQ
    positivity
  have hM0 : (0 : ℝ)≤M := Nat.cast_nonneg _
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hnr : (256 : ℝ)≤N := by exact_mod_cast hN
  have hn2 : (65536 : ℝ)≤(N : ℝ)^2 := by nlinarith
  have hA : 1≤(N : ℝ)^2*L := by
    have h := mul_le_mul_of_nonneg_left hL (sq_nonneg (N : ℝ))
    nlinarith
  have hroot0 : 0≤4096*(N : ℝ)*Real.sqrt ((M : ℝ)*L) := by positivity
  have he : (4096*(N : ℝ)*Real.sqrt ((M : ℝ)*L))^2=16777216*(N : ℝ)^2*(M : ℝ)*L := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hM0 (by linarith : 0≤L))]
    ring
  have hm := mul_le_mul_of_nonneg_left hS hM0
  have hsq : (Real.sqrt ((M : ℝ)*S))^2≤(4096*(N : ℝ)*Real.sqrt ((M : ℝ)*L))^2 := by
    rw [Real.sq_sqrt (mul_nonneg hM0 hS0),he]
    nlinarith
  have hr := (sq_le_sq₀ (Real.sqrt_nonneg _) hroot0).mp hsq
  have hp : (0 : ℚ)≤256/(N : ℚ)^2 := by positivity
  have hε : (0 : ℚ)<200/(81*(D : ℚ)*(N : ℚ)^2) := by positivity
  have hc := bell_plan_copies_upper N M hM (256/(N : ℚ)^2)
    (200/(81*(D : ℚ)*(N : ℚ)^2)) (δ/(4*(D : ℚ))) hp hε
  change _ ≤4*S+2*Real.sqrt ((M : ℝ)*S)+2 at hc
  rw [physical_copies D N M rootM δ hD0 hD3 (by omega),Nat.cast_mul]
  have hd0 : (0 : ℝ)≤D := Nat.cast_nonneg _
  have hd3 : (D : ℝ)≤3 := by exact_mod_cast hD3
  calc
    _ ≤(D : ℝ)*(4*S+2*Real.sqrt ((M : ℝ)*S)+2) := mul_le_mul_of_nonneg_left hc hd0
    _ ≤3*(4*S+2*Real.sqrt ((M : ℝ)*S)+2) := mul_le_mul_of_nonneg_right hd3 (by positivity)
    _ ≤_ := by
      change _ ≤268435456*((N : ℝ)^2*L+(N : ℝ)*Real.sqrt ((M : ℝ)*L))
      have hnroot : 0≤(N : ℝ)*Real.sqrt ((M : ℝ)*L) := by positivity
      nlinarith

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

/-- Every original real confidence is implemented by an actual finite rational confidence parameter, with a uniform original natural-log cost comparison. -/
theorem rational_confidence (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) :
    ∃ q : ℚ,0<q ∧ (q : ℝ)≤δ ∧ q≤1/10 ∧ Real.log (1/(q : ℝ))≤4*Real.log (1/δ) := by
  obtain ⟨q,hlo,hhi⟩ := exists_rat_btwn (show δ/2<δ by linarith)
  have hqR : (0 : ℝ)<q := by linarith
  have hq : (0 : ℚ)<q := Rat.cast_pos.mp hqR
  have hqmax : q≤1/10 := by
    have hh : (q : ℝ)≤((1/10 : ℚ) : ℝ) := by
      calc (q : ℝ)≤1/10 := hhi.le.trans hmax
           _ = ((1/10 : ℚ) : ℝ) := by norm_num
    exact Rat.cast_le.mp hh
  have hratio : 1/(q : ℝ)≤2/δ := by
    apply (div_le_div_iff₀ hqR hδ).2
    nlinarith
  have hlog := Real.log_le_log (one_div_pos.mpr hqR) hratio
  have he : Real.log (2/δ)=Real.log 2+Real.log (1/δ) := by
    rw [Real.log_div (by norm_num : (2 : ℝ)≠0) hδ.ne',one_div,Real.log_inv]
    ring
  rw [he] at hlog
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have hL := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδ)
  simp only [inv_div,div_one] at hL
  refine ⟨q,hq,hhi.le,hqmax,?_⟩
  nlinarith

/-- An actual rational schedule is chosen using only public parameters, and its exact complete-plan copy count obeys the original real-confidence physical rate. -/
theorem real_confidence_plan (D N M : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hN : 256≤N) (hM : 0<M)
    (rootM : ℚ) (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) :
    ∃ q : ℚ,0<q ∧ (q : ℝ)≤δ ∧ q≤1/10 ∧
      ((physicalPlan D N M rootM q).copies : ℝ)≤1073741824*
        ((N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt ((M : ℝ)*Real.log (1/δ))) := by
  obtain ⟨q,hq,hqδ,hqmax,hql⟩ := rational_confidence δ hδ hmax
  have hc := physical_copy_rate D N M hD0 hD3 hN hM rootM q hq hqmax
  have hM0 : (0 : ℝ)≤M := Nat.cast_nonneg _
  have hL : 0≤Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hqroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hql hM0)
  have he : Real.sqrt ((M : ℝ)*(4*Real.log (1/δ)))=2*Real.sqrt ((M : ℝ)*Real.log (1/δ)) := by
    rw [show (M : ℝ)*(4*Real.log (1/δ))=4*((M : ℝ)*Real.log (1/δ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ)≤4)]
    norm_num
  rw [he] at hqroot
  have hA := mul_le_mul_of_nonneg_left hql (sq_nonneg (N : ℝ))
  have hB := mul_le_mul_of_nonneg_left hqroot (Nat.cast_nonneg N : (0 : ℝ)≤N)
  refine ⟨q,hq,hqδ,hqmax,?_⟩
  have hnroot : 0≤(N : ℝ)*Real.sqrt ((M : ℝ)*Real.log (1/δ)) := by positivity
  nlinarith

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
open scoped Classical BigOperators
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Matching.Matched

/-- The same actual native output law preserves accuracy when the requested failure probability is increased. -/
theorem native_accuracy_mono (D r : ℕ) (p : LowSpinPlanQ) (α γ : ℚ) (δ0 δ : ℝ)
    (a b c k : (Fin D → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (hacc : NativeOriginalAccurate D r p α γ δ0 a b c k hz) (hle : δ0≤δ) :
    NativeOriginalAccurate D r p α γ δ a b c k hz := le_trans hacc hle

/-- One actual public finite schedule estimates the original full physical loss on every original promised input at any real confidence, with its same complete-plan copy rate. -/
theorem original_full_high_confidence_upper (D r : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hsize : 256≤(2^r : ℕ))
    (δ : ℝ) (hδ : 0<δ) (hmax : δ≤1/10) :
    ∃ (q : ℚ) (p : LowSpinPlanQ),
      (0<q ∧ (q : ℝ)≤δ ∧ p=physicalPlan D (2^r) (2^(D*r)) ((2^((D*r+1)/2) : ℕ) : ℚ) q) ∧
      (p.copies : ℝ)≤1073741824*((((2^r : ℕ) : ℝ)^2)*Real.log (1/δ)+
        ((2^r : ℕ) : ℝ)*Real.sqrt ((2^(D*r) : ℕ)*Real.log (1/δ))) ∧
      ∀ (a b c k : (Fin D → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1),
        (∀ j,bellMean a b c k (periodicDoubleShift D (2^r) j)≤256/((2^r : ℕ) : ℝ)^2) →
        NativeOriginalAccurate D r p (((2^r : ℕ) : ℚ)/6) (81*((2^r : ℕ) : ℚ)^4/6400) δ a b c k hz := by
  obtain ⟨q,hq,hqδ,hqmax,hcopy⟩ := real_confidence_plan D (2^r) (2^(D*r)) hD0 hD3 hsize
    (by positivity) ((2^((D*r+1)/2) : ℕ) : ℚ) δ hδ hmax
  refine ⟨q,physicalPlan D (2^r) (2^(D*r)) ((2^((D*r+1)/2) : ℕ) : ℚ) q,⟨hq,hqδ,rfl⟩,hcopy,?_⟩
  intro a b c k hz hmean
  have ha := original_native_accuracy D r hD0 hD3 hsize q hq (by linarith) a b c k hz hmean
  exact native_accuracy_mono D r _ _ _ (q : ℝ) δ a b c k hz ha hqδ

/-- The bound charges the same returned native execution receipt, including every consumed physical copy, for the complete unchanged schedule. -/
theorem physical_executed_copy_rate {S : Type} [Fintype S] [Nonempty S] [DecidableEq S] [LinearOrder S]
    (D N : ℕ) (hD0 : 0<D) (hD3 : D≤3) (hN : 256≤N) (rootM δ : ℚ) (hδ : 0<δ) (hmax : δ≤1/10)
    (e : Fin D → Equiv.Perm S)
    (z : LowSpinData S D e (physicalPlan D N (Fintype.card S) rootM δ)) :
    let p := physicalPlan D N (Fintype.card S) rootM δ
    ((executeLowSpinQ p (fun _ _ => 0) e ((N : ℚ)/6) 1 0 (81*(N : ℚ)^4/6400) z).copies : ℝ)≤
      268435456*((N : ℝ)^2*Real.log (1/(δ : ℝ))+
        (N : ℝ)*Real.sqrt ((Fintype.card S : ℝ)*Real.log (1/(δ : ℝ)))) := by
  have he := executed_low_spin_copies N D rootM ((N : ℚ)/6) 1 0 (81*(N : ℚ)^4/6400)
    ((N : ℚ)^2) δ (256/(N : ℚ)^2) (fun _ _ => 0) e z
  change (executeLowSpinQ (physicalPlan D N (Fintype.card S) rootM δ) (fun _ _ => 0) e
    ((N : ℚ)/6) 1 0 (81*(N : ℚ)^4/6400) z).copies=(physicalPlan D N (Fintype.card S) rootM δ).copies at he
  change (_ : ℝ)≤_
  rw [he]
  exact physical_copy_rate D N (Fintype.card S) hD0 hD3 hN (Fintype.card_pos) rootM δ hδ hmax

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalUpper
