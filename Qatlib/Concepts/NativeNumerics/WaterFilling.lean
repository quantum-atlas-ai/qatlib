/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.HhlAlgorithms.Postselection.FreshTrials
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.NativeNumerics.WaterFilling
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

def waterFill {m : ℕ} (pi sigma : Fin m  → ℚ) (lam : ℚ) (i : Fin m) : ℚ := min (pi i) (lam*sigma i)

def waterGamma {m : ℕ} (pi sigma : Fin m  → ℚ) (lam : ℚ) (i : Fin m) : ℚ :=
  if pi i=0 then 0 else waterFill pi sigma lam i/pi i

noncomputable def waterMass {m : ℕ} (pi sigma : Fin m  → ℚ) (lam : ℚ) : ℝ :=
  ∑ i : Fin m,(waterFill pi sigma lam i:ℝ)^2

noncomputable def waterSource {m D : ℕ} (pi : Fin m  → ℚ) (xi : Fin m  → QState (Fin D)) : QState (Fin m ×Fin D) :=
  fun p => (pi p.1:ℂ)*xi p.1 p.2

noncomputable def waterTarget {m D : ℕ} (sigma : Fin m  → ℚ) (xi : Fin m  → QState (Fin D)) :
    QState ((Fin m ×Fin D) ×Bool) :=
  fun p => if p.2 then (sigma p.1.1:ℂ)*xi p.1.1 p.1.2 else 0

noncomputable def waterIdealPrepare {m D : ℕ} (pi sigma : Fin m  → ℚ) (lam : ℚ)
    (A : Matrix (Fin m ×Fin D) (Fin m ×Fin D) ℂ) :
    Matrix ((Fin m ×Fin D) ×Bool) ((Fin m ×Fin D) ×Bool) ℂ :=
  payoffRotation (fun p => (waterGamma pi sigma lam p.1:ℝ)^2) *
    TensorGate A (1 : Matrix Bool Bool ℂ)

noncomputable def waterNumericPrepare {m D : ℕ} (pi sigma : Fin m  → ℚ) (lam : ℚ) (k : ℕ)
    (A : Matrix (Fin m ×Fin D) (Fin m ×Fin D) ℂ) :
    Matrix ((Fin m ×Fin D) ×Bool) ((Fin m ×Fin D) ×Bool) ℂ :=
  rationalPayoffRotation (fun p => waterGamma pi sigma lam p.1^2) k *
    TensorGate A (1 : Matrix Bool Bool ℂ)

def waterEvent (m D : ℕ) : Finset ((Fin m ×Fin D) ×Bool) := Finset.univ.filter (fun p => p.2=true)

def waterSafeScale {m : ℕ} (c : Fin m  → ℚ) : ℚ := 1/(1+(List.ofFn c).sum)

set_option maxHeartbeats 2000000

theorem coherent_waterfill_computed_support_and_range
    (m : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) :
    (∀ i, 0 ≤ waterFill pi sigma lam i ∧ waterFill pi sigma lam i ≤ pi i ∧
      0 ≤ waterGamma pi sigma lam i ∧ waterGamma pi sigma lam i ≤ 1 ∧
      pi i*waterGamma pi sigma lam i = waterFill pi sigma lam i) ∧
    (∀ i, pi i = 0 → waterFill pi sigma lam i = 0) := by
  have hfill (i : Fin m) : 0 ≤ waterFill pi sigma lam i ∧ waterFill pi sigma lam i ≤ pi i :=
    ⟨le_min (h i).1 (mul_nonneg hlam (h i).2), min_le_left _ _⟩
  have hzero (i : Fin m) (hi : pi i = 0) : waterFill pi sigma lam i = 0 := by
    unfold waterFill; rw [hi, min_eq_left (mul_nonneg hlam (h i).2)]
  refine ⟨?_, hzero⟩
  intro i
  refine ⟨(hfill i).1, (hfill i).2, ?_, ?_, ?_⟩
  all_goals unfold waterGamma; split_ifs with hi
  · norm_num
  · exact div_nonneg (hfill i).1 (h i).1
  · norm_num
  · exact (div_le_one (lt_of_le_of_ne (h i).1 (Ne.symm hi))).mpr (hfill i).2
  · simp [hzero i hi]
  · field_simp

theorem coherent_waterfill_fixed_mass_variational_optimum
    (m : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ) (w : Fin m → ℝ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 < lam)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (pi i : ℝ)) (hmass : (∑ i, w i^2) = waterMass pi sigma lam) :
    (∑ i, w i*(sigma i : ℝ)) ≤ ∑ i, (waterFill pi sigma lam i : ℝ)*(sigma i : ℝ) := by
  have hl : (0:ℝ) < lam := by exact_mod_cast hlam
  have hi (i : Fin m) :
      2*(lam : ℝ)*(w i*(sigma i : ℝ)-(waterFill pi sigma lam i : ℝ)*(sigma i : ℝ)) ≤
        w i^2-(waterFill pi sigma lam i : ℝ)^2 := by
    have hp : (0:ℝ) ≤ pi i := by exact_mod_cast (h i).1
    have hs : (0:ℝ) ≤ sigma i := by exact_mod_cast (h i).2
    by_cases hsat : pi i ≤ lam*sigma i
    · have he : (waterFill pi sigma lam i : ℝ) = (pi i : ℝ) := by rw [waterFill, min_eq_left hsat]
      have hsr : (pi i : ℝ) ≤ (lam : ℝ)*(sigma i : ℝ) := by exact_mod_cast hsat
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hw i).2) (show 0 ≤ 2*(lam : ℝ)*(sigma i : ℝ)-(pi i : ℝ)-w i by nlinarith [(hw i).2])]
    · have he : (waterFill pi sigma lam i : ℝ) = (lam : ℝ)*(sigma i : ℝ) := by
        rw [waterFill, min_eq_right (le_of_not_ge hsat), Rat.cast_mul]
      rw [he]
      nlinarith [sq_nonneg (w i-(lam : ℝ)*(sigma i : ℝ))]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hi i)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hh
  change (∑ i, w i^2) = ∑ i, (waterFill pi sigma lam i : ℝ)^2 at hmass
  rw [hmass, sub_self] at hh
  nlinarith

private theorem water_payoff_bounds (m : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) :
    ∀ i, 0 ≤ waterGamma pi sigma lam i^2 ∧ waterGamma pi sigma lam i^2 ≤ 1 := by
  intro i
  have hg := (coherent_waterfill_computed_support_and_range m pi sigma lam h hlam).1 i
  exact ⟨sq_nonneg _, by nlinarith [hg.2.2.1, hg.2.2.2.1]⟩

theorem waterIdealPrepare_unitary (m D : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    waterIdealPrepare pi sigma lam A ∈ Matrix.unitaryGroup _ ℂ := by
  apply mul_mem
  · apply payoffRotation_mem_unitaryGroup
    intro p
    have hh := water_payoff_bounds m pi sigma lam h hlam p.1
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  · exact tensorGate_unitary hA (by simp)

theorem coherent_waterfill_actual_numeric_gate_and_error
    (m D k : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    waterNumericPrepare pi sigma lam k A ∈ Matrix.unitaryGroup _ ℂ ∧
    ‖waterNumericPrepare pi sigma lam k A-waterIdealPrepare pi sigma lam A‖ ≤ 32/2^k := by
  have hf : ∀ p : Fin m × Fin D, 0 ≤ waterGamma pi sigma lam p.1^2 ∧ waterGamma pi sigma lam p.1^2 ≤ 1 :=
    fun p => water_payoff_bounds m pi sigma lam h hlam p.1
  have hh :=
      rational_payoff_unitary_value_and_operator_error (Fin m × Fin D)
      (fun p => waterGamma pi sigma lam p.1^2) k hf
  have hT := tensorGate_unitary hA (by simp : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ)
  refine ⟨mul_mem hh.1 hT, ?_⟩
  have herr : ‖rationalPayoffRotation (fun p : Fin m × Fin D => waterGamma pi sigma lam p.1^2) k -
      payoffRotation (fun p => (waterGamma pi sigma lam p.1 : ℝ)^2)‖ ≤ 32/2^k := by
    simpa only [Rat.cast_pow] using! hh.2.2
  unfold waterNumericPrepare waterIdealPrepare
  rw [← Matrix.sub_mul]
  exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_left (l2_norm_unitary_le_one hT) (norm_nonneg _)).trans (by simpa using! herr))

theorem water_ideal_collapse (m D : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hsource : A *ᵥ Ket j = waterSource pi xi) :
    Collapse (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D) = waterTarget (waterFill pi sigma lam) xi := by
  have hg := (coherent_waterfill_computed_support_and_range m pi sigma lam h hlam).1
  have hcol (p : Fin m × Fin D) : A p j = (pi p.1 : ℂ)*xi p.1 p.2 := by
    have hh := congrFun hsource p
    have hk : (A *ᵥ Ket j) p = A p j := applyGate_eq_mulVec_ket A j p
    simpa only [waterSource, hk] using! hh
  change Collapse
      (payoffPreparation A (fun p => (waterGamma pi sigma lam p.1 : ℝ)^2) *ᵥ Ket (j,false)) _ = _
  rw [payoffPreparation_mulVec_ket]
  funext p
  obtain ⟨⟨i,d⟩,b⟩ := p
  cases b
  · simp [collapse_apply, waterEvent, waterTarget]
  · have hgamma : Real.sqrt ((waterGamma pi sigma lam i : ℝ)^2) = (waterGamma pi sigma lam i : ℝ) :=
      Real.sqrt_sq (by exact_mod_cast (hg i).2.2.1)
    simp only [collapse_apply, waterEvent, Finset.mem_filter, Finset.mem_univ, and_true,
      if_true, if_false, Bool.false_eq_true, waterTarget, payoffRotation_apply, hgamma, hcol]
    have hmul : (pi i : ℂ)*(waterGamma pi sigma lam i : ℂ) = (waterFill pi sigma lam i : ℂ) := by
      exact_mod_cast (hg i).2.2.2.2
    rw [Complex.ofReal_ratCast]
    calc
      _ = ((pi i : ℂ)*(waterGamma pi sigma lam i : ℂ))*xi i d := by ring
      _ = _ := by rw [hmul]

theorem water_target_normSq (m D : ℕ) (c : Fin m → ℚ) (xi : Fin m → QState (Fin D))
    (hxi : ∀ i, Normalized (xi i)) :
    ∑ p, Complex.normSq (waterTarget c xi p) = ∑ i, (c i : ℝ)^2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, waterTarget, Bool.false_eq_true, if_false, if_true,
    Complex.normSq_zero, add_zero, Complex.normSq_mul, Complex.normSq_ratCast]
  have hxisq (i : Fin m) : (∑ d, Complex.normSq (xi i d)) = 1 := by
    simpa only [← Complex.sq_norm] using! hxi i
  calc
    _ = ∑ i, ((c i : ℝ)*(c i : ℝ))*(∑ d, Complex.normSq (xi i d)) := by simp_rw [← Finset.mul_sum]
    _ = _ := by simp only [hxisq, mul_one]; apply Finset.sum_congr rfl; intro i _; ring

theorem water_ideal_mass (m D : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hxi : ∀ i, Normalized (xi i))
    (hsource : A *ᵥ Ket j = waterSource pi xi) :
    MeasureProb (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D) = waterMass pi sigma lam := by
  rw [← sum_normSq_collapse, water_ideal_collapse m D pi sigma lam xi A j h hlam hsource]
  simpa only [← Complex.sq_norm] using! water_target_normSq m D (waterFill pi sigma lam) xi hxi

theorem water_prepared_state_error (m D k : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    ‖toEuclidean_fromVec (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false) -
      waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false))‖ ≤ 32/2^k := by
  have hh := (coherent_waterfill_actual_numeric_gate_and_error m D k pi sigma lam A h hlam hA).2
  rw [← Matrix.sub_mulVec]
  have hn :=
      norm_applyGate_le (waterNumericPrepare pi sigma lam k A-waterIdealPrepare pi sigma lam A)
      (Ket (j,false))
  have hk := (normalized_iff_norm_toEuclidean_fromVec (Ket (j,false))).mp (normalized_ket (j,false))
  simpa only [ApplyGate, hk, mul_one] using!
      hn.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))

theorem coherent_waterfill_same_unknown_state_flag_mass
    (m D k : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hxi : ∀ i, Normalized (xi i))
    (hA : A ∈ Matrix.unitaryGroup _ ℂ) (hsource : A *ᵥ Ket j = waterSource pi xi) :
    MeasureProb (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D) = waterMass pi sigma lam ∧
    |MeasureProb (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)) (waterEvent m D)-waterMass pi sigma lam| ≤ 64/2^k := by
  have hmass := water_ideal_mass m D pi sigma lam xi A j h hlam hxi hsource
  refine ⟨hmass, ?_⟩
  rw [← hmass]
  have hN := (coherent_waterfill_actual_numeric_gate_and_error m D k pi sigma lam A h hlam hA).1
  have hC := waterIdealPrepare_unitary m D pi sigma lam A h hlam hA
  have hh := measureProb_sub_le_two_mul_l2
    (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false))
    (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D)
    (normalized_applyGate hN (normalized_ket (j,false))) (normalized_applyGate hC (normalized_ket (j,false)))
  calc
    _ ≤ 2 * ‖toEuclidean_fromVec (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false) -
      waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false))‖ := hh
    _ ≤ 2*(32/(2:ℝ)^k) := mul_le_mul_of_nonneg_left (water_prepared_state_error m D k pi sigma lam A j h hlam hA) (by norm_num)
    _ = _ := by ring

end Qatlib.Concepts.NativeNumerics.WaterFilling
