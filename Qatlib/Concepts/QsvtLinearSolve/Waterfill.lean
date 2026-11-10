/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.WaterFilling
import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QsvtLinearSolve.Waterfill
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem water_real_family_normSq (m D : ℕ) (c : Fin m → ℝ)
    (xi : Fin m → QState (Fin D)) (hxi : ∀ i, Normalized (xi i)) :
    ‖toEuclidean_fromVec (fun p : (Fin m × Fin D) × Bool => if p.2 then (c p.1.1 : ℂ)*xi p.1.1 p.1.2 else 0)‖^2 =
      ∑ i, c i^2 := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    norm_zero, zero_pow (by omega : 2 ≠ 0), add_zero, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hxisum (i : Fin m) : ∑ d, ‖xi i d‖^2 = 1 := hxi i
  simp_rw [← Finset.mul_sum, hxisum, mul_one]

theorem water_ideal_conditional_distance (m D : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hsigma : (∑ i, (sigma i : ℝ)^2) = 1)
    (hxi : ∀ i, Normalized (xi i)) (hsource : A *ᵥ Ket j = waterSource pi xi)
    (hp : 0 < waterMass pi sigma lam) :
    ‖toEuclidean_fromVec (PostMeasure (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D)-waterTarget sigma xi)‖ =
      Real.sqrt (2-2*(∑ i, (waterFill pi sigma lam i : ℝ)*(sigma i : ℝ))/Real.sqrt (waterMass pi sigma lam)) := by
  let p := waterMass pi sigma lam
  let R := Real.sqrt p
  have hR : 0 < R := Real.sqrt_pos.mpr hp
  have hR2 : R^2 = p := Real.sq_sqrt hp.le
  have hmass := water_ideal_mass m D pi sigma lam xi A j h hlam hxi hsource
  have hstate : PostMeasure (waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)) (waterEvent m D)-waterTarget sigma xi =
      (fun z : (Fin m × Fin D) × Bool => if z.2 then
        (((waterFill pi sigma lam z.1.1 : ℝ)/R-(sigma z.1.1 : ℝ) : ℝ) : ℂ)*xi z.1.1 z.1.2 else 0) := by
    unfold PostMeasure
    rw [hmass]
    have hc := water_ideal_collapse m D pi sigma lam xi A j h hlam hsource
    rw [hc]
    funext z
    obtain ⟨⟨i,d⟩,b⟩ := z
    cases b <;> simp only [waterTarget, Pi.sub_apply, if_false, if_true, Bool.false_eq_true,
        mul_zero, sub_zero]
    dsimp only [R, p]
    push_cast
    ring
  have hn :=
      water_real_family_normSq m D (fun i => (waterFill pi sigma lam i : ℝ)/R-(sigma i : ℝ)) xi hxi
  rw [← hstate] at hn
  have hsum : (∑ i, ((waterFill pi sigma lam i : ℝ)/R-(sigma i : ℝ))^2) =
      2-2*(∑ i, (waterFill pi sigma lam i : ℝ)*(sigma i : ℝ))/R := by
    have he (i : Fin m) : ((waterFill pi sigma lam i : ℝ)/R-(sigma i : ℝ))^2 =
        (waterFill pi sigma lam i : ℝ)^2/R^2+(sigma i : ℝ)^2-2*((waterFill pi sigma lam i : ℝ)*(sigma i : ℝ))/R := by ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
      hsigma, hR2]
    change p/p+1-2*(∑ i, (waterFill pi sigma lam i : ℝ)*(sigma i : ℝ))/R = _
    rw [div_self (ne_of_gt hp)]
    ring
  rw [hsum] at hn
  rw [← hn]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem coherent_waterfill_conditional_target_fidelity_and_bias
    (m D k : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hsigma : (∑ i, (sigma i : ℝ)^2) = 1)
    (hxi : ∀ i, Normalized (xi i)) (hA : A ∈ Matrix.unitaryGroup _ ℂ) (hsource : A *ᵥ Ket j = waterSource pi xi) :
    let p := waterMass pi sigma lam;
    let e := 32/(2:ℝ)^k;
    e < Real.sqrt p →
    (Real.sqrt p-e)^2 ≤ MeasureProb (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)) (waterEvent m D) ∧
    ‖toEuclidean_fromVec (PostMeasure (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)) (waterEvent m D)-waterTarget sigma xi)‖ ≤
      2*e/Real.sqrt p+Real.sqrt (2-2*(∑ i, (waterFill pi sigma lam i : ℝ)*(sigma i : ℝ))/Real.sqrt p) := by
  (try dsimp only)
  intro hgap
  let x := waterIdealPrepare pi sigma lam A *ᵥ Ket (j,false)
  let y := waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)
  let S := waterEvent m D
  have hm : MeasureProb x S = waterMass pi sigma lam :=
      water_ideal_mass m D pi sigma lam xi A j h hlam hxi hsource
  have he : ‖toEuclidean_fromVec (y-x)‖ ≤ 32/(2:ℝ)^k :=
      water_prepared_state_error m D k pi sigma lam A j h hlam hA
  have hg : 32/(2:ℝ)^k < Real.sqrt (MeasureProb x S) := by rw [hm]; exact hgap
  have hpost := postMeasure_error_of_gap x y S he hg
  have hp : 0 < waterMass pi sigma lam := Real.sqrt_pos.mp (lt_of_le_of_lt (by positivity) hgap)
  have hid := water_ideal_conditional_distance m D pi sigma lam xi A j h hlam hsigma hxi hsource hp
  refine ⟨?_, ?_⟩
  · have hc := (norm_toEuclidean_collapse_sub_le x y S).trans he
    have hdiff :=
        abs_norm_sub_norm_le (toEuclidean_fromVec (Collapse y S))
        (toEuclidean_fromVec (Collapse x S))
    have hrev : Real.sqrt (MeasureProb x S)-32/(2:ℝ)^k ≤ Real.sqrt (MeasureProb y S) := by
      have hdiff' : |‖toEuclidean_fromVec (Collapse y S)‖-‖toEuclidean_fromVec (Collapse x S)‖| ≤
          ‖toEuclidean_fromVec (Collapse y S-Collapse x S)‖ := by
        simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using! hdiff
      have hh := hdiff'.trans hc
      rw [norm_toEuclidean_collapse_eq_sqrt_measureProb,
          norm_toEuclidean_collapse_eq_sqrt_measureProb] at hh
      have hh' := abs_le.mp hh
      linarith
    rw [hm] at hrev
    nlinarith [Real.sq_sqrt (measureProb_nonneg y S), Real.sqrt_nonneg (MeasureProb y S)]
  · rw [hm] at hpost
    have htri := norm_sub_le_norm_sub_add_norm_sub (toEuclidean_fromVec (PostMeasure y S))
      (toEuclidean_fromVec (PostMeasure x S)) (toEuclidean_fromVec (waterTarget sigma xi))
    simp only [toEuclidean_fromVec, ← WithLp.toLp_sub] at htri
    exact htri.trans (add_le_add hpost.2 hid.le)

private theorem water_eval_error {H : Type} [Fintype H] [DecidableEq H]
    (U B C : Matrix H H ℂ) (cs : List (PreparedStep H)) (e : ℝ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ) (hC : C ∈ Matrix.unitaryGroup H ℂ)
    (hcs : PreparedCircuitValid cs) (_he : 0 ≤ e) (hclose : ‖B-C‖ ≤ e) :
    ‖evaluatePrepared U B cs-evaluatePrepared U C cs‖ ≤ (preparedInputQueries cs : ℝ)*e := by
  induction cs with
  | nil => simp [evaluatePrepared, preparedInputQueries]
  | cons s cs ih =>
    have hv : PreparedCircuitValid cs := fun d hd => hcs d (List.mem_cons_of_mem s hd)
    have hs : PreparedInstructionValid s := hcs s List.mem_cons_self
    have ht := ih hv
    have hinst : ‖preparedInstruction U B s-preparedInstruction U C s‖ ≤ (preparedInputQueries [s] : ℝ)*e := by
      cases s with
      | gate V => simp [preparedInstruction, preparedInputQueries]
      | dataForward => simp [preparedInstruction, preparedInputQueries]
      | dataBackward => simp [preparedInstruction, preparedInputQueries]
      | prepareForward => simpa only [preparedInstruction, preparedInputQueries, Nat.zero_add, Nat.cast_one, one_mul] using! hclose
      | prepareBackward => simpa only [preparedInstruction, preparedInputQueries, Nat.zero_add, Nat.cast_one, one_mul,
          ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] using! hclose
    have htail : ‖evaluatePrepared U B cs‖ ≤ 1 := l2_norm_unitary_le_one (hv.evaluate_unitary hU hB)
    have hhead : ‖preparedInstruction U C s‖ ≤ 1 :=
        l2_norm_unitary_le_one (preparedInstruction_unitary hU hC hs)
    have hh := l2_norm_mul_sub_mul_le (preparedInstruction U B s) (evaluatePrepared U B cs)
      (preparedInstruction U C s) (evaluatePrepared U C cs)
    calc
      _ ≤ ‖preparedInstruction U B s-preparedInstruction U C s‖ * ‖evaluatePrepared U B cs‖ +
          ‖preparedInstruction U C s‖ * ‖evaluatePrepared U B cs-evaluatePrepared U C cs‖ := hh
      _ ≤ (preparedInputQueries [s] : ℝ)*e+(preparedInputQueries cs : ℝ)*e := add_le_add
        ((mul_le_mul_of_nonneg_left htail (norm_nonneg _)).trans (by simpa using! hinst))
        ((mul_le_mul_of_nonneg_right hhead (norm_nonneg _)).trans (by simpa using! ht))
      _ = _ := by cases s <;> simp [preparedInputQueries, Nat.cast_add] <;> ring

theorem water_aa_word_counts {H : Type} [Fintype H] [DecidableEq H] (j : H) (t : ℕ) :
    ((preparedAAWord j t).countP (fun s => match s with | .prepareForward => true | _ => false)) = t+1 ∧
    ((preparedAAWord j t).countP (fun s => match s with | .prepareBackward => true | _ => false)) = t ∧
    (preparedAAWord j t).length = 4*t+1 := by
  simp [preparedAAWord, List.countP_flatten, List.sum_replicate, List.length_flatten, Nat.mul_comm]

theorem coherent_waterfill_actual_paid_aa_and_robustness
    (m D k t : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    let B := waterNumericPrepare pi sigma lam k A;
    let C := waterIdealPrepare pi sigma lam A;
    let E := waterEvent m D;
    QueryCount (preparedAACircuit B (j,false) t) = t ∧ GateCount (preparedAACircuit B (j,false) t) = 3*t+1 ∧
    ((preparedAAWord (I := ((Fin m × Fin D) × Bool)) (j,false) t).countP (fun s => match s with | .prepareForward => true | _ => false)) = t+1 ∧
    ((preparedAAWord (I := ((Fin m × Fin D) × Bool)) (j,false) t).countP (fun s => match s with | .prepareBackward => true | _ => false)) = t ∧
    ‖toEuclidean_fromVec (Run (preparedMark E) (preparedAACircuit B (j,false) t) (Ket (j,false))-
      Run (preparedMark E) (preparedAACircuit C (j,false) t) (Ket (j,false)))‖ ≤ (2*t+1)*32/2^k := by
  (try dsimp only)
  let B := waterNumericPrepare pi sigma lam k A
  let C := waterIdealPrepare pi sigma lam A
  let E := waterEvent m D
  have hBC := coherent_waterfill_actual_numeric_gate_and_error m D k pi sigma lam A h hlam hA
  have hC := waterIdealPrepare_unitary m D pi sigma lam A h hlam hA
  have hn := prepared_aa_actual_circuit B (j,false) E t hBC.1
  have hwb := prepared_aa_separate_access_word B (j,false) E t hBC.1
  have hwc := prepared_aa_separate_access_word C (j,false) E t hC
  have hw := water_aa_word_counts (j,false) t
  refine ⟨hn.2.1, hn.2.2.1, ?_, ?_, ?_⟩
  · simp [preparedAAWord, List.countP_flatten, List.sum_replicate]
  · simp [preparedAAWord, List.countP_flatten, List.sum_replicate]
  rw [← hwb.2.2.2.2.2, ← hwc.2.2.2.2.2]
  have he := water_eval_error (preparedMark E) B C (preparedAAWord (j,false) t) (32/(2:ℝ)^k)
    (prepared_aa_reflection_and_access B (j,false) E hBC.1).1 hBC.1 hC hwb.1 (by positivity) hBC.2
  rw [hwb.2.2.1] at he
  have herr := norm_applyGate_le (evaluatePrepared (preparedMark E) B (preparedAAWord (j,false) t)-
    evaluatePrepared (preparedMark E) C (preparedAAWord (j,false) t)) (Ket (j,false))
  have hk := (normalized_iff_norm_toEuclidean_fromVec (Ket (j,false))).mp (normalized_ket (j,false))
  rw [hk, mul_one] at herr
  have hlin : ApplyGate (evaluatePrepared (preparedMark E) B (preparedAAWord (j,false) t)) (Ket (j,false))-
      ApplyGate (evaluatePrepared (preparedMark E) C (preparedAAWord (j,false) t)) (Ket (j,false)) =
      ApplyGate (evaluatePrepared (preparedMark E) B (preparedAAWord (j,false) t)-
      evaluatePrepared (preparedMark E) C (preparedAAWord (j,false) t)) (Ket (j,false)) := (Matrix.sub_mulVec _ _ _).symm
  rw [hlin]
  exact herr.trans (by convert! he using 1; push_cast; ring)

theorem coherent_waterfill_actual_aa_success_and_preparation_cost
    (m D k t : ℕ) (pi sigma : Fin m → ℚ) (lam : ℚ)
    (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D) (theta : ℝ)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ sigma i) (hlam : 0 ≤ lam) (hA : A ∈ Matrix.unitaryGroup _ ℂ)
    (htheta : 0 < theta) (htheta1 : theta < Real.pi/2)
    (hmass : MeasureProb (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)) (waterEvent m D) = Real.sin theta^2) :
    MeasureProb (Run (preparedMark (waterEvent m D)) (preparedAACircuit (waterNumericPrepare pi sigma lam k A) (j,false) t)
      (Ket (j,false))) (waterEvent m D) = Real.sin ((2*t+1)*theta)^2 ∧
    (preparedAAWord (I := ((Fin m × Fin D) × Bool)) (j,false) t).length = 4*t+1 := by
  exact ⟨prepared_aa_born_success _ _ _ theta t
    (coherent_waterfill_actual_numeric_gate_and_error m D k pi sigma lam A h hlam hA).1 htheta htheta1 hmass,
    (water_aa_word_counts (j,false) t).2.2⟩

theorem waterSafeScale_bounds (m : ℕ) (c : Fin m → ℚ) (hc : ∀ i, 0 ≤ c i) :
    0 < waterSafeScale c ∧ ∀ i, waterSafeScale c*c i ≤ 1 := by
  have hs : (0:ℚ) ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have hden : (0:ℚ) < 1+∑ i, c i := by linarith
  have hscale : waterSafeScale c = 1/(1+∑ i, c i) := by simp [waterSafeScale, List.sum_ofFn]
  refine ⟨by rw [hscale]; positivity, ?_⟩
  intro i
  have hi : c i ≤ ∑ j, c j := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
  rw [hscale, one_div_mul_eq_div]
  exact (div_le_one hden).mpr (by linarith)

theorem coherent_waterfill_computed_exact_proportional_consumer
    (m D k : ℕ) (pi c : Fin m → ℚ)
    (xi : Fin m → QState (Fin D)) (A : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j : Fin m × Fin D)
    (h : ∀ i, 0 ≤ pi i ∧ 0 ≤ c i) (hsigma : (∑ i, (pi i*c i : ℝ)^2) = 1) (hxi : ∀ i, Normalized (xi i))
    (hA : A ∈ Matrix.unitaryGroup _ ℂ) (hsource : A *ᵥ Ket j = waterSource pi xi) :
    let sigma := fun i => pi i*c i;
    let lam := waterSafeScale c;
    0 < lam ∧ (∀ i, waterFill pi sigma lam i = lam*sigma i) ∧
    waterMass pi sigma lam = (lam : ℝ)^2 ∧
    ((32:ℝ)/2^k < (lam : ℝ) →
      ‖toEuclidean_fromVec (PostMeasure (waterNumericPrepare pi sigma lam k A *ᵥ Ket (j,false)) (waterEvent m D)-waterTarget sigma xi)‖ ≤
        64/(2^k*(lam : ℝ))) := by
  (try dsimp only)
  have hb := waterSafeScale_bounds m c (fun i => (h i).2)
  have hfill (i : Fin m) : waterFill pi (fun i => pi i*c i) (waterSafeScale c) i = waterSafeScale c*(pi i*c i) := by
    unfold waterFill
    apply min_eq_right
    have hh := mul_le_mul_of_nonneg_left (hb.2 i) (h i).1
    nlinarith
  have hnorm : (∑ i, ((pi i*c i : ℚ) : ℝ)^2) = 1 := by exact_mod_cast hsigma
  have hmass : waterMass pi (fun i => pi i*c i) (waterSafeScale c) = (waterSafeScale c : ℝ)^2 := by
    unfold waterMass
    simp_rw [hfill, Rat.cast_mul, mul_pow]
    have hh : (∑ i, (pi i : ℝ)^2*(c i : ℝ)^2) = 1 := by
      simpa only [Rat.cast_mul, mul_pow] using! hnorm
    rw [← Finset.mul_sum, hh, mul_one]
  have hdot : (∑ i, (waterFill pi (fun i => pi i*c i) (waterSafeScale c) i : ℝ)*((pi i*c i : ℚ) : ℝ)) =
      (waterSafeScale c : ℝ) := by
    simp_rw [hfill, Rat.cast_mul]
    calc
      _ = (waterSafeScale c : ℝ)*(∑ i, ((pi i*c i : ℚ) : ℝ)^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
      _ = _ := by rw [hnorm, mul_one]
  have hr : (0:ℝ) < waterSafeScale c := by exact_mod_cast hb.1
  refine ⟨hb.1, hfill, hmass, ?_⟩
  intro hgap
  have hg := coherent_waterfill_conditional_target_fidelity_and_bias m D k pi (fun i => pi i*c i) (waterSafeScale c)
    xi A j (fun i => ⟨(h i).1, mul_nonneg (h i).1 (h i).2⟩) hb.1.le hnorm hxi hA hsource
  (try dsimp only at hg)
  rw [hmass, Real.sqrt_sq hr.le] at hg
  have hh := (hg hgap).2
  rw [hdot, mul_div_cancel_right₀ 2 hr.ne', sub_self, Real.sqrt_zero, add_zero] at hh
  exact hh.trans_eq (by ring)

end Qatlib.Concepts.QsvtLinearSolve.Waterfill
