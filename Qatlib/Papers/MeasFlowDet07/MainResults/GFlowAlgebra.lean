/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.ClusterPatterns.ResourceCompile.ClusterStabilizerResourceQuan
import Qatlib.Papers.MeasFlowDet07.MainResults.PlaneAnachronical
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Matrix

namespace Qatlib.Papers.MeasFlowDet07.MainResults

def mbqcSign (t : Bool) : ℂ := if t then -1 else 1

def mbqcPauliWord (a b : Bool) : Operator 2 :=
  (if a then pauliX else 1) * (if b then pauliZ else 1)

theorem mbqcPauliWord_mul_X (a b : Bool) :
    mbqcPauliWord a b * pauliX = mbqcSign b • (pauliX * mbqcPauliWord a b) := by
  cases a <;> cases b <;>
    simp only [mbqcPauliWord, mbqcSign, if_true, if_false, Bool.false_eq_true, one_mul,
      mul_one] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem mbqcPauliWord_mul_Z (a b : Bool) :
    mbqcPauliWord a b * pauliZ = mbqcSign a • (pauliZ * mbqcPauliWord a b) := by
  cases a <;> cases b <;>
    simp only [mbqcPauliWord, mbqcSign, if_true, if_false, Bool.false_eq_true, one_mul,
      mul_one] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem mbqcPauliWord_mul_Y (a b : Bool) :
    mbqcPauliWord a b * pauliY = mbqcSign (a != b) • (pauliY * mbqcPauliWord a b) := by
  cases a <;> cases b <;>
    simp only [mbqcPauliWord, mbqcSign, if_true, if_false, Bool.false_eq_true, one_mul,
      mul_one] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliZ, pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem mbqcPauliWord_anticomm_X (a b : Bool) (h : b = true) :
    mbqcPauliWord a b * pauliX = -(pauliX * mbqcPauliWord a b) := by
  rw [mbqcPauliWord_mul_X, h]
  simp [mbqcSign]

theorem mbqcPauliWord_comm_X (a b : Bool) (h : b = false) :
    mbqcPauliWord a b * pauliX = pauliX * mbqcPauliWord a b := by
  rw [mbqcPauliWord_mul_X, h]
  simp [mbqcSign]

theorem mbqcPauliWord_anticomm_Z (a b : Bool) (h : a = true) :
    mbqcPauliWord a b * pauliZ = -(pauliZ * mbqcPauliWord a b) := by
  rw [mbqcPauliWord_mul_Z, h]
  simp [mbqcSign]

theorem mbqcPauliWord_comm_Z (a b : Bool) (h : a = false) :
    mbqcPauliWord a b * pauliZ = pauliZ * mbqcPauliWord a b := by
  rw [mbqcPauliWord_mul_Z, h]
  simp [mbqcSign]

theorem mbqcPauliWord_anticomm_Y (a b : Bool) (h : a ≠ b) :
    mbqcPauliWord a b * pauliY = -(pauliY * mbqcPauliWord a b) := by
  rw [mbqcPauliWord_mul_Y]
  have hb : (a != b) = true := by
    cases a <;> cases b <;> simp_all
  rw [hb]
  simp [mbqcSign]

theorem mbqcPauliWord_comm_Y (a b : Bool) (h : a = b) :
    mbqcPauliWord a b * pauliY = pauliY * mbqcPauliWord a b := by
  rw [mbqcPauliWord_mul_Y]
  have hb : (a != b) = false := by
    cases a <;> cases b <;> simp_all
  rw [hb]
  simp [mbqcSign]

def mbqcAxisSignA : MbqcPlane → Bool → Bool → Bool
  | .XY, _, b => b
  | .XZ, a, _ => a
  | .YZ, a, b => a != b

def mbqcAxisSignB : MbqcPlane → Bool → Bool → Bool
  | .XY, a, b => a != b
  | .XZ, _, b => b
  | .YZ, a, _ => a

theorem mbqcPauliWord_mul_axisA (lam : MbqcPlane) (a b : Bool) :
    mbqcPauliWord a b * mbqcPlaneAxisA lam
      = mbqcSign (mbqcAxisSignA lam a b) • (mbqcPlaneAxisA lam * mbqcPauliWord a b) := by
  cases lam <;>
    simp only [mbqcPlaneAxisA, mbqcAxisSignA] <;>
    first
      | exact mbqcPauliWord_mul_X a b
      | exact mbqcPauliWord_mul_Z a b
      | exact mbqcPauliWord_mul_Y a b

theorem mbqcPauliWord_mul_axisB (lam : MbqcPlane) (a b : Bool) :
    mbqcPauliWord a b * mbqcPlaneAxisB lam
      = mbqcSign (mbqcAxisSignB lam a b) • (mbqcPlaneAxisB lam * mbqcPauliWord a b) := by
  cases lam <;>
    simp only [mbqcPlaneAxisB, mbqcAxisSignB] <;>
    first
      | exact mbqcPauliWord_mul_X a b
      | exact mbqcPauliWord_mul_Z a b
      | exact mbqcPauliWord_mul_Y a b

theorem mbqcSign_eq_neg_one (t : Bool) : mbqcSign t = -1 ↔ t = true := by
  cases t <;> simp [mbqcSign] <;> norm_num

theorem smul_eq_neg_iff {M : Operator 2} (hM : M ≠ 0) (s : ℂ) :
    s • M = -M ↔ s = -1 := by
  constructor
  · intro h
    have h' : (s + 1) • M = 0 := by
      rw [add_smul, one_smul, h]
      simp
    have hs : s + 1 = 0 := by
      rcases (smul_eq_zero.mp h') with h0 | h0
      · exact h0
      · exact absurd h0 hM
    linear_combination hs
  · intro hs
    rw [hs]
    simp

theorem det_ne_zero_imp_ne_zero {M : Operator 2} (h : M.det ≠ 0) : M ≠ 0 := by
  intro h0
  exact h (by rw [h0]; simp [Matrix.det_fin_two])

theorem pauliX_det_ne_zero : pauliX.det ≠ 0 := by
  simp [pauliX, Matrix.det_fin_two]

theorem pauliY_det_ne_zero : pauliY.det ≠ 0 := by
  simp [pauliY, Matrix.det_fin_two]

theorem pauliZ_det_ne_zero : pauliZ.det ≠ 0 := by
  simp [pauliZ, Matrix.det_fin_two]

theorem mbqcPauliWord_det_ne_zero (a b : Bool) : (mbqcPauliWord a b).det ≠ 0 := by
  cases a <;> cases b <;>
    simp [mbqcPauliWord, Matrix.det_mul, pauliX_det_ne_zero, pauliZ_det_ne_zero]

theorem mbqcPlaneAxisA_det_ne_zero (lam : MbqcPlane) :
    (mbqcPlaneAxisA lam).det ≠ 0 := by
  cases lam <;> simp [mbqcPlaneAxisA, pauliX_det_ne_zero, pauliY_det_ne_zero,
    pauliZ_det_ne_zero]

theorem mbqcPlaneAxisB_det_ne_zero (lam : MbqcPlane) :
    (mbqcPlaneAxisB lam).det ≠ 0 := by
  cases lam <;> simp [mbqcPlaneAxisB, pauliX_det_ne_zero, pauliY_det_ne_zero,
    pauliZ_det_ne_zero]

theorem axisA_mul_word_ne_zero (lam : MbqcPlane) (a b : Bool) :
    (mbqcPlaneAxisA lam * mbqcPauliWord a b) ≠ 0 := by
  apply det_ne_zero_imp_ne_zero
  rw [Matrix.det_mul]
  exact mul_ne_zero (mbqcPlaneAxisA_det_ne_zero lam) (mbqcPauliWord_det_ne_zero a b)

theorem axisB_mul_word_ne_zero (lam : MbqcPlane) (a b : Bool) :
    (mbqcPlaneAxisB lam * mbqcPauliWord a b) ≠ 0 := by
  apply det_ne_zero_imp_ne_zero
  rw [Matrix.det_mul]
  exact mul_ne_zero (mbqcPlaneAxisB_det_ne_zero lam) (mbqcPauliWord_det_ne_zero a b)

def mbqcPlaneWordA : MbqcPlane → Bool
  | .XY => false
  | .XZ => true
  | .YZ => true

def mbqcPlaneWordB : MbqcPlane → Bool
  | .XY => true
  | .XZ => true
  | .YZ => false

theorem mbqcAnachronical_eq_pauliWord (lam : MbqcPlane) :
    mbqcAnachronical lam = mbqcPauliWord (mbqcPlaneWordA lam) (mbqcPlaneWordB lam) := by
  cases lam <;> simp [mbqcAnachronical, mbqcPauliWord, mbqcPlaneWordA, mbqcPlaneWordB]

theorem mbqcAnachronical_anticomm_axisA (lam : MbqcPlane) :
    mbqcAnachronical lam * mbqcPlaneAxisA lam
      = -(mbqcPlaneAxisA lam * mbqcAnachronical lam) := by
  have h := mbqcAnachronical_anticomm lam 0
  simpa [mbqcPlaneObservable] using h

theorem mbqcAnachronical_anticomm_axisB (lam : MbqcPlane) :
    mbqcAnachronical lam * mbqcPlaneAxisB lam
      = -(mbqcPlaneAxisB lam * mbqcAnachronical lam) := by
  have h := mbqcAnachronical_anticomm lam (Real.pi / 2)
  simp only [mbqcPlaneObservable, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_mul, one_mul, zero_add] at h
  simpa using h

theorem gflowPlaneCond_of_anticomm (lam : MbqcPlane) (a b : Bool)
    (hA : mbqcPauliWord a b * mbqcPlaneAxisA lam
            = -(mbqcPlaneAxisA lam * mbqcPauliWord a b))
    (hB : mbqcPauliWord a b * mbqcPlaneAxisB lam
            = -(mbqcPlaneAxisB lam * mbqcPauliWord a b)) :
    mbqcGFlowPlaneCond lam (a = true) (b = true) := by
  have hsa := mbqcPauliWord_mul_axisA lam a b
  have hsb := mbqcPauliWord_mul_axisB lam a b
  have hMA := axisA_mul_word_ne_zero lam a b
  have hMB := axisB_mul_word_ne_zero lam a b
  have hsignA : mbqcAxisSignA lam a b = true := by
    have h : mbqcSign (mbqcAxisSignA lam a b) = -1 := by
      rw [hsa] at hA
      exact (smul_eq_neg_iff hMA (mbqcSign (mbqcAxisSignA lam a b))).mp hA
    exact (mbqcSign_eq_neg_one _).mp h
  have hsignB : mbqcAxisSignB lam a b = true := by
    have h : mbqcSign (mbqcAxisSignB lam a b) = -1 := by
      rw [hsb] at hB
      exact (smul_eq_neg_iff hMB (mbqcSign (mbqcAxisSignB lam a b))).mp hB
    exact (mbqcSign_eq_neg_one _).mp h
  cases lam
  · simp only [mbqcAxisSignA, mbqcAxisSignB] at hsignA hsignB
    have hb : b = true := hsignA
    have ha : a = false := by
      cases a <;> cases b <;> simp_all
    simp [mbqcGFlowPlaneCond, hb, ha]
  · simp only [mbqcAxisSignA, mbqcAxisSignB] at hsignA hsignB
    have ha : a = true := hsignA
    have hb : b = true := hsignB
    simp [mbqcGFlowPlaneCond, ha, hb]
  · simp only [mbqcAxisSignA, mbqcAxisSignB] at hsignA hsignB
    have ha : a = true := hsignB
    have hb : b = false := by
      cases a <;> cases b <;> simp_all
    simp [mbqcGFlowPlaneCond, ha, hb]

theorem anachronical_planeCond (lam : MbqcPlane) :
    mbqcGFlowPlaneCond lam (mbqcPlaneWordA lam = true) (mbqcPlaneWordB lam = true) := by
  refine gflowPlaneCond_of_anticomm lam (mbqcPlaneWordA lam) (mbqcPlaneWordB lam) ?_ ?_
  · rw [← mbqcAnachronical_eq_pauliWord]
    exact mbqcAnachronical_anticomm_axisA lam
  · rw [← mbqcAnachronical_eq_pauliWord]
    exact mbqcAnachronical_anticomm_axisB lam

theorem czMatrix_eq_diagonal_czPhase {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    czMatrix edges = Matrix.diagonal (czPhase edges) := by
  unfold czMatrix czPhase bitPhase
  exact Matrix.diagonal_injective (by funext x; rfl)

theorem stabilizer_eq_localX_neighborZ {n : ℕ} (edges : Finset (Fin n × Fin n))
    (v : Fin n) :
    stabilizer edges v = localX v * Matrix.diagonal (neighborPhase edges v) := by
  unfold stabilizer neighborPhase
  congr 1
  rw [Matrix.diagonal_injective.eq_iff]
  funext x
  apply Finset.prod_congr rfl
  intro w _
  by_cases h : (v, w) ∈ edges ∨ (w, v) ∈ edges <;> cases hx : x w <;>
    simp [h, hx, bitPhase]

theorem czMatrix_mul_self {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    czMatrix edges * czMatrix edges = 1 := by
  rw [czMatrix_eq_diagonal_czPhase, Matrix.diagonal_mul_diagonal]
  ext x y
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp [czPhase_sq]
  · simp [h]

theorem czMatrix_mul_localX {n : ℕ} (G : MbqcGraph n) (hG : mbqcCanonical G) (v : Fin n) :
    czMatrix G.edges * localX v = stabilizer G.edges v * czMatrix G.edges := by
  rw [czMatrix_eq_diagonal_czPhase, stabilizer_eq_localX_neighborZ]
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : x = flipBit v y
  · subst h
    rw [czPhase_flip G.edges (fun e he => hG e he) v y]
    simp [localX, permMatrix]
  · have hx : localX v x y = 0 := by
      simp only [localX, permMatrix, Matrix.of_apply]
      rw [if_neg]
      simpa [flipBit] using h
    simp [hx]

theorem czMatrix_mul_localZ {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) :
    czMatrix edges * localZ v = localZ v * czMatrix edges := by
  rw [czMatrix_eq_diagonal_czPhase, localZ, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  ring

theorem localX_eq_cz_conj_stabilizer {n : ℕ} (G : MbqcGraph n) (hG : mbqcCanonical G)
    (v : Fin n) :
    localX v = czMatrix G.edges * stabilizer G.edges v * czMatrix G.edges := by
  have h := czMatrix_mul_localX G hG v
  calc localX v = 1 * localX v := (one_mul _).symm
    _ = (czMatrix G.edges * czMatrix G.edges) * localX v := by
        rw [czMatrix_mul_self]
    _ = czMatrix G.edges * (czMatrix G.edges * localX v) := by rw [Matrix.mul_assoc]
    _ = czMatrix G.edges * (stabilizer G.edges v * czMatrix G.edges) := by rw [h]
    _ = czMatrix G.edges * stabilizer G.edges v * czMatrix G.edges := by
        rw [Matrix.mul_assoc]

theorem czResource_stabilizer_mbqc {n : ℕ} (G : MbqcGraph n) (hG : mbqcCanonical G)
    (v : Fin n) :
    ApplyGate (stabilizer G.edges v) (czResource G.edges) = czResource G.edges :=
  Qatlib.Concepts.ClusterPatterns.ResourceCompile.czResource_stabilizer
    G.edges (fun e he => hG e he) v

def mbqcPauliProj (A : Operator 2) (b : Bool) : Operator 2 :=
  (2 : ℂ)⁻¹ • ((1 : Operator 2) + mbqcSign b • A)

theorem mbqcPauliProj_mul_axis {A : Operator 2} (hA : A * A = 1) (b : Bool) :
    mbqcPauliProj A b * A = mbqcSign b • mbqcPauliProj A b := by
  have hs : mbqcSign b * mbqcSign b = 1 := by
    cases b <;> norm_num [mbqcSign]
  simpa [mbqcPauliProj] using projection_mul_axis (M := A) hA (s := mbqcSign b) hs

theorem mbqcPauliProj_X_mul (b : Bool) :
    mbqcPauliProj pauliX b * pauliX = mbqcSign b • mbqcPauliProj pauliX b := by
  apply mbqcPauliProj_mul_axis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem mbqcPauliProj_Y_mul (b : Bool) :
    mbqcPauliProj pauliY b * pauliY = mbqcSign b • mbqcPauliProj pauliY b := by
  apply mbqcPauliProj_mul_axis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem mbqcPauliProj_Z_mul (b : Bool) :
    mbqcPauliProj pauliZ b * pauliZ = mbqcSign b • mbqcPauliProj pauliZ b := by
  apply mbqcPauliProj_mul_axis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

end Qatlib.Papers.MeasFlowDet07.MainResults
