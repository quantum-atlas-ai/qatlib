/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedMarkedSetAmplitudes
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open scoped Classical BigOperators

noncomputable def aqErrorSuccessLower (N M L P : ℕ) : ℝ :=
  (Nat.totient P:ℝ)*aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/
    ((M+L:ℝ)*((N-M-L:ℕ):ℝ))

theorem aq_error_word_counts (N : ℕ) (hN : 0 < N) (T : ℕ) (C : Finset (Fin N)) :
    IsUnitaryCircuit (aqCircuit N hN T) ∧
    Normalized (aqState N hN T C) ∧
    QueryCount (aqCircuit N hN T) = aqRounds N T ∧
    GateCount (aqCircuit N hN T) = 3*aqRounds N T + 2 ∧
    (∑ y, BornProb (aqState N hN T C) y) = 1 := by
  have hqft := qftMatrix_unitary hN
  have hAA := prepared_aa_actual_circuit (QFTMatrix N) ⟨0,hN⟩ C (aqRounds N T) hqft
  have hInv := qftMatrix_conjTranspose_unitary N hN
  have hword : IsUnitaryCircuit (aqCircuit N hN T) := by
    rw [aqCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate]
    exact ⟨hAA.1,hInv,isUnitaryCircuit_nil⟩
  have hnorm : Normalized (aqState N hN T C) :=
    hword.normalized_run (prepared_aa_reflection_and_access (QFTMatrix N) ⟨0,hN⟩ C hqft).1
      (normalized_ket _)
  refine ⟨hword, hnorm, ?_, ?_, ?_⟩
  · rw [aqCircuit, queryCount_append, hAA.2.1]
    simp
  · rw [aqCircuit, gateCount_append, hAA.2.2.1]
    simp
  · simpa [MeasureProb] using! measureProb_univ hnorm

private theorem aq_error_root_sum_floor (N : ℕ) (hN : 0 < N) (s M L P : ℕ)
    (G : Finset (Fin N)) (y : Fin N) (hM : 0 < M) (hP : 0 < P)
    (hb : s+(M-1)*P < N) (hG : G.card = L)
    (hdis : Disjoint G (aqProgressionSet N s M P)) (hMP : M*P ≤ N)
    (hsep : (L:ℝ) < 2*(M:ℝ)/Real.pi) (a : ℕ)
    (hw : |(y.val:ℚ)/N-(a:ℚ)/P| ≤ 1/(2*(N:ℚ))) :
    (2*(M:ℝ)/Real.pi-(L:ℝ))^2 ≤
      Complex.normSq (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val) := by
  set F := aqProgressionFourier N s M P y.val with hF
  set S := ∑ z ∈ G, aqPhase N z.val y.val with hS
  have hA : (∑ x ∈ aqProgressionSet N s M P, aqPhase N x.val y.val) = F :=
    (aq_progression_root_sum N s M P y.val hM hP hb).trans hF
  have hunion : (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val) = F + S := by
    rw [Finset.sum_union hdis.symm, hA, ← hS]
  have hFn : 2*(M:ℝ)/Real.pi ≤ ‖F‖ := by
    have hr := aq_window_root_lower N s M P hN hM hP hMP y a hw
    rw [Complex.normSq_eq_norm_sq] at hr
    have hsq : (2*(M:ℝ)/Real.pi)^2 = 4*(M:ℝ)^2/Real.pi^2 := by ring
    have hr' : (2*(M:ℝ)/Real.pi)^2 ≤ ‖F‖^2 := by rw [hsq]; exact hr
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hr'
  have hone : ∀ z : Fin N, ‖aqPhase N z.val y.val‖ = 1 := by
    intro z
    have h1 := aqPhase_normSq N z.val y.val
    rw [← Complex.sq_norm] at h1
    calc
      ‖aqPhase N z.val y.val‖ = Real.sqrt ((‖aqPhase N z.val y.val‖)^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [h1]
      _ = 1 := Real.sqrt_one
  have hSn : ‖S‖ ≤ (L:ℝ) := by
    have h1 := norm_sum_le G (fun z => aqPhase N z.val y.val)
    have h2 : (∑ z ∈ G, ‖aqPhase N z.val y.val‖) = (G.card:ℝ) := by
      calc
        (∑ z ∈ G, ‖aqPhase N z.val y.val‖) = ∑ _z ∈ G, (1:ℝ) :=
          Finset.sum_congr rfl (fun z _ => hone z)
        _ = (G.card:ℝ) := by simp
    rw [hS, ← hG, ← h2]
    exact h1
  have htri : ‖F‖ ≤ ‖F + S‖ + ‖S‖ := by
    calc
      ‖F‖ = ‖(F + S) + (-S)‖ := by
        have h : (F + S) + (-S) = F := by ring
        rw [h]
      _ ≤ ‖F + S‖ + ‖-S‖ := norm_add_le _ _
      _ = ‖F + S‖ + ‖S‖ := by rw [norm_neg]
  have hlow : 2*(M:ℝ)/Real.pi - (L:ℝ) ≤ ‖F + S‖ := by
    linarith [htri, hSn]
  have hpos : 0 < 2*(M:ℝ)/Real.pi-(L:ℝ) := sub_pos.mpr hsep
  have hsqF : (2*(M:ℝ)/Real.pi-(L:ℝ))^2 ≤ Complex.normSq (F + S) := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ hpos.le (norm_nonneg _)).mpr hlow
  rw [← hunion] at hsqF
  exact hsqF

theorem aq_error_window_pointwise (N : ℕ) (hN : 0 < N) (s M L P : ℕ)
    (G : Finset (Fin N)) (h : Fin N → Bool) (y : Fin N)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s+(M-1)*P < N) (hMP : M*P ≤ N)
    (hG : G.card = L) (hdis : Disjoint G (aqProgressionSet N s M P)) (h2T : 2*(M+L) ≤ N)
    (hsep : (L:ℝ) < 2*(M:ℝ)/Real.pi)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G))
    (hy : y ∈ aqGoodWindow N P) :
    aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ)) ≤
      BornProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) y := by
  obtain ⟨a, ha, hcop, hw⟩ := (Finset.mem_filter.mp hy).2
  have hPN : P < N := by nlinarith
  have hy0 : y.val ≠ 0 := aq_good_nonzero N P hP hPN y hy
  have hTpos : 0 < M+L := by omega
  have hcard : (aqProgressionSet N s M P ∪ G).card = M+L := by
    rw [Finset.card_union_of_disjoint hdis.symm,
      aqProgression_card N s M P (by omega) (by omega) hb, hG]
  have hp := aq_marked_three_probabilities N hN (M+L) (aqProgressionSet N s M P ∪ G) h y
    hTpos hcard h2T hmark hy0
  have hfloor : (2*(M:ℝ)/Real.pi-(L:ℝ))^2 ≤
      Complex.normSq (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val) :=
    aq_error_root_sum_floor N hN s M L P G y (by omega) (by omega) hb hG hdis hMP hsep a hw
  have ht := aq_angle_properties N (M+L) hN hTpos h2T
  have hg := aq_floor_gain (aqAngle N (M+L)) ht.1 ht.2.1
  have hgain0 : 0 ≤ aqGain N (M+L) := hg.1.le
  have hnn : (0:ℝ) ≤ Complex.normSq
      (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  have hden : (0:ℝ) < (M+L:ℝ)*((N-M-L:ℕ):ℝ) := by
    have h1 : (0:ℝ) < (M+L:ℝ) := by exact_mod_cast hTpos
    have h2 : (0:ℝ) < ((N-M-L:ℕ):ℝ) := by
      exact_mod_cast (show 0 < N-M-L by omega)
    exact mul_pos h1 h2
  have hmul : aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ)) ≤
      aqGain N (M+L)*Complex.normSq
        (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val)
        / ((M+L:ℝ)*((N-M-L:ℕ):ℝ)) := by
    rw [div_le_div_iff_of_pos_right hden]
    exact mul_le_mul_of_nonneg_left hfloor hgain0
  have hborn : BornProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) y
      = aqGain N (M+L)*Complex.normSq
          (∑ x ∈ aqProgressionSet N s M P ∪ G, aqPhase N x.val y.val)
        / ((M+L:ℝ)*((N-M-L:ℕ):ℝ)) := by
    have hne : ((N-M-L:ℕ):ℝ) ≠ 0 := by
      exact_mod_cast (show N-M-L ≠ 0 by omega)
    have hneT : (M+L:ℝ) ≠ 0 := by exact_mod_cast hTpos.ne'
    have hcast : ((N-(M+L) : ℕ):ℝ) = ((N-M-L:ℕ):ℝ) := by
      have h1 : ((N-(M+L) : ℕ):ℝ) = (N:ℝ) - (M:ℝ) - (L:ℝ) := by
        rw [Nat.cast_sub (m := M + L) (n := N) (by omega)]
        push_cast
        ring
      have h3 : ((N-M:ℕ):ℝ) = (N:ℝ)-(M:ℝ) :=
        Nat.cast_sub (m := M) (n := N) (by omega)
      rw [h1, Nat.cast_sub (m := L) (n := N - M) (by omega), h3]
    rw [hp.1, aq_tan_density N (M+L) hN hTpos h2T, hcast]
    field_simp
    push_cast
    ring
  rw [hborn]
  exact hmul

theorem aq_error_window_mass_lower (N : ℕ) (hN : 0 < N) (s M L P : ℕ)
    (G : Finset (Fin N)) (h : Fin N → Bool)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s+(M-1)*P < N) (hMP : M*P ≤ N)
    (hG : G.card = L) (hdis : Disjoint G (aqProgressionSet N s M P)) (h2T : 2*(M+L) ≤ N)
    (hsep : (L:ℝ) < 2*(M:ℝ)/Real.pi)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    0 < aqErrorSuccessLower N M L P ∧
    aqErrorSuccessLower N M L P ≤
      MeasureProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) (aqGoodWindow N P) := by
  have hPN : P < N := by nlinarith
  have hTpos : 0 < M+L := by omega
  have hpt : ∀ y ∈ aqGoodWindow N P,
      aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ)) ≤
        BornProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) y :=
    fun y hy => aq_error_window_pointwise N hN s M L P G h y hM hP hb hMP hG hdis h2T hsep
      hmark hy
  have hcard := aq_good_window_card N P (by omega) hPN
  have hcardR : (Nat.totient P:ℝ) ≤ ((aqGoodWindow N P).card:ℝ) := by exact_mod_cast hcard
  have ht := aq_angle_properties N (M+L) hN hTpos h2T
  have hg := aq_floor_gain (aqAngle N (M+L)) ht.1 ht.2.1
  have hgain0 : 0 < aqGain N (M+L) := hg.1
  have hx : 0 < 2*(M:ℝ)/Real.pi-(L:ℝ) := sub_pos.mpr hsep
  have hT : (0:ℝ) < (M+L:ℝ) := by exact_mod_cast hTpos
  have hNT : (0:ℝ) < ((N-M-L:ℕ):ℝ) := by
    exact_mod_cast (show 0 < N-M-L by omega)
  have hphi : 0 < (Nat.totient P:ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega))
  have hpos : 0 < aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ)) := by
    refine div_pos (mul_pos hgain0 (by rw [pow_two]; exact mul_pos hx hx)) (mul_pos hT hNT)
  have hmass : MeasureProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G))
      (aqGoodWindow N P) = ∑ y ∈ aqGoodWindow N P,
      BornProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) y := by
    simp [MeasureProb]
  refine ⟨by
    unfold aqErrorSuccessLower
    refine div_pos (mul_pos (mul_pos hphi hgain0)
      (by rw [pow_two]; exact mul_pos hx hx)) (mul_pos hT hNT), ?_⟩
  rw [hmass]
  calc
    aqErrorSuccessLower N M L P
        = (Nat.totient P:ℝ)*(aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2
            /((M+L:ℝ)*((N-M-L:ℕ):ℝ))) := by
      unfold aqErrorSuccessLower
      ring
    _ ≤ ((aqGoodWindow N P).card:ℝ)*
          (aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_right hcardR hpos.le
    _ = ∑ y ∈ aqGoodWindow N P,
          (aqGain N (M+L)*(2*(M:ℝ)/Real.pi-(L:ℝ))^2/((M+L:ℝ)*((N-M-L:ℕ):ℝ))) := by
      simp
    _ ≤ _ := Finset.sum_le_sum hpt

theorem aq_error_success_lower_noiseless_anchor (N M P : ℕ) :
    aqErrorSuccessLower N M 0 P = aqSuccessLower N M P := by
  by_cases hN0 : N = 0
  · subst hN0
    simp [aqErrorSuccessLower, aqSuccessLower]
  by_cases hM0 : M = 0
  · subst hM0
    simp [aqErrorSuccessLower, aqSuccessLower]
  by_cases hNM : N = M
  · subst hNM
    simp [aqErrorSuccessLower, aqSuccessLower]
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0
  by_cases hle : M ≤ N
  · have hsub : ((N-M:ℕ):ℝ) ≠ 0 := by
      intro hz
      have h3 : N - M = 0 := by exact_mod_cast hz
      exact hNM (by omega)
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hpi2 : Real.pi ^ 2 ≠ 0 := by positivity
    unfold aqErrorSuccessLower aqSuccessLower
    simp only [Nat.cast_zero, add_zero, Nat.sub_zero, sub_zero]
    field_simp
    all_goals first | assumption | ring
  · have hz : N - M = 0 := by omega
    rw [aqErrorSuccessLower, aqSuccessLower, hz]
    simp

theorem aq_error_verify_semantics (N : ℕ) (s M P : ℕ) (G : Finset (Fin N))
    (h : Fin N → Bool) (hM : 2 ≤ M) (hP : 0 < P) (hb : s+(M-1)*P < N)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    (aqVerify h s M P).1 = true ∧
    (∀ s1 q : ℕ, (aqVerify h s1 M q).1 = true →
      0 < q ∧ s1 < N ∧ s1+q < N ∧ s1+(M-1)*q < N ∧
      (∃ hb0 : s1 < N, (⟨s1, hb0⟩ : Fin N) ∈ aqProgressionSet N s M P ∪ G) ∧
      (∃ hb1 : s1+q < N, (⟨s1+q, hb1⟩ : Fin N) ∈ aqProgressionSet N s M P ∪ G) ∧
      (∃ hb2 : s1+(M-1)*q < N,
        (⟨s1+(M-1)*q, hb2⟩ : Fin N) ∈ aqProgressionSet N s M P ∪ G)) ∧
    (∀ s1 q : ℕ, (aqVerify h s1 M q).2 ≤ 3) := by
  set C := aqProgressionSet N s M P ∪ G with hC
  have hmem (v : ℕ) (hv : ∃ r < M, v = s + r*P) (hlt : v < N) :
      (⟨v, hlt⟩ : Fin N) ∈ C := by
    simp only [hC, Finset.mem_union, aqProgressionSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range]
    obtain ⟨r, hr, he⟩ := hv
    exact Or.inl ⟨r, hr, he⟩
  have hsplit : ∀ x : Fin N, h x = true → (∃ hb0 : x.val < N, (⟨x.val, hb0⟩ : Fin N) ∈ C) := by
    intro x hx
    rw [hmark x] at hx
    exact ⟨x.isLt, of_decide_eq_true hx⟩
  have htrue : (aqVerify h s M P).1 = true := by
    have hb1 : s < N := by
      have hlt : s < s + P := by omega
      omega
    have hb2 : s+P < N := by
      have hle : P ≤ (M-1)*P := by
        simpa using! (Nat.mul_le_mul_right P (show 1 ≤ M-1 by omega))
      omega
    rw [aqVerify, dif_pos ⟨hP, hb1, hb2, hb⟩]
    have hfa : h (⟨s, hb1⟩ : Fin N) = true := by
      rw [hmark _]
      exact decide_eq_true (hmem s ⟨0, by omega, by omega⟩ hb1)
    have hfb : h (⟨s+P, hb2⟩ : Fin N) = true := by
      rw [hmark _]
      exact decide_eq_true (hmem (s+P) ⟨1, by omega, by omega⟩ hb2)
    have hfc : h (⟨s+(M-1)*P, hb⟩ : Fin N) = true := by
      rw [hmark _]
      exact decide_eq_true (hmem (s+(M-1)*P) ⟨M-1, by omega, rfl⟩ hb)
    simp [hfa, hfb, hfc]
  have hsound : ∀ s1 q : ℕ, (aqVerify h s1 M q).1 = true →
      0 < q ∧ s1 < N ∧ s1+q < N ∧ s1+(M-1)*q < N ∧
      (∃ hb0 : s1 < N, (⟨s1, hb0⟩ : Fin N) ∈ C) ∧
      (∃ hb1 : s1+q < N, (⟨s1+q, hb1⟩ : Fin N) ∈ C) ∧
      (∃ hb2 : s1+(M-1)*q < N, (⟨s1+(M-1)*q, hb2⟩ : Fin N) ∈ C) := by
    intro s1 q hq
    rw [aqVerify] at hq
    by_cases hc : 0 < q ∧ s1 < N ∧ s1+q < N ∧ s1+(M-1)*q < N
    · rw [dif_pos hc] at hq
      simp only [List.foldl_cons, List.foldl_nil, Bool.true_and, Bool.and_eq_true] at hq
      obtain ⟨⟨ha0, ha1⟩, ha2⟩ := hq
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2,
        hsplit _ ha0, hsplit _ ha1, hsplit _ ha2⟩
    · rw [dif_neg hc] at hq
      simp at hq
  exact ⟨htrue, hsound, fun _ _ => aqVerify_cost _ _ _ _⟩

theorem aq_error_attempt_sound_and_counts (N : ℕ) (s M P B : ℕ) (G : Finset (Fin N))
    (h : Fin N → Bool) (y : Fin N)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s+(M-1)*P < N) (hPB : P ≤ B) (hsepB : 2*B^2 < N)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    (y ∈ aqGoodWindow N P → (aqAttempt h s M B y).1 = some P) ∧
    (∀ q : ℕ, (aqAttempt h s M B y).1 = some q → (aqVerify h s M q).1 = true) ∧
    (aqAttempt h s M B y).2.1 ≤ 3 ∧
    (aqAttempt h s M B y).2.2.1 ≤ cfDepth N + 1 ∧
    (aqAttempt h s M B y).2.2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
  have hV := aq_error_verify_semantics N s M P G h hM (by omega) hb hmark
  have hd := continued_fraction_bad_output_soundness_and_work B N y.val
  have hg : (cfRationalDecode B N y.val).2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
    simp [cfRationalDecode, (show N ≠ 0 by omega), cfGenerationWork_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hy
    obtain ⟨a, ha⟩ := aq_good_decode N P B y (by omega) hPB hsepB hy
    simp [aqAttempt, ha, hV.1]
  · intro q hq
    unfold aqAttempt at hq
    (try dsimp only at hq)
    split at hq
    · simp at hq
    · rename_i c hc
      (try dsimp only at hq)
      split at hq
      · rename_i hv
        rw [Option.some.inj hq] at hv
        exact hv
      · simp at hq
  · unfold aqAttempt
    (try dsimp only)
    split
    · simp
    · exact aqVerify_cost _ _ _ _
  · unfold aqAttempt
    (try dsimp only)
    split <;> exact hd.1
  · unfold aqAttempt
    (try dsimp only)
    split <;> exact hg

theorem aq_error_attempt_mass_lower (N : ℕ) (hN : 0 < N) (s M L P B : ℕ)
    (G : Finset (Fin N)) (h : Fin N → Bool) {Z : Type} [DecidableEq Z] (z : Z)
    (a : Fin N → Option Z) (ha : ∀ y, y ∈ aqGoodWindow N P → a y = some z)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s+(M-1)*P < N) (hMP : M*P ≤ N) (hPB : P ≤ B)
    (hsepB : 2*B^2 < N) (hG : G.card = L)
    (hdis : Disjoint G (aqProgressionSet N s M P)) (h2T : 2*(M+L) ≤ N)
    (hsep : (L:ℝ) < 2*(M:ℝ)/Real.pi)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    aqErrorSuccessLower N M L P ≤
      ∑ y, if a y = some z then BornProb (aqState N hN (M+L) (aqProgressionSet N s M P ∪ G)) y
        else 0 := by
  set C := aqProgressionSet N s M P ∪ G with hC
  have hwin := aq_error_window_mass_lower N hN s M L P G h hM hP hb hMP hG hdis h2T hsep hmark
  have hmass : MeasureProb (aqState N hN (M+L) C) (aqGoodWindow N P) =
      (∑ y, if y ∈ aqGoodWindow N P then BornProb (aqState N hN (M+L) C) y else 0) := by
    simp [MeasureProb]
  calc
    aqErrorSuccessLower N M L P ≤ MeasureProb (aqState N hN (M+L) C) (aqGoodWindow N P) := hwin.2
    _ = ∑ y, if y ∈ aqGoodWindow N P then BornProb (aqState N hN (M+L) C) y else 0 := hmass
    _ ≤ ∑ y, if a y = some z then BornProb (aqState N hN (M+L) C) y else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ aqGoodWindow N P
      · rw [if_pos hy, if_pos (ha y hy)]
      · rw [if_neg hy]
        by_cases hz : a y = some z
        · rw [if_pos hz]
          exact bornProb_nonneg _ _
        · simp [hz]
    _ = _ := rfl

end Qatlib.Concepts.AmpTransform.ErrorStream
