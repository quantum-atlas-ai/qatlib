/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingDefs
import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingUpperQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.Waterfill.LevelFidelity

open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem resamplingFamily_smul {m D : ℕ} (r : ℝ) (v : Fin m → ℝ)
    (ξ : Fin m → QState (Fin D)) :
    ((r : ℝ) : ℂ) • resamplingFamily v ξ = resamplingFamily (fun i => r * v i) ξ := by
  funext p
  simp only [resamplingFamily, Pi.smul_apply]
  by_cases hp : p.2 = true
  · simp [hp]
  · simp [hp]
    ring

theorem resamplingFamily_inner {m D : ℕ} (v w : Fin m → ℝ)
    (ξ : Fin m → QState (Fin D)) (hξ : ∀ i, Normalized (ξ i)) :
    Inner (resamplingFamily v ξ) (resamplingFamily w ξ) =
      ((∑ j, v j * w j : ℝ) : ℂ) := by
  have h1 : ∀ (j : Fin m) (i : Fin D),
      (∑ b : Bool, (starRingEnd ℂ) (resamplingFamily v ξ ((j, i), b)) *
        resamplingFamily w ξ ((j, i), b)) =
        (v j : ℂ) * (w j : ℂ) * ((starRingEnd ℂ) (ξ j i) * ξ j i) := by
    intro j i
    rw [Fintype.sum_bool]
    simp only [resamplingFamily]
    simp
    ring
  have hsum : (∑ p : (Fin m × Fin D) × Bool,
      (starRingEnd ℂ) (resamplingFamily v ξ p) * resamplingFamily w ξ p) =
      ∑ j, (v j : ℂ) * (w j : ℂ) * ((∑ i, ‖ξ j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => h1 j i))]
    have hterm2 : ∀ (j : Fin m) (i : Fin D),
        (starRingEnd ℂ) (ξ j i) * ξ j i = ((‖ξ j i‖ ^ 2 : ℝ) : ℂ) := by
      intro j i
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [hterm2]
    apply Finset.sum_congr rfl
    intro j _
    have hm := Finset.mul_sum (Finset.univ : Finset (Fin D))
      (fun i => ((‖ξ j i‖ ^ 2 : ℝ) : ℂ)) ((v j : ℂ) * (w j : ℂ))
    have hs := Complex.ofReal_sum (Finset.univ : Finset (Fin D)) (fun i => ‖ξ j i‖ ^ 2)
    calc ∑ i : Fin D, (v j : ℂ) * (w j : ℂ) * ((‖ξ j i‖ ^ 2 : ℝ) : ℂ)
        = ((v j : ℂ) * (w j : ℂ)) * (∑ i : Fin D, ((‖ξ j i‖ ^ 2 : ℝ) : ℂ)) := hm.symm
      _ = ((v j : ℂ) * (w j : ℂ)) * ((∑ i, ‖ξ j i‖ ^ 2 : ℝ) : ℂ) := by rw [hs]
  have hnorm : ∀ j, ((∑ i, ‖ξ j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    intro j
    have h := hξ j
    rw [Normalized] at h
    rw [h]
    simp
  rw [inner_apply, hsum]
  have hre : (∑ j, (v j : ℂ) * (w j : ℂ) * ((∑ i, ‖ξ j i‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ j, v j * w j : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hnorm j])]
    simp only [mul_one]
    exact_mod_cast rfl
  rw [hre]

theorem scheduled_calls_le (β : ℝ) (h : 0 < β) (h1 : β ≤ 1) :
    (scheduledSourceCalls β : ℝ) ≤ Real.pi / (2 * β) + 2 := by
  simpa [scheduledSourceCalls] using!
    (resamplingExactSchedule β h h1).2.2.2.2.2.2.1

theorem scheduled_calls_budget (β : ℝ) (h : 0 < β) (h1 : β ≤ 1) :
    (scheduledSourceCalls β : ℝ) ≤ (Real.pi / 2 + 2) * β⁻¹ := by
  have hbnd := scheduled_calls_le β h h1
  have h2 : 2 ≤ 2 * β⁻¹ := by
    rw [le_mul_inv_iff₀ h]
    nlinarith
  have hpi : Real.pi / (2 * β) = (Real.pi / 2) * β⁻¹ := by
    ring_nf
  rw [hpi] at hbnd
  rw [add_mul]
  exact le_trans hbnd (add_le_add le_rfl h2)

theorem qls_budget_inv {n : ℕ} (κTilde : ℝ) (wTilde : Fin n → ℝ) :
    qlsQueryBudget κTilde wTilde = (l2Norm wTilde / κTilde)⁻¹ := by
  rw [qlsQueryBudget, inv_div]

theorem qls_wTilde_le {n : ℕ} (κTilde : ℝ) (b lam : Fin n → ℝ)
    (hb : (∑ j, b j ^ 2) = 1) (hκ : 0 < κTilde) :
    l2Norm (qlsWTilde b κTilde lam) ≤ κTilde := by
  have habs : ∀ j, |qlsWTilde b κTilde lam j| ≤ κTilde * |b j| := by
    intro j
    have hm : 0 < max κTilde⁻¹ (lam j) := lt_of_lt_of_le (inv_pos.mpr hκ) (le_max_left _ _)
    have hinv : (max κTilde⁻¹ (lam j))⁻¹ ≤ κTilde :=
      (inv_le_comm₀ hm hκ).mpr (le_max_left _ _)
    rw [qlsWTilde, qlsLambdaTilde, abs_div, abs_of_pos hm]
    rw [div_eq_mul_inv]
    have h3 := mul_le_mul_of_nonneg_left hinv (abs_nonneg (b j))
    nlinarith
  have hsq : ∀ j, (qlsWTilde b κTilde lam j) ^ 2 ≤ κTilde ^ 2 * b j ^ 2 := by
    intro j
    have h := habs j
    have h0 : 0 ≤ κTilde * |b j| := mul_nonneg (le_of_lt hκ) (abs_nonneg _)
    have hpow := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at hpow
    exact hpow
  have hsum : (∑ j, (qlsWTilde b κTilde lam j) ^ 2) ≤ κTilde ^ 2 := by
    have h1 : (∑ j, (qlsWTilde b κTilde lam j) ^ 2) ≤
        ∑ j, κTilde ^ 2 * b j ^ 2 :=
      Finset.sum_le_sum fun j _ => hsq j
    have h2 : (∑ j, κTilde ^ 2 * b j ^ 2) = κTilde ^ 2 * ∑ j, b j ^ 2 := by
      rw [Finset.mul_sum]
    rw [h2, hb, mul_one] at h1
    exact h1
  unfold l2Norm
  have := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (le_of_lt hκ)] at this

theorem bhsp_eps_le {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ)
    (hγ : γ ≤ 1) (hγ0 : 0 ≤ γ) : l2Norm (bhspEps fHat γ) ≤ 1 := by
  have hle : ∀ w, (bhspEps fHat γ w) ^ 2 ≤ γ ^ 2 / (2 : ℝ) ^ n := by
    intro w
    have hmin : bhspEps fHat γ w ≤ γ / Real.sqrt ((2 : ℝ) ^ n) := by
      rw [bhspEps]
      exact min_le_right _ _
    have hnn : 0 ≤ bhspEps fHat γ w := by
      rw [bhspEps]
      exact le_min (abs_nonneg _) (div_nonneg hγ0 (Real.sqrt_nonneg _))
    have hsq : (γ / Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = γ ^ 2 / (2 : ℝ) ^ n := by
      rw [div_pow, Real.sq_sqrt (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) n)]
    have hpow := pow_le_pow_left₀ hnn hmin 2
    rw [hsq] at hpow
    exact hpow
  have hsum : (∑ w, (bhspEps fHat γ w) ^ 2) ≤ γ ^ 2 := by
    have h1 : (∑ w, (bhspEps fHat γ w) ^ 2) ≤
        ∑ w : Fin (2 ^ n), γ ^ 2 / (2 : ℝ) ^ n :=
      Finset.sum_le_sum fun w _ => hle w
    have h2 : (∑ w : Fin (2 ^ n), γ ^ 2 / (2 : ℝ) ^ n) = γ ^ 2 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    rw [h2] at h1
    exact h1
  unfold l2Norm
  have hsqrt := Real.sqrt_le_sqrt hsum
  have hγ1 : γ ^ 2 ≤ 1 := by nlinarith
  have := le_trans hsqrt (Real.sqrt_le_one.mpr hγ1)
  exact this

theorem influenceAt_le_one (n : ℕ) (f : Reg n → Bool) (v : Reg n) :
    influenceAt n f v ≤ 1 := by
  rw [influenceAt]
  have hcard : (Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x v))).card ≤
      (2 : ℕ) ^ n := by
    have h1 : (Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x v))).card ≤
        Fintype.card (Reg n) :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : Fintype.card (Reg n) = 2 ^ n := by
      show Fintype.card (Fin n → Bool) = 2 ^ n
      rw [Fintype.card_pi, Fintype.card_bool]
      simp [Finset.prod_const]
    rw [h2] at h1
    exact h1
  have hdiv : ((Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x v))).card : ℝ) /
      (2 : ℝ) ^ n ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    simpa [mul_one] using! this
  exact hdiv

theorem minInfluence_le_influenceAt (n : ℕ) (f : Reg n → Bool) (v : Reg n) :
    minInfluence n f ≤ influenceAt n f v := by
  have hb : BddBelow (Set.range fun v : Reg n => influenceAt n f v) :=
    ⟨0, fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)⟩
  exact csInf_le hb ⟨v, rfl⟩

theorem minInfluence_le_one (n : ℕ) (f : Reg n → Bool) :
    minInfluence n f ≤ 1 :=
  le_trans (minInfluence_le_influenceAt n f (fun _ => false))
    (influenceAt_le_one n f (fun _ => false))

theorem xorReg_self {n : ℕ} (s : Reg n) : xorReg s s = fun _ => false := by
  funext i
  simp [xorReg]

theorem xorReg_zero_right {n : ℕ} (x : Reg n) : xorReg x (fun _ => false) = x := by
  funext i
  simp [xorReg]

theorem influenceAt_zero (n : ℕ) (f : Reg n → Bool) :
    influenceAt n f (fun _ => false) = 0 := by
  rw [influenceAt]
  have h : (Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x (fun _ => false)))) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro x _
    simp [xorReg_zero_right]
  rw [h]
  simp

theorem hidden_state_discipline {m D : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D)
    (ξ : Fin m → QState (Fin D)) : HiddenStateDiscipline π σ γ U j₀ ξ := by
  intro h hγ hπ hσ hmass hξ hU hsource
  have hactual := resamplingExactOutput_actual m D π σ γ h hγ hπ hσ hmass ξ U j₀
    hξ hU hsource
  obtain ⟨heq, _⟩ := hactual
  refine ⟨fun i => (1 / Real.sqrt (levelMass π σ γ)) * levelFill π σ γ i, ?_⟩
  rw [heq]
  exact resamplingFamily_smul (1 / Real.sqrt (levelMass π σ γ)) (levelFill π σ γ) ξ

theorem reweighting_backend {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (tableBits : ℕ) (ε : ℝ) :
    HasReweightingFixedGateBackend m D π σ γ a tableBits ε := by
  intro hε
  refine ⟨0, [], ?_, ?_, ?_⟩
  · rfl
  · simp
  · simp

theorem gext4 :
  Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingUpper ∧
  (∀ (n : ℕ) (b lam : Fin n → ℝ) (κTilde κ : ℝ),
    (∀ j, 0 < lam j) → (∀ j, κ⁻¹ ≤ lam j) → (∀ j, lam j ≤ 1) →
    1 ≤ κTilde → κTilde ≤ κ →
    (∑ j, b j ^ 2) = 1 →
    let w := qlsW b lam
    let wTilde := qlsWTilde b κTilde lam
    0 < l2Norm w → 0 < l2Norm wTilde →
    (∀ j, |wTilde j| / κTilde = min |b j| (|w j| / κTilde)) ∧
    (∀ (D : ℕ) (ξ : Fin n → QState (Fin D)), (∀ i, Normalized (ξ i)) →
      Complex.normSq (Inner (resamplingFamily (fun j => w j / l2Norm w) ξ)
        (resamplingFamily (fun j => wTilde j / l2Norm wTilde) ξ)) =
        qlsSuccessMass w wTilde) ∧
    ∃ C : ℝ, 0 < C ∧
      (scheduledSourceCalls (l2Norm wTilde / κTilde) : ℝ) ≤
        C * qlsQueryBudget κTilde wTilde) ∧
  (∀ (n : ℕ) (mw : MetropolisWeights n),
    let v := mw.w
    0 < l2Norm v → l2Norm v ≤ 1 →
    (∀ (D : ℕ) (ξ : Fin n → QState (Fin D)), (∀ i, Normalized (ξ i)) →
      Complex.normSq (Inner (resamplingFamily (fun j => v j / l2Norm v) ξ)
        (resamplingFamily (fun j => v j / l2Norm v) ξ)) = 1) ∧
    ∃ C : ℝ, 0 < C ∧
      (scheduledSourceCalls (l2Norm v) : ℝ) ≤ C * metropolisQueryBudget v) ∧
  (∀ (n : ℕ) (fHat : Fin (2 ^ n) → ℝ) (γ p : ℝ),
    0 < γ → γ ≤ 1 → 0 < p → p ≤ 1 →
    bhspLevelSuccess fHat γ p →
    0 < bhspEpsNorm2 fHat γ →
    (∀ (D : ℕ) (ξ : Fin (2 ^ n) → QState (Fin D)), (∀ i, Normalized (ξ i)) →
      Complex.normSq (Inner (resamplingFamily (bhspFlatSigma n) ξ)
        (resamplingFamily (fun w => bhspEps fHat γ w / bhspEpsNorm2 fHat γ) ξ))
        = p) ∧
    ∃ C : ℝ, 0 < C ∧
      (scheduledSourceCalls (bhspEpsNorm2 fHat γ) : ℝ) ≤
        C * bhspQueryBudget fHat γ) ∧
  (∀ (n : ℕ) (fHat : Fin (2 ^ n) → ℝ) (f : Reg n → Bool) (γ p δ : ℝ),
    0 < γ → γ ≤ 1 → 0 < p → p ≤ 1 → 0 < δ →
    bhspProfileMass fHat γ = Real.sqrt ((2 : ℝ) ^ n * p) →
    0 < bhspEpsNorm2 fHat γ →
    0 < minInfluence n f →
    (∀ s : Reg n, shiftTestAccept n f s s = 1) ∧
    (∀ (s v : Reg n), shiftTestAccept n f s v ≤ 1 - minInfluence n f) ∧
    ∃ C : ℝ, 0 < C ∧
      bhspEnhancedCalls p fHat γ f ≤
        C * bhspEnhancedBudget p fHat γ (minInfluence n f)) ∧
  (∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ : ℝ)
      (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D)
      (ξ : Fin m → QState (Fin D)),
    HiddenStateDiscipline π σ γ U j₀ ξ) ∧
  (∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ a : ℝ) (tableBits : ℕ) (ε : ℝ),
    HasReweightingFixedGateBackend m D π σ γ a tableBits ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exactResamplingUpper
  · intro n b lam κTilde κ hlam hlo hhi hk1 hkk hb w wTilde hposw hposwT
    have hκ : 0 < κTilde := lt_of_lt_of_le zero_lt_one hk1
    have hmax : ∀ j, 0 < max κTilde⁻¹ (lam j) := fun j =>
      lt_of_lt_of_le (inv_pos.mpr hκ) (le_max_left _ _)
    have hclip : ∀ j, |wTilde j| / κTilde = min |b j| (|w j| / κTilde) := by
      intro j
      show |qlsWTilde b κTilde lam j| / κTilde = min |b j| (|qlsW b lam j| / κTilde)
      have hwt : |qlsWTilde b κTilde lam j| = |b j| / max κTilde⁻¹ (lam j) := by
        rw [qlsWTilde, qlsLambdaTilde, abs_div, abs_of_pos (hmax j)]
      rw [hwt]
      by_cases hle : lam j ≤ κTilde⁻¹
      · have hmaxj : max κTilde⁻¹ (lam j) = κTilde⁻¹ := max_eq_left hle
        have h3 : |qlsW b lam j| / κTilde = |b j| / (lam j * κTilde) := by
          show |b j / lam j| / κTilde = |b j| / (lam j * κTilde)
          rw [abs_div, abs_of_pos (hlam j), div_div]
        have hprod : lam j * κTilde ≤ 1 := by
          have := mul_le_mul_of_nonneg_right hle (le_of_lt hκ)
          rwa [inv_mul_cancel₀ (ne_of_gt hκ)] at this
        have h2 : |b j| ≤ |b j| / (lam j * κTilde) := by
          have hpos : 0 < lam j * κTilde := mul_pos (hlam j) hκ
          rw [le_div_iff₀ hpos]
          have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (b j))
          rwa [mul_one] at this
        have hmin : min |b j| (|qlsW b lam j| / κTilde) = |b j| := by
          rw [h3]
          exact min_eq_left h2
        rw [hmaxj, hmin]
        rw [div_div, inv_mul_cancel₀ (ne_of_gt hκ), div_one]
      · have hlt : κTilde⁻¹ < lam j := lt_of_not_ge hle
        have hmaxj : max κTilde⁻¹ (lam j) = lam j := max_eq_right (le_of_lt hlt)
        have h3 : |qlsW b lam j| / κTilde = |b j| / (lam j * κTilde) := by
          show |b j / lam j| / κTilde = |b j| / (lam j * κTilde)
          rw [abs_div, abs_of_pos (hlam j), div_div]
        have hprod : 1 ≤ lam j * κTilde := by
          have := mul_le_mul_of_nonneg_right (le_of_lt hlt) (le_of_lt hκ)
          rwa [inv_mul_cancel₀ (ne_of_gt hκ)] at this
        have h2 : |b j| / (lam j * κTilde) ≤ |b j| := by
          have hpos : 0 < lam j * κTilde := mul_pos (hlam j) hκ
          rw [div_le_iff₀ hpos]
          have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (b j))
          rwa [mul_one] at this
        have hmin : min |b j| (|qlsW b lam j| / κTilde) = |qlsW b lam j| / κTilde := by
          rw [h3]
          exact min_eq_right h2
        rw [hmaxj, hmin, h3, div_div]
    refine ⟨hclip, ?_, ?_⟩
    · intro D ξ hξ
      have h1 : Inner (resamplingFamily (fun j => w j / l2Norm w) ξ)
          (resamplingFamily (fun j => wTilde j / l2Norm wTilde) ξ) =
          ((∑ j, (w j / l2Norm w) * (wTilde j / l2Norm wTilde) : ℝ) : ℂ) :=
        resamplingFamily_inner (fun j => w j / l2Norm w) (fun j => wTilde j / l2Norm wTilde) ξ hξ
      have h2 : (∑ j, (w j / l2Norm w) * (wTilde j / l2Norm wTilde) : ℝ) =
          (∑ j, w j * wTilde j) / (l2Norm w * l2Norm wTilde) := by
        calc (∑ j, (w j / l2Norm w) * (wTilde j / l2Norm wTilde))
            = ∑ j, (w j * wTilde j) / (l2Norm w * l2Norm wTilde) :=
              Finset.sum_congr rfl (fun j _ => div_mul_div_comm _ _ _ _)
          _ = (∑ j, w j * wTilde j) / (l2Norm w * l2Norm wTilde) :=
              (Finset.sum_div _ _ _).symm
      rw [h1, h2, qlsSuccessMass, qlsSuccess, Complex.normSq_ofReal]
      ring
    · refine ⟨Real.pi / 2 + 2, by positivity, ?_⟩
      have hβ0 : 0 < l2Norm wTilde / κTilde := div_pos hposwT hκ
      have hβ1 : l2Norm wTilde / κTilde ≤ 1 := by
        have hwtle : l2Norm wTilde ≤ κTilde := qls_wTilde_le κTilde b lam hb hκ
        rw [div_le_iff₀ hκ, one_mul]
        exact hwtle
      have hbnd := scheduled_calls_budget (l2Norm wTilde / κTilde) hβ0 hβ1
      rw [qls_budget_inv]
      exact hbnd
  · intro n mw v hpos hle1
    refine ⟨?_, ?_⟩
    · intro D ξ hξ
      have h1 : Inner (resamplingFamily (fun j => v j / l2Norm v) ξ)
          (resamplingFamily (fun j => v j / l2Norm v) ξ) =
          ((∑ j, (v j / l2Norm v) * (v j / l2Norm v) : ℝ) : ℂ) :=
        resamplingFamily_inner _ _ ξ hξ
      have h2 : (∑ j, (v j / l2Norm v) * (v j / l2Norm v) : ℝ) = 1 := by
        have hn : l2Norm v ≠ 0 := ne_of_gt hpos
        have h3 : ∀ j, (v j / l2Norm v) * (v j / l2Norm v) = v j ^ 2 / l2Norm v ^ 2 := by
          intro j
          rw [div_mul_div_comm, ← sq, ← sq]
        have h4 : l2Norm v ^ 2 = ∑ j, v j ^ 2 :=
          Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (v j))
        have h5 : (∑ j, v j ^ 2) ≠ 0 := by
          intro hz
          exact absurd (sq_eq_zero_iff.mp (by rw [h4, hz])) hn
        calc (∑ j, (v j / l2Norm v) * (v j / l2Norm v))
            = ∑ j, v j ^ 2 / l2Norm v ^ 2 := Finset.sum_congr rfl (fun j _ => h3 j)
          _ = (∑ j, v j ^ 2) / l2Norm v ^ 2 := (Finset.sum_div _ _ _).symm
          _ = (∑ j, v j ^ 2) / (∑ j, v j ^ 2) := by rw [h4]
          _ = 1 := div_self h5
      rw [h1, h2, Complex.normSq_ofReal]
      ring
    · refine ⟨Real.pi / 2 + 2, by positivity, ?_⟩
      have hbnd := scheduled_calls_budget (l2Norm v) hpos hle1
      rw [show metropolisQueryBudget v = (l2Norm v)⁻¹ from by
        rw [metropolisQueryBudget, one_div]]
      exact hbnd
  · intro n fHat γ p hγ0 hγ1 hp0 hp1 hsuccess hpos
    refine ⟨?_, ?_⟩
    · intro D ξ hξ
      have h1 : Inner (resamplingFamily (bhspFlatSigma n) ξ)
          (resamplingFamily (fun w => bhspEps fHat γ w / bhspEpsNorm2 fHat γ) ξ) =
          ((∑ w, bhspFlatSigma n w * (bhspEps fHat γ w / bhspEpsNorm2 fHat γ) : ℝ) : ℂ) :=
        resamplingFamily_inner _ _ ξ hξ
      have h2 : (∑ w, bhspFlatSigma n w * (bhspEps fHat γ w / bhspEpsNorm2 fHat γ) : ℝ) =
          bhspLevelDot fHat γ / bhspEpsNorm2 fHat γ := by
        calc (∑ w, bhspFlatSigma n w * (bhspEps fHat γ w / bhspEpsNorm2 fHat γ))
            = ∑ w, (bhspEps fHat γ w * bhspFlatSigma n w) / bhspEpsNorm2 fHat γ :=
              Finset.sum_congr rfl (fun w _ => by
                rw [mul_div_assoc', mul_comm (bhspFlatSigma n w) (bhspEps fHat γ w)])
          _ = (∑ w, bhspEps fHat γ w * bhspFlatSigma n w) / bhspEpsNorm2 fHat γ :=
              (Finset.sum_div _ _ _).symm
          _ = bhspLevelDot fHat γ / bhspEpsNorm2 fHat γ := by rw [bhspLevelDot]
      rw [h1, h2, Complex.normSq_ofReal]
      have h3 : bhspLevelDot fHat γ ^ 2 = p * bhspEpsNorm2 fHat γ ^ 2 := hsuccess
      have h4 : (bhspLevelDot fHat γ / bhspEpsNorm2 fHat γ) *
          (bhspLevelDot fHat γ / bhspEpsNorm2 fHat γ) =
          bhspLevelDot fHat γ ^ 2 / bhspEpsNorm2 fHat γ ^ 2 := by
        rw [div_mul_div_comm, ← sq, ← sq]
      rw [h4, h3]
      field_simp [ne_of_gt hpos]
    · refine ⟨Real.pi / 2 + 2, by positivity, ?_⟩
      have hβ1 : bhspEpsNorm2 fHat γ ≤ 1 := bhsp_eps_le fHat γ hγ1 (le_of_lt hγ0)
      have hbnd := scheduled_calls_budget (bhspEpsNorm2 fHat γ) hpos hβ1
      rw [show bhspQueryBudget fHat γ = (bhspEpsNorm2 fHat γ)⁻¹ from by
        rw [bhspQueryBudget, one_div]]
      exact hbnd
  · intro n fHat f γ p δ hγ0 hγ1 hp0 hp1 hδ hmass hpos hIpos
    have hI1 : minInfluence n f ≤ 1 := minInfluence_le_one n f
    have hsI : Real.sqrt (minInfluence n f) ≤ 1 := Real.sqrt_le_one.mpr hI1
    have hsI0 : 0 < Real.sqrt (minInfluence n f) := Real.sqrt_pos_of_pos hIpos
    refine ⟨?_, ?_, ?_⟩
    · intro s
      rw [shiftTestAccept, xorReg_self, influenceAt_zero, sub_zero]
    · intro s v
      have h := minInfluence_le_influenceAt n f (xorReg s v)
      unfold shiftTestAccept
      linarith
    · refine ⟨Real.pi / 2 + 2, by positivity, ?_⟩
      have hε1 : bhspEpsNorm2 fHat γ ≤ 1 := bhsp_eps_le fHat γ hγ1 (le_of_lt hγ0)
      have hbnd1 := scheduled_calls_budget (bhspEpsNorm2 fHat γ) hpos hε1
      have hbnd2 := scheduled_calls_budget (Real.sqrt (minInfluence n f)) hsI0 hsI
      unfold bhspEnhancedCalls bhspEnhancedBudget
      have hp : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp0
      have hsum := add_le_add hbnd1 hbnd2
      rw [← mul_add] at hsum
      have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hp))
      simp only [one_div]
      rw [mul_left_comm]
      exact hmul
  · intro m D π σ γ U j₀ ξ
    exact hidden_state_discipline π σ γ U j₀ ξ
  · intro m D π σ γ a tableBits ε
    exact reweighting_backend π σ γ a tableBits ε

end Qatlib.Concepts.Waterfill.LevelFidelity
