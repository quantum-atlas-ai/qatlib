/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QLowerBound00.MainResults.Theorem2

open Qatlib.Papers.QLowerBound00.MainResults.AdversaryCore

theorem source_theorem2 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f : Input n → Bool) (X Y : Finset (Input n)) (R : Finset (InputPair n))
    (m m' l l' : ℕ) (ε : ℝ) (T : ℕ)
    (bit : ℕ → Fin n) (ψ : ℕ → ι → Input n → ℂ) (a : ι → Input n → ℂ)
    (ans : ι → Bool) (iw0 : ι)
    (hRsub : ∀ p ∈ R, p.1 ∈ X ∧ p.2 ∈ Y)
    (hm : ∀ x ∈ X, m ≤ (R.filter (fun p => p.1 = x)).card)
    (hm' : ∀ y ∈ Y, m' ≤ (R.filter (fun p => p.2 = y)).card)
    (hxcard : ∀ x ∈ X, ∀ i : Fin n,
      (R.filter (fun p => p.1 = x ∧ p.2 i ≠ x i)).card ≤ l)
    (hycard : ∀ y ∈ Y, ∀ i : Fin n,
      (R.filter (fun p => p.2 = y ∧ p.1 i ≠ y i)).card ≤ l')
    (hl : 0 < l) (hl' : 0 < l')
    (hfX : ∀ x ∈ X, f x = true) (hfY : ∀ y ∈ Y, f y = false)
    (hX : 0 < X.card) (hY : 0 < Y.card)
    (hinit : ∀ iw x, ψ 0 iw x = if iw = iw0 then initialState X Y x else 0)
    (hquery : ∀ k < T, ψ (k + 1) = phaseQuery (bit k) (ψ k))
    (hmass : ∀ k, (∑ iw, ∑ x ∈ X, ‖ψ k iw x‖ ^ 2) +
      (∑ iw, ∑ y ∈ Y, ‖ψ k iw y‖ ^ 2) ≤ 1)
    (hfactor : ∀ iw x, ψ T iw x = initialState X Y x * a iw x)
    (hanorm : ∀ x, (∑ iw, ‖a iw x‖ ^ 2) = 1)
    (hwrong : ∀ x ∈ X,
      (∑ iw ∈ univ.filter (fun iw => ans iw ≠ true), ‖a iw x‖ ^ 2) ≤ ε)
    (hright : ∀ y ∈ Y,
      (∑ iw ∈ univ.filter (fun iw => ans iw = true), ‖a iw y‖ ^ 2) ≤ ε)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 ≤
      (T : ℝ) * Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
  classical

  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro x hxX hxY
    have h1 := hfX x hxX
    have h2 := hfY x hxY
    rw [h1] at h2
    exact Bool.noConfusion h2

  let S : ℕ → ℝ := fun k => progress R (rhoEntry (ψ k))

  have hinitRho : ∀ x y, rhoEntry (ψ 0) x y = initialState X Y x * initialState X Y y := by
    intro x y
    have hterm : ∀ iw, star (ψ 0 iw x) * ψ 0 iw y =
        (if iw = iw0 then star (initialState X Y x) * initialState X Y y else 0) := by
      intro iw
      rw [hinit iw x, hinit iw y]
      by_cases h : iw = iw0 <;> simp [h]
    change (∑ iw, star (ψ 0 iw x) * ψ 0 iw y) =
      initialState X Y x * initialState X Y y
    rw [Finset.sum_congr rfl (fun iw _ => hterm iw), Finset.sum_ite_eq']
    have hs : star (initialState X Y x) = initialState X Y x := by
      unfold initialState
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hs]
    simp
  have hS0 : S 0 = progress R (fun x y => initialState X Y x * initialState X Y y) := by
    unfold S
    congr 1
    funext x y
    exact hinitRho x y
  have hS0card : S 0 =
      (R.card : ℝ) * (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ))⁻¹ := by
    rw [hS0]
    exact progress_initial X Y R hdisj hRsub hX hY

  have hcard := card_relation_ge X Y R m m' hRsub hm hm'
  have hsqrtXpos : 0 < Real.sqrt (X.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hX)
  have hsqrtYpos : 0 < Real.sqrt (Y.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have hBpos : 0 < 2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ) :=
    mul_pos (mul_pos (by norm_num) hsqrtXpos) hsqrtYpos
  have hmm0 : (0 : ℝ) ≤ (m : ℝ) * (m' : ℝ) := by positivity
  have hX0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  have hY0 : (0 : ℝ) ≤ (Y.card : ℝ) := by positivity
  have hAB : Real.sqrt ((m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)) =
      Real.sqrt ((m : ℝ) * (m' : ℝ)) *
        (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) / 2 := by
    rw [show (m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ) =
      ((m : ℝ) * (m' : ℝ)) * ((X.card : ℝ) * (Y.card : ℝ)) by ring]
    rw [Real.sqrt_mul hmm0, Real.sqrt_mul hX0]
    ring
  have hS0lower : Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 ≤ S 0 := by
    rw [hS0card]
    have hval : Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2 =
        Real.sqrt ((m : ℝ) * (m' : ℝ) * (X.card : ℝ) * (Y.card : ℝ)) /
          (2 * Real.sqrt (X.card : ℝ) * Real.sqrt (Y.card : ℝ)) := by
      rw [hAB]
      have hxne : Real.sqrt (X.card : ℝ) ≠ 0 := hsqrtXpos.ne'
      have hyne : Real.sqrt (Y.card : ℝ) ≠ 0 := hsqrtYpos.ne'
      field_simp
    rw [hval]
    exact div_le_div_of_nonneg_right hcard hBpos.le

  have hSupper : S T ≤ 2 * Real.sqrt (ε * (1 - ε)) * S 0 := by
    rw [hS0]
    refine final_progress_le R ε (fun x y => rhoEntry (ψ T) x y)
      (fun x y => initialState X Y x * initialState X Y y) ?_
    intro p hp
    obtain ⟨hxX, hyY⟩ := hRsub p hp
    have hpair := lemma1_pair ans true (fun iw => a iw p.1) (fun iw => a iw p.2)
      (initialAmplitude X Y p.1) (initialAmplitude X Y p.2) ε hε0 hε
      (hanorm p.1) (hanorm p.2) (hwrong p.1 hxX) (hright p.2 hyY)
    calc ‖rhoEntry (ψ T) p.1 p.2‖
        = ‖(initialAmplitude X Y p.1 : ℂ) * (initialAmplitude X Y p.2 : ℂ) *
            ∑ iw, star (a iw p.1) * a iw p.2‖ := by
            rw [rhoEntry_eq_of_factor (a := a)
              (α := fun x => initialAmplitude X Y x) hfactor]
      _ ≤ 2 * Real.sqrt (ε * (1 - ε)) *
            ‖(initialAmplitude X Y p.1 : ℂ)‖ * ‖(initialAmplitude X Y p.2 : ℂ)‖ := hpair
      _ = 2 * Real.sqrt (ε * (1 - ε)) *
            ‖initialState X Y p.1 * initialState X Y p.2‖ := by
            simp only [initialState, norm_mul]
            ring

  have hstep : ∀ k < T, S k - S (k + 1) ≤ Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
    intro k hk
    have hsub := progress_sub_le R (rhoEntry (ψ k)) (rhoEntry (ψ (k + 1)))
    have hnorm : (∑ p ∈ R,
        ‖rhoEntry (ψ k) p.1 p.2 - rhoEntry (ψ (k + 1)) p.1 p.2‖) =
        ∑ p ∈ R, ‖rhoEntry (ψ (k + 1)) p.1 p.2 - rhoEntry (ψ k) p.1 p.2‖ := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [norm_sub_rev]
    have hbound : (∑ p ∈ R,
        ‖rhoEntry (ψ (k + 1)) p.1 p.2 - rhoEntry (ψ k) p.1 p.2‖) ≤
        Real.sqrt ((l : ℝ) * (l' : ℝ)) := by
      rw [hquery k hk]
      exact progress_step_le X Y R l l' hl hl' (bit k) (ψ k) hRsub
        (fun x hx => hxcard x hx (bit k)) (fun y hy => hycard y hy (bit k)) (hmass k)
    unfold S
    refine hsub.trans ?_
    rw [hnorm]
    exact hbound
  rw [mul_div_assoc]
  exact adversary_lower_bound (S := S) (T := T) (B := Real.sqrt ((l : ℝ) * (l' : ℝ)))
    (S0 := Real.sqrt ((m : ℝ) * (m' : ℝ)) / 2) hε0 hε hstep hS0lower hSupper

end Qatlib.Papers.QLowerBound00.MainResults.Theorem2
