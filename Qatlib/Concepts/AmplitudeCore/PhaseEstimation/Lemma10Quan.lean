/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma10Stat
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Lemma18Ampl

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

open scoped BigOperators
open ComplexConjugate

noncomputable def zoo_amplitude_estimation_phase_state_overlap_exp_sum (M : ℕ) (x : ℝ) : ℂ :=
  ∑ y : Fin M, Complex.exp (((2 * Real.pi * x * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)

lemma zoo_amplitude_estimation_phase_state_overlap_conj_exp (θ : ℝ) :
    conj (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((-θ : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul (starRingEnd ℂ), Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma zoo_amplitude_estimation_phase_state_overlap_inner (M : ℕ) (ω₀ ω₁ : ℝ) (hM : 0 < M) :
    ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2
      = ‖zoo_amplitude_estimation_phase_state_overlap_exp_sum M (ω₁ - ω₀)‖ ^ 2
        / (M : ℝ) ^ 2 := by
  have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMn : ((M : ℝ)) ≠ 0 := ne_of_gt hMp
  have hcoord : ∀ (ω : ℝ) (y : Fin M),
      (bhmtPhaseState M ω) y
        = ((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω * (y.val : ℝ) : ℝ) : ℂ) * Complex.I) :=
    fun _ _ => rfl
  have hcc : (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ) * ((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ))
      = ((1 / (M : ℝ) : ℝ) : ℂ) := by
    have h2 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := by
      have h := Real.sq_sqrt (le_of_lt hMp)
      rw [pow_two] at h
      exact h
    rw [← Complex.ofReal_mul, Complex.ofReal_inj, one_div, one_div, ← mul_inv,
      show Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) from h2]
  have hterm : ∀ y : Fin M,
      inner ℂ
          (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω₀ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
          (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω₁ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
      = ((1 / (M : ℝ) : ℝ) : ℂ)
          * Complex.exp (((2 * Real.pi * (ω₁ - ω₀) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro y
    rw [RCLike.inner_apply', map_mul (starRingEnd ℂ), Complex.conj_ofReal,
      zoo_amplitude_estimation_phase_state_overlap_conj_exp]
    have hprod : (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
          * Complex.exp (((-(2 * Real.pi * ω₀ * (y.val : ℝ) : ℝ) : ℝ) : ℂ) * Complex.I))
          * (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω₁ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
        = (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * ((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ))
          * (Complex.exp (((-(2 * Real.pi * ω₀ * (y.val : ℝ) : ℝ) : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((2 * Real.pi * ω₁ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      ring
    rw [hprod, hcc, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [show zoo_amplitude_estimation_phase_state_overlap_exp_sum M (ω₁ - ω₀)
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * (ω₁ - ω₀) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl,
    PiLp.inner_apply,
    Finset.sum_congr rfl (fun y _ => by
      show inner ℂ
          (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω₀ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
          (((1 / Real.sqrt (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * ω₁ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I))
        = ((1 / (M : ℝ) : ℝ) : ℂ)
            * Complex.exp (((2 * Real.pi * (ω₁ - ω₀) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      exact hterm y),
    ← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hMp), mul_pow]
  rw [div_pow, one_pow, one_div_mul_eq_div]

lemma zoo_amplitude_estimation_phase_state_overlap_distance (ω₀ ω₁ : ℝ) :
    ∃ k : ℤ,
      bhmtPhaseDistance ω₀ ω₁ = |ω₁ - ω₀ - (k : ℝ)| ∧ |ω₁ - ω₀ - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨round (ω₁ - ω₀), ?_, abs_sub_round _⟩
  show sInf (Set.range fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|)
      = |ω₁ - ω₀ - ((round (ω₁ - ω₀) : ℤ) : ℝ)|
  have hne : (Set.range fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|).Nonempty :=
    ⟨_, 0, rfl⟩
  have hbd : BddBelow (Set.range fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact abs_nonneg _⟩
  have hmem : |ω₁ - ω₀ - ((round (ω₁ - ω₀) : ℤ) : ℝ)|
      ∈ Set.range fun z : ℤ => |(z : ℝ) + ω₁ - ω₀| := by
    refine ⟨-round (ω₁ - ω₀), ?_⟩
    show |((-round (ω₁ - ω₀) : ℤ) : ℝ) + ω₁ - ω₀|
      = |ω₁ - ω₀ - ((round (ω₁ - ω₀) : ℤ) : ℝ)|
    congr 1
    push_cast
    ring
  have hlb : |ω₁ - ω₀ - ((round (ω₁ - ω₀) : ℤ) : ℝ)|
      ∈ lowerBounds (Set.range fun z : ℤ => |(z : ℝ) + ω₁ - ω₀|) := by
    rintro s ⟨z, rfl⟩
    refine (round_le (ω₁ - ω₀) (-z)).trans_eq ?_
    congr 1
    push_cast
    ring
  exact le_antisymm (csInf_le hbd hmem) (le_csInf hne hlb)

lemma zoo_amplitude_estimation_phase_state_overlap_exp_sum_int_shift (M : ℕ) (x : ℝ) (k : ℤ) :
    zoo_amplitude_estimation_phase_state_overlap_exp_sum M x
      = zoo_amplitude_estimation_phase_state_overlap_exp_sum M (x - (k : ℝ)) := by
  rw [show zoo_amplitude_estimation_phase_state_overlap_exp_sum M x
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * x * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl,
    show zoo_amplitude_estimation_phase_state_overlap_exp_sum M (x - (k : ℝ))
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * (x - (k : ℝ)) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hint : Complex.exp ((((k : ℤ) * (y.val : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I))
      = 1 :=
    Complex.exp_int_mul_two_pi_mul_I _
  have hsplit : ((2 * Real.pi * x * (y.val : ℝ) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * (x - (k : ℝ)) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I
        + (((k : ℤ) * (y.val : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, hint, mul_one]

lemma zoo_amplitude_estimation_phase_state_overlap_exp_sum_norm_abs (M : ℕ) (x : ℝ) :
    ‖zoo_amplitude_estimation_phase_state_overlap_exp_sum M x‖ ^ 2
      = ‖zoo_amplitude_estimation_phase_state_overlap_exp_sum M |x|‖ ^ 2 := by
  rw [show zoo_amplitude_estimation_phase_state_overlap_exp_sum M x
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * x * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl,
    show zoo_amplitude_estimation_phase_state_overlap_exp_sum M |x|
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * |x| * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx]
    have hterm : ∀ y : Fin M,
        Complex.exp (((2 * Real.pi * x * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
          = conj (Complex.exp (((2 * Real.pi * (-x) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      intro y
      rw [zoo_amplitude_estimation_phase_state_overlap_conj_exp]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun y _ => hterm y)]
    rw [show (∑ y : Fin M,
          conj (Complex.exp (((2 * Real.pi * (-x) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)))
        = conj (∑ y : Fin M,
          Complex.exp (((2 * Real.pi * (-x) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)) from
        (map_sum (starRingEnd ℂ) _ _).symm]
    rw [Complex.norm_conj]

lemma zoo_amplitude_estimation_phase_state_overlap_exp_sum_zero (M : ℕ) :
    zoo_amplitude_estimation_phase_state_overlap_exp_sum M 0 = (M : ℂ) := by
  rw [show zoo_amplitude_estimation_phase_state_overlap_exp_sum M 0
      = ∑ y : Fin M,
          Complex.exp (((2 * Real.pi * 0 * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
      from rfl]
  have hterm : ∀ y : Fin M,
      Complex.exp (((2 * Real.pi * 0 * (y.val : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro y
    have harg : ((2 * Real.pi * 0 * (y.val : ℝ) : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    rw [harg, Complex.exp_zero]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  simp

lemma zoo_amplitude_estimation_phase_state_overlap_exp_sum_sin (M : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ‖zoo_amplitude_estimation_phase_state_overlap_exp_sum M δ‖ ^ 2
      = Real.sin (Real.pi * (M : ℝ) * δ) ^ 2 / Real.sin (Real.pi * δ) ^ 2 := by
  have hπδ : 0 < Real.pi * δ := mul_pos Real.pi_pos hδ0
  have hπδlt : Real.pi * δ < Real.pi := by
    have h1 : δ < 1 := lt_of_le_of_lt hδhalf (by norm_num)
    have hlt := mul_lt_mul_of_pos_left h1 Real.pi_pos
    rwa [mul_one] at hlt
  have hsinne : Real.sin (Real.pi * δ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hπδ hπδlt)
  have hqne : Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have h0 : ‖(1 : ℂ) - Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I)‖ ^ 2
        = 0 := by
      rw [h]
      simp
    rw [zoo_amplified_qft_lemma18_chord_sq (2 * Real.pi * δ)] at h0
    rcases mul_eq_zero.mp h0 with h4 | h4
    · exact absurd h4 (by norm_num)
    · exfalso
      apply hsinne
      have hs : Real.sin ((2 * Real.pi * δ) / 2) = 0 := sq_eq_zero_iff.mp h4
      rwa [show (2 * Real.pi * δ) / 2 = Real.pi * δ from by ring] at hs
  have hE : zoo_amplitude_estimation_phase_state_overlap_exp_sum M δ
      = ∑ r ∈ Finset.range M,
          (Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I)) ^ r := by
    rw [show zoo_amplitude_estimation_phase_state_overlap_exp_sum M δ
        = ∑ y : Fin M,
            Complex.exp (((2 * Real.pi * δ * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)
        from rfl,
      Fin.sum_univ_eq_sum_range (fun r : ℕ =>
        Complex.exp (((2 * Real.pi * δ * (r : ℝ) : ℝ) : ℂ) * Complex.I)) M]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [zoo_amplified_qft_lemma18_exp_pow (2 * Real.pi * δ) r]
  rw [hE, geom_sum_eq hqne M, norm_div, div_pow,
    zoo_amplified_qft_lemma18_exp_pow (2 * Real.pi * δ) M]
  have hneg1 : Complex.exp (((2 * Real.pi * δ * (M : ℝ) : ℝ) : ℂ) * Complex.I) - (1 : ℂ)
      = -((1 : ℂ)
          - Complex.exp (((2 * Real.pi * δ * (M : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    ring
  have hneg2 : Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) - (1 : ℂ)
      = -((1 : ℂ) - Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I)) := by
    ring
  rw [hneg1, hneg2, norm_neg, norm_neg,
    zoo_amplified_qft_lemma18_chord_sq (2 * Real.pi * δ * (M : ℝ)),
    zoo_amplified_qft_lemma18_chord_sq (2 * Real.pi * δ),
    show (2 * Real.pi * δ * (M : ℝ)) / 2 = Real.pi * (M : ℝ) * δ from by ring,
    show (2 * Real.pi * δ) / 2 = Real.pi * δ from by ring,
    mul_div_mul_left _ _ (by norm_num : ((4 : ℝ)) ≠ 0)]

theorem zoo_amplitude_estimation_phase_state_overlap :
    ∀ (M : ℕ) (ω₀ ω₁ : ℝ),
      0 < M →
      0 ≤ ω₀ → ω₀ < 1 →
      0 ≤ ω₁ → ω₁ < 1 →
      let Δ : ℝ := bhmtPhaseDistance ω₀ ω₁;
      (Δ = 0 →
        ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 = 1) ∧
      (Δ ≠ 0 →
        ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 =
          Real.sin ((M : ℝ) * Δ * Real.pi) ^ 2 /
            ((M : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2)) := by
  intro M ω₀ ω₁ hM _ _ _ _
  have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨k, hk, hkhalf⟩ := zoo_amplitude_estimation_phase_state_overlap_distance ω₀ ω₁
  have hmaster : ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2
      = ‖zoo_amplitude_estimation_phase_state_overlap_exp_sum M
          (bhmtPhaseDistance ω₀ ω₁)‖ ^ 2 / (M : ℝ) ^ 2 := by
    rw [zoo_amplitude_estimation_phase_state_overlap_inner M ω₀ ω₁ hM,
      zoo_amplitude_estimation_phase_state_overlap_exp_sum_int_shift M (ω₁ - ω₀) k, hk,
      zoo_amplitude_estimation_phase_state_overlap_exp_sum_norm_abs]
  have hbr0 : bhmtPhaseDistance ω₀ ω₁ = 0 →
      ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 = 1 := by
    intro hΔ
    rw [hmaster, hΔ, zoo_amplitude_estimation_phase_state_overlap_exp_sum_zero,
      show ((M : ℕ) : ℂ) = ((M : ℝ) : ℂ) from by exact_mod_cast rfl, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hMp)]
    exact div_self (pow_ne_zero 2 (ne_of_gt hMp))
  have hbr1 : bhmtPhaseDistance ω₀ ω₁ ≠ 0 →
      ‖inner ℂ (bhmtPhaseState M ω₀) (bhmtPhaseState M ω₁)‖ ^ 2 =
        Real.sin ((M : ℝ) * bhmtPhaseDistance ω₀ ω₁ * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (bhmtPhaseDistance ω₀ ω₁ * Real.pi) ^ 2) := by
    intro hΔ
    have hd0 : 0 < bhmtPhaseDistance ω₀ ω₁ := by
      rw [hk, abs_pos]
      intro hz
      exact hΔ (by rw [hk, abs_eq_zero]; exact hz)
    have hdhalf : bhmtPhaseDistance ω₀ ω₁ ≤ 1 / 2 := by rw [hk]; exact hkhalf
    rw [hmaster, zoo_amplitude_estimation_phase_state_overlap_exp_sum_sin M _ hd0 hdhalf,
      show Real.pi * (M : ℝ) * bhmtPhaseDistance ω₀ ω₁
          = (M : ℝ) * bhmtPhaseDistance ω₀ ω₁ * Real.pi from by ring,
      show Real.pi * bhmtPhaseDistance ω₀ ω₁
          = bhmtPhaseDistance ω₀ ω₁ * Real.pi from by ring,
      div_div,
      mul_comm (Real.sin (bhmtPhaseDistance ω₀ ω₁ * Real.pi) ^ 2) ((M : ℝ) ^ 2)]
  exact ⟨hbr0, hbr1⟩

example : Lemma10Spec.expected :=
  zoo_amplitude_estimation_phase_state_overlap

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
