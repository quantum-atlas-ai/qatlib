/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false

/-! State-preparation and truncation lemmas of
"Quantum Differential Equation Solvers with Low State Preparation Cost"
(arXiv:2508.15170v1, 2025).

- `norm_normalized_sub_le` is Lemma 7 (Eq. (34)): the normalized states of
  two non-zero vectors are `2‖x − x̃‖/‖x‖`-close.
- `exp_tail_integral_eq` evaluates the exponential tail integral used in the
  proof of Lemma 9.
- `tail_truncation_error` is Lemma 9 (Eq. (69)/(70)), in a self-contained
  explicit-constant form: with the time-ordered propagator abstracted as an
  operator family `Φ` satisfying the dissipative decay
  `‖Φ t‖ ≤ e^{−η(T−t)}`, choosing `T` and `T₀` so that the two exponential
  tails are below `ε·‖u(T)‖/4` guarantees that the normalized solution state
  and the normalized tail state are `ε`-close.
- `history_norm_bound` is the per-time solution-norm core of Result 3: the
  Duhamel solution satisfies `‖u(t)‖ ≤ ‖u₀‖ + ∫₀ᵗ ‖b‖`, which is what makes
  the history-state preparation cost explicit.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

open MeasureTheory intervalIntegral

namespace Qatlib.Papers.DissipDESolve25.MainResults.PrepLemmas

/-! ## Lemma 7 (Eq. (34)): normalized-state perturbation -/

/-- **Lemma 7, Eq. (34)**: for two non-zero vectors `x` and `x̃`, the
distance of their normalized states is at most `2‖x − x̃‖/‖x‖`. -/
theorem norm_normalized_sub_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hnx : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hny : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have h1 : ‖(‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y‖ = ‖x - y‖ / ‖x‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx), inv_mul_eq_div]
  have key : |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [inv_sub_inv hnx.ne' hny.ne', abs_div, abs_mul, abs_of_pos hnx, abs_of_pos hny]
    field_simp
  have hrev : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_le]
    constructor
    · linarith [norm_sub_norm_le x y]
    · calc ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      _ = ‖x - y‖ := (norm_sub_rev _ _)
  have h2 : ‖(‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y‖ ≤ ‖x - y‖ / ‖x‖ := by
    have hc : (‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y = ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y :=
      (sub_smul _ _ _).symm
    rw [hc, norm_smul, Real.norm_eq_abs, key, le_div_iff₀ hnx, div_mul_cancel₀ _ hnx.ne']
    exact hrev
  have hsplit : (‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y
      = ((‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y) + ((‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y) := by abel
  rw [hsplit]
  calc ‖((‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y) + ((‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y)‖
      ≤ ‖(‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y‖ + ‖(‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y‖ :=
        norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + ‖(‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y‖ := by rw [h1]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := add_le_add (le_refl _) h2
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring

/-! ## Exponential tail integral (used by Lemma 9) -/

/-- The exact value of the exponential tail integral appearing in the proof
of Lemma 9. -/
theorem exp_tail_integral_eq (η T T0 : ℝ) (hη : 0 < η) :
    ∫ t in (0:ℝ)..(T - T0), Real.exp (-(η * (T - t)))
      = (Real.exp (-(η * T0)) - Real.exp (-(η * T))) / η := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) (T - T0),
      HasDerivAt (fun t => (1 / η) * Real.exp (-(η * (T - t))))
        (Real.exp (-(η * (T - t)))) t := by
    intro t _
    have hg : HasDerivAt (fun t => T - t) (-1 : ℝ) t := (hasDerivAt_id t).const_sub T
    have hg2 : HasDerivAt (fun t => -(η * (T - t))) η t := by
      have hcm := hg.const_mul η
      simpa only [Pi.neg_def, mul_neg, mul_one, neg_neg] using hcm.neg
    have h4 : HasDerivAt (fun t => (1 / η) * Real.exp (-(η * (T - t))))
        ((1 / η) * (Real.exp (-(η * (T - t))) * η)) t := hg2.exp.const_mul (1 / η)
    have hrw : (1 / η) * (Real.exp (-(η * (T - t))) * η)
        = Real.exp (-(η * (T - t))) := by field_simp
    rw [hrw] at h4
    exact h4
  rw [integral_eq_sub_of_hasDerivAt hderiv
    (show IntervalIntegrable (fun t => Real.exp (-(η * (T - t)))) volume 0 (T - T0) from
      Continuous.intervalIntegrable (by continuity) 0 (T - T0))]
  have hTT : T - (T - T0) = T0 := sub_sub_cancel _ _
  rw [hTT, sub_zero]
  field_simp

/-! ## Lemma 9 (Eq. (69)/(70)): tail truncation error -/

/-- **Lemma 9, Eq. (69)/(70), self-contained explicit-constant form**.
Let `u(T) = Φ 0 u₀ + ∫₀ᵀ Φ t (b t) dt` be the Duhamel solution of a
dissipative equation whose (abstracted) time-ordered propagator satisfies
`‖Φ t‖ ≤ e^{−η(T−t)}` on `[0, T]`, let `tail = ∫_{T−T₀}ᵀ Φ t (b t) dt` be
its final-segment part, and let `‖b t‖ ≤ bmax`. If `T` and `T₀` are chosen
so that `4‖u₀‖e^{−ηT} ≤ ε‖u(T)‖` and `4(bmax/η)e^{−ηT₀} ≤ ε‖u(T)‖`, then
the normalized solution state and the normalized tail state are `ε`-close.
This is the explicit sufficient condition behind Eq. (69)–(70) of the
paper. -/
theorem tail_truncation_error {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (η T T0 bmax ε : ℝ) (hη : 0 < η) (hT0le : 0 ≤ T0) (hT0 : T0 ≤ T)
    (Φ : ℝ → (E →L[ℂ] E)) (b : ℝ → E) (u0 uT tail : E)
    (hΦ : ∀ t ∈ Set.Icc (0:ℝ) T, ‖Φ t‖ ≤ Real.exp (-(η * (T - t))))
    (hble : ∀ t ∈ Set.Icc (0:ℝ) T, ‖b t‖ ≤ bmax)
    (hcont : Continuous (fun t => Φ t (b t)))
    (huTne : uT ≠ 0) (htailne : tail ≠ 0)
    (huT : uT = Φ 0 u0 + ∫ t in (0:ℝ)..T, Φ t (b t))
    (htail : tail = ∫ t in (T - T0)..T, Φ t (b t))
    (hT1 : 4 * ‖u0‖ * Real.exp (-(η * T)) ≤ ε * ‖uT‖)
    (hT2 : 4 * (bmax / η) * Real.exp (-(η * T0)) ≤ ε * ‖uT‖) :
    ‖(‖uT‖)⁻¹ • uT - (‖tail‖)⁻¹ • tail‖ ≤ ε := by
  have h0T : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_refl _, hT0le.trans hT0⟩
  have hT0' : (0:ℝ) ≤ T - T0 := sub_nonneg.mpr hT0
  have hTT : T - T0 ≤ T := by linarith
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) (T - T0), t ∈ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨ht.1, ht.2.trans hTT⟩
  have hintA : IntervalIntegrable (fun t => Φ t (b t)) volume 0 (T - T0) :=
    Continuous.intervalIntegrable hcont _ _
  have hintB : IntervalIntegrable (fun t => Φ t (b t)) volume (T - T0) T :=
    Continuous.intervalIntegrable hcont _ _
  have hsplit : ∫ t in (0:ℝ)..T, Φ t (b t)
      = (∫ t in (0:ℝ)..(T - T0), Φ t (b t)) + ∫ t in (T - T0)..T, Φ t (b t) :=
    (integral_add_adjacent_intervals (f := fun t => Φ t (b t)) hintA hintB).symm
  have huTtail : uT - tail = Φ 0 u0 + ∫ t in (0:ℝ)..(T - T0), Φ t (b t) := by
    rw [huT, htail, hsplit, ← add_assoc, add_sub_cancel_right]
  -- bound for the homogeneous (propagated initial-data) part
  have hΦ0 : ‖Φ 0 u0‖ ≤ Real.exp (-(η * T)) * ‖u0‖ := by
    have h0 := hΦ 0 h0T
    rw [sub_zero] at h0
    calc ‖Φ 0 u0‖ ≤ ‖Φ 0‖ * ‖u0‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (-(η * T)) * ‖u0‖ :=
        mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
  -- bound for the truncated inhomogeneous part
  have hbmax : 0 ≤ bmax := le_trans (norm_nonneg (b 0)) (hble 0 h0T)
  have hintA' : IntervalIntegrable (fun t => ‖Φ t (b t)‖) volume 0 (T - T0) :=
    Continuous.intervalIntegrable hcont.norm _ _
  have hintge : IntervalIntegrable
      (fun t => bmax * Real.exp (-(η * (T - t)))) volume 0 (T - T0) :=
    Continuous.intervalIntegrable (by continuity) _ _
  have hnormA : ‖∫ t in (0:ℝ)..(T - T0), Φ t (b t)‖
      ≤ bmax * (Real.exp (-(η * T0)) - Real.exp (-(η * T))) / η := by
    calc ‖∫ t in (0:ℝ)..(T - T0), Φ t (b t)‖
        ≤ ∫ t in (0:ℝ)..(T - T0), ‖Φ t (b t)‖ := norm_integral_le_integral_norm hT0'
      _ ≤ ∫ t in (0:ℝ)..(T - T0), bmax * Real.exp (-(η * (T - t))) := by
          refine integral_mono_on hT0' hintA' hintge ?_
          intro t ht
          calc ‖Φ t (b t)‖ ≤ ‖Φ t‖ * ‖b t‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ Real.exp (-(η * (T - t))) * ‖b t‖ :=
              mul_le_mul_of_nonneg_right (hΦ t (hmem t ht)) (norm_nonneg _)
          _ ≤ Real.exp (-(η * (T - t))) * bmax :=
              mul_le_mul_of_nonneg_left (hble t (hmem t ht)) (Real.exp_nonneg _)
          _ = bmax * Real.exp (-(η * (T - t))) := mul_comm _ _
      _ = bmax * (Real.exp (-(η * T0)) - Real.exp (-(η * T))) / η := by
          rw [intervalIntegral.integral_const_mul, exp_tail_integral_eq η T T0 hη, mul_div_assoc]
  have hpos_eT : 0 ≤ Real.exp (-(η * T)) := Real.exp_nonneg _
  have hA2 : bmax * (Real.exp (-(η * T0)) - Real.exp (-(η * T))) / η
      ≤ bmax / η * Real.exp (-(η * T0)) := by
    have hkey : bmax * (Real.exp (-(η * T0)) - Real.exp (-(η * T)))
        ≤ bmax * Real.exp (-(η * T0)) := by
      rw [mul_sub]
      linarith [mul_nonneg hbmax hpos_eT]
    calc bmax * (Real.exp (-(η * T0)) - Real.exp (-(η * T))) / η
        ≤ bmax * Real.exp (-(η * T0)) / η :=
          div_le_div_of_nonneg_right hkey (le_of_lt hη)
      _ = bmax / η * Real.exp (-(η * T0)) :=
          (div_mul_eq_mul_div bmax η _).symm
  -- combine both tails
  have h1' : Real.exp (-(η * T)) * ‖u0‖ ≤ ε * ‖uT‖ / 4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    calc Real.exp (-(η * T)) * ‖u0‖ * 4 = 4 * ‖u0‖ * Real.exp (-(η * T)) := by ring
    _ ≤ ε * ‖uT‖ := hT1
  have h2' : bmax / η * Real.exp (-(η * T0)) ≤ ε * ‖uT‖ / 4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    calc bmax / η * Real.exp (-(η * T0)) * 4 = 4 * (bmax / η) * Real.exp (-(η * T0)) := by ring
    _ ≤ ε * ‖uT‖ := hT2
  have hnormut : ‖uT - tail‖ ≤ ε * ‖uT‖ / 2 := by
    calc ‖uT - tail‖ = ‖Φ 0 u0 + ∫ t in (0:ℝ)..(T - T0), Φ t (b t)‖ := by rw [huTtail]
    _ ≤ ‖Φ 0 u0‖ + ‖∫ t in (0:ℝ)..(T - T0), Φ t (b t)‖ := norm_add_le _ _
    _ ≤ Real.exp (-(η * T)) * ‖u0‖ + bmax / η * Real.exp (-(η * T0)) :=
        add_le_add hΦ0 (le_trans hnormA hA2)
    _ ≤ ε * ‖uT‖ / 4 + ε * ‖uT‖ / 4 := add_le_add h1' h2'
    _ = ε * ‖uT‖ / 2 := by ring
  calc ‖(‖uT‖)⁻¹ • uT - (‖tail‖)⁻¹ • tail‖
      ≤ 2 * ‖uT - tail‖ / ‖uT‖ := norm_normalized_sub_le uT tail huTne htailne
    _ ≤ ε := by
        rw [div_le_iff₀ (norm_pos_iff.mpr huTne)]
        linarith [hnormut]

/-! ## Result 3 core: per-time Duhamel norm bound -/

/-- **Result 3, per-time Duhamel norm bound**. If `u(t) = Φₜ u₀ +
∫₀ᵗ Ψ s (b s) ds` with contraction-bounded propagators `‖Φₜ‖ ≤ 1` and
`‖Ψ s‖ ≤ 1` on `[0, t]`, then `‖u(t)‖ ≤ ‖u₀‖ + ∫₀ᵗ ‖b s‖ ds`. This is the
norm bound that makes the normalization factor of the history state in
Result 3 explicit. -/
theorem history_norm_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (ht : 0 ≤ t)
    (Φt : E →L[ℂ] E) (hΦt : ‖Φt‖ ≤ 1)
    (Ψ : ℝ → (E →L[ℂ] E)) (hΨ : ∀ s ∈ Set.Icc (0:ℝ) t, ‖Ψ s‖ ≤ 1)
    (b : ℝ → E) (hb : Continuous b) (u0 : E)
    (hcont : Continuous (fun s => Ψ s (b s))) :
    ‖Φt u0 + ∫ s in (0:ℝ)..t, Ψ s (b s)‖ ≤ ‖u0‖ + ∫ s in (0:ℝ)..t, ‖b s‖ := by
  have hintΨ : IntervalIntegrable (fun s => Ψ s (b s)) volume 0 t :=
    Continuous.intervalIntegrable hcont _ _
  have hintn' : IntervalIntegrable (fun s => ‖Ψ s (b s)‖) volume 0 t :=
    Continuous.intervalIntegrable hcont.norm _ _
  have hintn : IntervalIntegrable (fun s => ‖b s‖) volume 0 t :=
    Continuous.intervalIntegrable hb.norm _ _
  have hmono : ∫ s in (0:ℝ)..t, ‖Ψ s (b s)‖ ≤ ∫ s in (0:ℝ)..t, ‖b s‖ := by
    refine integral_mono_on ht hintn' hintn ?_
    intro s hs
    calc ‖Ψ s (b s)‖ ≤ ‖Ψ s‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖b s‖ := mul_le_mul_of_nonneg_right (hΨ s hs) (norm_nonneg _)
    _ = ‖b s‖ := one_mul _
  calc ‖Φt u0 + ∫ s in (0:ℝ)..t, Ψ s (b s)‖
      ≤ ‖Φt u0‖ + ‖∫ s in (0:ℝ)..t, Ψ s (b s)‖ := norm_add_le _ _
  _ ≤ ‖Φt u0‖ + ∫ s in (0:ℝ)..t, ‖Ψ s (b s)‖ :=
      add_le_add (le_refl _) (norm_integral_le_integral_norm ht)
  _ ≤ ‖Φt‖ * ‖u0‖ + ∫ s in (0:ℝ)..t, ‖Ψ s (b s)‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (le_refl _)
  _ ≤ 1 * ‖u0‖ + ∫ s in (0:ℝ)..t, ‖b s‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hΦt (norm_nonneg _)) hmono
  _ = ‖u0‖ + ∫ s in (0:ℝ)..t, ‖b s‖ := by rw [one_mul]

end Qatlib.Papers.DissipDESolve25.MainResults.PrepLemmas
