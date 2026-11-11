/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalStat
import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestConcentrationSubgoalQuan
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Accuracy of the Hadamard test phase estimator

This module proves `EigenphaseEstimateSubgoal` for the paired Hadamard test sampling law of
`eigenphaseSampleLaw`. It combines concentration of the two sample averages with a
chord-distance bound for phase reconstruction, in the phase estimation setting of [Kitaev1995].

The estimator achieves phase error at most `δ` modulo integers with failure probability at most
`ε` when each half has at least `36 * log (4 / ε) / sin (π * δ)^2` samples.

## Main statements

* `sample_halves`: the two marginal laws of the sample record.
* `arg_phase_good`: accurate cosine and sine estimates give an accurate phase modulo integers.
* `eigenphaseEstimateSubgoal`: the estimator failure bound.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.KitaevReadout
open Matrix
open scoped BigOperators

/-- Splits a Boolean record of length `s + s` into its first and second blocks of length `s`, as
an equivalence. -/
private def splitBits (s : ℕ) : (Fin (s + s) → Bool) ≃
    (Fin s → Bool) × (Fin s → Bool) where
  toFun ω := (fun j => ω (Fin.castAdd s j), fun j => ω (Fin.natAdd s j))
  invFun p := Fin.addCases p.1 p.2
  left_inv ω := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left, Fin.addCases_right]
  right_inv p := by
    apply Prod.ext <;> funext j <;> simp only [Fin.addCases_left, Fin.addCases_right]

/-- The mass of a concatenated sample record factors into the independent Hadamard bit record
masses at phases `φ` and `φ + 1/4`. -/
private theorem sample_prob_split (φ : ℝ) (s : ℕ) (a b : Fin s → Bool) :
    (eigenphaseSampleLaw φ s).prob ((splitBits s).symm (a, b)) =
      (hadamardBitDist φ).probOf a * (hadamardBitDist (φ + 1 / 4)).probOf b := by
  change (∏ j : Fin (s + s),
    (if (j : ℕ) < s then hadamardBitDist φ else hadamardBitDist (φ + 1 / 4)).prob
      (Fin.addCases a b j)) = _
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.addCases_left]
    simp
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.addCases_right]
    simp

/-- The probability of an event on a single draw is the sum of the point masses over the
elements satisfying that event. -/
private theorem one_draw_event {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] :
    p.probEvent (L := 1) (fun ω => E (ω 0)) =
      ∑ x ∈ Finset.univ.filter E, p.prob x := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_filter, Finset.sum_filter]
  simpa only [mul_ite, mul_one, mul_zero] using!
    p.expect_coord (L := 1) 0 (fun x => if E x then (1 : ℝ) else 0)

/-- Each half of `eigenphaseSampleLaw φ s` has the corresponding independent Hadamard bit sample
law, at phase `φ` for the first half and `φ + 1/4` for the second. -/
private theorem sample_halves (φ : ℝ) (s : ℕ) (E F : (Fin s → Bool) → Prop)
    [DecidablePred E] [DecidablePred F] :
    (eigenphaseSampleLaw φ s).probEvent (L := 1)
        (fun ω => E (fun j => ω 0 (Fin.castAdd s j))) =
      (hadamardBitDist φ).probEvent E ∧
    (eigenphaseSampleLaw φ s).probEvent (L := 1)
        (fun ω => F (fun j => ω 0 (Fin.natAdd s j))) =
      (hadamardBitDist (φ + 1 / 4)).probEvent F := by
  classical
  have hfirst (a b : Fin s → Bool) :
      (fun j => (splitBits s).symm (a, b) (Fin.castAdd s j)) = a := by
    funext j
    change Fin.addCases a b (Fin.castAdd s j) = a j
    exact Fin.addCases_left j
  have hsecond (a b : Fin s → Bool) :
      (fun j => (splitBits s).symm (a, b) (Fin.natAdd s j)) = b := by
    funext j
    change Fin.addCases a b (Fin.natAdd s j) = b j
    exact Fin.addCases_right j
  constructor
  · rw [one_draw_event (eigenphaseSampleLaw φ s)
      (fun x => E (fun j => x (Fin.castAdd s j))), Finset.sum_filter,
      ← (splitBits s).symm.sum_comp,
      Fintype.sum_prod_type]
    simp_rw [hfirst, sample_prob_split]
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : E a
    · simp only [if_pos h, ← Finset.mul_sum,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf, mul_one]
    · simp [h]
  · rw [one_draw_event (eigenphaseSampleLaw φ s)
      (fun x => F (fun j => x (Fin.natAdd s j))), Finset.sum_filter,
      ← (splitBits s).symm.sum_comp,
      Fintype.sum_prod_type]
    simp_rw [hsecond, sample_prob_split]
    rw [Finset.sum_comm]
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : F b
    · simp only [if_pos h, ← Finset.sum_mul,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf, one_mul]
    · simp [h]

/-- For `0 < δ ≤ 1/2`, phase factors at chord distance less than `2 * sin (π * δ)` have phase
difference at most `δ` modulo an integer. -/
private theorem chord_mod_one (x y δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hchord : ‖eigenPhase x - eigenPhase y‖ < 2 * Real.sin (Real.pi * δ)) :
    ∃ m : ℤ, |x - y + m| ≤ δ := by
  let k : ℤ := ⌊x - y + 1 / 2⌋
  let r : ℝ := x - y - k
  have hr0 : -(1 / 2 : ℝ) ≤ r := by
    have h := Int.floor_le (x - y + 1 / 2)
    dsimp [r, k]
    linarith
  have hr1 : r ≤ 1 / 2 := by
    have h := Int.lt_floor_add_one (x - y + 1 / 2)
    dsimp [r, k]
    linarith
  have hrabs : |r| ≤ 1 / 2 := abs_le.mpr ⟨hr0, hr1⟩
  have he : eigenPhase r = eigenPhase (x - y) := by
    have ht : (2 * Real.pi * Complex.I * r : ℂ) =
        2 * Real.pi * Complex.I * (x - y) - 2 * Real.pi * Complex.I * (k : ℝ) := by
      dsimp [r]
      push_cast
      ring
    unfold eigenPhase
    rw [ht, Complex.exp_sub, exp_two_pi_I_int, div_one]
    push_cast
    rfl
  have hmul : eigenPhase (x - y) * eigenPhase y = eigenPhase x := by
    unfold eigenPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnorm : ‖eigenPhase x - eigenPhase y‖ = ‖eigenPhase r - 1‖ := by
    calc
      _ = ‖(eigenPhase (x - y) - 1) * eigenPhase y‖ := by
        rw [sub_mul, hmul, one_mul]
      _ = ‖eigenPhase (x - y) - 1‖ := by rw [norm_mul, eigenPhase_norm, mul_one]
      _ = _ := by rw [he]
  have hsine : ‖eigenPhase r - 1‖ = 2 * |Real.sin (Real.pi * r)| := by
    have ht : (2 * Real.pi * Complex.I * r : ℂ) =
        Complex.I * ((2 * Real.pi * r : ℝ) : ℂ) := by push_cast; ring
    unfold eigenPhase
    rw [ht, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * r) / 2 = Real.pi * r by ring,
      Real.norm_eq_abs, abs_mul]
    norm_num
  have hsinabs : |Real.sin (Real.pi * r)| = Real.sin (Real.pi * |r|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]), abs_mul, abs_of_pos Real.pi_pos]
  rw [hnorm, hsine, hsinabs] at hchord
  have hrδ : |r| ≤ δ := by
    by_contra h
    have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.pi * δ by nlinarith [Real.pi_pos])
      (show Real.pi * |r| ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) Real.pi_pos)
    linarith
  refine ⟨-k, ?_⟩
  simpa [r] using! hrδ

/-- If the cosine and sine estimates each have error at most `sin (π * δ) / 3`, their complex
argument divided by `2π` estimates `φ` within `δ` modulo an integer, for `0 < δ ≤ 1/2`. -/
private theorem arg_phase_good (a b φ δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (ha : |a - Real.cos (2 * Real.pi * φ)| ≤ Real.sin (Real.pi * δ) / 3)
    (hb : |b - Real.sin (2 * Real.pi * φ)| ≤ Real.sin (Real.pi * δ) / 3) :
    ∃ m : ℤ, |Complex.arg ((a : ℂ) + b * Complex.I) / (2 * Real.pi) - φ + m| ≤ δ := by
  let z : ℂ := (a : ℂ) + b * Complex.I
  let v : ℂ := Complex.exp ((Complex.arg z : ℂ) * Complex.I)
  have hv : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hzv : (‖z‖ : ℂ) * v = z := Complex.norm_mul_exp_arg_mul_I z
  have hα : eigenPhase (Complex.arg z / (2 * Real.pi)) = v := by
    rw [eigenPhase_eq_exp_real]
    have ht : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
      field_simp [Real.pi_ne_zero]
    rw [ht]
  have he : ‖z - eigenPhase φ‖ ≤ 2 * Real.sin (Real.pi * δ) / 3 := by
    have hn := Complex.norm_le_abs_re_add_abs_im (z - eigenPhase φ)
    have hre : (eigenPhase φ).re = Real.cos (2 * Real.pi * φ) := by
      rw [eigenPhase_eq_exp_real]
      simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    have him : (eigenPhase φ).im = Real.sin (2 * Real.pi * φ) := by
      rw [eigenPhase_eq_exp_real]
      simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
    simp only [Complex.sub_re, Complex.sub_im, hre, him] at hn
    have hzr : z.re = a := by simp [z]
    have hzi : z.im = b := by simp [z]
    rw [hzr, hzi] at hn
    linarith
  have hd : ‖v - z‖ = |1 - ‖z‖| := by
    have ht : v - z = ((1 - ‖z‖ : ℝ) : ℂ) * v := by
      push_cast
      rw [sub_mul, one_mul, hzv]
    rw [ht, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnorm := abs_norm_sub_norm_le z (eigenPhase φ)
  rw [eigenPhase_norm, abs_sub_comm] at hnorm
  have hchord : ‖v - eigenPhase φ‖ ≤ 4 * Real.sin (Real.pi * δ) / 3 := by
    have hn : ‖v - eigenPhase φ‖ ≤ ‖v - z‖ + ‖z - eigenPhase φ‖ := by
      calc
        _ = ‖(v - z) + (z - eigenPhase φ)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [hd] at hn
    linarith
  have hsin : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hδ) (by nlinarith [Real.pi_pos])
  apply chord_mod_one _ φ δ hδ hδhalf
  rw [hα]
  linarith

/-- The probability of a sample event is at most that of any event containing it. -/
private theorem event_mono {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) {L : ℕ} (E F : (Fin L → X) → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀ ω, E ω → F ω) :
    p.probEvent E ≤ p.probEvent F := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hω).1,
      h ω (Finset.mem_filter.mp hω).2⟩
  · intro ω _ _
    exact Finset.prod_nonneg (fun i _ => p.nonneg (ω i))

/-- The probability of the union of two sample events is at most the sum of their probabilities. -/
private theorem event_or_le {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) {L : ℕ} (E F : (Fin L → X) → Prop)
    [DecidablePred E] [DecidablePred F] :
    p.probEvent (fun ω => E ω ∨ F ω) ≤ p.probEvent E + p.probEvent F := by
  classical
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hp : 0 ≤ p.probOf ω := Finset.prod_nonneg (fun i _ => p.nonneg (ω i))
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]
  linarith

/-- The paired Hadamard test estimator satisfies `EigenphaseEstimateSubgoal`: the prescribed
sample size bounds phase estimation failure modulo integers by `ε`, in the setting of
[Kitaev1995]. -/
theorem eigenphaseEstimateSubgoal : EigenphaseEstimateSubgoal := by
  classical
  intro δ ε hδ hδhalf hε hε1 _ _ _ _ _ φ _ s hsize
  have hsin : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hδ) (by nlinarith [Real.pi_pos])
  have hlog : 0 < Real.log (4 / ε) :=
    Real.log_pos ((lt_div_iff₀ hε).mpr (by linarith))
  let T : ℝ := Real.sin (Real.pi * δ) / 6
  have hT : 0 < T := by positivity
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  have hhalf1 : ε / 2 < 1 := by linarith
  have hsize' : Real.log (2 / (ε / 2)) / (2 * T ^ 2) ≤ s := by
    have hrat : (2 : ℝ) / (ε / 2) = 4 / ε := by field_simp; norm_num
    calc
      _ = 18 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 := by
        rw [hrat]
        dsimp [T]
        field_simp
        ring
      _ ≤ 36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith
      _ ≤ s := hsize
  let bit : Bool → ℝ := fun b => if b then 1 else 0
  let E : (Fin s → Bool) → Prop := fun ω =>
    T ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit ω - (1 - Real.cos (2 * Real.pi * φ)) / 2|
  let F : (Fin s → Bool) → Prop := fun ω =>
    T ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit ω - (1 - Real.cos (2 * Real.pi * (φ + 1 / 4))) / 2|
  let A : (Fin 1 → Fin (s + s) → Bool) → Prop := fun ω =>
    E (fun j => ω 0 (Fin.castAdd s j))
  let B : (Fin 1 → Fin (s + s) → Bool) → Prop := fun ω =>
    F (fun j => ω 0 (Fin.natAdd s j))
  have hE : (hadamardBitDist φ).probEvent E ≤ ε / 2 :=
    hadamardTestConcentrationSubgoal φ s T (ε / 2) hT hhalf hhalf1 hsize'
  have hF : (hadamardBitDist (φ + 1 / 4)).probEvent F ≤ ε / 2 :=
    hadamardTestConcentrationSubgoal (φ + 1 / 4) s T (ε / 2) hT hhalf hhalf1 hsize'
  have hmarg := sample_halves φ s E F
  have hA : (eigenphaseSampleLaw φ s).probEvent A ≤ ε / 2 := hmarg.1.trans_le hE
  have hB : (eigenphaseSampleLaw φ s).probEvent B ≤ ε / 2 := hmarg.2.trans_le hF
  have hfail : ∀ ω : Fin 1 → Fin (s + s) → Bool,
      (¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ) → A ω ∨ B ω := by
    intro ω hf
    by_contra h
    have hna : ¬ A ω := fun ha => h (Or.inl ha)
    have hnb : ¬ B ω := fun hb => h (Or.inr hb)
    have hca : |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit (fun j => ω 0 (Fin.castAdd s j)) -
        (1 - Real.cos (2 * Real.pi * φ)) / 2| < T := lt_of_not_ge hna
    have hsb : |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit (fun j => ω 0 (Fin.natAdd s j)) -
        (1 - Real.cos (2 * Real.pi * (φ + 1 / 4))) / 2| < T := lt_of_not_ge hnb
    have hshift : Real.cos (2 * Real.pi * (φ + 1 / 4)) =
        -Real.sin (2 * Real.pi * φ) := by
      rw [show 2 * Real.pi * (φ + 1 / 4) = 2 * Real.pi * φ + Real.pi / 2 by ring,
        Real.cos_add_pi_div_two]
    rw [hshift] at hsb
    let a : ℝ :=
        1 - 2 * Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit
        (fun j => ω 0 (Fin.castAdd s j))
    let b : ℝ :=
        2 * Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit
        (fun j => ω 0 (Fin.natAdd s j)) - 1
    have ha : |a - Real.cos (2 * Real.pi * φ)| ≤ Real.sin (Real.pi * δ) / 3 := by
      have he : a - Real.cos (2 * Real.pi * φ) =
          -(2 * (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit (fun j => ω 0 (Fin.castAdd s j)) -
            (1 - Real.cos (2 * Real.pi * φ)) / 2)) := by dsimp [a]; ring
      rw [he, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [T] at hca
      linarith
    have hb : |b - Real.sin (2 * Real.pi * φ)| ≤ Real.sin (Real.pi * δ) / 3 := by
      have he : b - Real.sin (2 * Real.pi * φ) =
          2 * (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg bit (fun j => ω 0 (Fin.natAdd s j)) -
            (1 - -Real.sin (2 * Real.pi * φ)) / 2) := by dsimp [b]; ring
      rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [T] at hsb
      linarith
    apply hf
    have hg := arg_phase_good a b φ δ hδ hδhalf ha hb
    dsimp [a, b, bit, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg] at hg
    dsimp [eigenphaseDecode]
    push_cast at hg ⊢
    exact hg
  have hm := event_mono (eigenphaseSampleLaw φ s)
    (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ)
    (fun ω => A ω ∨ B ω) hfail
  have hu := event_or_le (eigenphaseSampleLaw φ s) A B
  linarith

end Qatlib.Concepts.HspRecovery.KitaevReadout
