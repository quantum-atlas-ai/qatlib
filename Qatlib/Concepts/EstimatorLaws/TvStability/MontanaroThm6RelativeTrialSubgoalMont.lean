/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroThm6RelativeTrialSubgoalStat

/-!
# Pilot-scaled relative quantum mean trial

Proves the relative-error guarantee for one pilot-scaled layered quantum mean trial,
corresponding to the relative-estimation step of Theorem 6 in [Montanaro2015]. A classical pilot
average selects a scale, a good pilot ensures normalized second moment at most one, and the
layered estimate is rescaled to the original mean.

## Main statements

* `theorem6_good_pilot_moments` controls the scale and second moment when the pilot has error at
  most half the mean.
* `theorem6_good_record_error` converts normalized layer accuracy into relative error.
* `montanaroTheorem6RelativeTrialSubgoal` proves trial failure probability at most one quarter.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SketchArith.TransposeAccess.FinDist

set_option autoImplicit false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped Classical BigOperators

/-- Identifies the probability of an event on one sample with `SignedMean.mass` of that event
under the same finite law. -/
theorem theorem6_event_one_mass {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) :
    p.probEvent (fun ω : Fin 1 → X => E (ω 0)) = SignedMean.mass p E := by
  let e : (Fin 1 → X) ≃ X :=
    { toFun := fun ω => ω 0
      invFun := fun x _ => x
      left_inv := by
        intro ω
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := fun _ => rfl }
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter,
    ← e.symm.sum_comp (fun ω => if E (ω 0) then p.probOf ω else 0)]
  simp only [e, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, Fin.prod_univ_one,
      SignedMean.mass, Finset.sum_filter]
  rfl

/-- Shows that the pilot-scaled payoff is nonnegative whenever the original payoff is
nonnegative. -/
private theorem scaled_nonneg {I : Type} [Fintype I] (f : I → ℝ) (B : ℝ)
    (N : ℕ) (ω : Fin N → I) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ theorem6ScaledPayoff f B N ω i := by
  have havg : 0 ≤ avg f ω :=
    div_nonneg (Finset.sum_nonneg fun i _ => hf (ω i)) (by positivity)
  have hs : 0 ≤ theorem6Scale f B N ω := by
    unfold theorem6Scale
    exact add_nonneg (mul_nonneg havg (by positivity)) (by split_ifs <;> norm_num)
  exact fun i => div_nonneg (hf i) hs

/-- Shows that a pilot average within half the positive mean yields a positive scale at most `3
* sqrt (B + 1)` times the mean and a scaled second moment at most one, assuming the relative
variance bound. -/
theorem theorem6_good_pilot_moments {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (B : ℝ) (N : ℕ) (ω : Fin N → I)
    (hB : 1 ≤ B) (hμ : 0 < p.expect f)
    (hv : p.variance f ≤ B * (p.expect f)^2)
    (hseed : |avg f ω - p.expect f| ≤ p.expect f / 2) :
    0 < theorem6Scale f B N ω ∧
      theorem6Scale f B N ω ≤ 3 * Real.sqrt (B+1) * p.expect f ∧
      (∑ i, p.prob i * (theorem6ScaledPayoff f B N ω i)^2) ≤ 1 := by
  let c := avg f ω
  let μ := p.expect f
  have hc : μ/2 ≤ c := by have hh := (abs_le.mp hseed).1; dsimp [c, μ]; linarith
  have hc' : c ≤ 3*μ/2 := by have hh := (abs_le.mp hseed).2; dsimp [c, μ]; linarith
  have hcpos : 0 < c := by linarith
  have hspos : 0 < Real.sqrt (B+1) := Real.sqrt_pos.2 (by linarith)
  have hs : (Real.sqrt (B+1))^2 = B+1 := Real.sq_sqrt (by linarith)
  have hscale_eq : theorem6Scale f B N ω = 2*Real.sqrt (B+1)*c := by
    unfold theorem6Scale
    rw [if_neg (ne_of_gt hcpos)]
    dsimp [c]
    ring
  have hscale : 0 < theorem6Scale f B N ω := by
    rw [hscale_eq]
    exact mul_pos (mul_pos (by norm_num) hspos) hcpos
  refine ⟨hscale, ?_, ?_⟩
  · rw [hscale_eq]
    nlinarith [mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 2*Real.sqrt (B+1))]
  · have hraw : (∑ i, p.prob i*(f i)^2) ≤ (B+1)*μ^2 := by
      have he := SignedMean.shifted_second_moment p f 0
      simp only [sub_zero] at he
      rw [he]
      dsimp [μ]
      nlinarith
    have he : (∑ i, p.prob i*(theorem6ScaledPayoff f B N ω i)^2) =
        (∑ i, p.prob i*(f i)^2)/(theorem6Scale f B N ω)^2 := by
      simp only [theorem6ScaledPayoff, div_pow, mul_div_assoc, Finset.sum_div]
    rw [he]
    apply (div_le_one (by positivity : 0 < (theorem6Scale f B N ω)^2)).mpr
    have hcsq : μ^2 ≤ 4*c^2 := by
      have hh := mul_self_le_mul_self (by linarith : 0 ≤ μ/2) hc
      nlinarith
    have hssq : (theorem6Scale f B N ω)^2 = 4*(B+1)*c^2 := by
      rw [hscale_eq, mul_pow, mul_pow, hs]
      ring
    rw [hssq]
    exact hraw.trans (by nlinarith [mul_le_mul_of_nonneg_left hcsq (by linarith : 0 ≤ B+1)])

/-- Converts a layer-estimate error at most `2⁻ᵏ` into an output error at most `3 * sqrt (B + 1)
* 2⁻ᵏ` times the mean, using the stated scale bounds. -/
theorem theorem6_good_record_error {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (B : ℝ) (N k : ℕ)
    (ω : Fin N → I) (u : LayerRecord k)
    (hscale : 0 < theorem6Scale f B N ω)
    (hscale' : theorem6Scale f B N ω ≤ 3*Real.sqrt (B+1)*p.expect f)
    (hu : |layerEstimate k u-p.expect (theorem6ScaledPayoff f B N ω)| ≤ (1/2 : ℝ)^k) :
    |theorem6Output f B N k (ω,u)-p.expect f| ≤
      3*Real.sqrt (B+1)*(1/2 : ℝ)^k*p.expect f := by
  have hmean : p.expect (theorem6ScaledPayoff f B N ω) = p.expect f/theorem6Scale f B N ω := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect theorem6ScaledPayoff
    simp only [← mul_div_assoc, Finset.sum_div]
  have he : theorem6Output f B N k (ω,u)-p.expect f =
      theorem6Scale f B N ω*(layerEstimate k u-p.expect (theorem6ScaledPayoff f B N ω)) := by
    rw [hmean]
    unfold theorem6Output
    field_simp
  rw [he, abs_mul, abs_of_pos hscale]
  calc
    _ ≤ theorem6Scale f B N ω*(1/2 : ℝ)^k := mul_le_mul_of_nonneg_left hu hscale.le
    _ ≤ (3*Real.sqrt (B+1)*p.expect f)*(1/2 : ℝ)^k :=
      mul_le_mul_of_nonneg_right hscale' (by positivity)
    _ = _ := by ring

/-- Proves the single-trial relative guarantee associated with Theorem 6 of [Montanaro2015]. The
pilot-size, layer-accuracy, positive-mean, and relative-variance assumptions give failure
probability at most `1 / 4`. -/
theorem montanaroTheorem6RelativeTrialSubgoal : MontanaroTheorem6RelativeTrialSubgoal := by
  intro I _ _ A j f B ε N k hA hf hB _hε _hε1 hN hk hwindow μ hμ hv
  let p := signedMeanSource A j hA
  let seed : FinDist (Fin N → I) := independentSampleLaw (fun _ => p)
  let E := fun ω : Fin N → I => |avg f ω-p.expect f| ≤ p.expect f/2
  let Q := fun ω => layerLaw k A j (theorem6ScaledPayoff f B N ω) hA (scaled_nonneg f B N ω hf)
  let F := fun ω u => |layerEstimate k u-p.expect (theorem6ScaledPayoff f B N ω)| ≤ (1/2 : ℝ)^k
  change 0 < p.expect f at hμ
  change p.variance f ≤ B*(p.expect f)^2 at hv
  have hNR : 0 < (N : ℝ) := by linarith
  have hNat : 0 < N := by exact_mod_cast hNR
  have hb := p.chebyshev_avg f hNat (p.expect f/2) (by positivity)
  have hb' : SignedMean.mass seed (fun ω => p.expect f/2 < |avg f ω-p.expect f|) ≤ 1/8 := by
    calc
      _ ≤ p.variance f/((N : ℝ)*(p.expect f/2)^2) := hb
      _ ≤ B*(p.expect f)^2/((N : ℝ)*(p.expect f/2)^2) :=
        div_le_div_of_nonneg_right hv (by positivity)
      _ ≤ 1/8 := by
        apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)*(p.expect f/2)^2)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg (p.expect f))]
  have hseed : 7/8 ≤ SignedMean.mass seed E := by
    have hc := SignedMean.mass_complement seed E
    simp only [E, not_le] at hc
    linarith
  have hF (ω : Fin N → I) (hω : E ω) : 15/16 ≤ SignedMean.mass (Q ω) (F ω) := by
    have hs := theorem6_good_pilot_moments p f B N ω hB hμ hv hω
    have hg := layered_quantum_mean_actual_guarantee k (by omega) A j
      (theorem6ScaledPayoff f B N ω) hA (scaled_nonneg f B N ω hf) hs.2.2
    have hg' : 1-(1/2 : ℝ)^k ≤ SignedMean.mass (Q ω) (F ω) := by
      simpa only [SignedMean.mass, neg_pow_half_eq] using! hg
    have he : (1/2 : ℝ)^k ≤ 1/16 := by
      calc
        _ ≤ (1/2 : ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        _ = _ := by norm_num
    linarith
  have hl := SignedMean.conditional_good_lower seed E (fun ω => SignedMean.mass (Q ω) (F ω))
    (7/8) (15/16) (by norm_num) hseed hF
  have hm := SignedMean.conditional_one_event seed Q E F
  have hl' : (7/8 : ℝ)*(15/16) ≤
      ∑ ω with E ω.1 ∧ F ω.1 ω.2, (theorem6TrialLaw A j f B N k hA hf).prob ω := hm.symm ▸ hl
  have hgood : (7/8 : ℝ)*(15/16) ≤ SignedMean.mass (theorem6TrialLaw A j f B N k hA hf)
      (fun ω => |theorem6Output f B N k ω-p.expect f| ≤ ε*p.expect f) := by
    apply hl'.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      obtain ⟨_, he, hu⟩ := Finset.mem_filter.mp hω
      have hs := theorem6_good_pilot_moments p f B N ω.1 hB hμ hv he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (theorem6_good_record_error p f B N k ω.1 ω.2 hs.1 hs.2.1 hu).trans
          (mul_le_mul_of_nonneg_right hwindow hμ.le)⟩
    · intro ω _ _
      exact (theorem6TrialLaw A j f B N k hA hf).nonneg ω
  rw [theorem6_event_one_mass (theorem6TrialLaw A j f B N k hA hf)
    (fun ω => ε*μ < |theorem6Output f B N k ω-μ|)]
  have hc := SignedMean.mass_complement (theorem6TrialLaw A j f B N k hA hf)
    (fun ω => |theorem6Output f B N k ω-p.expect f| ≤ ε*p.expect f)
  simp only [not_le] at hc
  change SignedMean.mass _ (fun ω => ε*p.expect f < |theorem6Output f B N k ω-p.expect f|) ≤ 1/4
  linarith

end Qatlib.Concepts.EstimatorLaws.TvStability
