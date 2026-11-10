/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodOutputProbabilityStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogOriginalContracts
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogAmplitudeLower
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodPairCountingAnsw
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.MeasureImageBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

private theorem dlog_half_phase : offGridPhase 8 (8 : ℝ)⁻¹ (4 : Fin 8) =
    -(Real.sqrt 8 : ℂ)⁻¹ := by
  rw [offGridPhase]
  rw [show (4 : Fin 8).val = 4 from rfl]
  norm_num only
  push_cast
  rw [show 2*(Real.pi : ℂ)*Complex.I*(4*(1/8) : ℂ) =
    (Real.pi : ℂ)*Complex.I by ring, Complex.exp_pi_mul_I]
  ring

theorem dlog_trivial_group_dark_row (d : Fin 8) (y : ZMod 3) :
    dlogTwoDimState 3 8 1 1 (4, d, y) = 0 := by
  by_cases hy : y = (1 : ZMod 3)
  · subst y
    simp [dlogTwoDimState]
    simp only [dlog_half_phase]
    simp only [offGridPhase, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one]
    ring
  · simp [dlogTwoDimState, Ne.symm hy]

theorem dlogGoodOutputProbability_false : ¬ DlogGoodOutputProbabilityLegacy := by
  intro h
  have hg : dlogGoodPair 3 8 1 (4 : Fin 8) (4 : Fin 8) := by
    refine ⟨⟨1, ?_⟩, ?_⟩ <;>
      norm_num [dlogGoodPair, dlogT, dlogSmallResidue, centeredResidue]
  have hh := (h 3 8 1 (1 : ZMod 3) (1 : ZMod 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp)).2.1 (4 : Fin 8) (4 : Fin 8) 0 (by norm_num) hg
  norm_num [BornProb, dlog_trivial_group_dark_row] at hh

theorem dlog_orbit_injective (p : ℕ) [NeZero p] (g : ZMod p) (hp : 1 < p)
    (ho : orderOf g = p-1) : Function.Injective (fun k : Fin (p-1) => g ^ k.val) := by
  have hg : IsOfFinOrder g := orderOf_pos_iff.mp (by rw [ho]; omega)
  intro k l h
  apply Fin.ext
  have he := hg.pow_inj_mod.mp h
  simpa only [ho, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt] using! he

theorem dlogGoodOutputProbability : DlogGoodOutputProbability := by
  intro p q r _ g x hprime hp hx0 hpq ho hx
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 < p-1 := by omega
  have hPr : (0 : ℝ) < ((p-1 : ℕ) : ℝ) := by exact_mod_cast hP
  let S := Finset.univ.filter fun cd : Fin q × Fin q => dlogGoodPair p q r cd.1 cd.2
  let E := Finset.univ.filter fun t : Fin q × Fin q × ZMod p => dlogGoodPair p q r t.1 t.2.1
  let f := fun z : (Fin q × Fin q) × Fin (p-1) => (z.1.1, z.1.2, g ^ z.2.val)
  have hf : Function.Injective f := by
    intro z w h
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun t : Fin q × Fin q × ZMod p => t.1) h
      · exact congrArg (fun t : Fin q × Fin q × ZMod p => t.2.1) h
    · exact dlog_orbit_injective p g (by omega) ho
        (congrArg (fun t : Fin q × Fin q × ZMod p => t.2.2) h)
  have hsub : (S.product Finset.univ).image f ⊆ E := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2⟩
  have hstate (c d : Fin q) (k : ℕ) (hk : k < p-1) (hgood : dlogGoodPair p q r c d) :
      1/(20*(q : ℝ)^2) ≤ BornProb (dlogTwoDimState p q g x) (c,d,g ^ k) := by
    have hs := dlog_good_state_probability_strong p q r g x hp hprime hx0 hpq ho hx c d k hk hgood
    have hc : 1/(20*(q : ℝ)^2) ≤ 1/(16*(q : ℝ)^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (q : ℝ)]
    exact hc.trans hs
  have hmass := measureProb_ge_card_image (dlogTwoDimState p q g x)
    (S.product Finset.univ) E f hf hsub (1/(20*(q : ℝ)^2)) (by
      intro z hz
      exact hstate z.1.1 z.1.2 z.2.val z.2.isLt
          (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2)
  have hcard : (S.product (Finset.univ : Finset (Fin (p-1)))).card = S.card*(p-1) := by
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hcount : (q : ℝ)/12 ≤ (S.card : ℝ) := by
    have hs := dlog_small_residue_real_count p q hq
    have hg : ((Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card : ℝ) ≤ (S.card : ℝ) :=
      by exact_mod_cast dlog_good_pairs_ge_small p q r hq
    exact hs.trans hg
  have hmain : (p-1 : ℝ)/(240*(q : ℝ)) ≤ MeasureProb (dlogTwoDimState p q g x) E := by
    have hm :=
        mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ ((p-1 : ℕ) : ℝ)/(20*(q : ℝ)^2))
    calc
      (p-1 : ℝ)/(240*(q : ℝ)) = ((q : ℝ)/12)*(((p-1 : ℕ) : ℝ)/(20*(q : ℝ)^2)) := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        field_simp
        ring
      _ ≤ (S.card : ℝ)*(((p-1 : ℕ) : ℝ)/(20*(q : ℝ)^2)) := hm
      _ = (S.card : ℝ)*((p-1 : ℕ) : ℝ)*(1/(20*(q : ℝ)^2)) := by ring
      _ ≤ _ := by
        simpa only [hcard, Nat.cast_mul] using! hmass
  refine ⟨hmain, ?_, ?_⟩
  · intro c d k hk hgood
    exact hstate c d k hk hgood
  · intro hwidth
    have hw : (q : ℝ) ≤ 2*((p-1 : ℕ) : ℝ) := by exact_mod_cast hwidth
    have hl : 1/480 ≤ (p-1 : ℝ)/(240*(q : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hw
      linarith
    exact hl.trans hmain

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
