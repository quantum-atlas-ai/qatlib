/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodCMarginalAnsw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath

open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

theorem dlog_trivial_group_dark_marginal :
    MeasureProb (dlogTwoDimState 3 8 1 1)
      (Finset.univ.filter fun t : Fin 8 × Fin 8 × ZMod 3 => t.1 = 4) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  have hc : t.1 = 4 := (Finset.mem_filter.mp ht).2
  have hv : dlogTwoDimState 3 8 1 1 t = 0 := by
    change dlogTwoDimState 3 8 1 1 (t.1, t.2.1, t.2.2) = 0
    rw [hc]
    exact dlog_trivial_group_dark_row _ _
  simp only [BornProb, hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem dlogGoodCMarginal_false : ¬ DlogGoodCMarginalLegacy := by
  intro h
  have hc : dlogSmallResidue 3 8 (4 : Fin 8) := by norm_num [dlogSmallResidue, centeredResidue]
  have hh := (h 3 8 1 (1 : ZMod 3) (1 : ZMod 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (4 : Fin 8) hc).1
  rw [dlog_trivial_group_dark_marginal] at hh
  norm_num at hh

theorem dlogGoodCMarginal : DlogGoodCMarginal := by
  intro p q r _ g x hprime hp hx0 hpq ho hx c hc
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 < p-1 := by omega
  obtain ⟨d, hgood⟩ := dlog_extend_small_residue p q r hq c hc
  let E := Finset.univ.filter fun t : Fin q × Fin q × ZMod p => t.1 = c
  let f := fun k : Fin (p-1) => (c, d, g ^ k.val)
  have hf : Function.Injective f := by
    intro k l h
    exact dlog_orbit_injective p g (by omega) ho
        (congrArg (fun t : Fin q × Fin q × ZMod p => t.2.2) h)
  have hsub : Finset.univ.image f ⊆ E := by
    intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hg3 := dlogGoodOutputProbability p q r g x hprime hp hx0 hpq ho hx
  have hmass := measureProb_ge_card_image (dlogTwoDimState p q g x)
    Finset.univ E f hf hsub (1/(20*(q : ℝ)^2)) (by
      intro k _hk
      exact hg3.2.1 c d k.val k.isLt hgood)
  simp only [Finset.card_univ, Fintype.card_fin] at hmass
  have hmain : (p-1 : ℝ)/(20*(q : ℝ)^2) ≤ MeasureProb (dlogTwoDimState p q g x) E := by
    convert! hmass using 1
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    ring
  refine ⟨hmain, ?_⟩
  intro hwidth
  have hw : (q : ℝ) ≤ 2*((p-1 : ℕ) : ℝ) := by exact_mod_cast hwidth
  have hl : 1/(40*(q : ℝ)) ≤ (p-1 : ℝ)/(20*(q : ℝ)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hw
    nlinarith [mul_nonneg hqr.le (sub_nonneg.mpr hw)]
  exact hl.trans hmain
end Qatlib.Concepts.PeriodSampling.DlogGoodProb

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997

theorem DlogGoodCMarginal_proof : DlogGoodCMarginal := dlogGoodCMarginal
end Qatlib.Concepts.PeriodSampling.DlogGoodProb.Shor1997
