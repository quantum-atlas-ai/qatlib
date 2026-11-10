/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20ProbabilityBoundStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

theorem lemma20ProbabilityBound_answer : Lemma20ProbabilityBound := by
  unfold Lemma20ProbabilityBound
  intro N _ s M P G y hM hP hbound hhalf hdis hy _hres
  (try dsimp only)
  intro k
  let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))
  change Disjoint G A at hdis
  have hinj : Set.InjOn (fun r : ℕ => (s + r * P : ZMod N)) ↑(Finset.range M) := by
    intro r hr t ht he
    have hrN := aqProgression_index_lt N s M P r (by omega) hbound (Finset.mem_range.mp hr)
    have htN := aqProgression_index_lt N s M P t (by omega) hbound (Finset.mem_range.mp ht)
    have hnat : s + r * P = s + t * P := by
      have hv := congrArg ZMod.val he
      simpa only [← Nat.cast_add, ← Nat.cast_mul, ZMod.val_natCast,
        Nat.mod_eq_of_lt hrN, Nat.mod_eq_of_lt htN] using hv
    exact mul_right_cancel₀ hP.ne' (Nat.add_left_cancel hnat)
  have hc : A.card = M := by
    dsimp only [A]
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hu : (A ∪ G).card = M + G.card := by
    rw [Finset.card_union_of_disjoint hdis.symm, hc]
  have hθ := aq_angle_properties N (M + G.card) (NeZero.pos N) (by omega) hhalf
  have hb := conditional_amplified_qft_born N k (A ∪ G) y (aqAngle N (M + G.card))
    hy hθ.1 hθ.2.2.1 (by rw [hu]; exact hθ.2.2.2.1)
  have hf : distinctNoiseFourier (A ∪ G) y =
      (∑ r ∈ Finset.range M, ZMod.stdAddChar ((s + r * P : ZMod N) * y)) +
      ∑ z ∈ G, ZMod.stdAddChar (z * y) := by
    unfold distinctNoiseFourier
    rw [Finset.sum_union hdis.symm]
    dsimp only [A]
    rw [Finset.sum_image hinj]
  have hn : ‖distinctNoiseFourier (A ∪ G) y‖ ≤ (M + G.card : ℕ) := by
    simpa only [distinctNoiseFourier, norm_stdAddChar, Finset.sum_const,
      nsmul_eq_mul, mul_one, hu] using
      norm_sum_le (A ∪ G) (fun z => ZMod.stdAddChar (z * y))
  refine ⟨by simpa [hf] using hb, ?_⟩
  rw [hb]
  have hs : ‖distinctNoiseFourier (A ∪ G) y‖^2 ≤ ((M + G.card : ℕ) : ℝ)^2 := by
    nlinarith [norm_nonneg (distinctNoiseFourier (A ∪ G) y)]
  have hscale : 0 ≤ (conditionalAmplifiedGain k (aqAngle N (M + G.card)))^2 / (N : ℝ)^2 := by
    positivity
  simpa [mul_div_right_comm] using mul_le_mul_of_nonneg_left hs hscale

end Qatlib.Concepts.AmpTransform.ErrorStream
