/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem corollary2_2 : Corollary2_2RealRestricted := by
  intro N hN k l
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold twoAmplitudeMass distinguishedAfter ordinaryAfter
  field_simp
  ring

theorem diffusion_singleton_amplitudes {I : Type*} [Fintype I] [DecidableEq I]
    (w : I) (k l : ℝ) :
    ApplyGate (Diffusion I) (MarkedVector {w} (k : ℂ) (l : ℂ)) =
      MarkedVector {w} (distinguishedAfter (Fintype.card I) k l : ℂ)
        (ordinaryAfter (Fintype.card I) k l : ℂ) := by
  have hn : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨w⟩))
  funext i
  rw [applyGate_diffusion, sum_markedVector]
  simp only [Finset.card_singleton, Nat.cast_one]
  simp only [distinguishedAfter, ordinaryAfter, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_one, MarkedVector]
  split_ifs <;> field_simp <;> ring

theorem diffusion_preserves_bornMass {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (ψ : QState I) :
    (∑ i, BornProb (ApplyGate (Diffusion I) ψ) i) = ∑ i, BornProb ψ i := by
  simp only [BornProb, ApplyGate, ← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup (diffusion_unitary hN) ψ

end Qatlib.Concepts.SearchStopping.KnownCount
