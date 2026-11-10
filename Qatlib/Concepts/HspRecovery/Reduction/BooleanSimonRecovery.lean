/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonSampling
import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryTail
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

theorem booleanSimonSubgroup_eq_iff {n : ℕ} (s t : BooleanVec n) :
    booleanSimonSubgroup s = booleanSimonSubgroup t ↔ s = t := by
  constructor
  · intro hst
    by_cases hs : s = 0
    · subst s
      have htmem : t ∈ booleanSimonSubgroup (0 : BooleanVec n) := by
        rw [hst]
        exact self_mem_booleanSimonSubgroup t
      have ht0 : t = 0 := by
        rcases (mem_booleanSimonSubgroup_iff (0 : BooleanVec n) t).1 htmem with h | h
        · exact h
        · exact h
      exact ht0.symm
    · have hsmem : s ∈ booleanSimonSubgroup t := by
        rw [← hst]
        exact self_mem_booleanSimonSubgroup s
      rcases (mem_booleanSimonSubgroup_iff t s).1 hsmem with h0 | hst'
      · exact (hs h0).elim
      · exact hst'
  · rintro rfl
    rfl

theorem card_booleanSimonSubgroup_eq_two_of_ne_zero {n : ℕ}
    (s : BooleanVec n) (hs : s ≠ 0) :
    Fintype.card (booleanSimonSubgroup s) = 2 := by
  let e : booleanSimonSubgroup s ≃ ↥({(0 : BooleanVec n), s} : Finset (BooleanVec n)) :=
    { toFun := fun x => ⟨x.1, by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          (mem_booleanSimonSubgroup_iff s x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, by
        apply (mem_booleanSimonSubgroup_iff s x.1).2
        simpa only [Finset.mem_insert, Finset.mem_singleton] using x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (booleanSimonSubgroup s) =
        Fintype.card ↥({(0 : BooleanVec n), s} : Finset (BooleanVec n)) :=
      Fintype.card_congr e
    _ = ({(0 : BooleanVec n), s} : Finset (BooleanVec n)).card := Fintype.card_coe _
    _ = 2 := Finset.card_pair (Ne.symm hs)

@[simp] theorem card_booleanSimonSubgroup_zero (n : ℕ) :
    Fintype.card (booleanSimonSubgroup (0 : BooleanVec n)) = 1 := by
  rw [booleanSimonSubgroup_zero]
  simp

theorem booleanSimonSecret_eq_of_candidate_eq {n m : ℕ}
    (samples : Fin m → BooleanVec n) (s t : BooleanVec n)
    (hs : booleanSampleCandidate samples = booleanSimonSubgroup s)
    (ht : booleanSampleCandidate samples = booleanSimonSubgroup t) :
    s = t := by
  apply (booleanSimonSubgroup_eq_iff s t).1
  exact hs.symm.trans ht

variable {n : ℕ}
variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem hiddenSubgroupFreshSamples_simon_failure_le_rank_add_budget
    (f : BooleanVec n → R) (s : BooleanVec n) (hf : BooleanSimonPromise f s)
    (k : ℕ) :
    (∑ xs ∈ Finset.univ.filter
        (fun xs : Fin (booleanOrthogonalRank (booleanSimonSubgroup s) + k) →
            AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) ≠ booleanSimonSubgroup s),
      hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv
        (booleanOrthogonalRank (booleanSimonSubgroup s) + k) xs) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  exact hiddenSubgroupFreshSamples_boolean_failure_le_rank_add_budget
    f (booleanSimonSubgroup s) ((booleanSimonPromise_iff_hidesSubgroup f s).1 hf)
      (booleanCharacterEquiv n).toEquiv k

theorem hiddenSubgroupFreshSamples_simon_success_ge_rank_add_budget
    (f : BooleanVec n → R) (s : BooleanVec n) (hf : BooleanSimonPromise f s)
    (k : ℕ) :
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ k) ≤
      ∑ xs ∈ Finset.univ.filter
        (fun xs : Fin (booleanOrthogonalRank (booleanSimonSubgroup s) + k) →
            AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = booleanSimonSubgroup s),
        hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv
          (booleanOrthogonalRank (booleanSimonSubgroup s) + k) xs := by
  exact hiddenSubgroupFreshSamples_boolean_success_ge_rank_add_budget
    f (booleanSimonSubgroup s) ((booleanSimonPromise_iff_hidesSubgroup f s).1 hf)
      (booleanCharacterEquiv n).toEquiv k

end Qatlib.Concepts.HspRecovery.ReductionCore
