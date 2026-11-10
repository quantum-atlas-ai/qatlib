/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs
import Qatlib.Papers.QLattice03.MainResults.Reductions
import Qatlib.Papers.QLattice03.MainResults.Reduction.RadixEncoding
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults.Reduction

open Finset

noncomputable def dcpToTwoPoint (A : ∀ N : ℕ, DCPRegister N → ℤ) :
    ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ) :=
  fun n M r =>
    decode (2 * M) n M (A ((2 * M) ^ n) (enc (2 * M) n r.a, enc (2 * M) n r.a'))

theorem dcpToTwoPoint_correct (A : ∀ N : ℕ, DCPRegister N → ℤ) (hA : SolvesDCP A) :
    SolvesTwoPoint (dcpToTwoPoint A) := by
  intro n M r
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    by_cases hn : n = 0
    · subst hn
      funext i
      exact i.elim0
    · exfalso
      have hi : 0 < n := Nat.pos_of_ne_zero hn
      exact Nat.not_lt_zero _ (r.a ⟨0, hi⟩).isLt
  · unfold dcpToTwoPoint
    have hval : A ((2 * M) ^ n) (enc (2 * M) n r.a, enc (2 * M) n r.a')
        = (enc (2 * M) n r.a' : ℤ) - (enc (2 * M) n r.a : ℤ) := by
      have := hA ((2 * M) ^ n) (enc (2 * M) n r.a, enc (2 * M) n r.a')
      simpa using this
    rw [hval]
    exact decode_enc (by ring) hM r.a r.a'

theorem dcpToTwoPoint_correctWithFailure (f : ℝ)
    (A : ∀ N : ℕ, DCPRegister N → ℤ) (hA : SolvesDCPWithFailure f A) :
    SolvesTwoPointWithFailure f (dcpToTwoPoint A) :=
  dcpToTwoPoint_correct A hA

theorem hasTwoPointSolver_of_hasDCPSolver (f : ℝ) (h : HasDCPSolver f) :
    HasTwoPointSolver f := by
  obtain ⟨A, hA⟩ := h
  exact ⟨dcpToTwoPoint A, dcpToTwoPoint_correctWithFailure f A hA⟩

end Qatlib.Papers.QLattice03.MainResults.Reduction
