/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FiniteCounts.OffsetWord.CheckedWord
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem uniform_failure_exact (w : List (Instruction G))
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a w = none}).toReal = nonzeroFailureProbability w := by
  have hf : (Finset.univ.erase (0 : G)).filter (fun a => checkedRun a w = none) =
      (unsafeOffsets w).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
      checkedRun_eq_none, and_comm]
  rw [PMF.toOuterMeasure_uniformOfFinset'_apply]
  simp only [Set.mem_setOf_eq]
  rw [hf]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (0 : G)), Finset.card_univ,
    ENNReal.toReal_div, ENNReal.toReal_natCast, nonzeroFailureProbability]

theorem uniform_failure_le (w : List (Instruction G))
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a w = none}).toReal ≤
      (4 * w.length : ℕ) / (Fintype.card G - 1 : ℕ) := by
  rw [uniform_failure_exact]
  exact random_offset_failure_le w

end Qatlib.Concepts.FiniteCounts.OffsetWord
