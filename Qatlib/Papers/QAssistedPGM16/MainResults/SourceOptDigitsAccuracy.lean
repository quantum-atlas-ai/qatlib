/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — OptDigits classification accuracy (c004)

Fixed source: arXiv:1609.02542, Sec. IV B on p.9.

The paper clamps the pixel subgraphs to a test picture, samples the four class
variables 100 times on DW2X, and assigns the most frequent class (a generative
classifier, no discriminative post-training).  After 6000 learning iterations
the procedure reaches 90% accuracy on the test pictures, against 25% for a
random guess over four classes.

The measured accuracy is an empirical input of the source and cannot be derived
in Lean.  The theorem below faithfully records the metric definition and the
reported numerical relation `9/10` versus the random-guess baseline `1/4`; it
does not claim to prove the hardware experiment.  We also formalize the
majority-vote decision rule over the four sampled class frequencies.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Classification accuracy as a rational: correct test pictures over the
number of test pictures. -/
def accuracy (correct total : ℕ) : ℚ := (correct : ℚ) / total

/-- `c` is a majority class for the four sampled class counts: no class
received strictly more votes (the decision rule used on p.9). -/
def IsMajority (votes : Fin 4 → ℕ) (c : Fin 4) : Prop :=
  ∀ d : Fin 4, votes d ≤ votes c

/-- A majority class always exists, so the sampling decision rule of p.9 is
well defined. -/
theorem exists_majorityClass (votes : Fin 4 → ℕ) : ∃ c, IsMajority votes c := by
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 4)) votes ⟨0, Finset.mem_univ 0⟩
  exact ⟨c, fun d => hc d (Finset.mem_univ d)⟩

/-- OptDigits result of p.9: after 6000 learning iterations the generative
classifier achieves 90% accuracy, whereas a random guess over four classes
achieves 25%; the reported 90/100 strictly beats the 1/4 baseline.  The counts
are the measured input; the arithmetic relation is proved. -/
theorem optdigits_accuracy :
    accuracy 90 100 = 9 / 10 ∧
    accuracy 1 4 = 1 / 4 ∧
    accuracy 1 4 < accuracy 90 100 ∧
    accuracy 90 100 * 100 = 90 ∧
    accuracy 1 4 * 100 = 25 ∧
    (4 : ℚ) * accuracy 1 4 * 100 = 100 := by
  unfold accuracy
  norm_num

end Qatlib.Papers.QAssistedPGM16.MainResults
