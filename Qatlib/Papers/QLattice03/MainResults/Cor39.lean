/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def gridBall (n : ℕ) (L : ℕ) (R : ℝ) (c : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset (fun _ : Fin n =>
      Finset.Icc (-(↑⌈R * L⌉₊ : ℤ)) (↑⌈R * L⌉₊ : ℤ))).filter
    (fun x => Real.sqrt (∑ i : Fin n, (((x i : ℝ) - c i) / (L : ℝ)) ^ 2) ≤ R)

def gridBallIntersection_ratio : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R : ℝ) (d : Fin n → ℝ),
    1 ≤ R →
    (1 - C * Real.sqrt (n : ℝ) * Real.sqrt (∑ i : Fin n, (d i) ^ 2) / R) ≤
      (((gridBall n (2 ^ n) R (fun _ => 0)) ∩ gridBall n (2 ^ n) R d).card : ℝ) /
        ((gridBall n (2 ^ n) R (fun _ => 0)).card : ℝ)

end Qatlib.Papers.QLattice03.MainResults
