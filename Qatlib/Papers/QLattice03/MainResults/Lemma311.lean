/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Cor39
set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def uniformBallAmplitude (n : ℕ) (L : ℕ) (R : ℝ) : (Fin n → ℤ) → ℂ :=
  fun x =>
    if x ∈ gridBall n L R (fun _ => 0) then
      (((Real.sqrt ((gridBall n L R (fun _ => 0)).card : ℝ))⁻¹ : ℝ) : ℂ)
    else 0

def ballSuperposition_efficient (c : ℝ) (hc : 0 < c) : Prop :=
  ∃ (etat : ∀ n : ℕ, (Fin n → ℤ) → ℂ), ∀ (n : ℕ), 0 < n → ∀ (R : ℝ), 1 ≤ R →
    (∑ x ∈ gridBall n (2 ^ n) R (fun _ => 0),
        ‖etat n x - uniformBallAmplitude n (2 ^ n) R x‖ ^ 2) <
      1 / (n : ℝ) ^ (2 * c)

end Qatlib.Papers.QLattice03.MainResults
