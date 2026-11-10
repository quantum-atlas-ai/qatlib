/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

def FixesComplement {m : ℕ} (S : Finset (Fin m))
    (W : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  W ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
    ∀ i j : Fin m, (i ∉ S ∨ j ∉ S) → W i j = if i = j then 1 else 0

def lemma4_half_support_decomposition_statement : Prop :=
  ∀ (m : ℕ), 4 ∣ m →
  ∀ (U : Matrix (Fin m) (Fin m) ℂ), U ∈ Matrix.unitaryGroup (Fin m) ℂ →
    ∃ (S : Fin 7 → Finset (Fin m)) (W : Fin 7 → Matrix (Fin m) (Fin m) ℂ),
      (∀ j, (S j).card = m / 2) ∧
      (∀ j, FixesComplement (S j) (W j)) ∧
      U = W 6 * W 5 * W 4 * W 3 * W 2 * W 1 * W 0

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
