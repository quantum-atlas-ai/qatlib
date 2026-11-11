/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

/-!
# Statement of the half-support decomposition

The predicate `FixesComplement` packages unitarity together with identity matrix entries outside
a chosen set of coordinates. The proposition `lemma4_half_support_decomposition_statement`
states the seven-factor decomposition of Lemma 4 in [Jordan2008], with each factor supported on
exactly half the coordinates when the dimension is divisible by four.

## Main statements

* `FixesComplement`: a unitary matrix acting as the identity outside the indicated coordinate
  set.
* `lemma4_half_support_decomposition_statement`: the proposition specifying seven half-support
  factors.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- The property that `W` is unitary and its entries agree with the identity whenever either
index lies outside `S`. -/
def FixesComplement {m : ℕ} (S : Finset (Fin m))
    (W : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  W ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
    ∀ i j : Fin m, (i ∉ S ∨ j ∉ S) → W i j = if i = j then 1 else 0

/-- The proposition that, in every dimension divisible by four, each unitary is a product of
seven unitaries, each fixing the complement of a set of size `m / 2` [Jordan2008, Lemma
4][Jordan2008]. -/
def lemma4_half_support_decomposition_statement : Prop :=
  ∀ (m : ℕ), 4 ∣ m →
  ∀ (U : Matrix (Fin m) (Fin m) ℂ), U ∈ Matrix.unitaryGroup (Fin m) ℂ →
    ∃ (S : Fin 7 → Finset (Fin m)) (W : Fin 7 → Matrix (Fin m) (Fin m) ℂ),
      (∀ j, (S j).card = m / 2) ∧
      (∀ j, FixesComplement (S j) (W j)) ∧
      U = W 6 * W 5 * W 4 * W 3 * W 2 * W 1 * W 0

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
