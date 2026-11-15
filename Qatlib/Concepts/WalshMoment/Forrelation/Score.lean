/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped BigOperators

def realSign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def score {I : Type} [Fintype I] (H : I → I → ℝ) (f g : I → Bool) : ℝ :=
  (∑ i, ∑ j, realSign (f i) * H i j * realSign (g j)) / Fintype.card I

noncomputable def uniformScoreMean {I : Type} [Fintype I] (H : I → I → ℝ) : ℝ := by
  classical
  exact (∑ f : I → Bool, ∑ g : I → Bool, score H f g) / (Fintype.card (I → Bool) : ℝ) ^ 2

end Qatlib.Concepts.WalshMoment.Forrelation
