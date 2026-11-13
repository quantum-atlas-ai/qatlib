/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.AmbainisMethod
import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.ParityReduction

/-!
# Neighbor lists for the parity-clique gadget

This module defines the vertex type `GadgetVertex` and ordered neighbor function `gadgetNbr` for
a parity gadget augmented by a clique. The theorem `gadgetNbr_injective` verifies that each row
has distinct neighbors when the port modulus is nonzero. See [DurrMhallaLei2003].

## Main statements

* `gadgetNbr`: The ordered neighbor function with one designated forward parity port, other
  parity ports entering the clique, and clique rows pointing to the base vertex and the other
  clique vertices.
* `gadgetNbr_injective`: For nonzero `k`, distinct port labels in any gadget row give distinct
  neighbors.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Defs

attribute [local instance] Classical.propDecidable

/-- The disjoint union of the two-track parity vertices and the clique vertices indexed by `ZMod
k`. -/
abbrev GadgetVertex (p k : ℕ) := ParityVertex p ⊕ ZMod k

/-- The ordered neighbor function with one designated forward parity port, other parity ports
entering the clique, and clique rows pointing to the base vertex and the other clique
vertices. -/
def gadgetNbr {p k : ℕ} (b : ZMod p → Bool) (jf : ZMod p → Bool → ZMod k) :
    GadgetVertex p k → ZMod k → GadgetVertex p k
  | Sum.inl (i, l), j =>
      if j = jf i l then Sum.inl (i + 1, Bool.xor l (b i)) else Sum.inr j
  | Sum.inr i, j => if j = 0 then Sum.inl (0, false) else Sum.inr (i + j)

/-- For nonzero `k`, distinct port labels in any gadget row give distinct neighbors
[DurrMhallaLei2003]. -/
theorem gadgetNbr_injective {p k : ℕ} [NeZero k] (b : ZMod p → Bool)
    (jf : ZMod p → Bool → ZMod k) (v : GadgetVertex p k) :
    Function.Injective (gadgetNbr b jf v) := by
  intro j j' h
  cases v with
  | inl vl =>
      obtain ⟨i, l⟩ := vl
      by_cases hj : j = jf i l <;> by_cases hj' : j' = jf i l
      · rw [hj, hj']
      · simp only [gadgetNbr, if_pos hj, if_neg hj'] at h
        exact absurd h (by simp)
      · simp only [gadgetNbr, if_neg hj, if_pos hj'] at h
        exact absurd h (by simp)
      · simp only [gadgetNbr, if_neg hj, if_neg hj'] at h
        exact Sum.inr.inj h
  | inr i =>
      by_cases hj : j = 0 <;> by_cases hj' : j' = 0
      · rw [hj, hj']
      · simp only [gadgetNbr, if_pos hj, if_neg hj'] at h
        exact absurd h (by simp)
      · simp only [gadgetNbr, if_neg hj, if_pos hj'] at h
        exact absurd h (by simp)
      · simp only [gadgetNbr, if_neg hj, if_neg hj'] at h
        exact add_left_cancel (Sum.inr.inj h)

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
