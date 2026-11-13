/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySdpDuality

/-!
# Weighted Adversary Minimax Duality

This module gives the weighted nonnegative adversary minimax equalities corresponding to Theorem
18 of [HoyerLeeSpalek2007]. For strictly positive coordinate costs and a nonconstant Boolean
function, `advAlphaR` agrees with `minimaxAlpha`. The statements cover both the full Boolean
cube and an arbitrary promise set of Boolean words.

## Main statements

- `theorem18_duality` proves the equality on the full Boolean cube.
- `theorem18_duality_partial` proves the equality on a promise domain.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Theorem 18.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Duality

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

noncomputable section

/-- For a nonconstant Boolean function on the full Boolean cube and strictly positive coordinate
costs, `advAlphaR` equals `minimaxAlpha`. This is the weighted duality statement of Theorem
18 in [HoyerLeeSpalek2007]. -/
theorem theorem18_duality
    (n : ℕ) (f : (Fin n → Bool) → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : Fin n → Bool => x) f α =
      minimaxAlpha (fun x : Fin n → Bool => x) f α :=
  advAlphaR_eq_minimax (fun x : Fin n → Bool => x) f α hα hnc

/-- For a nonconstant Boolean function on a promise set of Boolean words and strictly positive
coordinate costs, `advAlphaR` equals `minimaxAlpha`. This gives the partial-domain form of
the duality in [HoyerLeeSpalek2007]. -/
theorem theorem18_duality_partial
    {n : ℕ} (D : Set (Fin n → Bool)) (f : D → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : D => x.val) f α =
      minimaxAlpha (fun x : D => x.val) f α :=
  advAlphaR_word_eq_minimax D f α hα hnc

end

end Qatlib.Concepts.SignedWeights.Representations.Duality
