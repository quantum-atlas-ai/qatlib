/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySdpDuality

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 18 — duality of the weighted adversary bounds

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 18 (Duality of adversary bounds), §6, printed page 17:

`ADV_α(f) = MM_α(f)` for every `f : {0,1}^n → {0,1}` and `α ∈ ℝ^n_+`.

The paper-layer theorem is a reference/bridge to the frozen strong-duality
theorem
`Qatlib.Concepts.AdversaryBounds.AdvDuality.advAlphaR_eq_minimax`,
which proves the equality on every finite observable Boolean input domain with
positive coordinate costs; the flat domain `Fin n → Bool` is the paper's
`{0,1}^n`.  The paper's implicit nonconstancy of `f` is made explicit: for a
constant function the printed minimax infimum is over an empty pair set, so the
source statement is only meaningful on a nonconstant function (the frozen
`g17Prop` documents the same boundary).
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Duality

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

noncomputable section

/-- **Theorem 18 (Duality of adversary bounds).**
For a nonconstant Boolean function `f : {0,1}^n → {0,1}` and a positive cost
vector `α : Fin n → ℝ`, the weighted adversary bound equals the weighted
minimax bound:
`ADV_α(f) = MM_α(f)`.

Here `ADV_α` is the frozen `advAlphaR` and `MM_α` is the frozen `minimaxAlpha`
(printed Definitions 5 and 7).  The paper's `{0,1}^n` is the flat word domain
`Fin n → Bool`. -/
theorem theorem18_duality
    (n : ℕ) (f : (Fin n → Bool) → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : Fin n → Bool => x) f α =
      minimaxAlpha (fun x : Fin n → Bool => x) f α :=
  advAlphaR_eq_minimax (fun x : Fin n → Bool => x) f α hα hnc

/-- **Theorem 18 on an actual finite partial Boolean-word domain.**
The printed Theorem 18 is also used for partial functions, where the domain is
a subset `D ⊆ {0,1}^n`.  This is the frozen `advAlphaR_word_eq_minimax` bridge:
the input map is the inclusion `x ↦ x.val`. -/
theorem theorem18_duality_partial
    {n : ℕ} (D : Set (Fin n → Bool)) (f : D → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : D => x.val) f α =
      minimaxAlpha (fun x : D => x.val) f α :=
  advAlphaR_word_eq_minimax D f α hα hnc

end

end Qatlib.Papers.NegWeights06.MainResults.Duality
