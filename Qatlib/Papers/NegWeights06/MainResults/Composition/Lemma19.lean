/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.GeneralAdversary

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Lemma 19 — composition upper bound for the nonnegative adversary

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Lemma 19, §6.1, printed page 17:

`ADV_α(h) ≤ ADV_β(f)` for `h = f ∘ (g₁, …, g_k)` and `βᵢ = ADV_{αᵢ}(gᵢ)`.

The paper-layer theorem is a reference/bridge to the frozen
`Qatlib.Concepts.QueryComplexity.DegreeMethod.composition_upper_bound_on_source_scope`.
The frozen statement is on the source's legitimate block scope: positive
coordinate costs, a nonconstant outer function, nonconstant blocks, and finite
block costs.  These are not extra strength assumptions — the raw unrestricted
`g18Prop` is refuted by the checked
`g18_raw_constant_block_counterexample` (a constant block makes the source
composition ill-posed), so the source statement is used where its own domain
makes it meaningful.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Composition

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod

noncomputable section

/-- **Lemma 19 (nonnegative adversary composition upper bound).**
For `h = f ∘ (g₁, …, g_k)`, positive block costs `α`, a nonconstant outer
function, nonconstant blocks, and finite block values `βᵢ = ADV_{αᵢ}(gᵢ)`,
`ADV_α(h) ≤ ADV_β(f)`.

This is quant-ph/0611054v2 Lemma 19 (p. 17).  The frozen `blockCosts gin g α`
is definitionally `fun i => advAlphaENN (gin i) (g i)
(fun j => ENNReal.ofReal (α ⟨i,j⟩))`, i.e. the printed `βᵢ`. -/
theorem lemma19_upper_bound
    {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (α : ((i : Fin k) × Fin (n i)) → ℝ)
    (hα : ∀ c, 0 < α c) (hfn : ∃ u v : Fin k → Bool, f u ≠ f v)
    (hgn : ∀ i, ∃ a b : Y i, g i a ≠ g i b)
    (hfin : ∀ i, blockCosts gin g α i < ⊤) :
    advAlphaENN (composedInput gin) (composedFunction g f)
      (fun c => ENNReal.ofReal (α c)) ≤
      advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g α) :=
  composition_upper_bound_on_source_scope gin g f α hα hfn hgn hfin

end

end Qatlib.Papers.NegWeights06.MainResults.Composition
