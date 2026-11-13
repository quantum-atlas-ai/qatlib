/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryNegativeWeightComp
import Qatlib.Concepts.AdversaryBounds.OptimizedAdv

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 13 and Lemma 17 — weighted composition of `ADV±`

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 13 and Lemma 17, §6 (printed pages 15–16):

For `h = f ∘ (g₁, …, g_k)` and block costs `βᵢ = ADV±_{αᵢ}(gᵢ)`,

`ADV±_α(h) ≥ ADV±_β(f)`.

Theorem 13 is the optimized specialization; Lemma 17 is the same inequality
for any cost vector `β` dominated coordinatewise by the block values (which is
how the theorem is applied).  The paper-layer bridge uses the frozen
`Qatlib.Concepts.AdversaryBounds.AdvDuality.source_negative_adversary_composition_lower`
for the printed `ℝ≥0∞` value `advAlphaPmENN`, where `blockCostsPm` is exactly
`βᵢ = ADV±_{αᵢ}(gᵢ)`.  A second, conservative real-division form
`advPlus` is bridged to the frozen `advPlus_composition_ge`.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Composition

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

noncomputable section

/-- **Theorem 13 (weighted composition, `ADV±` flavor).**
For `h = f ∘ (g₁, …, g_k)`, positive block costs `α`, nonconstant outer
function and blocks, and observable (query-distinguishable) output
differences, the optimized signed adversary bound of `h` is at least the
optimized signed adversary bound of `f` at the block costs
`βᵢ = ADV±_{αᵢ}(gᵢ)`.

This is quant-ph/0611054v2 Theorem 13 (p. 15).  The frozen
`blockCostsPm gin g α` is definitionally `fun i => advAlphaPmENN (gin i) (g i)
(fun j => ENNReal.ofReal (α ⟨i,j⟩))`, i.e. the printed `βᵢ`. -/
theorem theorem13_pm_composition
    {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (α : ((i : Fin k) × Fin (n i)) → ℝ)
    (hα : ∀ c, 0 < α c) (hfn : ∃ u v : Fin k → Bool, f u ≠ f v)
    (hgn : ∀ i, ∃ a b : Y i, g i a ≠ g i b)
    (hobs : ∀ i, OutputObservable (gin i) (g i)) :
    advAlphaPmENN (fun u : Fin k → Bool => u) f (blockCostsPm gin g α) ≤
      advAlphaPmENN (composedInput gin) (composedFunction g f)
        (fun c => ENNReal.ofReal (α c)) :=
  source_negative_adversary_composition_lower gin g f α hα hfn hgn hobs

/-- The `ℝ≥0∞` cost-weighted signed adversary value is monotone in the cost
vector.  This is the cost-optimization step used in Lemma 17: replacing the
block values `βᵢ` by any coordinatewise smaller costs can only decrease
`ADV±_β(f)`. -/
theorem advAlphaPmENN_mono
    {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β β' : κ → ℝ≥0∞)
    (h : ∀ i, β i ≤ β' i) :
    advAlphaPmENN input g β ≤ advAlphaPmENN input g β' := by
  unfold advAlphaPmENN
  refine iSup_mono fun Γ => ?_
  refine iInf_mono fun i => ?_
  rw [mul_div_assoc, mul_div_assoc]
  gcongr
  exact h i

/-- **Lemma 17 (weighted composition, dominated cost vector).**
If every block cost `βᵢ` is at most the optimized signed block value
`ADV±_{αᵢ}(gᵢ)`, then `ADV±_β(f) ≤ ADV±_α(h)`.

This is the form in which the printed Lemma 17 (p. 16) is applied; taking
`β = blockCostsPm gin g α` recovers Theorem 13. -/
theorem lemma17_pm_composition_lower
    {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (α : ((i : Fin k) × Fin (n i)) → ℝ)
    (β : Fin k → ℝ≥0∞)
    (hβ : ∀ i, β i ≤ blockCostsPm gin g α i)
    (hα : ∀ c, 0 < α c) (hfn : ∃ u v : Fin k → Bool, f u ≠ f v)
    (hgn : ∀ i, ∃ a b : Y i, g i a ≠ g i b)
    (hobs : ∀ i, OutputObservable (gin i) (g i)) :
    advAlphaPmENN (fun u : Fin k → Bool => u) f β ≤
      advAlphaPmENN (composedInput gin) (composedFunction g f)
        (fun c => ENNReal.ofReal (α c)) :=
  (advAlphaPmENN_mono (fun u : Fin k → Bool => u) f β
    (blockCostsPm gin g α) hβ).trans
    (theorem13_pm_composition gin g f α hα hfn hgn hobs)

/-- **Lemma 17, conservative real-division form.**
The frozen `advPlus` value is the realized supremum with Lean's real division
(a zero filter counts as zero, a conservative estimate of the printed ratio).
With real block bounds `β`, the composition inequality `ADV±_β(f) ≤ ADV±_α(h)`
still holds, by the frozen `advPlus_composition_ge`. -/
theorem lemma17_realized_composition_lower
    {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (hne : ∀ i, 0 < n i)
    (g : ∀ i, X i → Bool) (hnc : ∀ i, ∃ u v, g i u ≠ g i v)
    (f : (Fin k → Bool) → Bool) (gin : ∀ i, X i → Fin (n i) → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) (hα : ∀ c, 0 ≤ α c)
    (β : Fin k → ℝ)
    (hβ : ∀ i, ENNReal.ofReal (β i) ≤ advPlus (gin i) (g i) (fun q => α ⟨i, q⟩)) :
    advPlus (fun t : Fin k → Bool => t) f β ≤
      advPlus (composedInput gin) (composedFunction g f) α :=
  advPlus_composition_ge k X n hne g hnc f gin α hα β hβ

end

end Qatlib.Papers.NegWeights06.MainResults.Composition
