/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryNegativeWeightComp
import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Composition

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

noncomputable section

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

end Qatlib.Concepts.SignedWeights.Representations.Composition
