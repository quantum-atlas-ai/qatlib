/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

def Theorem13OptimizedComposition : Prop :=
  ∀ (k : ℕ) (X : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (n : Fin k → ℕ) (hne : ∀ i, 0 < n i)
    (g : ∀ i, X i → Bool) (hnc : ∀ i, ∃ u v, g i u ≠ g i v)
    (f : (Fin k → Bool) → Bool) (gin : ∀ i, X i → Fin (n i) → Bool)
    (α : (i : Fin k) × Fin (n i) → ℝ) (hα : ∀ c, 0 ≤ α c)
    (β : Fin k → ℝ),
    (∀ i, ENNReal.ofReal (β i) ≤ advPlus (gin i) (g i) (fun q => α ⟨i, q⟩)) →
    advPlus (weightedAdvInput gin) (fun x => f (fun i => g i (x i))) α ≥
      advPlus (fun t => t) f β

end Qatlib.Concepts.AdversaryBounds.AdvDuality
