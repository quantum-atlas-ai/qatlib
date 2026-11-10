/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySdpDuality
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Duality

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

noncomputable section

theorem theorem18_duality
    (n : ℕ) (f : (Fin n → Bool) → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : Fin n → Bool => x) f α =
      minimaxAlpha (fun x : Fin n → Bool => x) f α :=
  advAlphaR_eq_minimax (fun x : Fin n → Bool => x) f α hα hnc

theorem theorem18_duality_partial
    {n : ℕ} (D : Set (Fin n → Bool)) (f : D → Bool) (α : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hnc : ∃ x z, f x ≠ f z) :
    advAlphaR (fun x : D => x.val) f α =
      minimaxAlpha (fun x : D => x.val) f α :=
  advAlphaR_word_eq_minimax D f α hα hnc

end

end Qatlib.Concepts.SignedWeights.Representations.Duality
