/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem lemma62_basis_move_id {A B : Submodule ℂ E} (hAB : Module.finrank ℂ A < Module.finrank ℂ B)
    (hApos : 0 < Module.finrank ℂ A) (W : E ≃ₗᵢ[ℂ] E)
    (u : Fin (Module.finrank ℂ A) → E) (v : Fin (Module.finrank ℂ B) → E)
    (hsame : u ⟨0, hApos⟩ = v ⟨0, lt_of_lt_of_le hApos hAB.le⟩) :
    ∃ T : E →L[ℂ] E, ApproximableBy (bridgeGenerators A B W) T ∧
      T (u ⟨0, hApos⟩) = v ⟨0, lt_of_lt_of_le hApos hAB.le⟩ ∧
      (∀ i : Fin (Module.finrank ℂ A), i ≠ ⟨0, hApos⟩ → T (u i) = u i) := by
  refine ⟨1, ApproximableBy.id _, ?_, ?_⟩
  · simpa using hsame
  · intro i _
    simp

end Qatlib.Papers.BQPJonesPoly06.MainResults
