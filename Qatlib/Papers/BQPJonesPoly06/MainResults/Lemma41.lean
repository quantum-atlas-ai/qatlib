/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge
import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Net
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem lemma41_generator {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    {Q : E →L[ℂ] E} (hQ : Q ∈ bridgeGenerators A B W) :
    ApproximableBy (bridgeGenerators A B W) Q :=
  ApproximableBy.of_mem hQ

theorem lemma41_identity (A B : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E) :
    ApproximableBy (bridgeGenerators A B W) (1 : E →L[ℂ] E) :=
  ApproximableBy.id _

theorem lemma41_product {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    {T U : E →L[ℂ] E}
    (hS : ∀ Q ∈ bridgeGenerators A B W, ∀ x : E, ‖Q x‖ ≤ ‖x‖)
    (hTnorm : ∀ x : E, ‖T x‖ ≤ ‖x‖)
    (hT : ApproximableBy (bridgeGenerators A B W) T)
    (hU : ApproximableBy (bridgeGenerators A B W) U) :
    ApproximableBy (bridgeGenerators A B W) (T.comp U) :=
  ApproximableBy.comp hS hTnorm hT hU

theorem lemma41_generators_nonExpanding {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E) :
    ∀ Q ∈ bridgeGenerators A B W, ∀ x : E, ‖Q x‖ ≤ ‖x‖ := by
  intro Q hQ x
  rw [bridgeGenerators, Set.mem_union, Set.mem_union] at hQ
  rcases hQ with (hA | hB) | hW
  · exact le_of_eq (specialUnitary_norm hA x)
  · exact le_of_eq (specialUnitary_norm hB x)
  · have hQeq : Q = (W : E →L[ℂ] E) := by simpa using hW
    subst hQeq
    exact le_of_eq (W.norm_map x)

theorem lemma41_bridge_density_of_covering {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    (hcover : ∀ T ∈ SpecialUnitaryTop, T ∈ bridgeGenerators A B W) :
    ∀ T ∈ SpecialUnitaryTop, ApproximableBy (bridgeGenerators A B W) T :=
  fun T hT => ApproximableBy.of_mem (hcover T hT)

end Qatlib.Papers.BQPJonesPoly06.MainResults
