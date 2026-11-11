/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge
import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Net

/-!
# Closure properties for bridge approximation

This module proves elementary approximation properties for bridge generators: generators and the
identity are approximable, and suitable products remain approximable. It also proves that every
special unitary is approximable under the explicit hypothesis that all such maps already belong
to the generator set. See [AharonovArad2011].

## Main statements

* `lemma41_generators_nonExpanding`: bridge generators do not increase norms.
* `lemma41_product`: combines approximations under norm bounds.
* `lemma41_bridge_density_of_covering`: deduces approximation from generator coverage.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Every member of the bridge generator set is approximable by words in that set. See [Aharonov
and Arad, Lemma 4.1][AharonovArad2011]. -/
theorem lemma41_generator {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    {Q : E →L[ℂ] E} (hQ : Q ∈ bridgeGenerators A B W) :
    ApproximableBy (bridgeGenerators A B W) Q :=
  ApproximableBy.of_mem hQ

/-- The identity map is approximable by words in any bridge generator set. See [Aharonov and
Arad, Lemma 4.1][AharonovArad2011]. -/
theorem lemma41_identity (A B : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E) :
    ApproximableBy (bridgeGenerators A B W) (1 : E →L[ℂ] E) :=
  ApproximableBy.id _

/-- The composition of two approximable maps is approximable when all generators and the left
target map do not increase norms. See [Aharonov and Arad, Lemma 4.1][AharonovArad2011]. -/
theorem lemma41_product {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    {T U : E →L[ℂ] E}
    (hS : ∀ Q ∈ bridgeGenerators A B W, ∀ x : E, ‖Q x‖ ≤ ‖x‖)
    (hTnorm : ∀ x : E, ‖T x‖ ≤ ‖x‖)
    (hT : ApproximableBy (bridgeGenerators A B W) T)
    (hU : ApproximableBy (bridgeGenerators A B W) U) :
    ApproximableBy (bridgeGenerators A B W) (T.comp U) :=
  ApproximableBy.comp hS hTnorm hT hU

/-- Every bridge generator is nonexpanding in norm. See [Aharonov and Arad, Lemma
4.1][AharonovArad2011]. -/
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

/-- If every ambient special unitary belongs to the bridge generator set, every such map is
approximable by words in that set. See [Aharonov and Arad, Lemma 4.1][AharonovArad2011]. -/
theorem lemma41_bridge_density_of_covering {A B : Submodule ℂ E} (W : E ≃ₗᵢ[ℂ] E)
    (hcover : ∀ T ∈ SpecialUnitaryTop, T ∈ bridgeGenerators A B W) :
    ∀ T ∈ SpecialUnitaryTop, ApproximableBy (bridgeGenerators A B W) T :=
  fun T hT => ApproximableBy.of_mem (hcover T hT)

end Qatlib.Papers.BQPJonesPoly06.MainResults
