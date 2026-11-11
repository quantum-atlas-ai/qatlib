/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# Eigenvalue transport under linear similarity

The endomorphism `tcTransform G H` is `G⁻¹ ∘ H ∘ G` for a linear equivalence `G`. This module
transports eigenvectors, eigenvalues, and dual eigen-equations through that similarity, as
required by transcorrelated operator changes [McArdleTew2020].

## Main statements

* `tcTransform_hasEigenvector_iff`: equivalence of eigenvector statements under `G`.
* `tcTransform_hasEigenvalue_iff`: preservation and reflection of eigenvalues.
* `tcTransform_dualMap_hasEigenvector`: transport of the dual eigen-equation.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.ImaginaryFlow.Similarity

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Conjugation of the endomorphism `H` by a linear equivalence `G`, with action `G⁻¹ ∘ H ∘ G`. -/
def tcTransform (G : M ≃ₗ[K] M) (H : Module.End K M) : Module.End K M :=
  (G.symm : M →ₗ[K] M).comp (H.comp (G : M →ₗ[K] M))

/-- The transformed endomorphism acts on `φ` as `G.symm (H (G φ))`. -/
@[simp]
lemma tcTransform_apply (G : M ≃ₗ[K] M) (H : Module.End K M) (φ : M) :
    tcTransform G H φ = G.symm (H (G φ)) := rfl

/-- A vector `φ` is an eigenvector of `tcTransform G H` with eigenvalue `μ` exactly when `G φ`
is an eigenvector of `H` with that eigenvalue. -/
theorem tcTransform_hasEigenvector_iff (G : M ≃ₗ[K] M) (H : Module.End K M) (μ : K) (φ : M) :
    (tcTransform G H).HasEigenvector μ φ ↔ H.HasEigenvector μ (G φ) := by
  rw [Module.End.hasEigenvector_iff, Module.End.hasEigenvector_iff,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, tcTransform_apply]
  constructor
  · rintro ⟨h, hne⟩
    refine ⟨?_, fun h0 => hne (G.injective (by simpa using h0))⟩
    have h' := congrArg (fun y => G y) h
    simpa [map_smul] using h'
  · rintro ⟨h, hne⟩
    refine ⟨?_, fun h0 => hne (G.injective (by simpa using h0))⟩
    have h' := congrArg (fun y => G.symm y) h
    simpa [map_smul] using h'

/-- Applying `G.symm` to an eigenvector of `H` gives an eigenvector of its similarity transform
with the same eigenvalue. -/
theorem tcTransform_hasEigenvector_of_hasEigenvector (G : M ≃ₗ[K] M) (H : Module.End K M)
    {μ : K} {ψ : M} (h : H.HasEigenvector μ ψ) :
    (tcTransform G H).HasEigenvector μ (G.symm ψ) := by
  rw [tcTransform_hasEigenvector_iff]
  simpa using h

/-- Conjugation by a linear equivalence preserves and reflects eigenvalues. -/
theorem tcTransform_hasEigenvalue_iff (G : M ≃ₗ[K] M) (H : Module.End K M) (μ : K) :
    (tcTransform G H).HasEigenvalue μ ↔ H.HasEigenvalue μ := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ((tcTransform_hasEigenvector_iff G H μ φ).mp hφ)
  · intro h
    obtain ⟨ψ, hψ⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (tcTransform_hasEigenvector_of_hasEigenvector G H hψ)

/-- A dual eigen-equation for `H` transports to the dual map of `tcTransform G H` by
precomposing the functional with `G`. -/
theorem tcTransform_dualMap_hasEigenvector (G : M ≃ₗ[K] M) (H : Module.End K M)
    {μ : K} {w : Module.Dual K M} (h : H.dualMap w = μ • w) :
    (tcTransform G H).dualMap (w.comp (G : M →ₗ[K] M)) =
      μ • w.comp (G : M →ₗ[K] M) := by
  ext x
  have hx := congrArg (fun (f : Module.Dual K M) => f (G x)) h
  simpa [LinearMap.dualMap_apply', LinearMap.comp_apply, tcTransform, LinearMap.smul_apply,
    smul_eq_mul] using hx

end Qatlib.Concepts.ImaginaryFlow.Similarity
