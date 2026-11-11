/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Hodge.Eigenvalues

set_option backward.isDefEq.respectTransparency false

/-!
# Chain maps, harmonic chains, and the harmonic projection

Source: arXiv:2501.12378v2, Section 6.2, Propositions 12-16 (pp. 34-36).

The paper's harmonic chains are `h(C) = ℋ = ker d ∩ ker d†` (Proposition 13).
Prop. 12 supplies a strong deformation retraction `(C, ℋ, i, p, K)` with
`h = i p` the orthogonal projection onto `ℋ`.  We take that projection as the
primary object: `harmonicProj K i = hᵢ` (Definition `harmonicProj` below).

The map of Proposition 14 is then `h(f) : h(C) → h(D)`, `x ↦ h_D(f x)`.

Cochains are indexed by `ℕ`; statements involving the "previous" differential
are phrased one degree up, with `K.dAdj i` playing the role of `dᵢ†`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults

open CochainComplex

/-- A chain map between cochain complexes: a family of linear maps commuting
with the differentials. -/
structure ChainMap (K L : CochainComplex) where
  /-- The underlying linear maps `fᵢ : Cⁱ → Dⁱ`. -/
  f : ∀ i, K.C i →ₗ[ℂ] L.C i
  /-- The chain condition `fᵢ₊₁ ∘ dᵢ = dᵢ ∘ fᵢ`. -/
  comm : ∀ (i : ℕ) (x : K.C i), f (i + 1) (K.d i x) = L.d i (f i x)

namespace ChainMap

variable {K L : CochainComplex} (f : ChainMap K L)

/-- The adjoint-chain-map hypothesis of Proposition 17: the transpose of `f`
commutes with the codifferentials, so that `f` commutes with the Laplacians.
At degree `i+1` this reads `fᵢ ∘ dᵢ† = dᵢ† ∘ fᵢ₊₁`. -/
def AdjointChainMap : Prop :=
  ∀ (i : ℕ) (y : K.C (i + 1)), f.f i (K.dAdj i y) = L.dAdj i (f.f (i + 1) y)

end ChainMap

namespace CochainComplex

variable (K : CochainComplex)

/-- The orthogonal projection `hᵢ` onto the harmonic subspace `ℋᵢ`, as a linear
map of the ambient cochain space (the map `h = i p` of Proposition 12). -/
def harmonicProj (i : ℕ) : K.C i →ₗ[ℂ] K.C i :=
  ((K.harmonic i).starProjection : K.C i →L[ℂ] K.C i).toLinearMap

/-- `hᵢ` is idempotent: it is a projection. -/
theorem harmonicProj_idem (i : ℕ) :
    (K.harmonicProj i).comp (K.harmonicProj i) = K.harmonicProj i := by
  apply LinearMap.ext
  intro x
  change (K.harmonic i).starProjection ((K.harmonic i).starProjection x) =
    (K.harmonic i).starProjection x
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.starProjection_apply_mem _ x

/-- `hᵢ` lands in the harmonic subspace `ℋᵢ`. -/
theorem harmonicProj_mem (i : ℕ) (x : K.C i) :
    K.harmonicProj i x ∈ K.harmonic i :=
  Submodule.starProjection_apply_mem _ x

/-- `hᵢ` fixes the harmonic chains. -/
@[simp]
theorem harmonicProj_apply_harmonic (i : ℕ) (x : K.harmonic i) :
    K.harmonicProj i (x : K.C i) = x :=
  Submodule.starProjection_mem_subspace_eq_self x

end CochainComplex

variable {K L : CochainComplex}

/-- Proposition 14's `h(f)`: the induced map on harmonic chains, defined by
projecting `f x` back onto the harmonic subspace of the target. -/
def harmonicMap (f : ChainMap K L) (i : ℕ) : K.harmonic i →ₗ[ℂ] L.harmonic i :=
  (((L.harmonic i).orthogonalProjection : L.C i →L[ℂ] L.harmonic i).toLinearMap).comp
    ((f.f i).comp (K.harmonic i).subtype)

/-- The underlying cochain representative of `h(f) x` is `h_D(f x)`. -/
@[simp]
theorem harmonicMap_apply (f : ChainMap K L) (i : ℕ) (x : K.harmonic i) :
    ((harmonicMap f i x : L.harmonic i) : L.C i) = L.harmonicProj i (f.f i x) := rfl

end Qatlib.Papers.KhovanovHom25.MainResults
