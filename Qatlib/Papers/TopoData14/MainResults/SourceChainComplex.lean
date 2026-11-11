/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceChainComplex — the abstract chain complex behind Eq. (7)

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

This file fixes the chain-complex vocabulary of Section 2 ("Step 2: Topological
analysis", PDF p. 11--12, text lines 445--505). A degree-`k` chain group `C k` is
the complex vector space spanned by the `k`-simplices in the simplicial complex at
grouping scale `ε`; in the paper this is written `H^ε_k` with `dim H^ε_k = |S^ε_k|`.
The boundary map `∂_k : C k → C (k-1)` is encoded by `d k : C (k+1) → C k`, so that
`d k` is the paper's `∂_{k+1}`; this shift is chosen so that all indices are natural
numbers. Eq. (5) is the concrete formula on simplex basis vectors and is not needed
for the dimension identity of Eq. (7).

Boundary: this file only records the *dimension identity* of Eq. (7) and the
chain-complex data it needs. It does not formalize the concrete signs of Eq. (5),
the persistent-homology filtration, or any quantum subroutine.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoData14.MainResults

open scoped Classical BigOperators

variable {C : ℕ → Type*}
variable [∀ k, AddCommGroup (C k)] [∀ k, Module ℂ (C k)]
variable [∀ k, FiniteDimensional ℂ (C k)]

/-- Fixed arXiv:1408.3106v1, Eq. (7) (PDF p. 12): the Betti number is the dimension
of the homology group, `dim Ker ∂_k − dim Im ∂_{k+1}`.

Indexing convention: `d k : C (k+1) → C k` encodes the paper's `∂_{k+1}`. Since a
degree shift is unavoidable in a `ℕ`-indexed chain complex (there is no `∂_0`), the
value `bettiNumber d k` below is exactly the paper's `β_{k+1}`, i.e.
`dim Ker ∂_{k+1} − dim Im ∂_{k+2}`. All statements are invariant under this uniform
shift; the concrete simplicial boundary maps are supplied by the caller. -/
def bettiNumber (d : ∀ k, C (k + 1) →ₗ[ℂ] C k) (k : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (d k)) -
    Module.finrank ℂ (LinearMap.range (d (k + 1)))

/-- Fixed arXiv:1408.3106v1, Eq. (5) chain condition `∂_k ∂_{k+1} = 0`
("the boundary of a boundary is zero", PDF p. 12): in the shifted indexing,
`d k ∘ d (k+1) = 0`. -/
def IsChainMap (d : ∀ k, C (k + 1) →ₗ[ℂ] C k) : Prop :=
  ∀ k, d k ∘ₗ d (k + 1) = 0

/-- Fixed arXiv:1408.3106v1, Eq. (7) (PDF p. 12): for a chain complex,
`β = dim Ker ∂ + dim Ker ∂' − dim H`, where `H` is the space of `(k+1)`-simplices
at scale `ε`. For `bettiNumber d k = β_{k+1}` the printed identity reads
`bettiNumber d k = dim Ker (d k) + dim Ker (d (k+1)) − dim C (k+2)`.

Proof route: rank--nullity for `d (k+1)` (whose domain is `C (k+2)`) gives
`dim Im (d (k+1)) + dim Ker (d (k+1)) = dim C (k+2)`, and the chain condition
gives `Im (d (k+1)) ⊆ Ker (d k)`, so the subtraction is untruncated and the two
expressions agree. -/
theorem bettiNumber_eq_ker_add_ker_sub_finrank
    (d : ∀ k, C (k + 1) →ₗ[ℂ] C k) (hchain : IsChainMap d) (k : ℕ) :
    bettiNumber d k =
      Module.finrank ℂ (LinearMap.ker (d k)) +
        Module.finrank ℂ (LinearMap.ker (d (k + 1))) -
          Module.finrank ℂ (C (k + 2)) := by
  have hrn : Module.finrank ℂ (LinearMap.range (d (k + 1))) +
      Module.finrank ℂ (LinearMap.ker (d (k + 1))) = Module.finrank ℂ (C (k + 2)) :=
    LinearMap.finrank_range_add_finrank_ker (d (k + 1))
  have hle : Module.finrank ℂ (LinearMap.range (d (k + 1))) ≤
      Module.finrank ℂ (LinearMap.ker (d k)) := by
    refine Submodule.finrank_mono ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hchain k, LinearMap.zero_apply]
  unfold bettiNumber
  omega

/-- Fixed arXiv:1408.3106v1, Eq. (7) (PDF p. 12): the homological dimension is exactly the
alternating kernel expression of Eq. (7), in the form used by the quantum algorithm: the count
`dim Ker ∂_k + dim Ker ∂_{k+1}` minus the simplicial register dimension. -/
theorem bettiNumber_add_finrank_eq
    (d : ∀ k, C (k + 1) →ₗ[ℂ] C k) (hchain : IsChainMap d) (k : ℕ) :
    bettiNumber d k + Module.finrank ℂ (C (k + 2)) =
      Module.finrank ℂ (LinearMap.ker (d k)) +
        Module.finrank ℂ (LinearMap.ker (d (k + 1))) := by
  have h := bettiNumber_eq_ker_add_ker_sub_finrank d hchain k
  have hle : Module.finrank ℂ (LinearMap.range (d (k + 1))) ≤
      Module.finrank ℂ (LinearMap.ker (d k)) := by
    refine Submodule.finrank_mono ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hchain k, LinearMap.zero_apply]
  have hrn : Module.finrank ℂ (LinearMap.range (d (k + 1))) +
      Module.finrank ℂ (LinearMap.ker (d (k + 1))) = Module.finrank ℂ (C (k + 2)) :=
    LinearMap.finrank_range_add_finrank_ker (d (k + 1))
  unfold bettiNumber at h ⊢
  omega

end Qatlib.Papers.TopoData14.MainResults

end
