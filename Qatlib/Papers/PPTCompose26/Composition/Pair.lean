/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.PairLemma
public import Qatlib.Foundations.PPTMatrix.OperatorCones.GurvitsBarnum
public import Qatlib.Foundations.PPTMatrix.OperatorCones.PPTDecomposition

@[expose] public section




/-!
# Lemma 3: a pair of PPT maps destroys entanglement with a qubit

* `isSeparable_refMap_of_ppt`: a PPT map sends every PPT operator with a qubit reference to a
  separable operator (Eq. (8) of the manuscript).
* `isSeparable_refMap_comp`: the composition of two PPT maps sends every positive operator with
  a qubit reference to a separable operator (Lemma 3, Eq. (7)).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p q : Type*}

/-- **Lemma 3, general form.** If `ρ ≥ 0` and `ρ^{Γ_R} ≥ 0` on `ℂ² ⊗ ℂ^n` and `Ψ` is a PPT map,
then `(id₂ ⊗ Ψ)(ρ)` is separable. -/
theorem isSeparable_refMap_of_ppt [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsPPTMap Ψ)
    {ρ : Matrix (Fin 2 × n) (Fin 2 × n) ℂ} (hρ : ρ.PosSemidef)
    (hρΓ : (partialTransposeRef ρ).PosSemidef) : IsSeparable (refMap (Fin 2) Ψ ρ) := by
  have hadj : block ρ 1 0 = (block ρ 0 1)ᴴ := by
    have h1 := hρ.isHermitian.eq
    rw [← qubitBlocks_block ρ, conjTranspose_qubitBlocks] at h1
    have h2 := congrArg (fun X => block X 1 0) h1
    simpa using h2.symm
  have hform : ρ = qubitBlocks (block ρ 0 0) (block ρ 0 1) (block ρ 0 1)ᴴ (block ρ 1 1) := by
    rw [← hadj, qubitBlocks_block]
  have h₁ : (Matrix.fromBlocks (block ρ 0 0) (block ρ 0 1) (block ρ 0 1)ᴴ
      (block ρ 1 1)).PosSemidef := by
    rw [← posSemidef_qubitBlocks_iff, ← hform]
    exact hρ
  have h₂ : (Matrix.fromBlocks (block ρ 0 0) (block ρ 0 1)ᴴ (block ρ 0 1)
      (block ρ 1 1)).PosSemidef := by
    rw [← posSemidef_qubitBlocks_iff, ← partialTransposeRef_qubitBlocks, ← hform]
    exact hρΓ
  obtain ⟨N, lam, u, v, R, hR, hC, hB, hA⟩ := exists_ppt_decomposition h₁ h₂
  rw [hform]
  exact isSeparable_refMap_of_decomposition
    (fun D Y hDY => isSeparable_qubitBlocks_of_posSemidef D Y hDY) hΨ lam u v hR hC hB hA

/-- **Lemma 3.** If `Φ` and `Ψ` are PPT maps, then `(id₂ ⊗ (Ψ ∘ Φ))(X)` is separable for every
positive operator `X` with a qubit reference. -/
theorem isSeparable_refMap_comp [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ} (hΦ : IsPPTMap Φ) (hΨ : IsPPTMap Ψ)
    {X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ} (hX : X.PosSemidef) :
    IsSeparable (refMap (Fin 2) (Ψ ∘ₗ Φ) X) := by
  rw [refMap_comp, LinearMap.comp_apply]
  exact isSeparable_refMap_of_ppt hΨ (hΦ.1 2 X hX) (hΦ.posSemidef_partialTransposeRef_refMap hX)

end Qatlib.Papers.PPTCompose26.Composition
