/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.KernelBridge
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Equality of the input and amplified ground-space dimensions

The equivalence is the actual uniform-register embedding and its inverse
is the conjugate-transpose compression. It follows from the physical kernel
characterization, without a simple-eigenvalue assumption.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults

open Matrix
open AmplifiedRegister KernelBridge
open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The physical uniform-register embedding restricted to the input kernel. -/
def kernelLift (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hK : 0 < Fintype.card K)
    (delta : ℂ) (hd : delta ≠ 0) (hLd : (Fintype.card K : ℂ) + delta ≠ 0) :
    LinearMap.ker (∑ k, Proj k).mulVecLin →ₗ[ℂ]
      LinearMap.ker (doubledHamiltonian Proj delta).mulVecLin where
  toFun psi := ⟨uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) *ᵥ psi.val,
    (actual_kernel_iff Proj hproj hHerm hK delta hd hLd _).2
      ⟨psi.val, psi.property, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact Matrix.mulVec_add _ x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact Matrix.mulVec_smul _ c x.val

/-- The kernel embedding is an equivalence, with no discarded amplified
zero modes and no assumption of a unique input ground state. -/
def kernelEquiv (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hK : 0 < Fintype.card K)
    (delta : ℂ) (hd : delta ≠ 0) (hLd : (Fintype.card K : ℂ) + delta ≠ 0) :
    LinearMap.ker (∑ k, Proj k).mulVecLin ≃ₗ[ℂ]
      LinearMap.ker (doubledHamiltonian Proj delta).mulVecLin := by
  apply LinearEquiv.ofBijective (kernelLift Proj hproj hHerm hK delta hd hLd)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hraw := congrArg Subtype.val hxy
    let J := uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K))
    have h := congrArg (fun v => Jᴴ *ᵥ v) hraw
    change Jᴴ *ᵥ (J *ᵥ x.val) = Jᴴ *ᵥ (J *ᵥ y.val) at h
    simp only [Matrix.mulVec_mulVec, show Jᴴ * J = 1 from lazyEmbed_isometry hK,
      Matrix.one_mulVec] at h
    exact h
  · intro y
    obtain ⟨psi, hpsi, hJpsi⟩ :=
      (actual_kernel_iff Proj hproj hHerm hK delta hd hLd y.val).1 y.property
    refine ⟨⟨psi, hpsi⟩, ?_⟩
    exact Subtype.ext hJpsi

/-- The amplified and input null spaces have equal dimension, as in the
last clause of source Theorem 1. -/
theorem doubled_kernel_finrank_eq (Proj : K → Matrix I I ℂ)
    (hproj : ∀ k, Proj k * Proj k = Proj k)
    (hHerm : ∀ k, (Proj k).IsHermitian) (hK : 0 < Fintype.card K)
    (delta : ℂ) (hd : delta ≠ 0) (hLd : (Fintype.card K : ℂ) + delta ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (doubledHamiltonian Proj delta).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker (∑ k, Proj k).mulVecLin) :=
  (kernelEquiv Proj hproj hHerm hK delta hd hLd).finrank_eq.symm

end

end Qatlib.Papers.SpectralGap11.MainResults
