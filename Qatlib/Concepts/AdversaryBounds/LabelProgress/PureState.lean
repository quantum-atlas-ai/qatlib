/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {I A G : Type*} [Fintype I] [Fintype A]

def reducedInput (C : Matrix I A ℂ) : Matrix I I ℂ := C*Cᴴ
omit [Fintype I] in

theorem reducedInput_entry (C : Matrix I A ℂ) (i j : I) :
    reducedInput C i j=∑ a, C i a*star (C j a) := rfl

theorem reducedInput_psd (C : Matrix I A ℂ) : (reducedInput C).PosSemidef :=
  posSemidef_self_mul_conjTranspose C

theorem reducedInput_rank (C : Matrix I A ℂ) : (reducedInput C).rank ≤ Fintype.card A :=
  (rank_mul_le_left C Cᴴ).trans C.rank_le_card_width

def support (C : Matrix I A ℂ) : Submodule ℂ (I → ℂ) := (reducedInput C).mulVecLin.range

theorem support_finrank (C : Matrix I A ℂ) : finrank ℂ (support C) ≤ Fintype.card A :=
  reducedInput_rank C

def orbitSpan (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (v : I → ℂ) : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ (Set.range (fun g => π g v))

theorem orbitSpan_le_support (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (v : I → ℂ) (hv : v ∈ support C) : orbitSpan π v ≤ support C := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  obtain ⟨x,hx⟩ := hv
  refine ⟨π g x,?_⟩
  have he := congrArg (fun f : (I → ℂ) →ₗ[ℂ] (I → ℂ) => f x) (hinv g)
  simpa only [LinearMap.comp_apply,hx] using! he

theorem actual_orbit_finrank (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (v : I → ℂ) (hv : v ∈ support C) : finrank ℂ (orbitSpan π v) ≤ Fintype.card A :=
  (Submodule.finrank_mono (orbitSpan_le_support C π hinv v hv)).trans (support_finrank C)

theorem actual_qubit_orbit (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (S : ℕ) (hspace : Fintype.card A ≤ 2^S) (v : I → ℂ) (hv : v ∈ support C) :
    finrank ℂ (orbitSpan π v) ≤ 2^S := (actual_orbit_finrank C π hinv v hv).trans hspace
omit [Fintype I] in

theorem reducedInput_unitary (C : Matrix I A ℂ) (U : Matrix A A ℂ)
    (hU : U*Uᴴ=1) : reducedInput (C*U)=reducedInput C := by
  simp only [reducedInput,conjTranspose_mul]
  calc
    (C*U)*(Uᴴ*Cᴴ)=(C*(U*Uᴴ))*Cᴴ := by simp only [Matrix.mul_assoc]
    _ = C*Cᴴ := by rw [hU,Matrix.mul_one]
end Qatlib.Concepts.AdversaryBounds.LabelProgress
