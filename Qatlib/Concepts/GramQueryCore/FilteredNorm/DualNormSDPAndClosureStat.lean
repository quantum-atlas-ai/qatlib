/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Dual filtered norm SDP specification

The proposition `DualNormSDPAndClosure` collects the minimum and maximum SDP descriptions of the
rectangular dual filtered norm, including attainment, together with filter extension, Hadamard
transport, and tensor product laws. It states the dual norm properties used in the filtered γ₂
framework of [LeeEtAl2011].

## Main statements

* `DualNormSDPAndClosure`: The conjunction of attained minimum and maximum SDP
  characterizations, filter extension laws, Hadamard transport and bounds, and tensor
  multiplicativity for the dual filtered norm.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The conjunction of attained minimum and maximum SDP characterizations, filter extension
laws, Hadamard transport and bounds, and tensor multiplicativity for the dual filtered norm. -/
def DualNormSDPAndClosure : Prop :=
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      ∃ Ω : Matrix (R ⊕ S) (R ⊕ S) ℂ,
        Ω.PosSemidef ∧ (∀ r s, r ≠ s → Ω r s=0) ∧
        (∀ j, (Ω-sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) ∧
        sourceDualNorm A Z=ENNReal.ofReal ((Matrix.trace Ω).re/2) ∧
        (∀ Ω' : Matrix (R ⊕ S) (R ⊕ S) ℂ,
          Ω'.PosSemidef → (∀ r s, r ≠ s → Ω' r s=0) →
          (∀ j, (Ω'-sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) →
          (Matrix.trace Ω).re ≤ (Matrix.trace Ω').re)) ∧
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ), 0<n →
      ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
        (∀ j, (Y j).PosSemidef) ∧ (∀ i, ∑ j, Y j i i=1) ∧
        sourceDualNorm A Z=ENNReal.ofReal
          ((∑ j, (Matrix.trace ((Y j)ᴴ *
            sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re)/2) ∧
        (∀ Y' : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
          (∀ j, (Y' j).PosSemidef) → (∀ i, ∑ j, Y' j i i=1) →
          (∑ j, (Matrix.trace ((Y' j)ᴴ *
            sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re) ≤
          (∑ j, (Matrix.trace ((Y j)ᴴ *
            sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re))) ∧
  (∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n m : ℕ) (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ)
      (Z : Fin n → Matrix R S ℂ) (p : Fin n → ℂ) (B : Matrix R S ℂ),
      sourceDualNorm A Z ≤ sourceDualNorm A (sourceFilterUnion Y Z) ∧
      ((∑ j, ‖p j‖) ≤ 1 → sourceDualNorm A
        (sourceFilterUnion Z (fun _ : Fin 1 => ∑ j, p j • Z j))=sourceDualNorm A Z) ∧
      sourceDualNorm (A ⊙ B) Z=sourceDualNorm A (fun j => Z j ⊙ sourceConjugate B) ∧
      sourceDualNorm (A ⊙ B) Z ≤ sourceDualNorm A Z*sourceUnfiltered B) ∧
  (∀ (R S U V : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] (n m : ℕ)
      (A : Matrix R S ℂ) (B : Matrix U V ℂ)
      (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ),
      sourceDualNorm (sourceTensor A B) (sourceFilterTensor Y Z)=
        sourceDualNorm A Y*sourceDualNorm B Z)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
