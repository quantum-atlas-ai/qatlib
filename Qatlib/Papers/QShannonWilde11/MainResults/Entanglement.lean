/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QShannonWilde11.MainResults.EntanglementDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.QShannonWilde11.MainResults

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem clause17_witness_certifies :
    (star (Ket (0 : Fin 2 × Fin 2) + Ket (1, 1)) ⬝ᵥ
      (PartialTranspose (outerProduct (bell (true, true))) *ᵥ
        (Ket (0 : Fin 2 × Fin 2) + Ket (1, 1))) = (-1 : ℂ)) ∧
    ¬ IsSeparableState (outerProduct (bell (true, true))) :=
  ⟨singlet_partialTranspose_form, bell_singlet_not_isSeparableState⟩

theorem clause17_product_criterion (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    IsSeparableState (outerProduct ψ) ↔ IsProductState ψ :=
  isSeparableState_outerProduct_iff_isProductState ψ hψ

theorem clause17_ppt_necessary (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hρ : IsSeparableState ρ) : (PartialTranspose ρ).PosSemidef :=
  partialTranspose_posSemidef_of_isSeparableState ρ hρ

theorem clause17_entropy_values (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    0 ≤ entropy ψ hψ ∧ entropy ψ hψ ≤ Real.log D ∧ entropy ψ hψ ≤ Real.log E := by
  refine And.intro ?_ (And.intro (entropy_le_log_left ψ hψ) (entropy_le_log_right ψ hψ))
  exact entropy_nonneg ψ hψ

theorem clause17_entropy_bell (s : Bool × Bool) :
    entropy (bell s) (bell_normalized s) = Real.log 2 :=
  entropy_bell s

theorem clause4_endpoint :
    (¬ IsSeparableState (outerProduct (bell (true, true))) ∧
    (∀ (D E : ℕ) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
      IsSeparableState (outerProduct ψ) ↔ IsProductState ψ) ∧
    (∀ (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : IsSeparableState ρ),
      (PartialTranspose ρ).PosSemidef)) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact bell_singlet_not_isSeparableState
  · exact clause17_product_criterion
  · intro D E ρ hρ
    exact clause17_ppt_necessary D E ρ hρ

end Qatlib.Papers.QShannonWilde11.MainResults
