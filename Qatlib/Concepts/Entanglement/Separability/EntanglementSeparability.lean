/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import QuantumInfo.Channels.Unbundled
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.Entanglement.Separability
open Matrix
open scoped MatrixMap ComplexOrder

theorem isSeparableState_localCPTP {D E D' E' : ℕ}
    (Φ : MatrixMap (Fin D) (Fin D') ℂ) (Ψ : MatrixMap (Fin E) (Fin E') ℂ)
    (hΦcp : Φ.IsCompletelyPositive) (hΦtp : Φ.IsTracePreserving)
    (hΨcp : Ψ.IsCompletelyPositive) (hΨtp : Ψ.IsTracePreserving)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : IsSeparableState ρ) :
    IsSeparableState ((Φ ⊗ₖₘ Ψ) ρ) := by
  obtain ⟨n, p, σ, τ, hp, hsum, hσ, hτ, he⟩ :=
    (isSeparableState_iff_isSeparableMixed ρ).mp hρ
  apply (isSeparableState_iff_isSeparableMixed _).mpr
  refine ⟨n, p, fun i => Φ (σ i), fun i => Ψ (τ i), hp, hsum, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hΦcp.IsPositive (hσ i).1, (hΦtp (σ i)).trans (hσ i).2⟩
  · intro i
    exact ⟨hΨcp.IsPositive (hτ i).1, (hΨtp (τ i)).trans (hτ i).2⟩
  · rw [he, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    exact MatrixMap.kron_map_of_kron_state Φ Ψ (σ i) (τ i)

theorem g2 :
    (∀ (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ),
      IsSeparableState ρ ↔ IsSeparableMixed ρ) ∧
    (∀ (D E D' E' : ℕ)
      (Φ : MatrixMap (Fin D) (Fin D') ℂ) (Ψ : MatrixMap (Fin E) (Fin E') ℂ),
      Φ.IsCompletelyPositive → Φ.IsTracePreserving →
      Ψ.IsCompletelyPositive → Ψ.IsTracePreserving →
      ∀ ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ,
        IsSeparableState ρ → IsSeparableState ((Φ ⊗ₖₘ Ψ) ρ)) ∧
    (∀ (D E : ℕ) (ψ : QState (Fin D × Fin E)), Normalized ψ →
      (IsSeparableState (outerProduct ψ) ↔ IsProductState ψ)) ∧
    (∀ (D E : ℕ) (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ),
      IsSeparableState ρ → (PartialTranspose ρ).PosSemidef) ∧
    (star (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2 × Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1, 1)) ⬝ᵥ
      (PartialTranspose (outerProduct (bell (true, true))) *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2 × Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1, 1))) = (-1 : ℂ)) ∧
    ¬ IsSeparableState (outerProduct (bell (true, true))) :=
  ⟨fun _ _ => isSeparableState_iff_isSeparableMixed,
   fun _ _ _ _ => isSeparableState_localCPTP,
   fun _ _ ψ hψ => isSeparableState_outerProduct_iff_isProductState ψ hψ,
   fun _ _ => partialTranspose_posSemidef_of_isSeparableState,
   singlet_partialTranspose_form, bell_singlet_not_isSeparableState⟩

end Qatlib.Concepts.Entanglement.Separability
