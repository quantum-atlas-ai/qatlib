/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!
# Local unitary invariance of Schmidt data

The Schmidt spectrum and Schmidt entropy of a normalized bipartite pure state are invariant
under a unitary on either register, or under a tensor product of local unitaries. This develops
part of the framework of [Nielsen1999].

## Main statements

* `schmidtSpectrum_apply_localUnitary`: preserves the Schmidt spectrum under local unitaries.
* `schmidtEntropy_apply_localUnitary`: preserves the Schmidt entropy under local unitaries.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Unitary

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Foundations.PureStateMath.BornBridge

variable {D E : ℕ}

/-- Equal normalized bipartite states have equal Schmidt spectra, independently of the
normalization proofs. -/
theorem schmidtSpectrum_congr {X Y : QState (Fin D × Fin E)}
    (hXY : X = Y) (hX : Normalized X) (hY : Normalized Y) :
    schmidtSpectrum X hX = schmidtSpectrum Y hY := by
  subst hXY
  exact congrArg (fun h => schmidtSpectrum _ h) (Subsingleton.elim hX hY)

/-- Applying a unitary to the left register preserves the Schmidt spectrum of a normalized
bipartite state. See [Nielsen1999]. -/
theorem schmidtSpectrum_apply_tensorLeft (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix (Fin D) (Fin D) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hψ' : Normalized (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ)) :
    schmidtSpectrum (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ) hψ'
      = schmidtSpectrum ψ hψ := by
  unfold schmidtSpectrum
  have hmatM : (state (reducedDensity
        (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ) hψ')).M.mat
      = (HermitianMat.conj (⟨U, hU⟩ : Matrix.unitaryGroup (Fin D) ℂ).val
          ((state (reducedDensity ψ hψ)).M)).mat := by
    show (state (reducedDensity
        (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ) hψ')).m
      = (HermitianMat.conj (⟨U, hU⟩ : Matrix.unitaryGroup (Fin D) ℂ).val
          ((state (reducedDensity ψ hψ)).M)).mat
    rw [state_m, reducedDensity_val, HermitianMat.conj_apply_mat]
    have hU' : (⟨U, hU⟩ : Matrix.unitaryGroup (Fin D) ℂ).val = U := rfl
    rw [hU']
    exact partialTrace_outerProduct_apply_tensorLeft D E U ψ
  exact (hermitian_eigenvalues_congr _ _ hmatM).trans (HermitianMat.eigenvalues_conj _ _)

/-- Applying a tensor product of local unitaries preserves the Schmidt spectrum of a normalized
bipartite state. See [Nielsen1999]. -/
theorem schmidtSpectrum_apply_localUnitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix (Fin D) (Fin D) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (V : Matrix (Fin E) (Fin E) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (hψ' : Normalized
      (ApplyGate (TensorGate U V) ψ)) :
    schmidtSpectrum (ApplyGate (TensorGate U V) ψ) hψ' = schmidtSpectrum ψ hψ := by
  have hkey : TensorGate U V
      = TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ) * TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V := by
    rw [tensorGate_mul]
    simp
  set ψV := ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ with hψVdef
  have hnorm : Normalized ψV := by
    rw [hψVdef]
    exact normalized_applyGate (tensorGate_unitary (U := (1 : Matrix (Fin D) (Fin D) ℂ))
      (V := V) (by simp) hV) hψ
  have hsplit : ApplyGate (TensorGate U V) ψ
      = ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψV := by
    rw [hψVdef, hkey]
    simp only [ApplyGate]
    rw [Matrix.mulVec_mulVec]
  have hψV' : Normalized
      (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψV) := hsplit ▸ hψ'
  calc schmidtSpectrum (ApplyGate (TensorGate U V) ψ) hψ'
      = schmidtSpectrum (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψV) hψV' :=
        schmidtSpectrum_congr hsplit hψ' hψV'
    _ = schmidtSpectrum ψV hnorm :=
        schmidtSpectrum_apply_tensorLeft ψV hnorm U hU hψV'
    _ = schmidtSpectrum ψ hψ :=
        schmidtSpectrum_apply_tensorRight ψ hψ V hV hnorm

/-- Applying a unitary to the left register preserves the Schmidt entropy of a normalized
bipartite state. -/
theorem schmidtEntropy_apply_tensorLeft (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix (Fin D) (Fin D) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hψ' : Normalized (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ)) :
    schmidtEntropy (ApplyGate (TensorGate U (1 : Matrix (Fin E) (Fin E) ℂ)) ψ) hψ'
      = schmidtEntropy ψ hψ := by
  unfold schmidtEntropy
  rw [schmidtSpectrum_apply_tensorLeft ψ hψ U hU hψ']

/-- Applying a tensor product of local unitaries preserves the Schmidt entropy of a normalized
bipartite state. See [Nielsen1999]. -/
theorem schmidtEntropy_apply_localUnitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix (Fin D) (Fin D) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (V : Matrix (Fin E) (Fin E) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (hψ' : Normalized (ApplyGate (TensorGate U V) ψ)) :
    schmidtEntropy (ApplyGate (TensorGate U V) ψ) hψ' = schmidtEntropy ψ hψ := by
  unfold schmidtEntropy
  rw [schmidtSpectrum_apply_localUnitary ψ hψ U hU V hV hψ']

end Qatlib.Papers.EntangleTrans99.MainResults.Unitary
