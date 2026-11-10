/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.CanonicalCompilation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.KrausCompile.SignedChoi
open Qatlib.Concepts.KrausCompile.BornMoments
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction

theorem cp_preserves_hermitian {d : ℕ} (T : Op d →ₗ[ℂ] Op d) (hCP : CompletelyPositive T)
    (X : Op d) (hX : X.IsHermitian) : (T X).IsHermitian := by
  obtain ⟨n, K, hK, _⟩ := (clause2_conj2 T).mp hCP
  rw [hK X]
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

theorem cp_output_psd {d : ℕ} (T : Op d →ₗ[ℂ] Op d) (hCP : CompletelyPositive T)
    (X : Op d) (hX : X.PosSemidef) : (T X).PosSemidef := by
  obtain ⟨n, K, hK, _⟩ := (clause2_conj2 T).mp hCP
  rw [hK X]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same (K i))

theorem inverse_preserves_hermitian {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (E X).IsHermitian)
    (X : Op d) (hX : X.IsHermitian) : (E.symm X).IsHermitian := by
  change (E.symm X).conjTranspose = E.symm X
  apply E.injective
  change E.toLinearMap ((E.symm X).conjTranspose) = E.toLinearMap (E.symm X)
  rw [hp_preserves_adjoint E.toLinearMap hHP]
  simpa only [LinearEquiv.coe_coe, E.apply_symm_apply] using hX.eq

theorem inverse_trace_preserving {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hTP : TracePreserving E.toLinearMap) : TracePreserving E.symm.toLinearMap := by
  intro X
  have h := hTP (E.symm X)
  simpa only [LinearEquiv.coe_coe, E.apply_symm_apply] using h.symm

def inverseNoiseFamily {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hCP : CompletelyPositive E.toLinearMap) (hTP : TracePreserving E.toLinearMap) :
    SignedKraus d (ChoiMatrix E.symm.toLinearMap).rank :=
  canonicalSignedKraus E.symm.toLinearMap
    (inverse_preserves_hermitian E (cp_preserves_hermitian E.toLinearMap hCP))
    (inverse_trace_preserving E hTP)

theorem inverseNoiseFamily_action {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hCP : CompletelyPositive E.toLinearMap) (hTP : TracePreserving E.toLinearMap) (X : Op d) :
    (inverseNoiseFamily E hCP hTP).action (E X) = X := by
  rw [inverseNoiseFamily, canonicalSignedKraus_action]
  exact E.symm_apply_apply X

theorem inverse_noise_estimator {d : ℕ} (hd : 0 < d) (E : Op d ≃ₗ[ℂ] Op d)
    (hCP : CompletelyPositive E.toLinearMap) (hTP : TracePreserving E.toLinearMap)
    (ρ : Op d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (V : Op d) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) :
    let D := inverseNoiseFamily E hCP hTP
    (D.shotLaw hd (E ρ) V (cp_output_psd E.toLinearMap hCP ρ hρ)
      (by simpa only [LinearEquiv.coe_coe, htρ] using hTP ρ) hV).expect
      (readout D.shotWeight eig) = (ρ * observable V eig).trace.re := by
  (try dsimp only)
  rw [SignedKraus.actual_shot_mean, SignedKraus.compiledMean, inverseNoiseFamily_action]

end Qatlib.Papers.HermitianMap26.Construction
