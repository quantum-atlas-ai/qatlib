/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.CanonicalCompilation

/-!
# Unbiased estimation through inverse noise

This module applies the signed Kraus construction to the inverse of an invertible completely
positive, trace-preserving noise map, as in [CaiEtAl2026]. It proves that Hermitian preservation
and trace preservation pass to the inverse, then defines `inverseNoiseFamily` by canonical
signed Kraus decomposition.

The inverse family recovers the input operator from its noisy image. For a density matrix, the
corresponding weighted spectral readout on the noisy state has the expectation of the original
observable on the original state.

## Main statements

* `inverseNoiseFamily_action`: identifies the inverse family's action on a noisy operator.
* `inverse_noise_estimator`: proves the unbiased readout identity for noise cancellation.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

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

/-- A completely positive linear map sends Hermitian matrices to Hermitian matrices. -/
theorem cp_preserves_hermitian {d : ℕ} (T : Op d →ₗ[ℂ] Op d) (hCP : CompletelyPositive T)
    (X : Op d) (hX : X.IsHermitian) : (T X).IsHermitian := by
  obtain ⟨n, K, hK, _⟩ := (clause2_conj2 T).mp hCP
  rw [hK X]
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

/-- A completely positive linear map sends positive semidefinite matrices to positive
semidefinite matrices. -/
theorem cp_output_psd {d : ℕ} (T : Op d →ₗ[ℂ] Op d) (hCP : CompletelyPositive T)
    (X : Op d) (hX : X.PosSemidef) : (T X).PosSemidef := by
  obtain ⟨n, K, hK, _⟩ := (clause2_conj2 T).mp hCP
  rw [hK X]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same (K i))

/-- The inverse of a complex linear equivalence that preserves Hermitian matrices also preserves
Hermitian matrices. -/
theorem inverse_preserves_hermitian {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hHP : ∀ X : Op d, X.IsHermitian → (E X).IsHermitian)
    (X : Op d) (hX : X.IsHermitian) : (E.symm X).IsHermitian := by
  change (E.symm X).conjTranspose = E.symm X
  apply E.injective
  change E.toLinearMap ((E.symm X).conjTranspose) = E.toLinearMap (E.symm X)
  rw [hp_preserves_adjoint E.toLinearMap hHP]
  simpa only [LinearEquiv.coe_coe, E.apply_symm_apply] using hX.eq

/-- The inverse of a trace-preserving complex linear equivalence is trace preserving. -/
theorem inverse_trace_preserving {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hTP : TracePreserving E.toLinearMap) : TracePreserving E.symm.toLinearMap := by
  intro X
  have h := hTP (E.symm X)
  simpa only [LinearEquiv.coe_coe, E.apply_symm_apply] using h.symm

/-- The canonical signed Kraus family for the inverse of an invertible completely positive,
trace-preserving noise map. -/
def inverseNoiseFamily {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hCP : CompletelyPositive E.toLinearMap) (hTP : TracePreserving E.toLinearMap) :
    SignedKraus d (ChoiMatrix E.symm.toLinearMap).rank :=
  canonicalSignedKraus E.symm.toLinearMap
    (inverse_preserves_hermitian E (cp_preserves_hermitian E.toLinearMap hCP))
    (inverse_trace_preserving E hTP)

/-- The signed Kraus action of the inverse-noise family recovers `X` from `E X`. -/
theorem inverseNoiseFamily_action {d : ℕ} (E : Op d ≃ₗ[ℂ] Op d)
    (hCP : CompletelyPositive E.toLinearMap) (hTP : TracePreserving E.toLinearMap) (X : Op d) :
    (inverseNoiseFamily E hCP hTP).action (E X) = X := by
  rw [inverseNoiseFamily, canonicalSignedKraus_action]
  exact E.symm_apply_apply X

/-- On the noisy density matrix `E ρ`, the inverse-noise compilation's weighted spectral readout
has expectation equal to the original state's real expectation of `observable V eig`.
[CaiEtAl2026]. -/
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
