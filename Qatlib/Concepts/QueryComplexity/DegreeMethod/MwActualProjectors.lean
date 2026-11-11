/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Verifier acceptance and clean-subspace projectors

The operators `pulledAccept` and `cleanProjector` represent verifier acceptance pulled back
through a unitary and the subspace embedded by a witness isometry. Their compression
`witnessAcceptOperator` relates alternating acceptance and clean-subspace returns to operations
on the original witness space.

The mathematical background is developed in [MarriottWatrous2005].

## Main statements

* `pulledAccept_probability`: identifies the pulled-back measurement mass with verifier
  acceptance.
* `witness_return`: relates a clean return to the compressed witness operator.
* `clean_no_of_verifier_promise`: transfers a witness soundness promise to all normalized clean
  states.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped BigOperators Classical
set_option linter.unusedSectionVars false

variable {H W : Type} [Fintype H] [DecidableEq H] [Fintype W] [DecidableEq W]

/-- The verifier acceptance matrix `Uᴴ * Projector S * U` pulled back to the input space. -/
noncomputable def pulledAccept (U : Matrix H H ℂ) (S : Finset H) : Matrix H H ℂ :=
  Uᴴ * Projector S * U

/-- The matrix `E * Eᴴ`, which projects onto the embedded witness space when `E` is an isometry. -/
noncomputable def cleanProjector (E : Matrix H W ℂ) : Matrix H H ℂ := E * Eᴴ

/-- Pulling a coordinate acceptance projector back through a unitary gives an orthogonal
projector. -/
theorem pulledAccept_projector (U : Matrix H H ℂ) (S : Finset H)
    (hU : U ∈ unitaryGroup H ℂ) : IsOrthogonalProjector (pulledAccept U S) := by
  have hu : U * Uᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using (mem_unitaryGroup_iff.mp hU)
  constructor
  · change (Uᴴ * Projector S * U) * (Uᴴ * Projector S * U) = _
    calc
      _ = Uᴴ * (Projector S * (U * Uᴴ) * Projector S) * U := by noncomm_ring
      _ = Uᴴ * Projector S * U := by rw [hu]; simp [projector_mul_self]
  · change (Uᴴ * Projector S * U)ᴴ = Uᴴ * Projector S * U
    simp only [conjTranspose_mul, conjTranspose_conjTranspose,
      projector_conjTranspose, mul_assoc]

/-- If `Eᴴ * E = 1`, then `E * Eᴴ` is an orthogonal projector. -/
theorem cleanProjector_projector (E : Matrix H W ℂ) (hE : Eᴴ * E = 1) :
    IsOrthogonalProjector (cleanProjector E) := by
  constructor
  · change (E * Eᴴ) * (E * Eᴴ) = _
    calc
      _ = E * (Eᴴ * E) * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = E * Eᴴ := by rw [hE, Matrix.mul_one]
  · change (E * Eᴴ)ᴴ = E * Eᴴ
    rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- The clean projector fixes every vector embedded by the isometry `E`. -/
theorem clean_embed (E : Matrix H W ℂ) (hE : Eᴴ * E = 1) (w : QState W) :
    cleanProjector E *ᵥ (E *ᵥ w) = E *ᵥ w := by
  rw [mulVec_mulVec, cleanProjector]
  have he : E * Eᴴ * E = E := by rw [Matrix.mul_assoc, hE, Matrix.mul_one]
  rw [he]

/-- Every output of `cleanProjector E` lies in the image of `E`. -/
theorem clean_output (E : Matrix H W ℂ) (ψ : QState H) :
    ∃ w : QState W, cleanProjector E *ᵥ ψ = E *ᵥ w := by
  exact ⟨Eᴴ *ᵥ ψ, (mulVec_mulVec ψ E Eᴴ).symm⟩

/-- Applying the pulled-back acceptance matrix equals applying `U`, restricting to `S`, and then
applying `Uᴴ`. -/
theorem pulledAccept_apply (U : Matrix H H ℂ) (S : Finset H) (ψ : QState H) :
    pulledAccept U S *ᵥ ψ = Uᴴ *ᵥ Collapse (U *ᵥ ψ) S := by
  simp only [pulledAccept, Collapse, ApplyGate, mulVec_mulVec, Matrix.mul_assoc]

/-- A unitary matrix preserves the total measurement mass of any state vector. -/
theorem unitary_mass (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ)
    (ψ : QState H) : MeasureProb (U *ᵥ ψ) Finset.univ = MeasureProb ψ Finset.univ := by
  have h := congrArg Complex.re (inner_applyGate hU ψ ψ)
  simpa only [inner_self, Complex.re_sum, Complex.ofReal_re,
    MeasureProb, BornProb] using! h

/-- For unitary `U`, the total mass after applying `pulledAccept U S` equals the measurement
mass of `U *ᵥ ψ` on `S`. -/
theorem pulledAccept_probability (U : Matrix H H ℂ) (S : Finset H)
    (hU : U ∈ unitaryGroup H ℂ) (ψ : QState H) :
    MeasureProb (pulledAccept U S *ᵥ ψ) Finset.univ = MeasureProb (U *ᵥ ψ) S := by
  rw [pulledAccept_apply]
  have hstar : Uᴴ ∈ unitaryGroup H ℂ := by
    simpa only [star_eq_conjTranspose] using Unitary.star_mem hU
  rw [unitary_mass Uᴴ hstar]
  exact sum_normSq_collapse _ _

/-- The acceptance matrix compressed to witness coordinates, `Eᴴ * pulledAccept U S * E`. -/
noncomputable def witnessAcceptOperator (U : Matrix H H ℂ) (S : Finset H)
    (E : Matrix H W ℂ) : Matrix W W ℂ := Eᴴ * pulledAccept U S * E

/-- Applying acceptance and then the clean matrix to an embedded witness equals embedding the
compressed witness-operator output. -/
theorem witness_return (U : Matrix H H ℂ) (S : Finset H)
    (E : Matrix H W ℂ) (w : QState W) :
    cleanProjector E *ᵥ (pulledAccept U S *ᵥ (E *ᵥ w)) =
      E *ᵥ (witnessAcceptOperator U S E *ᵥ w) := by
  simp only [cleanProjector, witnessAcceptOperator, mulVec_mulVec, Matrix.mul_assoc]

/-- An eigenvector of the compressed witness operator embeds into a vector with the same
eigenvalue for a clean return after acceptance. -/
theorem witness_eigen_bridge (U : Matrix H H ℂ) (S : Finset H)
    (E : Matrix H W ℂ) (w : QState W) (p : ℝ)
    (he : witnessAcceptOperator U S E *ᵥ w = (p : ℂ) • w) :
    cleanProjector E *ᵥ (pulledAccept U S *ᵥ (E *ᵥ w)) = (p : ℂ) • (E *ᵥ w) := by
  rw [witness_return, he, Matrix.mulVec_smul]

/-- The `k`th power of the clean-return matrix, followed by `E`, equals `E` followed by the
`k`th power of the compressed witness operator. -/
theorem repeated_clean_return (U : Matrix H H ℂ) (S : Finset H)
    (E : Matrix H W ℂ) (k : ℕ) :
    (cleanProjector E * pulledAccept U S) ^ k * E =
      E * witnessAcceptOperator U S E ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    have hstep : cleanProjector E * pulledAccept U S * E =
        E * witnessAcceptOperator U S E := by
      simp only [cleanProjector, witnessAcceptOperator, Matrix.mul_assoc]
    rw [hstep, Matrix.mul_assoc, ← pow_succ']

/-- Every normalized vector fixed by the clean projector of an isometry is the embedding of a
normalized witness. -/
theorem normalized_clean_original_coordinates {W : Type} [Fintype W] [DecidableEq W]
    (E : Matrix H W ℂ) (hE : Eᴴ * E = 1) (φ : QState H)
    (hφ : cleanProjector E *ᵥ φ = φ) (hnφ : Normalized φ) :
    ∃ w : QState W, Normalized w ∧ E *ᵥ w = φ := by
  let w : QState W := Eᴴ *ᵥ φ
  have hw : E *ᵥ w = φ := by
    change E *ᵥ (Eᴴ *ᵥ φ) = φ
    rw [Matrix.mulVec_mulVec]
    exact hφ
  refine ⟨w, (normalized_iff_inner_self _).mpr ?_, hw⟩
  calc
    Inner w w = Inner (E *ᵥ w) (E *ᵥ w) := by
      rw [inner_mulVec_left_rect E w (E *ᵥ w), Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
    _ = 1 := by rw [hw]; exact (normalized_iff_inner_self _).mp hnφ

/-- A uniform verifier acceptance bound on normalized witnesses also bounds the pulled-back
acceptance mass of every normalized clean state. -/
theorem clean_no_of_verifier_promise {W : Type} [Fintype W] [DecidableEq W]
    (U : Matrix H H ℂ) (S : Finset H) (E : Matrix H W ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hE : Eᴴ * E = 1)
    (b : ℝ) (hno : ∀ w : QState W, Normalized w →
      MeasureProb (U *ᵥ (E *ᵥ w)) S ≤ b) :
    ∀ φ : QState H, Normalized φ → cleanProjector E *ᵥ φ = φ →
      MeasureProb (pulledAccept U S *ᵥ φ) Finset.univ ≤ b := by
  intro φ hnφ hφ
  obtain ⟨w, hnw, hw⟩ := normalized_clean_original_coordinates E hE φ hφ hnφ
  rw [pulledAccept_probability U S hU, ← hw]
  exact hno w hnw

end Qatlib.Concepts.QueryComplexity.DegreeMethod
