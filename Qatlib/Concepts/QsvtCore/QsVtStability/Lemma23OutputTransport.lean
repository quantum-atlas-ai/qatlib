/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt
open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem interior_complex_output_of_operator_error {I O : Type}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (base : ℂ) (zs : List ℂ) (ψ : I → ℂ) (η : ℝ)
    (herr : ‖oddSingularTransform A (interiorResponse base zs) -
      oddSingularTransform B (interiorResponse base zs)‖ ≤ η)
    (hψ : ‖toEuclidean_fromVec ψ‖ = 1) :
    let v := toEuclidean_fromVec ((oddSingularTransform A (interiorResponse base zs)).mulVec ψ)
    let y := toEuclidean_fromVec ((oddSingularTransform B (interiorResponse base zs)).mulVec ψ)
    η < ‖v‖ → (‖v‖ - η) ^ 2 ≤ ‖y‖ ^ 2 ∧
      ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ≤ 2 * η / ‖v‖ := by
  (try dsimp only)
  intro hgap
  have hvec : ‖toEuclidean_fromVec
      ((oddSingularTransform B (interiorResponse base zs)).mulVec ψ) -
      toEuclidean_fromVec ((oddSingularTransform A (interiorResponse base zs)).mulVec ψ)‖ ≤ η := by
    have h := Matrix.l2_opNorm_mulVec
      (oddSingularTransform B (interiorResponse base zs) -
        oddSingularTransform A (interiorResponse base zs)) (toEuclidean_fromVec ψ)
    rw [hψ, mul_one, norm_sub_rev] at h
    have h' := h.trans herr
    change ‖toEuclidean_fromVec
      ((oddSingularTransform B (interiorResponse base zs) -
        oddSingularTransform A (interiorResponse base zs)).mulVec ψ)‖ ≤ η at h'
    rw [Matrix.sub_mulVec] at h'
    exact h'
  have hdir := normalize_error_of_gap hvec hgap
  refine ⟨?_, hdir.2⟩
  have hnorm := (norm_sub_norm_le
    (toEuclidean_fromVec ((oddSingularTransform A (interiorResponse base zs)).mulVec ψ))
    (toEuclidean_fromVec ((oddSingularTransform B (interiorResponse base zs)).mulVec ψ))).trans
      (by simpa only [norm_sub_rev] using hvec)
  apply (sq_le_sq₀ (by linarith) (norm_nonneg _)).mpr
  linarith

theorem interior_complex_response_actual_conditional_consumer :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (base : ℂ) (zs : List ℂ) (ψ : I → ℂ),
      IsPhase base → (∀ z ∈ zs, IsPhase z) → ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
      ‖(2 : ℂ)⁻¹ • (A + B)‖ < 1 →
      ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
      zs.length % 2 = 1 → ‖toEuclidean_fromVec ψ‖ = 1 →
      let v := toEuclidean_fromVec ((oddSingularTransform A (interiorResponse base zs)).mulVec ψ)
      let y := toEuclidean_fromVec ((oddSingularTransform B (interiorResponse base zs)).mulVec ψ)
      let η := interiorRate A B zs.length
      η < ‖v‖ → (‖v‖ - η) ^ 2 ≤ ‖y‖ ^ 2 ∧
        ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ≤ 2 * η / ‖v‖ := by
  intro I O _ _ _ _ A B base zs ψ hb hz hnA hnB hm hg hodd hψ
  have herr := (interior_complex_singular_response_stability I O A B base zs
    hb hz hnA hnB hm hg).1 hodd
  exact interior_complex_output_of_operator_error A B base zs ψ _ herr hψ

end Qatlib.Concepts.QsvtCore.QsVtStability
