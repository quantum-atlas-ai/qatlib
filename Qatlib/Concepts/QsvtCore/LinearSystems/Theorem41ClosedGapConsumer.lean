/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41OriginalPseudoinverseGily
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

theorem theorem41WindowedPolynomial_closedGapError
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (Pw : Polynomial ℝ) (ε δ : ℝ)
    (hA : ‖A‖ ≤ 1) (hε : 0 ≤ ε)
    (hgap : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i)
    (happrox : ∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) :
    ‖(oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ -
      (δ/2 : ℂ) • matrixPseudoinverse A‖ ≤ ε := by
  rw [show (δ/2 : ℂ) = ((δ/2 : ℝ) : ℂ) from by push_cast; rfl]
  rw [← inverseTransform_adjoint A (δ/2), ← Matrix.conjTranspose_sub,
    Matrix.l2_opNorm_conjTranspose]
  apply oddSingularTransform_error_le_positive A _ _ hε
  intro i hi
  have hx : matrixSingularValues A i ∈ Set.Icc δ 1 :=
    ⟨hgap i hi.ne', (matrixSingularValues_le_spectralNorm A i).trans hA⟩
  have he : ((Pw.eval (matrixSingularValues A i) : ℝ) : ℂ) -
      ((δ/2 : ℝ) : ℂ)/(matrixSingularValues A i : ℂ) =
      ((Pw.eval (matrixSingularValues A i) - (δ/2)/matrixSingularValues A i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact happrox _ hx

theorem theorem41OriginalPseudoinverse_closedGapConsumer
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδ : δ ≤ 1/2)
    (hgap : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i) :
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      (let C : Matrix I O ℂ :=
          (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
       let sectorR : Matrix I I ℂ :=
          1 - (rightThresholdProjection A 0 - rightThresholdProjection A δ)
       let sectorL : Matrix O O ℂ :=
          1 - (leftThresholdProjection A 0 - leftThresholdProjection A δ)
       ‖sectorR * C * sectorL - (δ/2 : ℂ) • (matrixPseudoinverse A * sectorL)‖ ≤ ε) ∧
      ‖(oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ -
        (δ/2 : ℂ) • matrixPseudoinverse A‖ ≤ ε ∧
      BlockEncoding ((δ/2 : ℂ) • matrixPseudoinverse A)
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
        (sourceAverageClean R) (sourceAverageClean L) 1 ε := by
  obtain ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox,
      hexact, hcounts, hsector⟩ :=
    theorem41OriginalPseudoinverse H I O A U L R ε δ henc hε hεδ hδ hgap
  have hA : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  have herr := theorem41WindowedPolynomial_closedGapError A Pw ε δ hA hε.le hgap happrox
  have hb := (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding.adjoint hexact)).perturb hε.le
    (show ‖(δ/2 : ℂ) • matrixPseudoinverse A -
      (oddSingularTransform A (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ‖ ≤ ε by
        rw [norm_sub_rev]
        exact herr)
  exact ⟨Pw, J, k, Φ, hlen, hbudget, h3k, hbound, heval0, happrox,
    hexact, hcounts, hsector, herr, by simpa only [zero_add] using! hb⟩

end Qatlib.Concepts.QsvtCore.LinearSystems
