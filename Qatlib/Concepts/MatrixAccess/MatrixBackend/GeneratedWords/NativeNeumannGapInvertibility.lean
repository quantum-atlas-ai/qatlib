/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannStability
import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SpectralSketch.NearIsometry
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

/-! Two-sided inverses from a gapped shift and an operator-norm perturbation. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The actual perturbed matrix retains at least half of the ideal gap. -/
theorem perturbed_singular_gap (X S : Matrix I I ℂ) (a δ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i)
    (hδ : ‖X-S‖ ≤ δ) (hsmall : δ ≤ a^2/4) :
    ∀ i : Fin (Fintype.card I), a/2 ≤ matrixSingularValues X i := by
  intro i
  have hweyl := singular_sub_le_norm S X i
  rw [norm_sub_rev] at hweyl
  have ha2 : a^2 ≤ a := by nlinarith
  have hi := hgap i
  linarith

/-- The same pseudoinverses are actual two-sided inverses, with norm bounds
needed by the Neumann stability argument.  Empty dimension is included. -/
theorem perturbed_gap_two_sided_inverses (X S : Matrix I I ℂ) (a δ : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), a ≤ matrixSingularValues S i)
    (hδ : ‖X-S‖ ≤ δ) (hsmall : δ ≤ a^2/4) :
    matrixPseudoinverse S * S = 1 ∧ S * matrixPseudoinverse S = 1 ∧
    ‖matrixPseudoinverse S‖ ≤ a⁻¹ ∧
    matrixPseudoinverse X * X = 1 ∧ X * matrixPseudoinverse X = 1 ∧
    ‖matrixPseudoinverse X‖ ≤ 2*a⁻¹ := by
  have hxgap := perturbed_singular_gap X S a δ ha ha1 hgap hδ hsmall
  have hspos : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues S i :=
    fun i => ha.trans_le (hgap i)
  have hxpos : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues X i :=
    fun i => (by linarith : 0 < a/2).trans_le (hxgap i)
  have hsleft : matrixPseudoinverse S * S = 1 := (nearColumnPolar_full_support S hspos).2.2
  have hxleft : matrixPseudoinverse X * X = 1 := (nearColumnPolar_full_support X hxpos).2.2
  have hsnorm : ‖matrixPseudoinverse S‖ ≤ a⁻¹ :=
    matrixPseudoinverse_norm_le ha (fun i _ => hgap i)
  have hxnorm : ‖matrixPseudoinverse X‖ ≤ (a/2)⁻¹ :=
    matrixPseudoinverse_norm_le (by linarith : 0 < a/2) (fun i _ => hxgap i)
  have hinv : (a/2)⁻¹ = 2*a⁻¹ := by field_simp
  refine ⟨hsleft, mul_eq_one_comm.mp hsleft, hsnorm,
    hxleft, mul_eq_one_comm.mp hxleft, ?_⟩
  simpa only [hinv] using hxnorm

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
