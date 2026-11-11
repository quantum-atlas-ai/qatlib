/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT

/-!
# Circuit realization of threshold integral amplification

An integrated threshold amplifier yields a phase word whose encoded matrix approximates `γ • A`
when the singular values of `A` lie in the inner approximation interval. The construction
includes the word length and compilation counts, using the singular value transformation
framework of [GilyenSuLowWiebe2019]

## Main statements

* `oddSingularTransform_linear`: identifies a linear singular value transform with matrix
  scaling.
* `integrated_threshold_query_consumer`: constructs the approximate scaled block encoding with
  explicit counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix Polynomial
open scoped Matrix.Norms.L2Operator

/-- Applying the odd singular value transform for `x ↦ γ * x` gives the scalar multiple `γ • A`. -/
theorem oddSingularTransform_linear {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (γ : ℝ) :
    oddSingularTransform A (fun x : ℝ => ((γ * x : ℝ) : ℂ)) = (γ : ℂ) • A := by
  conv_rhs => rw [← oddSingularTransform_id A]
  unfold oddSingularTransform
  have hdiag :
      diagonal (fun i : Fin (Fintype.card I) => ((γ * matrixSingularValues A i : ℝ) : ℂ)) =
      (γ : ℂ) • diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [smul_eq_mul, Complex.ofReal_mul]
    · simp [hij]
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]

/-- Under the stated parameter and norm bounds, there is a real phase word of length `D = 2 *
3^k + 1` that block encodes `γ • A` with error `ε / 2`. Its compiled counts are `(D, 2 *
3^k, 2 * 3^k + 2, D)`, and its length satisfies the explicit logarithmic tolerance bound. -/
theorem integrated_threshold_query_consumer
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (γ δ ε : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hA : ‖A‖ ≤ (1 - δ) / γ) :
    let k := integratedThresholdCutoff γ δ ε
    let D := 2 * 3 ^ k + 1
    ∃ Φ : List ℝ, Φ.length = D ∧
      BlockEncoding ((γ : ℂ) • A)
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) 1 (ε / 2) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (D, 2 * 3 ^ k, 2 * 3 ^ k + 2, D) ∧
      (Φ.length : ℝ) ≤
        1 + 2048 * γ ^ 8 / δ ^ 4 *
          (Real.log (1 / integratedThresholdTolerance γ δ ε)) ^ 2 := by
  let k := integratedThresholdCutoff γ δ ε
  let D := 2 * 3 ^ k + 1
  let p := integratedThresholdPolynomial γ δ k
  obtain ⟨hdegree, hbudget, hodd, hglobal, hinner⟩ :=
    integrated_threshold_amplifier γ δ ε hγ hδ hδ1 hε hε1
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDodd : D % 2 = 1 := by dsimp [D]; omega
  have hpar : HasRealParity D p := by
    unfold HasRealParity
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    simpa [D, pow_add, pow_mul] using hodd x
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 := by
    intro x hx
    exact (hglobal x hx).trans (by linarith)
  obtain ⟨Φ, hlen, hoddenc, _, hcounts⟩ :=
    source_length_cpp_real_singular_transform H I O A U L R p D henc hDpos
      (Polynomial.degree_le_of_natDegree_le hdegree) hpar hb
  have herr : ‖oddSingularTransform A (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      (γ : ℂ) • A‖ ≤ ε / 2 := by
    rw [← oddSingularTransform_linear A γ]
    apply oddSingularTransform_error_le_positive A _ _ (by positivity)
    intro i _
    have hx : |matrixSingularValues A i| ≤ (1 - δ) / γ := by
      rw [abs_of_nonneg (matrixSingularValues_nonneg A i)]
      exact (matrixSingularValues_le_spectralNorm A i).trans hA
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hinner _ hx
  have hblock := (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (hoddenc hDodd)).perturb
    (by positivity : 0 ≤ ε / 2)
    (show ‖(γ : ℂ) • A -
        oddSingularTransform A (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤ ε / 2 by
      rw [norm_sub_rev]
      exact herr)
  refine ⟨Φ, hlen, by simpa only [zero_add] using hblock, ?_, ?_⟩
  · have hdiv : D / 2 = 3 ^ k := by dsimp [D]; omega
    have hdiv' : (D + 1) / 2 = 3 ^ k + 1 := by dsimp [D]; omega
    simp only [hcounts, hdiv, hdiv', Nat.mul_add, Nat.mul_one]
    rfl
  · rw [hlen]
    simpa only [D, k, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] using hbudget

end Qatlib.Concepts.NonNormalSpec.ResolventWord
