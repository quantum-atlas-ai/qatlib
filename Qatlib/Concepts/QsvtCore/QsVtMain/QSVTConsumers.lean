/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Postselection examples for compiled QSVT

This module applies the length-controlled compiler to two concrete postselection problems in the
QSVT framework of [GilyenSuLowWiebe2019]. The first treats an unknown positive encoded scalar
with an iterated sign polynomial; the second uses an even polynomial on a two-dimensional matrix
with a nontrivial kernel.

## Main statements

* `cpp_unknown_scalar_fixed_point_postselection`: Obtain a success lower bound and the exact
  conditional unit state in the scalar case.
* `cpp_even_full_kernel_consumer`: Compute the compressed matrix, success probability, and
  conditional output for a length-two example.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The two-dimensional diagonal matrix with entries zero and one half. -/
noncomputable def sourceKernelMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i => if i=0 then 0 else 1/2)
/-- The two-dimensional uniform input state with amplitudes `1 / √2`. -/
noncomputable def sourceKernelInput : QState (Fin 2) := fun _=>(Real.sqrt 2:ℂ)⁻¹
/-- The two-dimensional output state with amplitudes `4 / 5` and `3 / 5`. -/
noncomputable def sourceKernelOutput : QState (Fin 2) := fun i=>if i=0 then 4/5 else 3/5

/-- The Euclidean linear map of a scalar identity matrix acts by scalar multiplication. -/
private theorem source_scalar_action {I : Type} [Fintype I] [DecidableEq I]
    (σ : ℝ) (v : EuclideanSpace ℂ I) :
    ((σ : ℂ) • (1 : Matrix I I ℂ)).toEuclideanLin v = (σ : ℂ) • v := by
  ext i
  change (((σ : ℂ) • (1 : Matrix I I ℂ)) *ᵥ (fun j => v j)) i = (σ : ℂ) * v i
  simp [Matrix.smul_mulVec]

/-- Every singular value of a nonnegative scalar identity matrix equals that scalar. -/
private theorem source_scalar_singularValues {I : Type} [Fintype I] [DecidableEq I]
    (σ : ℝ) (hσ : 0 ≤ σ) (i : Fin (Fintype.card I)) :
    matrixSingularValues ((σ : ℂ) • (1 : Matrix I I ℂ)) i = σ := by
  rw [← norm_apply_rightSingularBasis,source_scalar_action,norm_smul,
    (rightSingularBasis ((σ : ℂ) • (1 : Matrix I I ℂ))).norm_eq_one i,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ]

/-- The odd singular transform of a positive scalar identity is the identity scaled by the
response at that scalar. -/
theorem source_scalar_odd_transform {I : Type} [Fintype I] [DecidableEq I]
    (σ : ℝ) (hσ : 0 < σ) (f : ℝ → ℂ) :
    oddSingularTransform ((σ : ℂ) • (1 : Matrix I I ℂ)) f =
      f σ • (1 : Matrix I I ℂ) := by
  have hc : leftSingularColumns ((σ : ℂ) • (1 : Matrix I I ℂ)) =
      basisColumns (rightSingularBasis ((σ : ℂ) • (1 : Matrix I I ℂ))) := by
    ext j i
    simp only [leftSingularColumns,leftSingularVector,source_scalar_singularValues σ hσ.le,
      source_scalar_action,smul_smul]
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hσ.ne'),one_smul]
    rfl
  unfold oddSingularTransform
  rw [hc]
  simp only [source_scalar_singularValues σ hσ.le]
  exact spectralDiagonal_const _ (f σ)

/-- A positive real multiple of a normalized state has full-space probability equal to the
squared multiplier and conditions back to the original state. -/
private theorem source_conditional_positive_smul {I : Type} [Fintype I] [DecidableEq I]
    (c : ℝ) (hc : 0 < c) (ψ : QState I) (hψ : Normalized ψ) :
    MeasureProb ((c : ℂ) • ψ) Finset.univ = c^2 ∧
    ConditionalState ((c : ℂ) • ψ) = some ψ := by
  have hm : MeasureProb ((c : ℂ) • ψ) Finset.univ = c^2 := by
    rw [measureProb_smul,measureProb_univ hψ,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hc,mul_one]
  refine ⟨hm,?_⟩
  have hp : 0 < c^2 := sq_pos_of_pos hc
  rw [ConditionalState,hm,if_pos hp]
  congr 1
  have hn : ‖stateVector ((c : ℂ) • ψ)‖ = c := by
    have he := stateVector_norm_sq ((c : ℂ) • ψ)
    rw [hm] at he
    nlinarith [norm_nonneg (stateVector ((c : ℂ) • ψ))]
  rw [postMeasure_univ_eq_smul,hn]
  funext i
  simp [Pi.smul_apply,Complex.real_smul,Complex.ofReal_inv,← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')]

/-- The iterated sign polynomial has real parity `3 ^ k`. -/
private theorem source_sign_parity (k : ℕ) : HasRealParity (3^k) (signPolynomial k) := by
  have ho : Odd (3^k) := (by decide : Odd (3 : ℕ)).pow
  simp [HasRealParity,signPolynomial_comp_neg_X,ho.neg_one_pow]

/-- For an encoded scalar `σ` with `0 < δ ≤ σ ≤ 1` and sign-polynomial error below one, a
length-`3 ^ k` compiled word postselects the unit state with the stated success lower bound
[GilyenSuLowWiebe2019]. -/
theorem cpp_unknown_scalar_fixed_point_postselection : ∀ (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (L R : Matrix H Unit ℂ) (σ δ : ℝ) (k : ℕ),
  0<δ → δ≤σ → σ≤1 → signPolynomialError δ k<1 →
  ProjectedUnitaryEncoding ((σ:ℂ) • (1:Matrix Unit Unit ℂ)) U L R →
  ∃ Φ : List ℝ,Φ.length=3^k ∧
    let V:=sourceRealWord U (rangeProjector R) (rangeProjector L) Φ;
    (1-signPolynomialError δ k)^2≤
      postselectionProbability V (sourceAverageClean L) (sourceAverageClean R) (Ket ()) ∧
    postselectionOutput V (sourceAverageClean L) (sourceAverageClean R) (Ket ())=some (Ket ()) ∧
    (cppCounts (cppCompile (sourceRealFamily Φ))).1=3^k := by
  intro H _ _ U L R σ δ k hδ hgap hσ1 hE h
  have hσ : 0 < σ := hδ.trans_le hgap
  have hodd : (3^k)%2=1 := Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
  have hdeg : (signPolynomial k).degree ≤ ((3^k : ℕ) : WithBot ℕ) := by
    rw [← signPolynomial_natDegree]; exact degree_le_natDegree
  obtain ⟨Φ,hlen,hoddEnc,_,hcounts⟩ := source_length_cpp_real_singular_transform H Unit Unit
    ((σ : ℂ) • (1 : Matrix Unit Unit ℂ)) U L R (signPolynomial k) (3^k)
    h (by positivity) hdeg (source_sign_parity k) (fun x hx => signPolynomial_abs_le_one k hx)
  have hv := hoddEnc hodd
  rw [source_scalar_odd_transform σ hσ] at hv
  let c := (signPolynomial k).eval σ
  have hc : 0 < c := signPolynomial_eval_pos k hσ hσ1
  have he := signPolynomial_error_le k (x:=σ) hδ
    (by simpa [abs_of_pos hσ] using! hgap) (by simpa [abs_of_pos hσ] using! hσ1)
  rw [Real.sign_of_pos hσ] at he
  have hlower : 1-signPolynomialError δ k ≤ c := by
    have he' := (le_abs_self (1-c)).trans he
    linarith
  have hb : postselectionVector (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean L) (sourceAverageClean R) (Ket ()) = (c : ℂ) • Ket () := by
    simp only [postselectionVector,hv.encoded,Matrix.smul_mulVec,Matrix.one_mulVec]; rfl
  have hcond := source_conditional_positive_smul c hc (Ket ()) (normalized_ket ())
  have hm : postselectionProbability (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean L) (sourceAverageClean R) (Ket ()) = c^2 := by
    rw [postselectionProbability_eq_norm_sq hv.left_isometry, hb, stateVector_norm_sq,hcond.1]
  refine ⟨Φ,hlen,?_,?_,?_⟩
  · (try dsimp only)
    rw [hm]
    nlinarith
  · (try dsimp only)
    rw [postselectionOutput,hb,hcond.2]
  · exact congrArg Prod.fst hcounts

/-- A length-two compiled word for `sourceKernelMatrix` has compressed diagonal `(1, 3 / 4)`,
success probability `25 / 32` on `sourceKernelInput`, and conditional output
`sourceKernelOutput` [GilyenSuLowWiebe2019]. -/
theorem cpp_even_full_kernel_consumer : ∀ (H : Type) [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (L R : Matrix H (Fin 2) ℂ),
  ProjectedUnitaryEncoding sourceKernelMatrix U L R →
  ∃ Φ : List ℝ,Φ.length=2 ∧
    let V:=sourceRealWord U (rangeProjector R) (rangeProjector L) Φ;
    compress (sourceAverageClean R) V (sourceAverageClean R)=
      diagonal (fun i : Fin 2=>if i=0 then 1 else 3/4) ∧
    postselectionProbability V (sourceAverageClean R) (sourceAverageClean R) sourceKernelInput=25/32 ∧
    postselectionOutput V (sourceAverageClean R) (sourceAverageClean R) sourceKernelInput=
      some sourceKernelOutput ∧ cppCounts (cppCompile (sourceRealFamily Φ))=(2,2,2,2)
 := by
  intro H _ _ U L R h
  let p : Polynomial ℝ := 1-X^2
  have hdeg : p.degree ≤ (2 : WithBot ℕ) := by
    apply degree_le_of_natDegree_le
    exact (natDegree_sub_le _ _).trans (by norm_num)
  have hpar : HasRealParity 2 p := by
    simp [HasRealParity,p,sub_comp,pow_comp]
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 := by
    intro x hx
    simp only [p,eval_sub,eval_one,eval_pow,eval_X]
    apply abs_le.mpr
    constructor <;> nlinarith [hx.1,hx.2,sq_nonneg x]
  obtain ⟨Φ,hlen,_,hev,hcounts⟩ := source_length_cpp_real_singular_transform H (Fin 2) (Fin 2)
    sourceKernelMatrix U L R p 2 h (by norm_num) hdeg hpar hb
  have hv := hev (by norm_num)
  have ht : rightSingularTransform sourceKernelMatrix (fun x => ((p.eval x : ℝ) : ℂ)) =
      diagonal (fun i : Fin 2 => if i=0 then 1 else 3/4) := by
    have hf : (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) =
        (fun x : ℝ => (1-X : Polynomial ℂ).eval ((x : ℂ)^2)) := by
      funext x
      simp [p]
    rw [hf,← gram_aeval_eq_rightSingularTransform]
    simp only [aeval_sub,aeval_one,aeval_X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceKernelMatrix,Matrix.diagonal_apply,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Matrix.one_apply,Fin.sum_univ_two]
    rw [map_ofNat]
    norm_num
  rw [ht] at hv
  let c : ℝ := 5/(4*Real.sqrt 2)
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcout : Normalized sourceKernelOutput := by
    norm_num [Normalized,sourceKernelOutput,Fin.sum_univ_two,Complex.norm_def]
  have hbvec : postselectionVector (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
      (sourceAverageClean R) (sourceAverageClean R) sourceKernelInput =
      (c : ℂ) • sourceKernelOutput := by
    rw [postselectionVector,hv.encoded]
    funext i
    fin_cases i <;>
      simp [sourceKernelInput,sourceKernelOutput,Matrix.mulVec,Matrix.diagonal_apply,
        c,Complex.ofReal_div,Complex.ofReal_mul]
    all_goals ring
  have hcond := source_conditional_positive_smul c hc sourceKernelOutput hcout
  have hc2 : c^2=25/32 := by
    dsimp [c]
    field_simp
    nlinarith
  refine ⟨Φ,hlen,hv.encoded,?_,?_,hcounts⟩
  · (try dsimp only)
    rw [postselectionProbability_eq_norm_sq hv.left_isometry,hbvec,stateVector_norm_sq,hcond.1,hc2]
  · (try dsimp only)
    rw [postselectionOutput,hbvec,hcond.2]

end Qatlib.Concepts.QsvtCore.QsVtMain
