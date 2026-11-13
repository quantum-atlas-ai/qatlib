/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.ActualEulerVariance

/-!
# Trace normalization with positive variance noise

This module defines `normalizePositive` and bounds the effect of adding positive semidefinite
noise before normalization. It applies the estimate to the reduced Euler output, expressing the
normalized error through the entangling residual and the positive ideal target mass in the step
analysis of [LloydEtAl2020].

## Main statements

* `normalizePositive_density`: A positive semidefinite matrix with positive real trace becomes
  positive semidefinite with trace one after normalization.
* `positive_add_normalization`: Adding positive semidefinite noise to a positive semidefinite
  matrix of positive trace changes its normalization by at most twice the noise trace divided by
  the total trace.
* `actualEuler_normalized_error`: For normalized environment and positive ideal target trace,
  the normalized Euler error is bounded by twice the residual noise mass divided by ideal mass
  plus noise mass.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

/-- Rescale a matrix by the reciprocal of its real trace, viewed as a complex scalar. -/
def normalizePositive {I : Type} [Fintype I] (ρ : Matrix I I ℂ) : Matrix I I ℂ :=
  (((ρ.trace.re)⁻¹:ℝ):ℂ) •ρ

/-- The trace norm of a positive semidefinite matrix equals the real part of its trace. -/
theorem positive_traceNorm {I : Type} [Fintype I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    ρ.traceNorm=ρ.trace.re := by
  have h := congrArg Complex.re hρ.traceNorm_eq_trace
  simpa using h

/-- A positive semidefinite matrix with positive real trace becomes positive semidefinite with
trace one after normalization. -/
theorem normalizePositive_density {I : Type} [Fintype I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef)
    (hp : 0<ρ.trace.re) : (normalizePositive ρ).PosSemidef ∧ (normalizePositive ρ).trace=1 := by
  have hi := (RCLike.nonneg_iff.mp hρ.trace_nonneg).2
  change ρ.trace.im=0 at hi
  have ht : ρ.trace=(ρ.trace.re:ℂ) := by apply Complex.ext <;> simp [hi]
  constructor
  · exact hρ.smul (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hp.le))
  · rw [normalizePositive,Matrix.trace_smul,ht]
    simp [hp.ne']

/-- Adding positive semidefinite noise to a positive semidefinite matrix of positive trace
changes its normalization by at most twice the noise trace divided by the total trace. -/
theorem positive_add_normalization {I : Type} [Fintype I]
    (P V : Matrix I I ℂ) (hP : P.PosSemidef) (hV : V.PosSemidef) (hq : 0<P.trace.re) :
    (normalizePositive (P+V)-normalizePositive P).traceNorm≤
      2*V.trace.re/(P.trace.re+V.trace.re) := by
  let q : ℝ:=P.trace.re
  let d : ℝ:=V.trace.re
  have hd : 0≤d := by
    dsimp [d]
    rw [← positive_traceNorm V hV]
    exact Matrix.traceNorm_nonneg _
  have hp : 0<q+d := by dsimp [q];linarith
  have hq' : 0<q := hq
  have he : normalizePositive (P+V)-normalizePositive P=
      (((q+d)⁻¹:ℝ):ℂ) •V+(((q+d)⁻¹-q⁻¹:ℝ):ℂ) •P := by
    unfold normalizePositive
    rw [Matrix.trace_add,Complex.add_re,Complex.ofReal_sub,sub_smul,smul_add]
    change (((q+d)⁻¹:ℝ):ℂ) •P+(((q+d)⁻¹:ℝ):ℂ) •V-((q⁻¹:ℝ):ℂ) •P=_
    abel
  have hfirst : ((((q+d)⁻¹:ℝ):ℂ) •V).traceNorm=d/(q+d) := by
    rw [Matrix.traceNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),positive_traceNorm V hV]
    change (q+d)⁻¹*d=d/(q+d)
    ring
  have hdiff : (q+d)⁻¹-q⁻¹= -d/((q+d)*q) := by
    field_simp
    ring
  have hsecond : ((((q+d)⁻¹-q⁻¹:ℝ):ℂ) •P).traceNorm=d/(q+d) := by
    rw [Matrix.traceNorm_smul,Complex.norm_real,Real.norm_eq_abs,positive_traceNorm P hP]
    change |(q+d)⁻¹-q⁻¹| * q=d/(q+d)
    rw [hdiff,abs_div,abs_neg,abs_of_nonneg hd,abs_of_pos (mul_pos hp hq')]
    field_simp
  rw [he]
  calc
    _ ≤ ((((q+d)⁻¹:ℝ):ℂ) •V).traceNorm+((((q+d)⁻¹-q⁻¹:ℝ):ℂ) •P).traceNorm := Matrix.traceNorm_add_le _ _
    _ = _ := by rw [hfirst,hsecond];change d/(q+d)+d/(q+d)=2*d/(q+d);ring

/-- For normalized environment and positive ideal target trace, the normalized Euler error is
bounded by twice the residual noise mass divided by ideal mass plus noise mass. -/
theorem actualEuler_normalized_error {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1)
    (x : I→ℂ) (c : ℂ) (hp : 0<(outer (idealEulerVector F q x c)).trace.re) :
    (normalizePositive (actualEulerReduced F q x c)-normalizePositive (outer (idealEulerVector F q x c))).traceNorm≤
      2*(Complex.normSq c*∑ p : I×E,Complex.normSq (entanglingResidual q (F*ᵥ inflate q x) p))/
        ((outer (idealEulerVector F q x c)).trace.re+
          Complex.normSq c*∑ p : I×E,Complex.normSq (entanglingResidual q (F*ᵥ inflate q x) p)) := by
  let P := outer (idealEulerVector F q x c)
  let V := actualEulerReduced F q x c-P
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hV : V.PosSemidef := actualEuler_difference_psd F q hq x c
  have hv : V.trace.re=Complex.normSq c*∑ p : I×E,Complex.normSq (entanglingResidual q (F*ᵥ inflate q x) p) := by
    rw [← positive_traceNorm V hV]
    exact actualEuler_traceNorm F q hq x c
  have he : actualEulerReduced F q x c=P+V := by dsimp [V];abel
  have h := positive_add_normalization P V hP hV hp
  rw [← he,hv] at h
  exact h

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
