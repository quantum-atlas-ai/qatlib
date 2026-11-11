/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditionalDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transporting conditional bounds from pure to mixed states

Proves linearity and positivity of `selectedBranch` and constructs a finite pure-state
decomposition of every density operator. These facts extend uniform pure-input branch estimates
to mixed inputs.

The theorem `pureToMixed_holds` gives the conditional normalized-output guarantee encoded by
`transportPureToMixed` under `PureUniformBranchBound` and `2 * e < g`. The density-operator and
instrument framework is described in [Watrous2018].

## Main statements

* `density_pure_decomposition`: a convex decomposition into normalized pure states.
* `pureToMixed_holds`: a mixed-input guarantee from uniform pure-input branch bounds.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical Matrix.Norms.L2Operator ComplexOrder

/-- The selected instrument branch sum maps the zero operator to zero. -/
theorem selectedBranch_zero {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) : selectedBranch J S (0 : Operator D) = 0 := by
  unfold selectedBranch
  show (∑ o ∈ S, (J.branch o) 0) = 0
  simp only [map_zero]
  exact Finset.sum_const_zero

/-- The selected instrument branch sum preserves addition. -/
theorem selectedBranch_add {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) (ρ σ : Operator D) :
    selectedBranch J S (ρ + σ) = selectedBranch J S ρ + selectedBranch J S σ := by
  unfold selectedBranch
  show (∑ o ∈ S, (J.branch o) (ρ + σ)) = (∑ o ∈ S, (J.branch o) ρ) + (∑ o ∈ S, (J.branch o) σ)
  simp only [map_add]
  exact Finset.sum_add_distrib

/-- The selected instrument branch sum preserves complex scalar multiplication. -/
theorem selectedBranch_smul {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) (c : ℂ) (ρ : Operator D) :
    selectedBranch J S (c • ρ) = c • selectedBranch J S ρ := by
  unfold selectedBranch
  show (∑ o ∈ S, (J.branch o) (c • ρ)) = c • (∑ o ∈ S, (J.branch o) ρ)
  simp only [map_smul]
  exact Finset.smul_sum.symm

/-- The selected instrument branch sum commutes with finite complex linear combinations. -/
theorem selectedBranch_sum {O : Type} [Fintype O] {D E : ℕ} (J : Instrument O D E)
    (S : Finset O) {ι : Type} (t : Finset ι) (c : ι → ℂ) (X : ι → Operator D) :
    selectedBranch J S (∑ k ∈ t, (c k : ℂ) • X k) =
      ∑ k ∈ t, (c k : ℂ) • selectedBranch J S (X k) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact selectedBranch_zero J S
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, selectedBranch_add, selectedBranch_smul, ih]

/-- The selected instrument branch sum preserves positive semidefiniteness. -/
theorem selectedBranch_posSemidef {O : Type} [Fintype O] {D E : ℕ}
    (J : Instrument O D E) (S : Finset O) {ρ : Operator D} (hρ : ρ.PosSemidef) :
    (selectedBranch J S ρ).PosSemidef := by
  unfold selectedBranch
  show (∑ o ∈ S, (J.branch o) ρ).PosSemidef
  exact Matrix.posSemidef_sum S (fun o _ => (J.cp o).positive hρ)

/-- The trace norm of a positive semidefinite matrix equals the real part of its trace. -/
theorem psd_traceNorm_eq_re_trace {D : ℕ} {X : Operator D} (hX : X.PosSemidef) :
    Matrix.traceNorm X = (Matrix.trace X).re := by
  simpa using! congrArg Complex.re hX.traceNorm_eq_trace

/-- Each column of the eigenvector unitary of a Hermitian operator is a normalized state vector. -/
theorem eigenvectorUnitary_col_normalized {D : ℕ} {ρ : Operator D}
    (hherm : ρ.IsHermitian) (k : Fin D) :
    Normalized (fun i => (hherm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) i k) := by
  set U : Matrix (Fin D) (Fin D) ℂ := (hherm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
  have h1 : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hherm.eigenvectorUnitary
    rw [show U = (hherm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) from rfl]
    simpa [Matrix.star_eq_conjTranspose] using! h
  have hk := congrFun (congrFun h1 k) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hk
  have hterm : ∀ i, (star (U i k) * U i k : ℂ) = ((‖U i k‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hsum : (∑ i, ((‖U i k‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    have hsum0 : (∑ i, star (U i k) * U i k) = 1 := by simpa [U] using! hk
    rw [Finset.sum_congr rfl (fun i _ => (hterm i).symm)]
    exact hsum0
  have hsumre : (∑ i, ‖U i k‖ ^ 2) = 1 := by
    have h := congrArg Complex.re hsum
    simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re] at h
    exact h
  simpa [U] using! hsumre

/-- Every density operator is a finite convex combination of outer products of normalized
vectors, indexed by `Fin D`. -/
theorem density_pure_decomposition {D : ℕ} (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧
        (∀ k, Normalized (ψ k)) ∧
        (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) := by
  classical
  have hherm : ρ.IsHermitian := hρ.1.isHermitian
  refine ⟨hherm.eigenvalues,
    fun k i => (hherm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) i k,
    (fun k => hρ.1.eigenvalues_nonneg k),
    (fun k => eigenvectorUnitary_col_normalized hherm k), ?_, ?_⟩
  · have hsum : (∑ k, (hherm.eigenvalues k : ℂ)) = 1 :=
      hherm.trace_eq_sum_eigenvalues.symm.trans hρ.2
    have h := congrArg Complex.re hsum
    simpa [Complex.re_sum] using! h
  · set U : Matrix (Fin D) (Fin D) ℂ := (hherm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
    have hspec : ρ = U * Matrix.diagonal (fun k => (hherm.eigenvalues k : ℂ)) * Uᴴ := by
      have h := hherm.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
      simpa [U] using! h
    ext a b
    have hinner : ∀ y, (∑ x, U a x * (if x = y then (hherm.eigenvalues x : ℂ) else 0))
        = U a y * (hherm.eigenvalues y : ℂ) := by
      intro y
      have hite : ∀ x : Fin D,
          U a x * (if x = y then (hherm.eigenvalues x : ℂ) else 0)
            = if x = y then U a x * (hherm.eigenvalues x : ℂ) else 0 := by
        intro x
        by_cases hx : x = y
        · rw [if_pos hx, if_pos hx]
        · rw [if_neg hx, if_neg hx, mul_zero]
      have hsw : (∑ x, U a x * (if x = y then (hherm.eigenvalues x : ℂ) else 0))
          = ∑ x, (if x = y then U a x * (hherm.eigenvalues x : ℂ) else 0) :=
        Finset.sum_congr rfl (fun x _ => hite x)
      rw [hsw, Finset.sum_ite_eq']
      exact if_pos (Finset.mem_univ y)
    have hcore : (U * Matrix.diagonal (fun k => (hherm.eigenvalues k : ℂ)) * Uᴴ) a b
        = ∑ k, ((hherm.eigenvalues k : ℂ) * (U a k * star (U b k))) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      have hstep : (∑ y, (∑ x, U a x * (if x = y then (hherm.eigenvalues x : ℂ) else 0))
          * star (U b y)) = ∑ y, (U a y * (hherm.eigenvalues y : ℂ)) * star (U b y) :=
        Finset.sum_congr rfl (fun y _ => by rw [hinner y])
      rw [hstep]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hrhs : (∑ k, ((hherm.eigenvalues k : ℂ) •
        outerProduct (fun i => U i k) : Operator D)) a b =
        ∑ k, ((hherm.eigenvalues k : ℂ) * (U a k * star (U b k))) := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl (fun k _ => rfl)
    conv_lhs => rw [hspec]
    rw [hcore, hrhs]

/-- A uniform pure-input branch bound with `2 * e < g` implies the mixed-input conditional
guarantee with direction error `2 * e / (g - e)` and success gap `g - e`. -/
theorem pureToMixed_holds {O : Type} [Fintype O] {D E : ℕ}
    (J K : Instrument O D E) (S : Finset O) (e g : ℝ)
    (hb : PureUniformBranchBound J K S e g) (h2 : 2 * e < g) :
    (transportPureToMixed e g).Holds J K S := by
  have he : 0 ≤ e := hb.1
  have hg : 0 < g := hb.2.1
  have hpure : ∀ ψ : QState (Fin D), Normalized ψ →
      Matrix.traceNorm (selectedBranch J S (outerProduct ψ) -
          selectedBranch K S (outerProduct ψ)) ≤ e ∧
        g ≤ (Matrix.trace (selectedBranch K S (outerProduct ψ))).re := hb.2.2.2
  have hg0 : 0 < g - e := by linarith
  have hdiv : 0 ≤ 2 * e / (g - e) := by
    apply div_nonneg
    · linarith
    · linarith
  refine ⟨hg0, hdiv, ?_⟩
  intro ρ hρ
  obtain ⟨w, ψ, hw, hψ, hsum, hρeq⟩ := density_pure_decomposition ρ hρ
  have hpurek : ∀ k,
      Matrix.traceNorm (selectedBranch J S (outerProduct (ψ k)) -
          selectedBranch K S (outerProduct (ψ k))) ≤ e ∧
        g ≤ (Matrix.trace (selectedBranch K S (outerProduct (ψ k)))).re :=
    fun k => hpure (ψ k) (hψ k)
  have ha : selectedBranch J S ρ =
      ∑ k, (w k : ℂ) • selectedBranch J S (outerProduct (ψ k)) := by
    rw [hρeq, selectedBranch_sum]
  have hbK : selectedBranch K S ρ =
      ∑ k, (w k : ℂ) • selectedBranch K S (outerProduct (ψ k)) := by
    rw [hρeq, selectedBranch_sum]
  have hdiff : selectedBranch J S ρ - selectedBranch K S ρ =
      ∑ k, ((w k : ℂ) • (selectedBranch J S (outerProduct (ψ k)) -
          selectedBranch K S (outerProduct (ψ k)))) := by
    rw [ha, hbK, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_sub]
  have hdiffnorm : Matrix.traceNorm (selectedBranch J S ρ - selectedBranch K S ρ) ≤ e := by
    rw [hdiff]
    refine le_trans (diamond_traceNorm_sum_le Finset.univ _) ?_
    have hterm : ∀ k, Matrix.traceNorm
        (((w k : ℂ) • (selectedBranch J S (outerProduct (ψ k)) -
            selectedBranch K S (outerProduct (ψ k))))) ≤ (w k : ℝ) * e := by
      intro k
      rw [Matrix.traceNorm_smul]
      have h0 : 0 ≤ w k := hw k
      have hn := (hpurek k).1
      calc
        ‖((w k : ℂ))‖ * Matrix.traceNorm
            (selectedBranch J S (outerProduct (ψ k)) - selectedBranch K S (outerProduct (ψ k))) ≤
            ‖((w k : ℂ))‖ * e :=
          mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ = (w k : ℝ) * e := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) ?_
    rw [← Finset.sum_mul, hsum, one_mul]
  have hK : g ≤ (Matrix.trace (selectedBranch K S ρ)).re := by
    rw [hbK]
    have htrace : (Matrix.trace
        (∑ k, (w k : ℂ) • selectedBranch K S (outerProduct (ψ k)))).re =
        ∑ k, (w k : ℝ) * (Matrix.trace (selectedBranch K S (outerProduct (ψ k)))).re := by
      rw [Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.trace_smul]
      have hz : ∀ z : ℂ, (((w k : ℂ)) * z).re = (w k : ℝ) * z.re := by
        intro z
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact hz _
    rw [htrace]
    calc
      g = ∑ k, (w k : ℝ) * g := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ k, (w k : ℝ) * (Matrix.trace (selectedBranch K S (outerProduct (ψ k)))).re :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hpurek k).2 (hw k))
  have hsub : Matrix.trace (selectedBranch J S ρ) - Matrix.trace (selectedBranch K S ρ) =
      Matrix.trace (selectedBranch J S ρ - selectedBranch K S ρ) :=
    (Matrix.trace_sub _ _).symm
  have hbound : ‖Matrix.trace (selectedBranch J S ρ) - Matrix.trace (selectedBranch K S ρ)‖ ≤ e := by
    have hle := abs_trace_le_traceNorm (selectedBranch J S ρ - selectedBranch K S ρ)
    rw [← hsub] at hle
    exact le_trans hle hdiffnorm
  have hre : |(Matrix.trace (selectedBranch J S ρ)).re -
      (Matrix.trace (selectedBranch K S ρ)).re| ≤ e := by
    have h := Complex.abs_re_le_norm
      (Matrix.trace (selectedBranch J S ρ) - Matrix.trace (selectedBranch K S ρ))
    rw [Complex.sub_re] at h
    exact le_trans h hbound
  have hneg : -e ≤ (Matrix.trace (selectedBranch J S ρ)).re -
      (Matrix.trace (selectedBranch K S ρ)).re := neg_le_of_abs_le hre
  have hJ : 0 < (Matrix.trace (selectedBranch J S ρ)).re := by linarith
  have hKres : g - e ≤ (Matrix.trace (selectedBranch K S ρ)).re := by linarith
  refine ⟨hKres, hJ, ?_⟩
  have hJn : normalizedBranch (selectedBranch J S ρ) =
      ((Matrix.trace (selectedBranch J S ρ))⁻¹ : ℂ) • selectedBranch J S ρ := by
    unfold normalizedBranch
    have hne : Matrix.trace (selectedBranch J S ρ) ≠ 0 := by
      intro hz
      rw [hz, Complex.zero_re] at hJ
      linarith
    rw [if_neg hne]
  have hKn : normalizedBranch (selectedBranch K S ρ) =
      ((Matrix.trace (selectedBranch K S ρ))⁻¹ : ℂ) • selectedBranch K S ρ := by
    unfold normalizedBranch
    have hne : Matrix.trace (selectedBranch K S ρ) ≠ 0 := by
      intro hz
      rw [hz, Complex.zero_re] at hK
      have : (0 : ℂ).re = 0 := by simp
      linarith
    rw [if_neg hne]
  set σ : Operator E := selectedBranch J S ρ
  set τ : Operator E := selectedBranch K S ρ
  have hσpsd : σ.PosSemidef := selectedBranch_posSemidef J S hρ.1
  have hτpsd : τ.PosSemidef := selectedBranch_posSemidef K S hρ.1
  have hτnorm : Matrix.traceNorm τ = (Matrix.trace τ).re := psd_traceNorm_eq_re_trace hτpsd
  have hστ : Matrix.traceNorm (σ - τ) ≤ e := by
    have : σ - τ = selectedBranch J S ρ - selectedBranch K S ρ := rfl
    rw [this]
    exact hdiffnorm
  have htrσre : g - e ≤ (Matrix.trace σ).re := by
    have : (Matrix.trace σ).re = (Matrix.trace (selectedBranch J S ρ)).re := rfl
    rw [this]
    linarith
  have htrτre : g ≤ (Matrix.trace τ).re := by
    have : (Matrix.trace τ).re = (Matrix.trace (selectedBranch K S ρ)).re := rfl
    rw [this]
    exact hK
  have htrσp : 0 < (Matrix.trace σ).re := by linarith
  have htrσne : Matrix.trace σ ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at htrσp
    linarith
  have htrτne : Matrix.trace τ ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at htrτre
    linarith
  have hnormσ : g - e ≤ ‖Matrix.trace σ‖ := by
    have := Complex.re_le_norm (Matrix.trace σ)
    linarith
  have hnormτ : g - e ≤ ‖Matrix.trace τ‖ := by
    have := Complex.re_le_norm (Matrix.trace τ)
    linarith
  have hσnormpos : 0 < ‖Matrix.trace σ‖ := by linarith
  have hτnormpos : 0 < ‖Matrix.trace τ‖ := by linarith
  have hsplit : ((Matrix.trace σ)⁻¹ : ℂ) • σ - ((Matrix.trace τ)⁻¹ : ℂ) • τ =
      ((Matrix.trace σ)⁻¹ : ℂ) • (σ - τ) +
        (((Matrix.trace σ)⁻¹ - (Matrix.trace τ)⁻¹ : ℂ)) • τ := by
    rw [smul_sub, sub_smul]
    abel
  have hnum : ‖Matrix.trace τ - Matrix.trace σ‖ ≤ e := by
    have h : Matrix.trace τ - Matrix.trace σ = -(Matrix.trace (σ - τ)) := by
      rw [Matrix.trace_sub]
      abel
    rw [h, norm_neg]
    exact le_trans (abs_trace_le_traceNorm (σ - τ)) hστ
  have hc : ‖Matrix.trace τ‖⁻¹ * (Matrix.trace τ).re ≤ 1 := by
    have h := Complex.re_le_norm (Matrix.trace τ)
    rw [← div_eq_inv_mul]
    exact (div_le_one₀ hτnormpos).mpr h
  have hterm1 : ‖((Matrix.trace σ)⁻¹ : ℂ)‖ * Matrix.traceNorm (σ - τ) ≤ e / (g - e) := by
    rw [norm_inv]
    have h1a : ‖Matrix.trace σ‖⁻¹ * Matrix.traceNorm (σ - τ) ≤ ‖Matrix.trace σ‖⁻¹ * e :=
      mul_le_mul_of_nonneg_left hστ (inv_nonneg.mpr (norm_nonneg _))
    have h1b : ‖Matrix.trace σ‖⁻¹ ≤ (g - e)⁻¹ := by
      exact inv_le_inv₀ hσnormpos (by linarith : 0 < g - e) |>.mpr hnormσ
    refine le_trans h1a ?_
    have h1c : ‖Matrix.trace σ‖⁻¹ * e ≤ (g - e)⁻¹ * e :=
      mul_le_mul_of_nonneg_right h1b he
    rw [div_eq_inv_mul]
    exact h1c
  have hterm2 : ‖((Matrix.trace σ)⁻¹ - (Matrix.trace τ)⁻¹ : ℂ)‖ * Matrix.traceNorm τ ≤
      e / (g - e) := by
    have hkey : ((Matrix.trace σ)⁻¹ - (Matrix.trace τ)⁻¹ : ℂ) =
        (Matrix.trace τ - Matrix.trace σ) * (Matrix.trace σ)⁻¹ * (Matrix.trace τ)⁻¹ := by
      field_simp [htrσne, htrτne]
    rw [hkey, norm_mul, norm_mul, norm_inv, norm_inv, hτnorm]
    calc
      ‖Matrix.trace τ - Matrix.trace σ‖ * ‖Matrix.trace σ‖⁻¹ * ‖Matrix.trace τ‖⁻¹ *
          (Matrix.trace τ).re =
          ‖Matrix.trace τ - Matrix.trace σ‖ * ‖Matrix.trace σ‖⁻¹ *
            (‖Matrix.trace τ‖⁻¹ * (Matrix.trace τ).re) := by ring
      _ ≤ ‖Matrix.trace τ - Matrix.trace σ‖ * ‖Matrix.trace σ‖⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hc
          (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)))
      _ = ‖Matrix.trace τ - Matrix.trace σ‖ * ‖Matrix.trace σ‖⁻¹ := by ring
      _ ≤ e * ‖Matrix.trace σ‖⁻¹ := mul_le_mul_of_nonneg_right hnum
          (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ e * (g - e)⁻¹ := mul_le_mul_of_nonneg_left
          (inv_le_inv₀ hσnormpos (by linarith : 0 < g - e) |>.mpr hnormσ) he
      _ = e / (g - e) := by rw [div_eq_mul_inv]
  show Matrix.traceNorm (normalizedBranch σ - normalizedBranch τ) ≤ 2 * e / (g - e)
  rw [hJn, hKn, hsplit]
  refine le_trans (Matrix.traceNorm_add_le _ _) ?_
  rw [Matrix.traceNorm_smul, Matrix.traceNorm_smul]
  have hsum2 : e / (g - e) + e / (g - e) = 2 * e / (g - e) := by
    rw [← two_mul, ← mul_div]
  rw [← hsum2]
  exact add_le_add hterm1 hterm2

end Qatlib.Concepts.MbqcFlow.FlowDecision
