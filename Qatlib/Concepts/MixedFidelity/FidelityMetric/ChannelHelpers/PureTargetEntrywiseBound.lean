/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound

open Matrix
open scoped BigOperators ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

theorem pureTarget_sub_quadratic_nonpos
    (v : Qatlib.Foundations.PureStateMath.QState I) (σ : Matrix I I ℂ) (hσ : σ.PosSemidef)
    (x : Qatlib.Foundations.PureStateMath.QState I) (hx : Qatlib.Foundations.PureStateMath.Inner v x = 0) :
    (Qatlib.Foundations.PureStateMath.Inner x ((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) *ᵥ x)).re ≤ 0 := by
  have hp : 0 ≤ (Qatlib.Foundations.PureStateMath.Inner x (σ *ᵥ x)).re :=
    (Complex.nonneg_iff.mp (hσ.dotProduct_mulVec_nonneg x)).1
  rw [Matrix.sub_mulVec, Qatlib.Foundations.PureStateMath.Reflection.outerProduct_mulVec, hx, zero_smul,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right]
  have hz :
      Qatlib.Foundations.PureStateMath.Inner x
      (0 : Qatlib.Foundations.PureStateMath.QState I) = 0 := by
        simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct]
  rw [hz, zero_sub, Complex.neg_re]
  linarith

theorem pureTarget_sub_positive_eigenvalue_unique
    (v : Qatlib.Foundations.PureStateMath.QState I) (σ : Matrix I I ℂ) (hσ : σ.PosSemidef)
    (hE : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ).IsHermitian)
    (i j : I) (hi : 0 < hE.eigenvalues i) (hj : 0 < hE.eigenvalues j) : i = j := by
  classical
  by_contra hij
  let x : Qatlib.Foundations.PureStateMath.QState I := ⇑(hE.eigenvectorBasis i)
  let y : Qatlib.Foundations.PureStateMath.QState I := ⇑(hE.eigenvectorBasis j)
  have hxx : Qatlib.Foundations.PureStateMath.Inner x x = 1 := by
    rw [← Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec]
    exact hE.eigenvectorBasis.inner_eq_one i
  have hyy : Qatlib.Foundations.PureStateMath.Inner y y = 1 := by
    rw [← Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec]
    exact hE.eigenvectorBasis.inner_eq_one j
  have hxy : Qatlib.Foundations.PureStateMath.Inner x y = 0 := by
    rw [← Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec]
    exact hE.eigenvectorBasis.inner_eq_zero hij
  have hyx : Qatlib.Foundations.PureStateMath.Inner y x = 0 := by
    rw [← Qatlib.Foundations.PureStateMath.BornBridge.inner_euclidean_fromVec]
    exact hE.eigenvectorBasis.inner_eq_zero (Ne.symm hij)
  have hex : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) *ᵥ x = (hE.eigenvalues i : ℂ) • x :=
    hE.mulVec_eigenvectorBasis i
  have hey : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) *ᵥ y = (hE.eigenvalues j : ℂ) • y :=
    hE.mulVec_eigenvectorBasis j
  let a : ℂ := Qatlib.Foundations.PureStateMath.Inner v x
  let b : ℂ := Qatlib.Foundations.PureStateMath.Inner v y
  have ha : a ≠ 0 := by
    intro hzero
    have h :=
        Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound.pureTarget_sub_quadratic_nonpos v σ hσ x hzero
    rw [hex, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, hxx, mul_one,
      Complex.ofReal_re] at h
    linarith
  let z : Qatlib.Foundations.PureStateMath.QState I := b • x - a • y
  have hvz : Qatlib.Foundations.PureStateMath.Inner v z = 0 := by
    dsimp only [z]
    rw [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]
    change b * a - a * b = 0
    ring
  have hez : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) *ᵥ z =
      b • ((hE.eigenvalues i : ℂ) • x) - a • ((hE.eigenvalues j : ℂ) • y) := by
    dsimp only [z]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hex, hey]
  have hform : Qatlib.Foundations.PureStateMath.Inner z ((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) *ᵥ z) =
      ((hE.eigenvalues i * Complex.normSq b +
        hE.eigenvalues j * Complex.normSq a : ℝ) : ℂ) := by
    rw [hez]
    dsimp only [z]
    simp only [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      hxx, hyy, hxy, hyx, mul_zero, mul_one, sub_zero, zero_sub]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have hnonpos :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound.pureTarget_sub_quadratic_nonpos v σ hσ z hvz
  rw [hform, Complex.ofReal_re] at hnonpos
  have ha_pos : 0 < Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hb_nonneg := Complex.normSq_nonneg b
  have hfirst : 0 ≤ hE.eigenvalues i * Complex.normSq b :=
    mul_nonneg hi.le hb_nonneg
  have hsecond : 0 < hE.eigenvalues j * Complex.normSq a := mul_pos hj ha_pos
  linarith

theorem halfTraceNorm_eq_positive_eigenvalue_or_zero
    (E : Matrix I I ℂ) (hE : E.IsHermitian) (htr : E.trace = 0)
    (hunique : ∀ i j, 0 < hE.eigenvalues i → 0 < hE.eigenvalues j → i = j) :
    E.traceNorm / 2 = 0 ∨
      ∃ i, 0 < hE.eigenvalues i ∧ E.traceNorm / 2 = hE.eigenvalues i := by
  cases Subsingleton.elim (inferInstance : DecidableEq I) (Classical.decEq I)
  classical
  have hsum : (∑ i, hE.eigenvalues i) = 0 := by
    simpa only [htr, Complex.re_sum, Complex.ofReal_re, Complex.zero_re] using!
      congrArg Complex.re hE.sum_eigenvalues_eq_trace
  by_cases hp : ∃ i, 0 < hE.eigenvalues i
  · obtain ⟨i, hi⟩ := hp
    right
    refine ⟨i, hi, ?_⟩
    have hterm (j : I) : |hE.eigenvalues j| =
        -hE.eigenvalues j + if j = i then 2 * hE.eigenvalues i else 0 := by
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl, abs_of_pos hi]
        ring
      · have hj : hE.eigenvalues j ≤ 0 := by
          by_contra hn
          exact hji (hunique j i (lt_of_not_ge hn) hi)
        rw [if_neg hji, abs_of_nonpos hj, add_zero]
    rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hE]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum]
    simp
  · left
    have hn (i : I) : hE.eigenvalues i ≤ 0 := by
      exact le_of_not_gt fun hi => hp ⟨i, hi⟩
    rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hE]
    simp_rw [abs_of_nonpos (hn _)]
    rw [Finset.sum_neg_distrib, hsum]
    norm_num

omit [DecidableEq I] in

theorem quadratic_re_le_of_entrywise_norm
    (A : Matrix I I ℂ) (v : Qatlib.Foundations.PureStateMath.QState I) (s : ℝ)
    (hv : Qatlib.Foundations.PureStateMath.Normalized v) (hs : 0 ≤ s)
    (hbound : ∀ i j, ‖A i j‖ ≤ s * ‖v i‖ * ‖v j‖)
    (x : Qatlib.Foundations.PureStateMath.QState I) (hx : Qatlib.Foundations.PureStateMath.Normalized x) : (Qatlib.Foundations.PureStateMath.Inner x (A *ᵥ x)).re ≤ s := by
  have hform : Qatlib.Foundations.PureStateMath.Inner x (A *ᵥ x) =
      ∑ i, ∑ j, star (x i) * A i j * x j := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.mulVec, dotProduct,
        Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : I => ‖v i‖) (fun i : I => ‖x i‖)
  have hc : (∑ i, ‖v i‖ * ‖x i‖) ^ 2 ≤ 1 := by
    simpa only [show (∑ i, ‖v i‖ ^ 2) = 1 from hv,
      show (∑ i, ‖x i‖ ^ 2) = 1 from hx, one_mul] using hcauchy
  have hfactor : (∑ i, ∑ j, ‖x i‖ * (s * ‖v i‖ * ‖v j‖) * ‖x j‖) =
      s * (∑ i, ‖v i‖ * ‖x i‖) ^ 2 := by
    rw [pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (Qatlib.Foundations.PureStateMath.Inner x (A *ᵥ x)).re ≤ ‖Qatlib.Foundations.PureStateMath.Inner x (A *ᵥ x)‖ := Complex.re_le_norm _
    _ = ‖∑ i, ∑ j, star (x i) * A i j * x j‖ := by rw [hform]
    _ ≤ ∑ i, ‖∑ j, star (x i) * A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖star (x i) * A i j * x j‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ = ∑ i, ∑ j, ‖x i‖ * ‖A i j‖ * ‖x j‖ := by simp only [norm_mul, norm_star]
    _ ≤ ∑ i, ∑ j, ‖x i‖ * (s * ‖v i‖ * ‖v j‖) * ‖x j‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound i j) (norm_nonneg _)) (norm_nonneg _)
    _ = s * (∑ i, ‖v i‖ * ‖x i‖) ^ 2 := hfactor
    _ ≤ s := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc hs

theorem halfTraceDistance_outerProduct_sub_le_of_entrywise
    (v : Qatlib.Foundations.PureStateMath.QState I) (σ : Matrix I I ℂ) (s : ℝ)
    (hv : Qatlib.Foundations.PureStateMath.Normalized v) (hσ : σ.PosSemidef)
    (htr : Matrix.trace σ = 1) (hs : 0 ≤ s)
    (hreal : ∀ i j, ((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j).im = 0)
    (hnonneg : ∀ i j, 0 ≤ ((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j).re)
    (hbound : ∀ i j,
      ((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j).re ≤ s * ‖v i‖ * ‖v j‖) :
    Matrix.traceNorm (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) / 2 ≤ s := by
  have hE : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ).IsHermitian :=
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_isHermitian v).sub hσ.isHermitian
  have htrace : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ).trace = 0 := by
    rw [Matrix.trace_sub, (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density hv).2, htr,
        sub_self]
  have hnorm (i j : I) : ‖(Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j‖ ≤ s * ‖v i‖ * ‖v j‖ := by
    have hre : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j =
        (((Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) i j).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hreal i j
    rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg i j)]
    exact hbound i j
  rcases Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound.halfTraceNorm_eq_positive_eigenvalue_or_zero (Qatlib.Foundations.PureStateMath.Reflection.outerProduct v - σ) hE htrace
      (Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound.pureTarget_sub_positive_eigenvalue_unique v σ hσ hE) with hz | ⟨i, _, hi⟩
  · rw [hz]
    exact hs
  · rw [hi, hE.eigenvalues_eq i]
    apply Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound.quadratic_re_le_of_entrywise_norm _ v s hv hs hnorm
    exact (Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec _).mpr
      (hE.eigenvectorBasis.orthonormal.1 i)

end Qatlib.Concepts.MixedFidelity.FidelityMetric.PureTargetEntrywiseBound
