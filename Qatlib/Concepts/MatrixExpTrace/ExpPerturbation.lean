/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option warningAsError false
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

theorem norm_trace_mul_le (A B : Matrix I I ℂ) :
    ‖Matrix.trace (A * B)‖ ≤ ‖A‖ * Matrix.traceNorm B :=
  (Matrix.abs_trace_le_traceNorm _).trans (Matrix.traceNorm_mul_le_opNorm_traceNorm A B)

theorem exp_trace_eq_sum (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (Matrix.trace (NormedSpace.exp H)).re = ∑ i, Real.exp (orderedHermitianValues hH i) := by
  let U := Unitary.toUnits hH.eigenvectorUnitary
  have hd : H = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
      (↑U⁻¹ : Matrix I I ℂ) := hH.spectral_theorem
  conv_lhs => rw [hd, Matrix.exp_units_conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Units.inv_mul, Matrix.one_mul, Matrix.exp_diagonal, Matrix.trace_diagonal,
    Complex.re_sum, Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_re]
  exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))).symm.sum_comp
    (fun i => Real.exp (orderedHermitianValues hH i))

theorem exp_trace_le (H K : Matrix I I ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (Matrix.trace (NormedSpace.exp K)).re ≤
      Real.exp ‖H - K‖ * (Matrix.trace (NormedSpace.exp H)).re := by
  rw [exp_trace_eq_sum H hH, exp_trace_eq_sum K hK, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw := (ordered_hermitian_weyl_and_hoffman_wielandt I K H hK hH).1 i
  rw [norm_sub_rev K H] at hw
  linarith [(abs_le.mp hw).2]

theorem schatten_one (A : Matrix I I ℂ) : schattenNorm A 1 = Matrix.traceNorm A := by
  rw [schattenNorm_eq_sum_singularValues_rpow A (by norm_num),
    Matrix.traceNorm_eq_sum_singularValues]
  simp

theorem schatten_mul_le_op (A B : Matrix I I ℂ) (p : ℝ) (hp : 0 < p) :
    schattenNorm (A * B) p ≤ ‖A‖ * schattenNorm B p := by
  have hbound (i : Fin (Fintype.card I)) : singularValuesSorted A i ≤ ‖A‖ := by
    have hc : 0 < Fintype.card I := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    letI : NeZero (Fintype.card I) := ⟨hc.ne'⟩
    apply ((singularValuesSorted_antitone A) (Fin.zero_le i)).trans
    change singularValuesSorted A ⟨0, hc⟩ ≤ ‖A‖
    rw [singularValuesSorted_zero_eq_sup A hc, Finset.sup'_le_iff]
    exact fun j _ => Matrix.singularValues_le_opNorm A j
  rw [schattenNorm_eq_sum_singularValues_rpow _ hp,
    schattenNorm_eq_sum_singularValues_rpow _ hp,
    sum_singularValues_rpow_eq_sum_sorted (A * B) p,
    sum_singularValues_rpow_eq_sum_sorted B p]
  calc
    _ ≤ (∑ i : Fin (Fintype.card I), singularValuesSorted A i ^ p *
        singularValuesSorted B i ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg
        (singularValuesSorted_nonneg _ _) _) (sum_rpow_singularValues_mul_le A B hp)
        (by positivity)
    _ ≤ (∑ i : Fin (Fintype.card I), ‖A‖ ^ p * singularValuesSorted B i ^ p) ^ (1 / p) := by
      apply Real.rpow_le_rpow
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg
          (Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _)
          (Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _)
      · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (singularValuesSorted_nonneg _ _) (hbound i) hp.le)
          (Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _)
      · positivity
    _ = _ := by
      rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg A) _)
        (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _),
        ← Real.rpow_mul (norm_nonneg A), mul_one_div_cancel hp.ne', Real.rpow_one]

section Nonempty
variable [Nonempty I]

omit [Nonempty I] in

theorem hermitian_exp_mat (H : HermitianMat I ℂ) : H.exp.mat = NormedSpace.exp H.mat := by
  rw [HermitianMat.exp, HermitianMat.mat_cfc]
  letI : ContinuousFunctionalCalculus ℝ (Matrix I I ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  exact CFC.real_exp_eq_normedSpace_exp H.H

omit [Nonempty I] in

theorem schatten_exp_inv (H : HermitianMat I ℂ) (s : ℝ) (hs : 0 < s) :
    schattenNorm (NormedSpace.exp (s • H.mat)) (1 / s) =
      (Matrix.trace (NormedSpace.exp H.mat)).re ^ s := by
  rw [← HermitianMat.mat_smul, ← hermitian_exp_mat,
    schattenNorm_hermitian_pow (s • H).exp_nonneg (by positivity)]
  have he : (s • H).exp ^ (1 / s) = H.exp := by
    rw [HermitianMat.rpow_eq_cfc, HermitianMat.exp,
      ← HermitianMat.cfc_const_mul_id (r := s), ← HermitianMat.cfc_comp_apply,
      ← HermitianMat.cfc_comp_apply]
    congr 1
    funext x
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [he, one_div_one_div, HermitianMat.trace_eq_re_trace, hermitian_exp_mat]
  rfl

theorem exp_trace_pos (H : HermitianMat I ℂ) :
    0 < (Matrix.trace (NormedSpace.exp H.mat)).re := by
  have h := HermitianMat.trace_pos H.exp_pos
  rw [HermitianMat.trace_eq_re_trace, hermitian_exp_mat] at h
  exact h

theorem product_path_bound (H K : HermitianMat I ℂ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Matrix.traceNorm (NormedSpace.exp ((1 - t) • H.mat) * (K.mat - H.mat) *
      NormedSpace.exp (t • K.mat)) ≤
      ‖H.mat - K.mat‖ * (Matrix.trace (NormedSpace.exp H.mat)).re *
        Real.exp (t * ‖H.mat - K.mat‖) := by
  let Z := (Matrix.trace (NormedSpace.exp H.mat)).re
  have hZ : 0 < Z := exp_trace_pos H
  have hKZ : 0 ≤ (Matrix.trace (NormedSpace.exp K.mat)).re := (exp_trace_pos K).le
  have hδ : ‖K.mat - H.mat‖ = ‖H.mat - K.mat‖ := norm_sub_rev _ _
  have hholder := schattenNorm_mul_le (NormedSpace.exp ((1-t) • H.mat))
    ((K.mat-H.mat) * NormedSpace.exp (t • K.mat))
    (r := 1) (p := 1/(1-t)) (q := 1/t) (by norm_num) (by positivity) (by positivity)
    (by simp)
  rw [schatten_one, ← Matrix.mul_assoc] at hholder
  have hideal := schatten_mul_le_op (K.mat-H.mat) (NormedSpace.exp (t • K.mat))
    (1/t) (by positivity)
  rw [schatten_exp_inv H (1-t) (by linarith)] at hholder
  rw [schatten_exp_inv K t ht, hδ] at hideal
  calc
    _ ≤ Z ^ (1-t) * (‖H.mat-K.mat‖ *
        (Matrix.trace (NormedSpace.exp K.mat)).re ^ t) :=
      hholder.trans (mul_le_mul_of_nonneg_left hideal (Real.rpow_nonneg hZ.le _))
    _ ≤ Z ^ (1-t) * (‖H.mat-K.mat‖ * (Real.exp ‖H.mat-K.mat‖ * Z) ^ t) := by
      gcongr
      exact exp_trace_le H.mat K.mat H.H K.H
    _ = _ := by
      rw [Real.mul_rpow (Real.exp_pos _).le hZ.le, ← Real.exp_mul]
      have hz : Z ^ (1-t) * Z ^ t = Z := by
        rw [← Real.rpow_add hZ, sub_add_cancel, Real.rpow_one]
      calc
        _ = ‖H.mat-K.mat‖ * (Z ^ (1-t) * Z ^ t) * Real.exp (‖H.mat-K.mat‖ * t) := by ring
        _ = _ := by rw [hz]; simp only [Z, mul_comm t]

omit [Nonempty I] in

theorem hasDerivAt_product_path (H K : Matrix I I ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((1-s) • H) * NormedSpace.exp (s • K))
      (NormedSpace.exp ((1-t) • H) * (K-H) * NormedSpace.exp (t • K)) t := by
  have hsub : HasDerivAt (fun s : ℝ => 1-s) (-1) t := by
    simpa using! (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hh := (hasDerivAt_exp_smul_const H (1-t)).scomp t hsub
  have hk := hasDerivAt_exp_smul_const' K t
  convert! hh.mul hk using 1
  simp only [Function.comp_def, neg_smul, one_smul]
  noncomm_ring

theorem unitary_trace_exp_sub_le (H K : HermitianMat I ℂ) (U : Matrix.unitaryGroup I ℂ) :
    (Matrix.trace (U.val * (NormedSpace.exp K.mat - NormedSpace.exp H.mat))).re ≤
      (Real.exp ‖H.mat-K.mat‖ - 1) * (Matrix.trace (NormedSpace.exp H.mat)).re := by
  let T : Matrix I I ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap
  let Z := (Matrix.trace (NormedSpace.exp H.mat)).re
  let δ := ‖H.mat-K.mat‖
  let P := fun t : ℝ => NormedSpace.exp ((1-t) • H.mat) * NormedSpace.exp (t • K.mat)
  let D := fun t : ℝ => NormedSpace.exp ((1-t) • H.mat) * (K.mat-H.mat) *
    NormedSpace.exp (t • K.mat)
  let f := fun t : ℝ => T (U.val * P t) - Z * Real.exp (t * δ)
  let f' := fun t : ℝ => T (U.val * D t) - Z * (Real.exp (t * δ) * δ)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hP := (hasDerivAt_product_path H.mat K.mat t).const_mul U.val
    have hT := T.hasFDerivAt.comp_hasDerivAt t hP
    have he := ((hasDerivAt_id t).mul_const δ).exp.const_mul Z
    simpa only [Function.id_def, one_mul] using! hT.sub he
  have hnU : ‖U.val‖ = 1 := CStarRing.norm_coe_unitary U
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hb := product_path_bound H K t ht.1 ht.2
    have htest := (Complex.re_le_norm (Matrix.trace (U.val * D t))).trans
      (norm_trace_mul_le U.val (D t))
    rw [hnU, one_mul] at htest
    change T (U.val * D t) ≤ Matrix.traceNorm (D t) at htest
    change Matrix.traceNorm (D t) ≤ δ * Z * Real.exp (t * δ) at hb
    change T (U.val * D t) - Z * (Real.exp (t * δ) * δ) ≤ 0
    nlinarith
  have he := hanti (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [f, P] at he
  simp only [sub_self, zero_smul, one_smul, NormedSpace.exp_zero,
    zero_mul, Real.exp_zero, mul_one, one_mul, sub_zero] at he
  change (Matrix.trace (U.val * NormedSpace.exp K.mat)).re - Z * Real.exp δ ≤
    (Matrix.trace (U.val * NormedSpace.exp H.mat)).re - Z at he
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  change _ ≤ (Real.exp δ - 1) * Z
  nlinarith

end Nonempty

theorem noncommuting_exp_trace_norm :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H K : Matrix I I ℂ),
      H.IsHermitian → K.IsHermitian →
      Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) ≤
        (Real.exp ‖H-K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re := by
  intro I _ inst H K hH hK
  cases Subsingleton.elim inst (Classical.decEq I)
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    letI := h
    simp [Subsingleton.elim H 0, Subsingleton.elim K 0, Matrix.trace]
  | inr h =>
    letI := h
    obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U
      (NormedSpace.exp K - NormedSpace.exp H)).1
    have hb := unitary_trace_exp_sub_le ⟨H, hH⟩ ⟨K, hK⟩ U
    change (Matrix.trace (U.val * (NormedSpace.exp K - NormedSpace.exp H))).re ≤
      (Real.exp ‖H-K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re at hb
    rw [hU] at hb
    have hn : Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) =
        Matrix.traceNorm (NormedSpace.exp K - NormedSpace.exp H) := by
      rw [← Matrix.traceNorm_neg, neg_sub]
    exact hn.trans_le hb

theorem trace_duality_exp_consumer :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ),
      ‖Matrix.trace (A * B)‖ ≤ ‖A‖ * Matrix.traceNorm B) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (H K A : Matrix I I ℂ),
      H.IsHermitian → K.IsHermitian →
      ‖Matrix.trace (A * (NormedSpace.exp H - NormedSpace.exp K))‖ ≤
        ‖A‖ * (Real.exp ‖H-K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re) := by
  constructor
  · intro I _ _ A B
    exact norm_trace_mul_le A B
  · intro I _ _ H K A hH hK
    exact (norm_trace_mul_le A _).trans (by
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left
        (noncommuting_exp_trace_norm I H K hH hK) (norm_nonneg A))

end Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
