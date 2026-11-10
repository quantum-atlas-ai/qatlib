/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixtureComposition
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorLeft
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ReferenceError.RefTraceError

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable def mixtureAccessDistance {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U V : J → Operator D) : ℝ :=
  ∑ j, d.prob j * ‖U j - V j‖

noncomputable def referenceMixture {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  ChannelMixture d (fun j => TensorGate (U j) (1 : Operator r)) ρ

noncomputable def referenceMixturePower {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r n : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  (referenceMixture d U r)^[n] ρ

noncomputable def channelMixtureMap {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) : Operator D →ₗ[ℂ] Operator D where
  toFun ρ := ChannelMixture d U ρ
  map_add' ρ σ := channelMixture_add d U ρ σ
  map_smul' c ρ := channelMixture_smul d U c ρ

noncomputable def mixturePowerMap {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) : ℕ → (Operator D →ₗ[ℂ] Operator D)
  | 0 => LinearMap.id
  | n + 1 => (mixturePowerMap d U n).comp (channelMixtureMap d U)

noncomputable def mixturePowerChannel {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ℕ → QuantumChannel D D
  | 0 => QuantumChannel.id D
  | n + 1 => (mixturePowerChannel d U hU n).comp (unitaryMixtureInstrument d U hU).forget

theorem tensorGate_one_unitary {D R : ℕ} {U : Operator D}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    TensorGate U (1 : Operator R) ∈ Matrix.unitaryGroup (Fin D × Fin R) ℂ := by
  have hU' : U * Uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff.mp hU)
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, tensorGate_conjTranspose,
    tensorGate_mul, Matrix.conjTranspose_one, hU', Matrix.one_mul, tensorGate_one]

set_option maxHeartbeats 400000 in

theorem finite_reference_unitary_traceNorm {D : ℕ} (U : Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (TensorGate U (1 : Operator r) * ρ * (TensorGate U (1 : Operator r))ᴴ)
      = Matrix.traceNorm ρ := by
  have hUhU : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.mp hU)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hWhW : (TensorGate U (1 : Operator r))ᴴ * TensorGate U (1 : Operator r) = 1 := by
    rw [tensorGate_conjTranspose, tensorGate_mul, hUhU, Matrix.conjTranspose_one,
      Matrix.one_mul, tensorGate_one]
  have hnorm : ‖TensorGate U (1 : Operator r)‖ ≤ 1 := by
    rw [l2_norm_tensorGate]
    exact (mul_le_mul (l2_norm_unitary_le_one hU) l2_norm_one_le
      (norm_nonneg (1 : Operator r)) zero_le_one).trans_eq (mul_one 1)
  have hnormH : ‖(TensorGate U (1 : Operator r))ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hnorm
  refine le_antisymm (Matrix.traceNorm_sandwich_le hnorm hnormH) ?_
  have hcollapse : (TensorGate U (1 : Operator r))ᴴ *
      (TensorGate U (1 : Operator r) * ρ * (TensorGate U (1 : Operator r))ᴴ) *
      TensorGate U (1 : Operator r) = ρ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWhW, Matrix.one_mul, Matrix.mul_assoc,
      hWhW, Matrix.mul_one]
  refine le_trans (le_of_eq (congrArg Matrix.traceNorm hcollapse.symm))
    (Matrix.traceNorm_sandwich_le hnormH hnorm)

private lemma conj_conj_sub {n : Type} [Fintype n] (W X ρ : Matrix n n ℂ) :
    W * ρ * Wᴴ - X * ρ * Xᴴ
      = (W - X) * ρ * Wᴴ + X * ρ * (W - X)ᴴ := by
  have step1 : (W - X) * ρ * Wᴴ = W * ρ * Wᴴ - X * ρ * Wᴴ := by
    rw [Matrix.sub_mul, Matrix.sub_mul]
  have step2 : X * ρ * (W - X)ᴴ = X * ρ * Wᴴ - X * ρ * Xᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub]
  rw [step1, step2, sub_add_sub_cancel]

private lemma l2_tensorGate_sub_le {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (A B : Matrix I I ℂ) :
    ‖TensorGate A (1 : Matrix J J ℂ) - TensorGate B (1 : Matrix J J ℂ)‖ ≤ ‖A - B‖ := by
  rw [tensorGate_sub_left, l2_norm_tensorGate]
  have h2 : (0 : ℝ) ≤ ‖A - B‖ := norm_nonneg (A - B)
  have h3 : ‖(1 : Matrix J J ℂ)‖ ≤ 1 := l2_norm_one_le
  have h4 : ‖A - B‖ * ‖(1 : Matrix J J ℂ)‖ ≤ ‖A - B‖ * 1 :=
    mul_le_mul_of_nonneg_left h3 h2
  exact h4.trans_eq (mul_one _)

set_option maxHeartbeats 400000 in

theorem finite_reference_conjugation_error {D : ℕ} (U V : Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (TensorGate U (1 : Operator r) * ρ * (TensorGate U (1 : Operator r))ᴴ -
      TensorGate V (1 : Operator r) * ρ * (TensorGate V (1 : Operator r))ᴴ) ≤
      2 * ‖U - V‖ * Matrix.traceNorm ρ := by
  have hnormU : ‖TensorGate U (1 : Operator r)‖ ≤ 1 := by
    rw [l2_norm_tensorGate]
    exact (mul_le_mul (l2_norm_unitary_le_one hU) l2_norm_one_le
      (norm_nonneg (1 : Operator r)) zero_le_one).trans_eq (mul_one 1)
  have hnormV : ‖TensorGate V (1 : Operator r)‖ ≤ 1 := by
    rw [l2_norm_tensorGate]
    exact (mul_le_mul (l2_norm_unitary_le_one hV) l2_norm_one_le
      (norm_nonneg (1 : Operator r)) zero_le_one).trans_eq (mul_one 1)
  have hnormUH : ‖(TensorGate U (1 : Operator r))ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hnormU
  have hnormUV : ‖TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r)‖
      ≤ ‖U - V‖ := l2_tensorGate_sub_le U V
  have hnormUVH : ‖(TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r))ᴴ‖
      ≤ ‖U - V‖ := le_trans (le_of_eq (Matrix.l2_opNorm_conjTranspose _)) hnormUV
  have hsplit : TensorGate U (1 : Operator r) * ρ * (TensorGate U (1 : Operator r))ᴴ
        - TensorGate V (1 : Operator r) * ρ * (TensorGate V (1 : Operator r))ᴴ
      = (TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r)) *
          (ρ * (TensorGate U (1 : Operator r))ᴴ)
        + TensorGate V (1 : Operator r) *
          (ρ * ((TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r))ᴴ)) := by
    rw [conj_conj_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hsplit]
  refine le_trans (Matrix.traceNorm_add_le _ _) ?_
  have hA : Matrix.traceNorm ((TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r)) *
      (ρ * (TensorGate U (1 : Operator r))ᴴ)) ≤ ‖U - V‖ * Matrix.traceNorm ρ := by
    have h2 : Matrix.traceNorm (ρ * (TensorGate U (1 : Operator r))ᴴ)
        ≤ Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r))ᴴ‖ :=
      Matrix.traceNorm_mul_le_traceNorm_opNorm ρ _
    have h3 : Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r))ᴴ‖
        ≤ Matrix.traceNorm ρ * 1 :=
      mul_le_mul_of_nonneg_left hnormUH (Matrix.traceNorm_nonneg ρ)
    calc Matrix.traceNorm ((TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r)) *
          (ρ * (TensorGate U (1 : Operator r))ᴴ))
        ≤ ‖TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r)‖ *
            Matrix.traceNorm (ρ * (TensorGate U (1 : Operator r))ᴴ) :=
              Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
      _ ≤ ‖U - V‖ * Matrix.traceNorm (ρ * (TensorGate U (1 : Operator r))ᴴ) :=
            mul_le_mul_of_nonneg_right hnormUV (Matrix.traceNorm_nonneg _)
      _ ≤ ‖U - V‖ * (Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r))ᴴ‖) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg (U - V))
      _ ≤ ‖U - V‖ * (Matrix.traceNorm ρ * 1) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg (U - V))
      _ = ‖U - V‖ * Matrix.traceNorm ρ := by rw [mul_one]
  have hB : Matrix.traceNorm (TensorGate V (1 : Operator r) *
      (ρ * ((TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r))ᴴ)))
      ≤ Matrix.traceNorm ρ * ‖U - V‖ := by
    have h2 : Matrix.traceNorm (ρ * ((TensorGate U (1 : Operator r)
        - TensorGate V (1 : Operator r))ᴴ))
        ≤ Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r)
          - TensorGate V (1 : Operator r))ᴴ‖ :=
      Matrix.traceNorm_mul_le_traceNorm_opNorm ρ _
    have h3 : Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r)
        - TensorGate V (1 : Operator r))ᴴ‖ ≤ Matrix.traceNorm ρ * ‖U - V‖ :=
      mul_le_mul_of_nonneg_left hnormUVH (Matrix.traceNorm_nonneg ρ)
    calc Matrix.traceNorm (TensorGate V (1 : Operator r) *
          (ρ * ((TensorGate U (1 : Operator r) - TensorGate V (1 : Operator r))ᴴ)))
        ≤ ‖TensorGate V (1 : Operator r)‖ *
            Matrix.traceNorm (ρ * ((TensorGate U (1 : Operator r)
              - TensorGate V (1 : Operator r))ᴴ)) :=
              Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
      _ ≤ 1 * Matrix.traceNorm (ρ * ((TensorGate U (1 : Operator r)
            - TensorGate V (1 : Operator r))ᴴ)) :=
            mul_le_mul_of_nonneg_right hnormV (Matrix.traceNorm_nonneg _)
      _ ≤ 1 * (Matrix.traceNorm ρ * ‖(TensorGate U (1 : Operator r)
            - TensorGate V (1 : Operator r))ᴴ‖) :=
            mul_le_mul_of_nonneg_left h2 (zero_le_one)
      _ ≤ 1 * (Matrix.traceNorm ρ * ‖U - V‖) :=
            mul_le_mul_of_nonneg_left h3 (zero_le_one)
      _ = Matrix.traceNorm ρ * ‖U - V‖ := by rw [one_mul]
  exact le_trans (add_le_add hA hB) (le_of_eq (by ring))

private theorem traceNorm_sum_le {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type}
    [Fintype n] (f : ι → Matrix n n ℂ) :
    Matrix.traceNorm (∑ i, f i) ≤ ∑ i, Matrix.traceNorm (f i) := by
    have main : ∀ s : Finset ι,
        Matrix.traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Matrix.traceNorm (f i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, Matrix.traceNorm_zero]
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          exact le_trans (Matrix.traceNorm_add_le _ _) (add_le_add (le_refl _) ih)
    exact main Finset.univ

private lemma traceNorm_smul_ofReal_nonneg {n : Type} [Fintype n] {p : ℝ} (hp : 0 ≤ p)
    (X : Matrix n n ℂ) : Matrix.traceNorm ((p : ℂ) • X) = p * Matrix.traceNorm X := by
  rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]

theorem referenceMixture_apply {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixture d U r ρ
      = ∑ j, (d.prob j : ℂ) • (TensorGate (U j) (1 : Operator r) * ρ *
          (TensorGate (U j) (1 : Operator r))ᴴ) :=
  rfl

theorem finite_reference_mixture_contraction {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (referenceMixture d U r ρ) ≤ Matrix.traceNorm ρ := by
  rw [referenceMixture_apply]
  refine le_trans (traceNorm_sum_le _) ?_
  have hterm : ∀ j : J, Matrix.traceNorm ((d.prob j : ℂ) •
      (TensorGate (U j) (1 : Operator r) * ρ * (TensorGate (U j) (1 : Operator r))ᴴ))
      = d.prob j * Matrix.traceNorm ρ := fun j => by
    rw [traceNorm_smul_ofReal_nonneg (d.nonneg j),
      finite_reference_unitary_traceNorm (U j) r ρ (hU j)]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, d.sum_one, one_mul]

theorem finite_reference_mixture_error {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U V : J → Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (referenceMixture d U r ρ - referenceMixture d V r ρ) ≤
      2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ := by
  have hsplit : referenceMixture d U r ρ - referenceMixture d V r ρ
      = ∑ j, (d.prob j : ℂ) • (TensorGate (U j) (1 : Operator r) * ρ *
          (TensorGate (U j) (1 : Operator r))ᴴ
          - (TensorGate (V j) (1 : Operator r) * ρ *
            (TensorGate (V j) (1 : Operator r))ᴴ)) := by
    rw [referenceMixture_apply, referenceMixture_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
  rw [hsplit]
  refine le_trans (traceNorm_sum_le _) ?_
  have hterm : ∀ j : J, Matrix.traceNorm ((d.prob j : ℂ) •
      (TensorGate (U j) (1 : Operator r) * ρ * (TensorGate (U j) (1 : Operator r))ᴴ
        - (TensorGate (V j) (1 : Operator r) * ρ *
          (TensorGate (V j) (1 : Operator r))ᴴ)))
      ≤ d.prob j * (2 * ‖U j - V j‖ * Matrix.traceNorm ρ) := fun j => by
    rw [traceNorm_smul_ofReal_nonneg (d.nonneg j)]
    exact mul_le_mul_of_nonneg_left
      (finite_reference_conjugation_error (U j) (V j) r ρ (hU j) (hV j)) (d.nonneg j)
  have hsum : ∑ j, (d.prob j * ‖U j - V j‖) * (2 * Matrix.traceNorm ρ)
      = 2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ := by
    simp only [mixtureAccessDistance]
    rw [(Finset.sum_mul (Finset.univ : Finset J)
      (fun j => d.prob j * ‖U j - V j‖) (2 * Matrix.traceNorm ρ)).symm]
    ring
  calc ∑ j, Matrix.traceNorm ((d.prob j : ℂ) •
        (TensorGate (U j) (1 : Operator r) * ρ * (TensorGate (U j) (1 : Operator r))ᴴ
          - (TensorGate (V j) (1 : Operator r) * ρ *
            (TensorGate (V j) (1 : Operator r))ᴴ)))
      ≤ ∑ j, d.prob j * (2 * ‖U j - V j‖ * Matrix.traceNorm ρ) :=
          Finset.sum_le_sum fun j _ => hterm j
    _ = ∑ j, (d.prob j * ‖U j - V j‖) * (2 * Matrix.traceNorm ρ) :=
          Finset.sum_congr rfl fun j _ => by ring
    _ = 2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ := hsum

theorem channelMixtureMap_eq_sum {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) :
    channelMixtureMap d U = ∑ j, (d.prob j : ℂ) • conjBranch (U j) := by
  apply LinearMap.ext
  intro ρ
  simp only [channelMixtureMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, conjBranch_apply, ChannelMixture]

theorem tensorLeft_channelMixtureMap {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (channelMixtureMap d U) ρ = referenceMixture d U r ρ := by
  rw [channelMixtureMap_eq_sum, tensorLeft_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [tensorLeft_smul, tensorLeft_conjBranch]

theorem tensorLeft_mixturePowerMap {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r n : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (mixturePowerMap d U n) ρ = referenceMixturePower d U r n ρ := by
  induction n generalizing ρ with
  | zero =>
      simp only [mixturePowerMap, tensorLeft_id, referenceMixturePower,
        Function.iterate_zero_apply]
  | succ n ih =>
      simp only [mixturePowerMap, tensorLeft_comp, ih, tensorLeft_channelMixtureMap]
      rfl

theorem finite_reference_mixture_instrument {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixture d U r ρ = tensorLeft ((unitaryMixtureInstrument d U hU).forget.map) ρ := by
  have hmap : (unitaryMixtureInstrument d U hU).forget.map = channelMixtureMap d U :=
    LinearMap.ext fun ρ' => unitaryMixture_forget d U hU ρ'
  rw [hmap, tensorLeft_channelMixtureMap d U r ρ]

theorem mixturePowerChannel_map {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (n : ℕ) :
    (mixturePowerChannel d U hU n).map = mixturePowerMap d U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hmap : (unitaryMixtureInstrument d U hU).forget.map = channelMixtureMap d U :=
        LinearMap.ext fun ρ' => unitaryMixture_forget d U hU ρ'
      have hcomp : ((mixturePowerChannel d U hU n).comp
          (unitaryMixtureInstrument d U hU).forget).map
          = (mixturePowerChannel d U hU n).map.comp
            (unitaryMixtureInstrument d U hU).forget.map := rfl
      show ((mixturePowerChannel d U hU n).comp
        (unitaryMixtureInstrument d U hU).forget).map = _
      rw [hcomp, ih, hmap]
      rfl

theorem tensorLeft_mixturePowerChannel {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (n r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft (mixturePowerChannel d U hU n).map ρ = referenceMixturePower d U r n ρ := by
  rw [mixturePowerChannel_map]
  exact tensorLeft_mixturePowerMap d U r n ρ

theorem finite_reference_mixture_iteration {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (n r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    (mixturePowerChannel d U hU n).map = mixturePowerMap d U n ∧
    tensorLeft (mixturePowerChannel d U hU n).map ρ = referenceMixturePower d U r n ρ ∧
    (ρ.PosSemidef → (referenceMixturePower d U r n ρ).PosSemidef) ∧
    Matrix.trace (referenceMixturePower d U r n ρ) = Matrix.trace ρ := by
  refine ⟨mixturePowerChannel_map d U hU n, tensorLeft_mixturePowerChannel d U hU n r ρ,
    ?_, ?_⟩
  · intro hρ
    rw [← tensorLeft_mixturePowerChannel d U hU n r ρ]
    exact tensorLeft_posSemidef (mixturePowerChannel d U hU n).completelyPositive hρ
  · rw [← tensorLeft_mixturePowerChannel d U hU n r ρ]
    exact tensorLeft_trace_map _ (mixturePowerChannel d U hU n).tracePreserving ρ

theorem referenceMixture_sub {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r : ℕ)
    (ρ σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixture d U r (ρ - σ) = referenceMixture d U r ρ - referenceMixture d U r σ := by
  rw [referenceMixture_apply, referenceMixture_apply, referenceMixture_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub]

theorem referenceMixturePower_sub {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r n : ℕ)
    (ρ σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixturePower d U r n (ρ - σ)
      = referenceMixturePower d U r n ρ - referenceMixturePower d U r n σ := by
  induction n generalizing ρ σ with
  | zero => rfl
  | succ n ih =>
      have hiter : ∀ x : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
          referenceMixturePower d U r (n + 1) x
            = referenceMixture d U r (referenceMixturePower d U r n x) :=
        fun x => Function.iterate_succ_apply' (referenceMixture d U r) n x
      rw [hiter, hiter, hiter, ih, referenceMixture_sub]

theorem referenceMixturePower_contraction {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (r n : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (referenceMixturePower d U r n ρ) ≤ Matrix.traceNorm ρ := by
  induction n generalizing ρ with
  | zero => exact le_rfl
  | succ n ih =>
      have hiter : referenceMixturePower d U r (n + 1) ρ
          = referenceMixturePower d U r n (referenceMixture d U r ρ) := rfl
      rw [hiter]
      exact le_trans (ih _) (finite_reference_mixture_contraction d U r ρ hU)

theorem finite_reference_iterated_mixture_error {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (U V : J → Operator D) (r n : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (referenceMixturePower d U r n ρ
      - referenceMixturePower d V r n ρ) ≤
      2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ := by
  induction n generalizing ρ with
  | zero =>
      have h0 : referenceMixturePower d U r 0 ρ = ρ := rfl
      have h0' : referenceMixturePower d V r 0 ρ = ρ := rfl
      rw [h0, h0', sub_self, Matrix.traceNorm_zero]
      simp
  | succ n ih =>
      have hstepU : referenceMixturePower d U r (n + 1) ρ
          = referenceMixture d U r (referenceMixturePower d U r n ρ) :=
        Function.iterate_succ_apply' (referenceMixture d U r) n ρ
      have hstepV : referenceMixturePower d V r (n + 1) ρ
          = referenceMixture d V r (referenceMixturePower d V r n ρ) :=
        Function.iterate_succ_apply' (referenceMixture d V r) n ρ
      have hsplit : referenceMixture d U r (referenceMixturePower d U r n ρ)
          - referenceMixture d V r (referenceMixturePower d V r n ρ)
          = (referenceMixture d U r (referenceMixturePower d U r n ρ)
              - referenceMixture d U r (referenceMixturePower d V r n ρ))
            + (referenceMixture d U r (referenceMixturePower d V r n ρ)
              - referenceMixture d V r (referenceMixturePower d V r n ρ)) := by
        rw [sub_add_sub_cancel]
      rw [hstepU, hstepV, hsplit]
      refine le_trans (Matrix.traceNorm_add_le _ _) ?_
      rw [← referenceMixture_sub]
      have h1 := finite_reference_mixture_contraction d U r
        (referenceMixturePower d U r n ρ - referenceMixturePower d V r n ρ) hU
      have h2 := finite_reference_mixture_error d U V r
        (referenceMixturePower d V r n ρ) hU hV
      have h3 : Matrix.traceNorm (referenceMixturePower d V r n ρ) ≤ Matrix.traceNorm ρ :=
        referenceMixturePower_contraction d V r n ρ hV
      have hfinal : 2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ
          + 2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ
          = 2 * ((n : ℝ) + 1) * mixtureAccessDistance d U V * Matrix.traceNorm ρ := by
        ring
      have hfirst : Matrix.traceNorm (referenceMixture d U r
          (referenceMixturePower d U r n ρ - referenceMixturePower d V r n ρ))
          ≤ 2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ :=
        le_trans h1 (ih ρ)
      have hΔ : (0 : ℝ) ≤ mixtureAccessDistance d U V := by
        simp only [mixtureAccessDistance]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (d.nonneg j) (norm_nonneg _)
      have hsecond : Matrix.traceNorm (referenceMixture d U r (referenceMixturePower d V r n ρ)
          - referenceMixture d V r (referenceMixturePower d V r n ρ))
          ≤ 2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ :=
        le_trans h2 (mul_le_mul_of_nonneg_left h3 (mul_nonneg zero_le_two hΔ))
      have hcast : 2 * ((n : ℝ) + 1) * mixtureAccessDistance d U V * Matrix.traceNorm ρ
          = 2 * ((n + 1 : ℕ) : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ := by
        push_cast
        ring
      calc Matrix.traceNorm (referenceMixture d U r
            (referenceMixturePower d U r n ρ - referenceMixturePower d V r n ρ))
            + Matrix.traceNorm (referenceMixture d U r (referenceMixturePower d V r n ρ)
              - referenceMixture d V r (referenceMixturePower d V r n ρ))
          ≤ (2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ)
            + (2 * mixtureAccessDistance d U V * Matrix.traceNorm ρ) :=
              add_le_add hfirst hsecond
        _ = 2 * ((n : ℝ) + 1) * mixtureAccessDistance d U V * Matrix.traceNorm ρ := hfinal
        _ = 2 * ((n + 1 : ℕ) : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm ρ :=
              hcast

theorem finite_reference_input_and_access_error {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (U V : J → Operator D) (r n : ℕ)
    (ρ σ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.traceNorm (referenceMixturePower d U r n ρ
      - referenceMixturePower d V r n σ) ≤
      Matrix.traceNorm (ρ - σ)
      + 2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm σ := by
  have hsplit : referenceMixturePower d U r n ρ - referenceMixturePower d V r n σ
      = (referenceMixturePower d U r n ρ - referenceMixturePower d U r n σ)
        + (referenceMixturePower d U r n σ - referenceMixturePower d V r n σ) := by
    rw [sub_add_sub_cancel]
  rw [hsplit]
  refine le_trans (Matrix.traceNorm_add_le _ _) ?_
  rw [← referenceMixturePower_sub]
  have h1 : Matrix.traceNorm (referenceMixturePower d U r n (ρ - σ))
      ≤ Matrix.traceNorm (ρ - σ) :=
    referenceMixturePower_contraction d U r n (ρ - σ) hU
  have h2 := finite_reference_iterated_mixture_error d U V r n σ hU hV
  exact add_le_add h1 h2

theorem finite_reference_observable_error {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (U V : J → Operator D) (r n : ℕ)
    (ρ σ M : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    |(Matrix.trace (M * referenceMixturePower d U r n ρ)).re -
      (Matrix.trace (M * referenceMixturePower d V r n σ)).re| ≤
      ‖M‖ * (Matrix.traceNorm (ρ - σ)
        + 2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm σ) := by
  have hre : (Matrix.trace (M * referenceMixturePower d U r n ρ)).re -
      (Matrix.trace (M * referenceMixturePower d V r n σ)).re
      = (Matrix.trace (M * (referenceMixturePower d U r n ρ
          - referenceMixturePower d V r n σ))).re := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub]
  rw [hre]
  have h1 : |(Matrix.trace (M * (referenceMixturePower d U r n ρ
      - referenceMixturePower d V r n σ))).re|
      ≤ Matrix.traceNorm (M * (referenceMixturePower d U r n ρ
        - referenceMixturePower d V r n σ)) :=
    le_trans (Complex.abs_re_le_norm _)
      (Matrix.abs_trace_le_traceNorm _)
  have h2 : Matrix.traceNorm (M * (referenceMixturePower d U r n ρ
      - referenceMixturePower d V r n σ))
      ≤ ‖M‖ * (Matrix.traceNorm (ρ - σ)
        + 2 * (n : ℝ) * mixtureAccessDistance d U V * Matrix.traceNorm σ) :=
    le_trans (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _)
      (mul_le_mul_of_nonneg_left
        (finite_reference_input_and_access_error d U V r n ρ σ hU hV) (norm_nonneg M))
  exact le_trans h1 h2

end Qatlib.Concepts.ReferenceError.RefTraceError
