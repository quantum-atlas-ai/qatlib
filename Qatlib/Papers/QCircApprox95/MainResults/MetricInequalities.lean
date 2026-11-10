/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.MetricCore
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.BornMetrics.FiniteStats

namespace Qatlib.Papers.QCircApprox95.MainResults

theorem lemma_two_one_mono {N A B : ℕ} (q : Fin N → Fin B) (r : Fin B → Fin A)
    (u v : Fin N → ℂ) :
    measDist (fun i => r (q i)) u v ≤ measDist q u v :=
  measDist_refine_le q r u v

theorem lemma_two_one_tv_le_two_norm (n l : ℕ) (hl : l ≤ n) (u v : Fin (2 ^ n) → ℂ)
    (hu : (∑ i, ‖u i‖ ^ 2) = 1) (hv : (∑ i, ‖v i‖ ^ 2) = 1) :
    vPrefix n l hl u v ≤ 2 * l2norm (u - v) := by
  exact measDist_le_two_l2 (prefixMap n l hl) u v hu hv

theorem lemma_two_two_weak_le_op {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    norm2k A k ≤ ‖A‖ := by
  exact column_norm_le_operator A k

theorem lemma_two_two_op_le_frob {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A‖ ≤ Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius A :=
  Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectral_operator_norm_le_frobenius A

theorem lemma_two_two_weak_mono {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {k k' : ℕ} :
    norm2k A k ≤ norm2k A (k + k') := by
  exact column_norm_mono A (Nat.le_add_right k k')

theorem lemma_two_two_tv_mono {n l l' k k' : ℕ} (hl : l ≤ n)
    (hll' : l + l' ≤ n) (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    maxPrefixTV n l hl U V k ≤ maxPrefixTV n (l + l') hll' U V (k + k') := by
  apply (maxPrefixTV_le_iff hl U V k _ (maxPrefixTV_nonneg hll' U V (k + k'))).mpr
  intro b hb
  exact (vPrefix_mono hl (Nat.le_add_right l l') hll' _ _).trans
    (maxPrefixTV_column_le hll' U V (k + k') b (by omega))

theorem lemma_two_two_tv_le_weak {n l k : ℕ} (hl : l ≤ n)
    (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    maxPrefixTV n l hl U V k ≤ 2 * norm2k (U - V) k := by
  apply (maxPrefixTV_le_iff hl U V k _ (mul_nonneg (by norm_num) (norm2k_nonneg _ _))).mpr
  intro b hb
  have h := measDist_le_two_l2 (prefixMap n l hl) (U *ᵥ ket b) (V *ᵥ ket b)
    (unitary_column_mass hU b) (unitary_column_mass hV b)
  refine h.trans ?_
  rw [← Matrix.sub_mulVec]
  exact mul_le_mul_of_nonneg_left (norm2k_column_le (U - V) k b hb) (by norm_num)

theorem lemma_three_opnorm {N : ℕ} (U1 U2 V1 V2 : Matrix (Fin N) (Fin N) ℂ)
    (_h1 : U1 ∈ Matrix.unitaryGroup (Fin N) ℂ) (h2 : U2 ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (h3 : V1 ∈ Matrix.unitaryGroup (Fin N) ℂ) (_h4 : V2 ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {δ ρ : ℝ} (hδ : ‖U1 - V1‖ ≤ δ) (hρ : ‖U2 - V2‖ ≤ ρ) :
    ‖U1 * U2 - V1 * V2‖ ≤ δ + ρ := by
  have key := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_rect_mul_sub_mul_le
    (I := Fin N) (J := Fin N) (K := Fin N) U1 V1 U2 V2
  have hU2 : ‖U2‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one h2
  have hV1 : ‖V1‖ ≤ 1 := Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one h3
  calc ‖U1 * U2 - V1 * V2‖
      ≤ ‖U1 - V1‖ * ‖U2‖ + ‖V1‖ * ‖U2 - V2‖ := key
    _ ≤ δ * 1 + 1 * ρ := by
        apply add_le_add
        · calc ‖U1 - V1‖ * ‖U2‖ ≤ δ * ‖U2‖ :=
                mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
            _ ≤ δ * 1 :=
                mul_le_mul_of_nonneg_left hU2 (le_trans (norm_nonneg _) hδ)
        · calc ‖V1‖ * ‖U2 - V2‖ ≤ 1 * ‖U2 - V2‖ :=
                mul_le_mul_of_nonneg_right hV1 (norm_nonneg _)
            _ ≤ 1 * ρ := mul_le_mul_of_nonneg_left hρ (by norm_num)
    _ = δ + ρ := by ring

theorem composition_error_mixed {N : ℕ} (U₁ U₂ V₁ V₂ : Matrix (Fin N) (Fin N) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV₂ : V₂ ∈ Matrix.unitaryGroup (Fin N) ℂ) (k : ℕ) :
    norm2k (U₁ * U₂ - V₁ * V₂) k ≤ ‖U₁ - V₁‖ + norm2k (U₂ - V₂) k := by
  have he : U₁ * U₂ - V₁ * V₂ = (U₁ - V₁) * V₂ + U₁ * (U₂ - V₂) := by
    noncomm_ring
  have hu : ‖U₁‖ ≤ 1 :=
    Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hU₁
  have hv : norm2k V₂ k ≤ 1 := (column_norm_le_operator V₂ k).trans
    (Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hV₂)
  rw [he]
  calc
    _ ≤ norm2k ((U₁ - V₁) * V₂) k + norm2k (U₁ * (U₂ - V₂)) k := norm2k_add_le _ _ _
    _ ≤ ‖U₁ - V₁‖ * norm2k V₂ k + ‖U₁‖ * norm2k (U₂ - V₂) k :=
      add_le_add (norm2k_mul_left_le _ _ _) (norm2k_mul_left_le _ _ _)
    _ ≤ ‖U₁ - V₁‖ * 1 + 1 * norm2k (U₂ - V₂) k := add_le_add
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hu (norm2k_nonneg _ _))
    _ = _ := by ring

end Qatlib.Papers.QCircApprox95.MainResults
