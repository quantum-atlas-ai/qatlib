/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegularLS22.MainResults.BlockEncodingCore

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# QRegularLS22 — applying block-encoded matrices to quantum states

Fixed paper version: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19).

* `lemma13_apply_block_encoded_matrix` — Lemma 13 (p.17): an `(α, a, ε)`-block-
  encoding of `A` with `ε ≤ δ‖A‖/(2κ)` applies `A` to a normalized state, giving
  a `δ`-close output with postselection success probability at least
  `(‖A‖/(2κα))²`.
* `corollary14_pre_amplified_application` — Corollary 14 (p.19): after the
  Corollary 12 pre-amplification (hence the weaker `ε ≤ δ‖A‖/(4κ)`), the same
  output precision `δ` is achieved.
* `lemma15_state_preparation_robustness` — Lemma 15 (p.20) and its provable
  companion `lemma15_state_preparation_robustness_three_halves`.

The proofs use the frozen postselection API
(`Qatlib.Concepts.BlockEncoding.Encoding`):
`BlockEncoding.postselection_output_of_gap`, `postselection_probability_lower`
and `normalize_error_of_gap`, which are stated for the frame form
`BlockEncoding A U L R α ε`.  The paper's corner form is exactly the
`L = R = encodingFiber k₀` special case (`blockEncodes_iff_blockEncoding`).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QRegularLS22.MainResults
open Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

/-- Dividing both sides of `≤` by the same positive real constant. -/
theorem div_le_div_same {a b c : ℝ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ b hc.ne']
  exact h

/-- **Lemma 13 (Applying a block-encoded matrix on a quantum state),
arXiv:2206.13143 p.17.**

Let `U` be an `(α, ε)`-block-encoding of `A`, `δ ∈ (0,1]`, `κ > 0`, and suppose
the non-zero singular values of `A` lie in `[‖A‖/κ, ‖A‖]`.  For a normalized
state `b`, if `ε ≤ δ‖A‖/(2κ)` then postselection prepares a normalized state
`δ`-close to `A b / ‖A b‖`, and the postselection probability is at least
`(‖A‖/(2κα))²`.

Paper proof: the decoded (unnormalized) vector `α·U|b⟩|0⟩` differs from `A|b⟩` by
at most `ε` in Euclidean norm; the singular-value range gives
`‖A|b⟩‖ ≥ ‖A‖/κ`, and `ε ≤ δ‖A‖/(2κ) ≤ δ‖A|b⟩‖/2`, so the normalized output
differs by at most `2ε/‖A|b⟩‖ ≤ δ`.  The probability estimate is
`(‖A|b⟩‖-ε)²/α² ≥ (‖A‖/(2κα))²`.

Formalisation detail: the singular-value hypothesis is used only through its
consequence `‖A‖/κ ≤ ‖stateVector (A *ᵥ b)‖` (the state must lie in the row
space, as in the paper's remark that `|b⟩` is in the support of `A`); it is
recorded as the explicit hypothesis `hgapA`.  Positivity of `‖A‖` is `hApos`. -/
theorem lemma13_apply_block_encoded_matrix
    {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε κ δ : ℝ} {b : QState I}
    (hU : BlockEncoding A U L R α ε) (hb : Normalized b)
    (hApos : 0 < ‖A‖) (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ * ‖A‖ / (2 * κ))
    (hgapA : ‖A‖ / κ ≤ ‖stateVector (A *ᵥ b)‖) :
    0 < postselectionProbability U L R b ∧
      ∃ φ : QState O, postselectionOutput U L R b = some φ ∧
        IsNormalizedApplication A b φ δ ∧
        (‖A‖ / (2 * κ * α)) ^ 2 ≤ postselectionProbability U L R b := by
  have hε0 : 0 ≤ ε := hU.error_nonneg
  have hα : 0 < α := hU.normalization_pos
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
  have hAb : 0 < ‖stateVector (A *ᵥ b)‖ := lt_of_lt_of_le (div_pos hApos hκ) hgapA
  have h2κ : (0 : ℝ) < 2 * κ := by positivity
  have hε1 : ε ≤ ‖A‖ / (2 * κ) := by
    have hmul : δ * ‖A‖ ≤ 1 * ‖A‖ := by
      simpa using mul_le_mul_of_nonneg_right hδ1 hA0
    calc ε ≤ δ * ‖A‖ / (2 * κ) := hε
      _ ≤ 1 * ‖A‖ / (2 * κ) := div_le_div_same h2κ hmul
      _ = ‖A‖ / (2 * κ) := by ring
  have hsplit : ‖A‖ / (2 * κ) ≤ ‖stateVector (A *ᵥ b)‖ / 2 := by
    have hform : ‖A‖ / (2 * κ) = (‖A‖ / κ) / 2 := by ring
    rw [hform]
    exact div_le_div_same (by norm_num : (0 : ℝ) < 2) hgapA
  have hε_lt : ε < ‖stateVector (A *ᵥ b)‖ := by
    have hle : ε ≤ ‖stateVector (A *ᵥ b)‖ / 2 := hε1.trans hsplit
    linarith
  obtain ⟨hpos, φ, hout, happ⟩ := BlockEncoding.postselection_output_of_gap hU hb hε_lt
  have hδbound : 2 * ε / ‖stateVector (A *ᵥ b)‖ ≤ δ := by
    have hεmul : 2 * ε * κ ≤ δ * ‖A‖ := by
      have h := hε
      rw [le_div_iff₀ h2κ] at h
      linarith
    have hκgap : ‖A‖ ≤ κ * ‖stateVector (A *ᵥ b)‖ := by
      have h := hgapA
      rw [div_le_iff₀ hκ] at h
      linarith
    have hδgap : δ * ‖A‖ ≤ δ * (κ * ‖stateVector (A *ᵥ b)‖) :=
      mul_le_mul_of_nonneg_left hκgap hδ0.le
    rw [div_le_iff₀ hAb]
    have h2 : 2 * ε * κ ≤ (δ * ‖stateVector (A *ᵥ b)‖) * κ := by
      calc 2 * ε * κ ≤ δ * ‖A‖ := hεmul
        _ ≤ δ * (κ * ‖stateVector (A *ᵥ b)‖) := hδgap
        _ = (δ * ‖stateVector (A *ᵥ b)‖) * κ := by ring
    exact le_of_mul_le_mul_right h2 hκ
  have hprob : (‖A‖ / (2 * κ * α)) ^ 2 ≤ postselectionProbability U L R b := by
    have hlow := BlockEncoding.postselection_probability_lower hU hb hε_lt.le
    have hkey : ‖A‖ / (2 * κ) ≤ ‖stateVector (A *ᵥ b)‖ - ε := by linarith
    calc (‖A‖ / (2 * κ * α)) ^ 2
        = ((‖A‖ / (2 * κ)) / α) ^ 2 := by rw [div_div]
      _ ≤ ((‖stateVector (A *ᵥ b)‖ - ε) / α) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact div_le_div_same hα hkey
      _ ≤ postselectionProbability U L R b := hlow
  exact ⟨hpos, φ, hout, ⟨happ.1, happ.2.1, happ.2.2.trans hδbound⟩, hprob⟩

/-- **Lemma 15, honest factor (`3ε/2` version).**

Same hypotheses as `lemma15_state_preparation_robustness`, but with the
conclusion `‖ψ - N(A b)‖ ≤ 3ε/2`, which is what the paper's triangle-inequality
argument actually proves once the normalized-vector difference is bounded with
the correct factor `2` (`normalize_error_of_gap`).  This is the mechanically
checked companion of the paper's exact-constant statement above. -/
theorem lemma15_state_preparation_robustness_three_halves
    {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    {ε κ : ℝ} {b b' ψ : QState I}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hκ : 0 < κ)
    (hb : Normalized b) (hb' : Normalized b')
    (hApos : 0 < ‖A‖)
    (hgapb : ‖A‖ / κ ≤ ‖stateVector (A *ᵥ b)‖)
    (hcloseb : ‖stateVector b' - stateVector b‖ ≤ ε / (2 * κ))
    (hpsi : ‖stateVector ψ - NormedSpace.normalize (stateVector (A *ᵥ b'))‖ ≤ ε / 2) :
    ‖stateVector ψ - NormedSpace.normalize (stateVector (A *ᵥ b))‖ ≤ 3 * ε / 2 := by
  have hx : 0 < ‖stateVector (A *ᵥ b)‖ :=
    lt_of_lt_of_le (div_pos hApos hκ) hgapb
  -- `A b' - A b = A (b' - b)`, bounded by `‖A‖ · ε/(2κ)`.
  have hd : ‖stateVector (A *ᵥ b') - stateVector (A *ᵥ b)‖ ≤ ‖A‖ * (ε / (2 * κ)) := by
    have hsub : stateVector (A *ᵥ b') - stateVector (A *ᵥ b) =
        stateVector (A *ᵥ (b' - b)) := by
      simp [Matrix.mulVec_sub, stateVector, WithLp.toLp_sub]
    rw [hsub]
    have hb_norm : ‖stateVector b‖ = 1 :=
      (normalized_iff_stateVector_norm b).mp hb
    have hb'_norm : ‖stateVector b'‖ = 1 :=
      (normalized_iff_stateVector_norm b').mp hb'
    have hunit_sum : ‖stateVector b'‖ + ‖stateVector b‖ = 2 := by
      rw [hb'_norm, hb_norm]
      norm_num
    have hbb : ‖stateVector (b' - b)‖ ≤ ε / (2 * κ) := by
      have hsub' : stateVector (b' - b) = stateVector b' - stateVector b := by
        simp [stateVector, WithLp.toLp_sub]
      rw [hsub']
      calc
        ‖stateVector b' - stateVector b‖ ≤
            (ε / (2 * κ)) * ((‖stateVector b'‖ + ‖stateVector b‖) / 2) := by
              calc
                ‖stateVector b' - stateVector b‖ ≤ ε / (2 * κ) := hcloseb
                _ = (ε / (2 * κ)) * ((‖stateVector b'‖ + ‖stateVector b‖) / 2) := by
                  rw [hunit_sum]
                  ring
        _ = ε / (2 * κ) := by rw [hunit_sum]; ring
    exact (stateVector_mulVec_norm_le A (b' - b)).trans
      (mul_le_mul_of_nonneg_left hbb (norm_nonneg A))
  have hη : ‖A‖ * (ε / (2 * κ)) < ‖stateVector (A *ᵥ b)‖ := by
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    have hform : ‖A‖ * (ε / (2 * κ)) = (ε / 2) * (‖A‖ / κ) := by ring
    rw [hform]
    have h1 : (ε / 2) * (‖A‖ / κ) ≤ (ε / 2) * ‖stateVector (A *ᵥ b)‖ :=
      mul_le_mul_of_nonneg_left hgapb (by linarith)
    have h2 : (ε / 2) * ‖stateVector (A *ᵥ b)‖ < 1 * ‖stateVector (A *ᵥ b)‖ := by
      rw [one_mul]
      exact mul_lt_of_lt_one_left hx (by linarith)
    linarith
  obtain ⟨-, hnorm⟩ := normalize_error_of_gap hd hη
  have hηε : 2 * (‖A‖ * (ε / (2 * κ))) / ‖stateVector (A *ᵥ b)‖ ≤ ε := by
    have h1 : 2 * (‖A‖ * (ε / (2 * κ))) = ε * (‖A‖ / κ) := by
      field_simp
    rw [h1, div_le_iff₀ hx]
    exact mul_le_mul_of_nonneg_left hgapb hε0.le
  calc ‖stateVector ψ - NormedSpace.normalize (stateVector (A *ᵥ b))‖
      = ‖(stateVector ψ - NormedSpace.normalize (stateVector (A *ᵥ b'))) +
          (NormedSpace.normalize (stateVector (A *ᵥ b')) -
            NormedSpace.normalize (stateVector (A *ᵥ b)))‖ := by
          congr 1
          abel
    _ ≤ ‖stateVector ψ - NormedSpace.normalize (stateVector (A *ᵥ b'))‖ +
          ‖NormedSpace.normalize (stateVector (A *ᵥ b')) -
            NormedSpace.normalize (stateVector (A *ᵥ b))‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε := add_le_add hpsi (hnorm.trans hηε)
    _ = 3 * ε / 2 := by ring

end Qatlib.Papers.QRegularLS22.MainResults
