/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# InversePerturbation — Lemma A.2 and Proposition E.8

RiccatiWang26, arXiv:2609.37207v1.
Covers: Lemma A.2 (p. 68), Eq. (A.4); Proposition E.8 (p. 90), Eqs. (E.28)–(E.30).

`T⁻¹` in the source is written here as an explicit right/left inverse pair `(T, Tinv)` so
that the statement does not depend on the junk-value convention of `Ring.inverse`.  The
conclusion asserts the existence of the perturbed inverse together with both bounds; this
is literally the source's "`T + ΔT` is invertible and ..." with the inverse named.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Perturb

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- RiccatiWang26, Lemma A.2 (p. 68), Eq. (A.4).  If `T` is invertible with inverse `Tinv`,
`‖ΔT‖ ≤ η`, and `η‖Tinv‖ < 1`, then `T + ΔT` is invertible, and its inverse `Tinv'` satisfies
`‖Tinv'‖ ≤ ‖Tinv‖/(1-η‖Tinv‖)` and `‖Tinv' - Tinv‖ ≤ η‖Tinv‖²/(1-η‖Tinv‖)`.

The proof expands `T + ΔT = T(1 + Tinv ΔT)` and sums the Neumann series of `B = Tinv ΔT`,
which is the source's argument ("write `T + ΔT = T(I + T⁻¹ΔT)` and use the geometric series"). -/
theorem lemma_A_2_inverse_perturbation
    (T ΔT Tinv : Sq n) (η : ℝ)
    (hη : 0 ≤ η) (hright : T * Tinv = 1) (hleft : Tinv * T = 1)
    (hΔ : ‖ΔT‖ ≤ η) (hsmall : η * ‖Tinv‖ < 1) :
    ∃ Tinv' : Sq n,
      (T + ΔT) * Tinv' = 1 ∧ Tinv' * (T + ΔT) = 1 ∧
        ‖Tinv'‖ ≤ ‖Tinv‖ / (1 - η * ‖Tinv‖) ∧
        ‖Tinv' - Tinv‖ ≤ η * ‖Tinv‖ ^ 2 / (1 - η * ‖Tinv‖) := by
  classical
  set B : Sq n := Tinv * ΔT with hBdef
  -- `T + ΔT = T (1 + B)`
  have hTΔ : T + ΔT = T * (1 + B) := by
    rw [hBdef, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hright, Matrix.one_mul]
  have hBnorm : ‖B‖ ≤ ‖Tinv‖ * η := by
    rw [hBdef]
    exact (norm_mul_le Tinv ΔT).trans (mul_le_mul_of_nonneg_left hΔ (norm_nonneg Tinv))
  have hB : ‖B‖ < 1 := by
    nlinarith [hBnorm, hsmall, hη, norm_nonneg Tinv]
  -- the Neumann sum and its two inverse identities
  set S : Sq n := ∑' k : ℕ, (-B) ^ k with hSdef
  have hgeom : (1 + B) * S = 1 := by
    have h := mul_neg_geom_series (-B) (by simpa using hB)
    simpa [hSdef, sub_neg_eq_add] using h
  have hgeom' : S * (1 + B) = 1 := by
    have h := geom_series_mul_neg (-B) (by simpa using hB)
    simpa [hSdef, sub_neg_eq_add] using h
  have hright' : (T + ΔT) * (S * Tinv) = 1 := by
    calc (T + ΔT) * (S * Tinv) = (T * (1 + B)) * (S * Tinv) := by rw [hTΔ]
      _ = T * ((1 + B) * S) * Tinv := by noncomm_ring
      _ = 1 := by rw [hgeom, Matrix.mul_one, hright]
  have hleft' : (S * Tinv) * (T + ΔT) = 1 := by
    calc (S * Tinv) * (T + ΔT) = (S * Tinv) * (T * (1 + B)) := by rw [hTΔ]
      _ = (S * (Tinv * T)) * (1 + B) := by noncomm_ring
      _ = S * (1 + B) := by rw [hleft, Matrix.mul_one]
      _ = 1 := hgeom'
  refine ⟨S * Tinv, hright', hleft', ?_, ?_⟩
  · -- first bound: `‖S Tinv‖ ≤ ‖Tinv‖ / (1 - η‖Tinv‖)`
    have hSnorm : ‖S‖ ≤ (1 - ‖B‖)⁻¹ := by
      have := tsum_geometric_le_of_norm_lt_one (-B) (by simpa using hB)
      simpa [hSdef, CStarRing.norm_one] using this
    have hden : 0 < 1 - η * ‖Tinv‖ := by nlinarith [hsmall]
    have hden' : 0 < 1 - ‖B‖ := by nlinarith [hB]
    have hinvle : (1 - ‖B‖)⁻¹ ≤ (1 - η * ‖Tinv‖)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hden (by nlinarith [hBnorm])
    calc ‖S * Tinv‖ ≤ ‖S‖ * ‖Tinv‖ := norm_mul_le S Tinv
      _ ≤ (1 - ‖B‖)⁻¹ * ‖Tinv‖ :=
          mul_le_mul_of_nonneg_right hSnorm (norm_nonneg Tinv)
      _ ≤ (1 - η * ‖Tinv‖)⁻¹ * ‖Tinv‖ :=
          mul_le_mul_of_nonneg_right hinvle (norm_nonneg Tinv)
      _ = ‖Tinv‖ / (1 - η * ‖Tinv‖) := by rw [div_eq_mul_inv, mul_comm]
  · -- second bound: the series starts at `k = 1`
    have hdiff : S * Tinv - Tinv = ((-B) * S) * Tinv := by
      have hsucc : S - 1 = ∑' k : ℕ, (-B) ^ (k + 1) := by
        rw [hSdef]
        exact (geom_series_succ (-B) (by simpa using hB)).symm
      have hshift : (-B) * S = ∑' k : ℕ, (-B) ^ (k + 1) := by
        rw [hSdef]; exact geom_series_mul_shift (-B) (by simpa using hB)
      calc S * Tinv - Tinv = (S - 1) * Tinv := by rw [Matrix.sub_mul, Matrix.one_mul]
        _ = ((-B) * S) * Tinv := by rw [hsucc, ← hshift]
    have hden : 0 < 1 - η * ‖Tinv‖ := by nlinarith [hsmall]
    have hSnorm : ‖S‖ ≤ (1 - η * ‖Tinv‖)⁻¹ := by
      have h1 : ‖S‖ ≤ (1 - ‖B‖)⁻¹ := by
        have := tsum_geometric_le_of_norm_lt_one (-B) (by simpa using hB)
        simpa [hSdef, CStarRing.norm_one] using this
      have hden' : 0 < 1 - ‖B‖ := by nlinarith [hB]
      refine h1.trans ?_
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hden (by nlinarith [hBnorm])
    have hBn : ‖-B‖ = ‖B‖ := norm_neg B
    calc ‖S * Tinv - Tinv‖ = ‖((-B) * S) * Tinv‖ := by rw [hdiff]
      _ ≤ ‖(-B) * S‖ * ‖Tinv‖ := norm_mul_le _ _
      _ ≤ (‖-B‖ * ‖S‖) * ‖Tinv‖ := by
          gcongr
          exact norm_mul_le (-B) S
      _ ≤ (η * ‖Tinv‖ * (1 - η * ‖Tinv‖)⁻¹) * ‖Tinv‖ := by
          have hle : ‖B‖ ≤ η * ‖Tinv‖ := by nlinarith [hBnorm, hη, norm_nonneg Tinv]
          have hstep : ‖B‖ * ‖S‖ ≤ (η * ‖Tinv‖) * (1 - η * ‖Tinv‖)⁻¹ :=
            mul_le_mul hle hSnorm (norm_nonneg _) (by positivity)
          simpa [hBn] using mul_le_mul_of_nonneg_right hstep (norm_nonneg Tinv)
      _ = η * ‖Tinv‖ ^ 2 / (1 - η * ‖Tinv‖) := by
          field_simp

/-! ## Proposition E.8: RR construction from approximate inputs -/

/-- `‖E₁‖ = 1` for the upper coordinate embedding. -/
lemma E1_norm : ‖E1 n‖ = 1 := by
  have h1 : ‖(E1 n)ᴴ * E1 n‖ = 1 := by
    have hE : (E1 n)ᴴ * E1 n = 1 := by
      ext i j
      simp [E1, blockCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
        Matrix.one_apply, eq_comm]
    rw [hE]
    simp
  have h2 : ‖(E1 n)ᴴ * E1 n‖ = ‖E1 n‖ * ‖E1 n‖ :=
    Matrix.l2_opNorm_conjTranspose_mul_self (E1 n)
  have hn : 0 ≤ ‖E1 n‖ := norm_nonneg _
  nlinarith

/-- `‖E₂‖ = 1` for the lower coordinate embedding. -/
lemma E2_norm : ‖E2 n‖ = 1 := by
  have h1 : ‖(E2 n)ᴴ * E2 n‖ = 1 := by
    have hE : (E2 n)ᴴ * E2 n = 1 := by
      ext i j
      simp [E2, blockCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
        Matrix.one_apply, eq_comm]
    rw [hE]
    simp
  have h2 : ‖(E2 n)ᴴ * E2 n‖ = ‖E2 n‖ * ‖E2 n‖ :=
    Matrix.l2_opNorm_conjTranspose_mul_self (E2 n)
  have hn : 0 ≤ ‖E2 n‖ := norm_nonneg _
  nlinarith

/-- The graph embedding decomposes as `E₁ * I + E₂ * Q`. -/
lemma graph_eq_E1_add_E2 (Q : Sq n) :
    graph Q = E1 n * (1 : Sq n) + E2 n * Q := by
  ext i j
  rcases i with i | i <;>
    simp [graph, blockCol, E1, E2, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- Operator-norm bound `‖[I; Q]‖ ≤ 1 + ‖Q‖` for the graph embedding.  This is the
`√(1+‖Q‖²) ≤ 1+‖Q‖` input factor used in Proposition E.8's error budget (E.28). -/
lemma graph_norm_le (Q : Sq n) : ‖graph Q‖ ≤ 1 + ‖Q‖ := by
  calc ‖graph Q‖ = ‖E1 n * (1 : Sq n) + E2 n * Q‖ := by rw [graph_eq_E1_add_E2]
    _ ≤ ‖E1 n * (1 : Sq n)‖ + ‖E2 n * Q‖ := norm_add_le _ _
    _ ≤ ‖E1 n‖ * ‖(1 : Sq n)‖ + ‖E2 n‖ * ‖Q‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = 1 + ‖Q‖ := by rw [E1_norm, E2_norm]; simp

/-- The block row `[I G]` decomposes as `I * E₁* + G * E₂*`. -/
lemma blockRow_eq (G : Sq n) :
    blockRow (1 : Sq n) G = (1 : Sq n) * (E1 n)ᴴ + G * (E2 n)ᴴ := by
  ext i j
  rcases j with j | j <;>
    simp [blockRow, blockCol, E1, E2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

/-- Operator-norm bound `‖[I G]‖ ≤ 1 + ‖G‖` for the block row. -/
lemma blockRow_norm_le (G : Sq n) : ‖blockRow (1 : Sq n) G‖ ≤ 1 + ‖G‖ := by
  have hE1 : ‖(E1 n)ᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, E1_norm]
  have hE2 : ‖(E2 n)ᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, E2_norm]
  calc ‖blockRow (1 : Sq n) G‖ = ‖(1 : Sq n) * (E1 n)ᴴ + G * (E2 n)ᴴ‖ := by rw [blockRow_eq]
    _ ≤ ‖(1 : Sq n) * (E1 n)ᴴ‖ + ‖G * (E2 n)ᴴ‖ := norm_add_le _ _
    _ ≤ ‖(1 : Sq n)‖ * ‖(E1 n)ᴴ‖ + ‖G‖ * ‖(E2 n)ᴴ‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = 1 + ‖G‖ := by rw [hE1, hE2]; simp

/-- RiccatiWang26, Proposition E.8 (p. 90), Eq. (E.28), input-error term.  The lift correction
`[I;Q] ΔA⁻¹ [I,G]` produced by an approximate inverse of `A` with error `‖ΔA⁻¹‖ ≤ εAinv` has
operator norm at most `(1+‖Q‖)(1+‖G‖) εAinv`.  This is the input-error contribution to the
right-hand side of (E.28); an implementation error `εSFimpl` adds to it by the triangle
inequality, and the E.7 recovery then applies verbatim. -/
theorem proposition_E_8_rr_lift_error_budget
    (Q G ΔAinv : Sq n) (εAinv : ℝ) (hΔ : ‖ΔAinv‖ ≤ εAinv) :
    ‖graph Q * ΔAinv * blockRow (1 : Sq n) G‖ ≤ (1 + ‖Q‖) * (1 + ‖G‖) * εAinv := by
  have hQ := graph_norm_le Q
  have hG := blockRow_norm_le G
  have hε : 0 ≤ εAinv := le_trans (norm_nonneg ΔAinv) hΔ
  calc ‖graph Q * ΔAinv * blockRow (1 : Sq n) G‖
      = ‖graph Q * (ΔAinv * blockRow (1 : Sq n) G)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖graph Q‖ * ‖ΔAinv * blockRow (1 : Sq n) G‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖graph Q‖ * (‖ΔAinv‖ * ‖blockRow (1 : Sq n) G‖) := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 + ‖Q‖) * (εAinv * (1 + ‖G‖)) := by gcongr
    _ = (1 + ‖Q‖) * (1 + ‖G‖) * εAinv := by ring

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Perturb
