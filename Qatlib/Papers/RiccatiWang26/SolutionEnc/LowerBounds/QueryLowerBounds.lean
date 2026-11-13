/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# QueryLowerBounds — product lower bounds, hardness, and matching upper bounds

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized cores: Lemma H.2 (p. 122, block separation and query hybrid) and
Lemma H.3 (p. 122, selected-value readout), together with the arithmetic cores of (H.24).
The product lower bounds (Theorems 5.1–5.4), the single-control hardness results
(Theorems 5.6–5.7), Remark 5.5, Proposition H.4 and the main result (1.2) are not
formalized in this layer; no declaration below claims them.

The legacy `Solver F ε` records a declared query count and mathematical block-encoding
existence for each member of `F`; it has no oracle execution relation. The retained hybrid
lemma takes its hybrid estimate as an explicit assumption. The upper bounds would require the
existence of a block-encoding together with an `Õ` cost (the paper's (1.2)), which is not
constructed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.LowerBounds

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Legacy numerical solver contract: mathematical block-encoding existence
for each target and an independent declared query count. No oracle program or
execution relation is present, so this record alone certifies no complexity. -/
structure Solver {n : Type*} [Fintype n] [DecidableEq n]
    (F : Set (Sq n)) (ε : ℝ) where
  /-- Number of ancilla qubits. -/
  a : ℕ
  /-- Output normalization of the solution block-encoding. -/
  α : ℝ
  /-- Declared query annotation; no execution count is derived here. -/
  queries : ℝ
  queries_nonneg : 0 ≤ queries
  correct : ∀ X ∈ F, BlockEncodes X a α ε

/-! ## The ancilla-block separation inequality (Lemma H.2, Eq. (H.3)) -/

/-- The `⟨0|·|0⟩` ancilla block of a matrix acting on `Fin (2^a) × n`. -/
def ancBlock {n : Type*} [Fintype n] [DecidableEq n] (a : ℕ)
    (U : Matrix (Fin (2 ^ a) × n) (Fin (2 ^ a) × n) ℂ) : Sq n :=
  Matrix.of fun i j => U (ancZero a, i) (ancZero a, j)

/-- RiccatiWang26, Lemma H.2 (p. 122), second inequality of (H.3) (the solution-block
separation).  If two output unitaries encode `Y₁` and `Y₀` with the same public normalization
`αY` and decoded error at most `ε`, then
`‖Y₁ - Y₀‖ ≤ (‖B₁ - B₀‖ + 2ε)/αY` for `αY > 0`, equivalently
`αY ‖Y₁ - Y₀‖ - 2ε ≤ ‖B₁ - B₀‖`.
The source obtains it by adding and subtracting the two encoded blocks. -/
theorem block_separation {n : Type*} [Fintype n] [DecidableEq n] {a : ℕ}
    (Y1 Y0 : Sq n) (U1 U0 : Matrix (Fin (2 ^ a) × n) (Fin (2 ^ a) × n) ℂ)
    (αY ε : ℝ) (hα : 0 < αY)
    (h1 : ‖ancBlock a U1 - (αY : ℂ) • Y1‖ ≤ ε)
    (h0 : ‖ancBlock a U0 - (αY : ℂ) • Y0‖ ≤ ε) :
    ‖Y1 - Y0‖ ≤ (‖ancBlock a U1 - ancBlock a U0‖ + 2 * ε) / αY := by
  have hsplit : (αY : ℂ) • (Y1 - Y0) =
      (ancBlock a U1 - ancBlock a U0) +
        ((αY : ℂ) • Y1 - ancBlock a U1) + (ancBlock a U0 - (αY : ℂ) • Y0) := by
    rw [smul_sub]; abel
  have hnorm : αY * ‖Y1 - Y0‖ ≤ ‖ancBlock a U1 - ancBlock a U0‖ + 2 * ε := by
    calc αY * ‖Y1 - Y0‖ = ‖(αY : ℂ) • (Y1 - Y0)‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
      _ = ‖(ancBlock a U1 - ancBlock a U0) +
            ((αY : ℂ) • Y1 - ancBlock a U1) + (ancBlock a U0 - (αY : ℂ) • Y0)‖ := by
          rw [hsplit]
      _ ≤ ‖ancBlock a U1 - ancBlock a U0‖ +
            ‖(αY : ℂ) • Y1 - ancBlock a U1‖ + ‖ancBlock a U0 - (αY : ℂ) • Y0‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ ‖ancBlock a U1 - ancBlock a U0‖ + 2 * ε := by
          have h1' : ‖(αY : ℂ) • Y1 - ancBlock a U1‖ ≤ ε := by
            rw [← norm_neg, neg_sub]; exact h1
          have h0' : ‖ancBlock a U0 - (αY : ℂ) • Y0‖ ≤ ε := h0
          nlinarith
  rw [le_div_iff₀ hα]
  linarith

/-- RiccatiWang26, Lemma H.2 (p. 122), Eq. (H.3).  For `c ∈ {0,1}` let `Vc` be the output
unitary of one common coherent circuit using at most `q` calls to the oracles `Uc`.  If both
`Vc` encode the targets `Yc` with common public normalization `αY`, common signal space, and
decoded error at most `ε`, then
`αY‖Y₁ - Y₀‖ - 2ε ≤ q · max_j ‖U₁⁽ʲ⁾ - U₀⁽ʲ⁾‖` (the paper's (H.3) with the
normalization moved to the left).

`δ` is the maximum oracle difference, `hhybrid` is the source's hybrid/telescoping bound
`‖V₁ - V₀‖ ≤ q δ` (a product of `q` oracle calls), and `hcompress` is the elementary fact that
the ancilla block of the difference is no larger than the full output difference. -/
theorem lemma_H_2_query_hybrid {n : Type*} [Fintype n] [DecidableEq n] {a : ℕ}
    (Y1 Y0 : Sq n) (V1 V0 : Matrix (Fin (2 ^ a) × n) (Fin (2 ^ a) × n) ℂ)
    (αY ε q δ : ℝ) (hα : 0 < αY) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hhybrid : ‖V1 - V0‖ ≤ q * δ)
    (hcompress : ‖ancBlock a V1 - ancBlock a V0‖ ≤ ‖V1 - V0‖)
    (h1 : ‖ancBlock a V1 - (αY : ℂ) • Y1‖ ≤ ε)
    (h0 : ‖ancBlock a V0 - (αY : ℂ) • Y0‖ ≤ ε) :
    αY * ‖Y1 - Y0‖ - 2 * ε ≤ q * δ := by
  have hsep := block_separation Y1 Y0 V1 V0 αY ε hα h1 h0
  have h1' : αY * ‖Y1 - Y0‖ ≤ ‖ancBlock a V1 - ancBlock a V0‖ + 2 * ε := by
    rw [le_div_iff₀ hα] at hsep
    linarith
  linarith

/-! ## Product lower bounds (Theorems 5.1–5.4) -/

/-! ## Hardness for single-control instances (Theorems 5.6–5.7) -/

/-- Arithmetic core of (H.24): the DARE readout is exactly `p²/2`. -/
lemma dare_readout_upper (p r : ℝ) (hr : r = p ^ 2 / 2) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) :
r ≤ 1 / 18 := by
  rw [hr]; nlinarith

/-- Arithmetic core of (H.24): the DARE readout is exactly `p²/2`. -/
lemma dare_readout_lower (p r : ℝ) (hr : r = p ^ 2 / 2) (hp : 2 / 3 ≤ p) : 2 / 9 ≤ r := by
  rw [hr]; nlinarith

/-! ## Selected-value lemmas and actual normalization (H.3–H.4) -/

/-- Threshold arithmetic associated with Lemma H.3: a supplied scalar readout
`y` with assumed error `hy` distinguishes the two promised value ranges.
No measurement procedure or constant-query implementation is constructed. -/
theorem lemma_H_3_selected_value_oracle
    (X : Sq n) (x0 : n → ℂ) (αX ε gap tYes tNo : ℝ)
    (hα : 0 < αX) (hα1 : 1 ≤ αX) (hgap : 0 < gap) (hε : ε < gap / 4)
    (hyes : tYes - tNo = gap)
    (hpromise : tYes ≤ (star x0 ⬝ᵥ (X *ᵥ x0)).re ∨ (star x0 ⬝ᵥ (X *ᵥ x0)).re ≤ tNo)
    (y : ℝ) (hy : |y - (star x0 ⬝ᵥ (X *ᵥ x0)).re| ≤ ε / αX) :
    (tYes - gap / 2 ≤ y ↔ tYes ≤ (star x0 ⬝ᵥ (X *ᵥ x0)).re) := by
  set val := (star x0 ⬝ᵥ (X *ᵥ x0)).re with hval
  -- `ε ≥ 0` follows from the readout hypothesis `|y - val| ≤ ε / αX`.
  have hε0 : 0 ≤ ε := by
    have h0 : 0 ≤ ε / αX := le_trans (abs_nonneg _) hy
    have hmul : 0 ≤ ε / αX * αX := mul_nonneg h0 hα.le
    rwa [div_mul_cancel₀ _ hα.ne'] at hmul
  have hsmall : ε / αX < gap / 2 := by
    have hle : ε / αX ≤ ε := by
      rw [div_le_iff₀ hα]
      nlinarith [hα1, hε0]
    linarith
  have hy' : y - val ≤ ε / αX ∧ val - y ≤ ε / αX := by
    rw [abs_le] at hy
    constructor <;> linarith [hy.1, hy.2]
  constructor
  · intro h
    rcases hpromise with hv | hv
    · exact hv
    · exfalso
      nlinarith [hy'.2, hsmall, hyes, hv, h]
  · intro h
    nlinarith [hy'.1, hsmall, h]

/-! ## Main result (1.2) -/

end Qatlib.Papers.RiccatiWang26.SolutionEnc.LowerBounds
