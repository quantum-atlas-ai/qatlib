/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TruncDyson18.MainResults.SourceParameters
import Qatlib.Papers.TruncDyson18.MainResults.TruncationBudget
import Qatlib.Foundations.OperatorErrors.OperatorError

set_option backward.isDefEq.respectTransparency false

/-!
# Query and Gate Complexity of the Truncated-Dyson Simulator

This module proves the headline query- and gate-complexity bounds of
[Kieferova, Scherer, and Berry, 2019][KieferovaSchererBerry2019] (§II, Eqs. (2)–(3);
§VI, pp. 10–11):

* `truncationOrder_rate`: Dyson order rate `K ≤ C · L / log L` (Eq. (35)), where
  `L = log(d Hmax T / ε)`.
* `composite_error` and `segmentErrorSum_le`: telescoping segment-product error bound
  and total accuracy budget across `r` segments.
* `query_complexity`: oracle-query complexity `O(d² Hmax T · L / log L)` (Eq. (2)).
* `gateBracket_growth` and `gate_complexity`: elementary-gate complexity
  `O(d² Hmax T · (L / log L) · (L + B + n))` (Eq. (3)), where
  `B = log(HdotMax T / (ε d Hmax))`.
* `main_result`: combined statement of Eqs. (2)–(3).

## Main statements

* `truncationOrder_rate`
* `composite_error`
* `query_complexity`
* `gateBracket_growth`
* `gate_complexity`
* `main_result`

## References

* [Kieferova, Scherer, and Berry, 2019][KieferovaSchererBerry2019]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.TruncDyson18.MainResults.MainResult
open Qatlib.Papers.TruncDyson18.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Papers.TruncDyson18.MainResults Qatlib.Papers.TruncDyson18.MainResults
open Qatlib.Papers.TruncDyson18.MainResults.SourceParameters
open Qatlib.Papers.TruncDyson18.MainResults.TruncationBudget

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## Arithmetic helpers -/

/-- `r ≤ 8 d² Hmax T`: from `r ≤ 4λT` and `λ < 2d²Hmax`. -/
theorem segmentCount_le_eight (p : SourceParameters) (h : p.Regime) :
    (p.segmentCount : ℝ) ≤ 8 * ((p.d : ℝ)^2 * p.Hmax) * p.T := by
  have hr := p.segmentCount_le h
  have hl := p.lcuWeight_lt_two h
  have hP : (0 : ℝ) < (p.d : ℝ)^2 * p.Hmax :=
    mul_pos (pow_pos (p.d_cast_pos h) 2) h.Hmax_pos
  nlinarith [hr, hl, h.T_pos, hP]

/-- `r/ε ≤ 2^k`: the per-segment precision covers the whole error budget. -/
theorem ratio_le_two_pow (p : SourceParameters) (h : p.Regime) :
    (p.segmentCount : ℝ) / p.eps ≤ (2 : ℝ) ^ p.segmentPrecision := by
  have hrpos : (0 : ℝ) < (p.segmentCount : ℝ) / p.eps :=
    div_pos (by exact_mod_cast p.segmentCount_pos h) h.eps_pos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log ((p.segmentCount : ℝ) / p.eps)
      ≤ (p.segmentPrecision : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2pos).mp (p.le_segmentPrecision h)
  calc (p.segmentCount : ℝ) / p.eps
      = Real.exp (Real.log ((p.segmentCount : ℝ) / p.eps)) := (Real.exp_log hrpos).symm
    _ ≤ Real.exp ((p.segmentPrecision : ℝ) * Real.log 2) := Real.exp_le_exp_of_le hlog
    _ = (2 : ℝ) ^ p.segmentPrecision := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- `L/log L ≥ 1` for `L ≥ 2`. -/
theorem one_le_logScale_div_log (p : SourceParameters) (h : p.Regime) :
    1 ≤ p.logScale / Real.log p.logScale := by
  have hL := logScale_ge_two p h
  have hlogpos : 0 < Real.log p.logScale := Real.log_pos (by linarith)
  have hlog_le : Real.log p.logScale ≤ p.logScale := by
    have := Real.log_le_sub_one_of_pos (x := p.logScale) (by linarith)
    linarith
  rw [le_div_iff₀ hlogpos]
  linarith

/-- `log₂ L ≤ clog₂(k+2)`: the ceiling log of the segment precision dominates the
logarithmic scale, since `k + 2 ≥ L`. -/
theorem logScale_div_log_two_le_clog (p : SourceParameters) (h : p.Regime) :
    Real.log p.logScale / Real.log 2 ≤ (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < p.logScale := logScale_pos p h
  have hk2' : p.logScale ≤ ((p.segmentPrecision + 2 : ℕ) : ℝ) := by
    have h1 := logScale_le_segmentPrecision p h
    push_cast
    linarith
  have hpow : ((p.segmentPrecision + 2 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (Nat.clog 2 (p.segmentPrecision + 2)) := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) (p.segmentPrecision + 2)
    exact_mod_cast this
  have h1 : p.logScale ≤ (2 : ℝ) ^ (Nat.clog 2 (p.segmentPrecision + 2)) :=
    hk2'.trans hpow
  have h2 : Real.log p.logScale
      ≤ Real.log ((2 : ℝ) ^ (Nat.clog 2 (p.segmentPrecision + 2))) :=
    Real.log_le_log hLpos h1
  have h3 : Real.log ((2 : ℝ) ^ (Nat.clog 2 (p.segmentPrecision + 2)))
      = (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  rw [h3] at h2
  rw [div_le_iff₀ hlog2pos]
  linarith

/-! ## Eq. (35): the truncation-order rate -/

/-- Eq. (35) of arXiv:1805.00582v1 (p. 10): `K = Θ(log(λT/ε)/loglog(λT/ε))`,
in the concrete form `K ≤ C·L/log L`, `L = log(dHmaxT/ε)`. The native
factorial cutoff satisfies `K·⌈log₂(k+2)⌉ ≤ C₀(k+2)`
(`effectiveDysonCutoff_clog_rate`, itself from `factorial_taylor_native_cutoff_and_rate`);
`k + 2 ≤ 8L` (`segmentPrecision_le_eight`), `L ≤ k` and `log₂ L ≤ ⌈log₂(k+2)⌉`
convert this into the paper's real-log rate. The small-precision case uses the
crude cutoff bound `K ≤ 2k + 21`. -/
theorem truncationOrder_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
      (p.truncationOrder : ℝ) ≤ C * (p.logScale / Real.log p.logScale) := by
  obtain ⟨C₀, m0, hrate₀⟩ :=
    Qatlib.Concepts.InteractionEvo.MeanDerivGrid.effectiveDysonCutoff_clog_rate
  have hm0nonneg : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg m0
  refine ⟨max (8 * (C₀ : ℝ)) (2 * (m0 : ℝ) + 21), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * (m0 : ℝ) + 21) (le_max_right _ _)
  · intro p h
    have hL := logScale_ge_two p h
    have hLpos : 0 < p.logScale := logScale_pos p h
    have hlogpos : 0 < Real.log p.logScale := logLog_pos p h
    have hge1 := one_le_logScale_div_log p h
    by_cases hbig : m0 ≤ p.segmentPrecision
    · -- large-precision case: convert the integer rate
      have hnat := hrate₀ p.segmentPrecision hbig
      have hreal : (p.truncationOrder : ℝ) * (Nat.clog 2 (p.segmentPrecision + 2) : ℝ)
          ≤ (C₀ : ℝ) * ((p.segmentPrecision : ℝ) + 2) := by
        have h0 : ((p.truncationOrder * Nat.clog 2 (p.segmentPrecision + 2) : ℕ) : ℝ)
            ≤ ((C₀ * (p.segmentPrecision + 2) : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h0
        exact h0
      have hclog_ge := logScale_div_log_two_le_clog p h
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hclogpos : (0 : ℝ) < (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) := by
        have h1 : 0 < Real.log p.logScale / Real.log 2 := div_pos hlogpos hlog2pos
        linarith
      have hlog2Lpos : 0 < Real.log p.logScale / Real.log 2 := div_pos hlogpos hlog2pos
      have hstep1 : (p.truncationOrder : ℝ)
          ≤ (C₀ : ℝ) * (((p.segmentPrecision : ℝ) + 2) /
              (Nat.clog 2 (p.segmentPrecision + 2) : ℝ)) := by
        rw [← mul_div_assoc]
        rw [le_div_iff₀ hclogpos]
        linarith [hreal]
      have hk2 := segmentPrecision_le_eight p h
      have hq0 : ((p.segmentPrecision : ℝ) + 2) /
            (Nat.clog 2 (p.segmentPrecision + 2) : ℝ)
          ≤ ((p.segmentPrecision : ℝ) + 2) / (Real.log p.logScale / Real.log 2) := by
        rw [div_le_div_iff₀ hclogpos hlog2Lpos]
        have hnn : (0 : ℝ) ≤ (p.segmentPrecision : ℝ) + 2 := by positivity
        have := mul_le_mul_of_nonneg_left hclog_ge hnn
        linarith
      have hq1 : ((p.segmentPrecision : ℝ) + 2) / (Real.log p.logScale / Real.log 2)
          ≤ (8 * p.logScale) / (Real.log p.logScale / Real.log 2) :=
        div_le_div_of_nonneg_right hk2 hlog2Lpos.le
      have hden_le : Real.log p.logScale ≤ Real.log p.logScale / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        nlinarith [hlogpos, Real.log_two_lt_d9.le]
      have hq2 : (8 * p.logScale) / (Real.log p.logScale / Real.log 2)
          ≤ 8 * (p.logScale / Real.log p.logScale) := by
        have hquot : (8 * p.logScale) / (Real.log p.logScale / Real.log 2)
            ≤ (8 * p.logScale) / Real.log p.logScale := by
          rw [div_le_div_iff₀ hlog2Lpos hlogpos]
          exact mul_le_mul_of_nonneg_left hden_le (by positivity)
        calc (8 * p.logScale) / (Real.log p.logScale / Real.log 2)
            ≤ (8 * p.logScale) / Real.log p.logScale := hquot
          _ = 8 * (p.logScale / Real.log p.logScale) := mul_div_assoc _ _ _
      have hchain : ((p.segmentPrecision : ℝ) + 2) /
            (Nat.clog 2 (p.segmentPrecision + 2) : ℝ)
          ≤ 8 * (p.logScale / Real.log p.logScale) :=
        le_trans hq0 (le_trans hq1 hq2)
      have hKle : (p.truncationOrder : ℝ)
          ≤ (C₀ : ℝ) * (8 * (p.logScale / Real.log p.logScale)) :=
        calc (p.truncationOrder : ℝ)
            ≤ (C₀ : ℝ) * (((p.segmentPrecision : ℝ) + 2) /
                (Nat.clog 2 (p.segmentPrecision + 2) : ℝ)) := hstep1
          _ ≤ (C₀ : ℝ) * (8 * (p.logScale / Real.log p.logScale)) :=
              mul_le_mul_of_nonneg_left hchain (by positivity)
      have hCle : (C₀ : ℝ) * (8 * (p.logScale / Real.log p.logScale))
          ≤ max (8 * (C₀ : ℝ)) (2 * (m0 : ℝ) + 21) *
              (p.logScale / Real.log p.logScale) := by
        have h1 : (C₀ : ℝ) * (8 * (p.logScale / Real.log p.logScale))
            = (8 * (C₀ : ℝ)) * (p.logScale / Real.log p.logScale) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (le_of_lt (div_pos hLpos hlogpos))
      linarith [hKle, hCle]
    · -- small-precision case: crude cutoff bound and `L/log L ≥ 1`
      have hklt : p.segmentPrecision < m0 := not_le.mp hbig
      have hcut : p.truncationOrder = factorialTaylorCutoff (p.segmentPrecision + 10) := by
        unfold truncationOrder computedDysonCutoff
        rw [show p.segmentPrecision + 8 + 2 = p.segmentPrecision + 10 by omega]
      have hKnat : p.truncationOrder ≤ 2 * p.segmentPrecision + 21 := by
        rw [hcut]
        have := (factorial_taylor_native_cutoff_and_rate.1 (p.segmentPrecision + 10)).2.2.1
        omega
      have hKle2 : (p.truncationOrder : ℝ) ≤ 2 * (m0 : ℝ) + 21 := by
        have hcast : (p.truncationOrder : ℝ)
            ≤ ((2 * p.segmentPrecision + 21 : ℕ) : ℝ) := by exact_mod_cast hKnat
        have hkltR : (p.segmentPrecision : ℝ) < (m0 : ℝ) := by exact_mod_cast hklt
        push_cast at hcast
        linarith
      have h3 : 2 * (m0 : ℝ) + 21 ≤ max (8 * (C₀ : ℝ)) (2 * (m0 : ℝ) + 21) :=
        le_max_right _ _
      have h4 : max (8 * (C₀ : ℝ)) (2 * (m0 : ℝ) + 21)
          ≤ max (8 * (C₀ : ℝ)) (2 * (m0 : ℝ) + 21) *
              (p.logScale / Real.log p.logScale) :=
        le_mul_of_one_le_right
          (lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * (m0 : ℝ) + 21) h3).le hge1
      linarith [hKle2, h3, h4]

/-! ## §VI error composition over the `r` segments -/

/-- §VI (pp. 10--11), error synthesis: if each of the `r` segment macros `W j` is a
contraction (`‖W j‖ ≤ 1`) and approximates the exact segment propagator `U j` to
`δ` (`‖W j - U j‖ ≤ δ`), with the exact segment also a contraction, then the
composed macro is within `rδ` of the full evolution. The proof is the telescoping
identity `P_W·W - P_U·U = P_W(W-U) + (P_W-P_U)U` and the submultiplicativity of the
L2 operator norm; it is the matrix-macro core of the Low--Wiebe statement
`Qatlib.Concepts.InteractionEvo.SegmentProduct.Corollary4CompositeError`
specialized to the paper's time-ordered setting. The truncated Dyson word is not
literally a contraction (its norm is `≤ 1 + δ`), so the paper's `1 + O(δ)`
variant is a separate strengthening not covered by the underlying layer. -/
theorem composite_error {I : Type} [Fintype I] [DecidableEq I]
    (W U : ℕ → Matrix I I ℂ) (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hW : ∀ j, ‖W j‖ ≤ 1) (hU : ∀ j, ‖U j‖ ≤ 1)
    (hclose : ∀ j, ‖W j - U j‖ ≤ δ) :
    ‖((List.range r).map W).prod - ((List.range r).map U).prod‖ ≤ (r : ℝ) * δ := by
  have hprodW : ∀ n : ℕ, ‖((List.range n).map W).prod‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simpa using (l2_norm_one_le (I := I))
    | succ n ih =>
        rw [List.range_succ, List.map_append]
        simp only [List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one]
        calc ‖((List.range n).map W).prod * W n‖
            ≤ ‖((List.range n).map W).prod‖ * ‖W n‖ := norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul ih (hW n) (norm_nonneg _) (by norm_num)
          _ = 1 := mul_one 1
  induction r with
  | zero => simp
  | succ n ih =>
      have hWr : ((List.range (n + 1)).map W).prod
          = ((List.range n).map W).prod * W n := by
        rw [List.range_succ, List.map_append]
        simp
      have hUr : ((List.range (n + 1)).map U).prod
          = ((List.range n).map U).prod * U n := by
        rw [List.range_succ, List.map_append]
        simp
      rw [hWr, hUr]
      have hid : ((List.range n).map W).prod * W n - ((List.range n).map U).prod * U n
          = ((List.range n).map W).prod * (W n - U n) +
            (((List.range n).map W).prod - ((List.range n).map U).prod) * U n := by
        noncomm_ring
      rw [hid]
      have h1 : ‖((List.range n).map W).prod * (W n - U n)‖ ≤ 1 * δ := by
        calc ‖((List.range n).map W).prod * (W n - U n)‖
            ≤ ‖((List.range n).map W).prod‖ * ‖W n - U n‖ := norm_mul_le _ _
          _ ≤ 1 * δ := mul_le_mul (hprodW n) (hclose n) (norm_nonneg _) (by norm_num)
      have h2 : ‖(((List.range n).map W).prod - ((List.range n).map U).prod) * U n‖
          ≤ ((n : ℝ) * δ) * 1 := by
        calc ‖(((List.range n).map W).prod - ((List.range n).map U).prod) * U n‖
            ≤ ‖((List.range n).map W).prod - ((List.range n).map U).prod‖ * ‖U n‖ :=
              norm_mul_le _ _
          _ ≤ ((n : ℝ) * δ) * 1 :=
              mul_le_mul ih (hU n) (norm_nonneg _)
                (mul_nonneg (Nat.cast_nonneg n) hδ)
      calc ‖((List.range n).map W).prod * (W n - U n) +
            (((List.range n).map W).prod - ((List.range n).map U).prod) * U n‖
          ≤ ‖((List.range n).map W).prod * (W n - U n)‖ +
            ‖(((List.range n).map W).prod - ((List.range n).map U).prod) * U n‖ :=
            norm_add_le _ _
        _ ≤ 1 * δ + ((n : ℝ) * δ) * 1 := add_le_add h1 h2
        _ = ((n + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- The `r` per-segment `ε/r` budgets sum to `ε/64`: with `2^k ≥ r/ε` the segment
error `2^{-(k+6)}` gives `r·2^{-(k+6)} ≤ ε/64`. Together with the sixty-four in
`effectiveDysonParameters_error` this is the paper's total accuracy budget of §VI,
used as the `ε`-accuracy half of the main theorem. -/
theorem segmentErrorSum_le (p : SourceParameters) (h : p.Regime) :
    (p.segmentCount : ℝ) * (1 / 2 : ℝ) ^ (p.segmentPrecision + 6) ≤ p.eps / 64 := by
  have hratio := ratio_le_two_pow p h
  have hr : (p.segmentCount : ℝ) ≤ p.eps * (2 : ℝ) ^ p.segmentPrecision := by
    have hmul := mul_le_mul_of_nonneg_right hratio h.eps_pos.le
    rw [div_mul_cancel₀ _ h.eps_pos.ne'] at hmul
    simpa [mul_comm] using hmul
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ p.segmentPrecision := by positivity
  have hinv : ((1 : ℝ) / 2) ^ p.segmentPrecision = 1 / (2 : ℝ) ^ p.segmentPrecision := by
    rw [one_div, inv_pow, one_div]
  have hstep : (p.segmentCount : ℝ) * ((1 : ℝ) / 2) ^ p.segmentPrecision ≤ p.eps := by
    rw [hinv]
    have h1 : (p.segmentCount : ℝ) * (1 / (2 : ℝ) ^ p.segmentPrecision)
        ≤ (p.eps * (2 : ℝ) ^ p.segmentPrecision) * (1 / (2 : ℝ) ^ p.segmentPrecision) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    have h2 : (p.eps * (2 : ℝ) ^ p.segmentPrecision) * (1 / (2 : ℝ) ^ p.segmentPrecision)
        = p.eps := by
      rw [mul_assoc, one_div, mul_inv_cancel₀ hkpos.ne', mul_one]
    linarith [h1, h2.le]
  have hδ : (1 / 2 : ℝ) ^ (p.segmentPrecision + 6)
      = (1 / 2 : ℝ) ^ p.segmentPrecision / 64 := by
    rw [pow_add]
    norm_num
    ring
  calc (p.segmentCount : ℝ) * (1 / 2 : ℝ) ^ (p.segmentPrecision + 6)
      = ((p.segmentCount : ℝ) * (1 / 2 : ℝ) ^ p.segmentPrecision) / 64 := by
        rw [hδ]
        exact (mul_div_assoc _ _ _).symm
    _ ≤ p.eps / 64 := div_le_div_of_nonneg_right hstep (by norm_num)

/-! ## Query complexity, Eq. (2) -/

/-- The query ledger: `4rK ≤ 32·C_K·d²HmaxT·L/log L`. -/
theorem four_r_K_le (p : SourceParameters) (h : p.Regime) {C_K : ℝ} (_hC : 0 ≤ C_K)
    (hK : (p.truncationOrder : ℝ) ≤ C_K * (p.logScale / Real.log p.logScale)) :
    4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ)
      ≤ (32 * C_K) * ((p.d : ℝ)^2 * p.Hmax * p.T *
          (p.logScale / Real.log p.logScale)) := by
  have hr := segmentCount_le_eight p h
  have hX : (0 : ℝ) ≤ (p.d : ℝ)^2 * p.Hmax * p.T :=
    mul_nonneg (mul_nonneg (pow_nonneg (p.d_cast_pos h).le 2) h.Hmax_pos.le) h.T_pos.le
  have hKnn : (0 : ℝ) ≤ (p.truncationOrder : ℝ) := Nat.cast_nonneg _
  calc 4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ)
      = 4 * ((p.segmentCount : ℝ) * (p.truncationOrder : ℝ)) := by ring
    _ ≤ 4 * ((8 * ((p.d : ℝ)^2 * p.Hmax) * p.T) * (p.truncationOrder : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hr hKnn
    _ = 4 * (8 * ((p.d : ℝ)^2 * p.Hmax * p.T)) * (p.truncationOrder : ℝ) := by ring
    _ ≤ 4 * (8 * ((p.d : ℝ)^2 * p.Hmax * p.T)) *
          (C_K * (p.logScale / Real.log p.logScale)) := by
        apply mul_le_mul_of_nonneg_left hK
        nlinarith [hX]
    _ = (32 * C_K) * ((p.d : ℝ)^2 * p.Hmax * p.T *
          (p.logScale / Real.log p.logScale)) := by ring

/-- Eq. (2) of arXiv:1805.00582v1 (§II p. 2, derived in §VI p. 11): the number of
oracle queries of the truncated-Dyson simulator scales as
`O(d² Hmax T · log(dHmaxT/ε)/loglog(dHmaxT/ε))`. The concrete ledger is
`queryCount = 4rK` (Eq. (42): `r` segments times `K` Hamiltonian queries, with the
oblivious amplitude amplification repetition absorbed into the constant `4`). -/
theorem query_complexity :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
      (p.queryCount : ℝ) ≤ C * p.queryFormula := by
  obtain ⟨C_K, hC_K_pos, hK⟩ := truncationOrder_rate
  refine ⟨32 * C_K, by positivity, ?_⟩
  intro p h
  have hQ := four_r_K_le p h hC_K_pos.le (hK p h)
  have hcast : (p.queryCount : ℝ)
      = 4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ) := by
    unfold queryCount
    push_cast
    ring
  have hform : p.queryFormula
      = (p.d : ℝ)^2 * p.Hmax * p.T * (p.logScale / Real.log p.logScale) := by
    unfold queryFormula
    rw [mul_div_assoc]
  rw [hcast, hform]
  exact hQ

/-! ## Gate complexity, Eq. (3) -/

/-- Exponential bound `2k + 21 ≤ 2^(k + 5)` used to control the squared Dyson cutoff. -/
private theorem two_mul_add_twenty_one_le_pow : ∀ k : ℕ, 2 * k + 21 ≤ 2 ^ (k + 5)
  | 0 => by decide
  | k + 1 => by
      have ih := two_mul_add_twenty_one_le_pow k
      have hp : 2 ^ (k + 1 + 5) = 2 ^ (k + 5) * 2 := by
        rw [show k + 1 + 5 = (k + 5) + 1 by omega, pow_succ]
      omega

/-- Elementary ceiling-log bound `⌈log₂ m⌉ ≤ m`. -/
private theorem clog_two_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := m)).le

/-- Ceiling-log bound for the LCU decomposition size: `⌈log₂ L_decomp⌉ ≤ 3k`. -/
private theorem clog_decompositionSize_le (p : SourceParameters) (h : p.Regime) :
    Nat.clog 2 p.decompositionSize ≤ 3 * p.segmentPrecision := by
  apply Nat.clog_le_of_le_pow
  rw [p.decompositionSize_eq_ratio h]
  apply Nat.ceil_le.mpr
  push_cast
  let Z : ℝ := (p.d : ℝ) * p.Hmax * p.T / p.eps
  have hd_pos := p.d_cast_pos h
  have hd1 := p.one_le_d h
  have hHmax_pos := h.Hmax_pos
  have hT_pos := h.T_pos
  have heps_pos := h.eps_pos
  have hZ_nn : 0 ≤ Z :=
    div_nonneg (mul_nonneg (mul_nonneg hd_pos.le hHmax_pos.le) hT_pos.le) heps_pos.le
  have hd2_le_Z : (p.d : ℝ) ^ 2 ≤ Z := by
    dsimp [Z]
    rw [le_div_iff₀ heps_pos]
    nlinarith [h.sparse_regime, hd_pos.le]
  have hZ_le_pow : Z ≤ (2 : ℝ) ^ p.segmentPrecision := by
    refine le_trans ?_ (ratio_le_two_pow p h)
    dsimp [Z]
    apply div_le_div_of_nonneg_right _ heps_pos.le
    have hl := p.le_lcuWeight h
    have hs := p.segmentCount_ge h
    have hd_sq : (p.d : ℝ) ≤ (p.d : ℝ) ^ 2 := by nlinarith [hd1]
    have hstep1 : (p.d : ℝ) * p.Hmax ≤ p.lcuWeight :=
      (mul_le_mul_of_nonneg_right hd_sq hHmax_pos.le).trans hl
    have hstep2 : (p.d : ℝ) * p.Hmax * p.T ≤ p.lcuWeight * p.T :=
      mul_le_mul_of_nonneg_right hstep1 hT_pos.le
    have hlw_nn : 0 ≤ p.lcuWeight * p.T :=
      mul_nonneg (le_trans (mul_nonneg (sq_nonneg (p.d : ℝ)) hHmax_pos.le) hl) hT_pos.le
    linarith [hs, hstep2, hlw_nn]
  have hd2_pow : (p.d : ℝ) ^ 2 ≤ (2 : ℝ) ^ p.segmentPrecision := hd2_le_Z.trans hZ_le_pow
  have hd4_pow : (p.d : ℝ) ^ 4 ≤ ((2 : ℝ) ^ p.segmentPrecision) ^ 2 := by
    calc (p.d : ℝ) ^ 4 = ((p.d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ p.segmentPrecision) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hd2_pow 2
  calc (p.d : ℝ) ^ 5 * p.Hmax * p.T / p.eps
      = (p.d : ℝ) ^ 4 * Z := by dsimp [Z]; ring
    _ ≤ ((2 : ℝ) ^ p.segmentPrecision) ^ 2 * (2 : ℝ) ^ p.segmentPrecision :=
        mul_le_mul hd4_pow hZ_le_pow hZ_nn (by positivity)
    _ = (2 : ℝ) ^ (3 * p.segmentPrecision) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

/-- Ceiling-log bound for the dyadic time-grid size `M`:
`⌈log₂ M⌉ ≤ 2k + 2⌈B⌉ + 11`. -/
private theorem clog_gridSize_le (p : SourceParameters) (h : p.Regime) :
    Nat.clog 2 p.gridSize ≤ 2 * p.segmentPrecision + 2 * ⌈p.derivativeLog⌉₊ + 11 := by
  have hg_le : Nat.clog 2 p.gridSize ≤ p.gridBits :=
    Nat.clog_le_of_le_pow le_rfl
  refine hg_le.trans ?_
  unfold SourceParameters.gridBits
  apply Nat.clog_le_of_le_pow
  unfold computedDysonGridSize
  refine max_le (max_le ?_ ?_) ?_
  · exact Nat.one_le_pow _ _ (by norm_num)
  · have hcut : computedDysonCutoff (p.segmentPrecision + 8) ≤ 2 * p.segmentPrecision + 21 := by
      unfold computedDysonCutoff
      rw [show p.segmentPrecision + 8 + 2 = p.segmentPrecision + 10 by omega]
      have := (factorial_taylor_native_cutoff_and_rate.1 (p.segmentPrecision + 10)).2.2.1
      omega
    have hK_le : computedDysonCutoff (p.segmentPrecision + 8) ≤ 2 ^ (p.segmentPrecision + 5) :=
      hcut.trans (two_mul_add_twenty_one_le_pow p.segmentPrecision)
    calc (computedDysonCutoff (p.segmentPrecision + 8)) ^ 2
        ≤ (2 ^ (p.segmentPrecision + 5)) ^ 2 := Nat.pow_le_pow_left hK_le 2
      _ = 2 ^ (2 * p.segmentPrecision + 10) := by
          rw [← pow_mul]
          congr 1
          omega
      _ ≤ 2 ^ (2 * p.segmentPrecision + 2 * ⌈p.derivativeLog⌉₊ + 11) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  · apply Nat.ceil_le.mpr
    push_cast
    set b := ⌈p.derivativeLog⌉₊
    have hd_pos := p.d_cast_pos h
    have hd1 := p.one_le_d h
    have hHmax_pos := h.Hmax_pos
    have hT_pos := h.T_pos
    have heps_pos := h.eps_pos
    have hd4 : (1 : ℝ) ≤ (p.d : ℝ) ^ 4 := one_le_pow₀ hd1
    have ht_sq : p.segmentTime ^ 2 ≤ 1 / (4 * (p.d : ℝ) ^ 4 * p.Hmax ^ 2) := by
      calc p.segmentTime ^ 2
          ≤ (1 / (2 * ((p.d : ℝ) ^ 2 * p.Hmax))) ^ 2 :=
            pow_le_pow_left₀ (p.segmentTime_pos h).le (p.segmentTime_le h) 2
        _ = 1 / (4 * (p.d : ℝ) ^ 4 * p.Hmax ^ 2) := by ring
    have hcoeff : 16 * p.segmentTime ^ 2 * (p.HdotMax + p.Hmax ^ 2)
        ≤ 4 / (p.d : ℝ) ^ 4 + 4 * (p.HdotMax / ((p.d : ℝ) ^ 4 * p.Hmax ^ 2)) := by
      have hsum_nn : 0 ≤ p.HdotMax + p.Hmax ^ 2 :=
        add_nonneg h.HdotMax_nonneg (sq_nonneg p.Hmax)
      have hmul : 16 * p.segmentTime ^ 2 * (p.HdotMax + p.Hmax ^ 2)
          ≤ 16 * (1 / (4 * (p.d : ℝ) ^ 4 * p.Hmax ^ 2)) * (p.HdotMax + p.Hmax ^ 2) := by
        have h16 := mul_le_mul_of_nonneg_left ht_sq (by norm_num : (0 : ℝ) ≤ 16)
        exact mul_le_mul_of_nonneg_right h16 hsum_nn
      have hid : 16 * (1 / (4 * (p.d : ℝ) ^ 4 * p.Hmax ^ 2)) * (p.HdotMax + p.Hmax ^ 2)
          = 4 / (p.d : ℝ) ^ 4 + 4 * (p.HdotMax / ((p.d : ℝ) ^ 4 * p.Hmax ^ 2)) := by
        have hd_ne : (p.d : ℝ) ≠ 0 := hd_pos.ne'
        have hH_ne : p.Hmax ≠ 0 := hHmax_pos.ne'
        field_simp
        ring
      exact hmul.trans_eq hid
    have hterm1 : 4 / (p.d : ℝ) ^ 4 ≤ 4 := by
      rw [div_le_iff₀ (pow_pos hd_pos 4)]
      linarith
    have hterm2 : p.HdotMax / ((p.d : ℝ) ^ 4 * p.Hmax ^ 2) ≤ Real.exp p.derivativeLog := by
      by_cases hHdot0 : p.HdotMax = 0
      · rw [hHdot0, zero_div]
        exact (Real.exp_pos _).le
      · have hHdot_pos : 0 < p.HdotMax := lt_of_le_of_ne h.HdotMax_nonneg (Ne.symm hHdot0)
        have hden1_pos : 0 < (p.d : ℝ) ^ 4 * p.Hmax ^ 2 :=
          mul_pos (pow_pos hd_pos 4) (pow_pos hHmax_pos 2)
        have hden2_pos : 0 < p.eps * (p.d : ℝ) * p.Hmax :=
          mul_pos (mul_pos heps_pos hd_pos) hHmax_pos
        have hQ_pos : 0 < p.HdotMax * p.T / (p.eps * (p.d : ℝ) * p.Hmax) :=
          div_pos (mul_pos hHdot_pos hT_pos) hden2_pos
        unfold SourceParameters.derivativeLog
        rw [Real.exp_log hQ_pos]
        rw [div_le_div_iff₀ hden1_pos hden2_pos]
        have hHT_pos : 0 < p.Hmax * p.T := mul_pos hHmax_pos hT_pos
        have hsp : (p.d : ℝ) * p.eps ≤ (p.d : ℝ) ^ 4 * (p.Hmax * p.T) :=
          h.sparse_regime.trans (le_mul_of_one_le_left hHT_pos.le hd4)
        have hmul := mul_le_mul_of_nonneg_left hsp (mul_pos hHdot_pos hHmax_pos).le
        calc p.HdotMax * (p.eps * (p.d : ℝ) * p.Hmax)
            = p.HdotMax * p.Hmax * ((p.d : ℝ) * p.eps) := by ring
          _ ≤ p.HdotMax * p.Hmax * ((p.d : ℝ) ^ 4 * (p.Hmax * p.T)) := hmul
          _ = p.HdotMax * p.T * ((p.d : ℝ) ^ 4 * p.Hmax ^ 2) := by ring
    have hexp_le : Real.exp p.derivativeLog ≤ (2 : ℝ) ^ (2 * b) := by
      have hB_le : p.derivativeLog ≤ (b : ℝ) := Nat.le_ceil _
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      have hB_log : p.derivativeLog ≤ ((2 * b : ℕ) : ℝ) * Real.log 2 := by
        have h2b : (b : ℝ) ≤ (2 * (b : ℝ)) * Real.log 2 := by nlinarith [hb_nn, hlog2]
        have hcast : ((2 * b : ℕ) : ℝ) * Real.log 2 = (2 * (b : ℝ)) * Real.log 2 := by
          push_cast; ring
        rw [hcast]
        exact hB_le.trans h2b
      calc Real.exp p.derivativeLog
          ≤ Real.exp (((2 * b : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hB_log
        _ = (2 : ℝ) ^ (2 * b) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hpow2b_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * b) := one_le_pow₀ (by norm_num)
    have hcoeff2 : 16 * p.segmentTime ^ 2 * (p.HdotMax + p.Hmax ^ 2) ≤ 8 * (2 : ℝ) ^ (2 * b) := by
      have hstep : 4 / (p.d : ℝ) ^ 4 + 4 * (p.HdotMax / ((p.d : ℝ) ^ 4 * p.Hmax ^ 2))
          ≤ 4 + 4 * (2 : ℝ) ^ (2 * b) :=
        add_le_add hterm1 (mul_le_mul_of_nonneg_left (hterm2.trans hexp_le) (by norm_num))
      have hstep2 : 4 + 4 * (2 : ℝ) ^ (2 * b) ≤ 8 * (2 : ℝ) ^ (2 * b) := by
        linarith [hpow2b_ge1]
      exact hcoeff.trans (hstep.trans hstep2)
    calc 16 * p.segmentTime ^ 2 * (p.HdotMax + p.Hmax ^ 2) * (2 : ℝ) ^ (p.segmentPrecision + 8)
        ≤ (8 * (2 : ℝ) ^ (2 * b)) * (2 : ℝ) ^ (p.segmentPrecision + 8) :=
          mul_le_mul_of_nonneg_right hcoeff2 (by positivity)
      _ = (2 : ℝ) ^ (p.segmentPrecision + 2 * b + 11) := by
          have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
          rw [h8, ← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ (2 : ℝ) ^ (2 * p.segmentPrecision + 2 * b + 11) :=
          pow_le_pow_right₀ (by norm_num) (by omega)

/-- §VI p. 11 of [Kieferova, Scherer, and Berry, 2019][KieferovaSchererBerry2019], the bracket
growth behind Eq. (3): the per-segment gate bracket
`⌈log₂ L_decomp⌉ + ⌈log₂ M⌉ + ⌈log₂(k+2)⌉ + n + 1` is `O(L + B + n)`, where
`L = log(d Hmax T / ε)` and `B = log(HdotMax T / (ε d Hmax))`. -/
theorem gateBracket_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
      ((Nat.clog 2 p.decompositionSize : ℝ) + (Nat.clog 2 p.gridSize : ℝ) +
          (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) + (p.n : ℝ) + 1)
        ≤ C * (p.logScale + p.derivativeLog + (p.n : ℝ)) := by
  refine ⟨56, by norm_num, ?_⟩
  intro p h
  have h1 : (Nat.clog 2 p.decompositionSize : ℝ) ≤ 3 * (p.segmentPrecision : ℝ) := by
    exact_mod_cast clog_decompositionSize_le p h
  have h2 : (Nat.clog 2 p.gridSize : ℝ) ≤
      2 * (p.segmentPrecision : ℝ) + 2 * (⌈p.derivativeLog⌉₊ : ℝ) + 11 := by
    exact_mod_cast clog_gridSize_le p h
  have h3 : (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) ≤ (p.segmentPrecision : ℝ) + 2 := by
    exact_mod_cast clog_two_le_self (p.segmentPrecision + 2)
  have hB_nn : 0 ≤ p.derivativeLog := h.deriv_log_nonneg
  have hB_ceil : (⌈p.derivativeLog⌉₊ : ℝ) ≤ p.derivativeLog + 1 :=
    (Nat.ceil_lt_add_one hB_nn).le
  have hk8 := segmentPrecision_le_eight p h
  have hL2 := logScale_ge_two p h
  have hn_nn : (0 : ℝ) ≤ (p.n : ℝ) := Nat.cast_nonneg p.n
  linarith

/-- The gate ledger: from `4rK ≤ 32·C_K·X·L/log L` and bracket `≤ C_B(L+B+n)`. -/
theorem gate_complexity :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
      (p.gateCount : ℝ) ≤ C * p.gateFormula := by
  obtain ⟨C_K, hC_K_pos, hK⟩ := truncationOrder_rate
  obtain ⟨C_B, hC_B_pos, hB⟩ := gateBracket_growth
  refine ⟨32 * C_K * C_B, by positivity, ?_⟩
  intro p h
  have hLpos : 0 < p.logScale := logScale_pos p h
  have hlogpos : 0 < Real.log p.logScale := logLog_pos p h
  have hLpnn : (0 : ℝ) ≤ p.logScale / Real.log p.logScale :=
    le_of_lt (div_pos hLpos hlogpos)
  have hX : (0 : ℝ) ≤ (p.d : ℝ)^2 * p.Hmax * p.T :=
    mul_nonneg (mul_nonneg (pow_nonneg (p.d_cast_pos h).le 2) h.Hmax_pos.le) h.T_pos.le
  have hQ := four_r_K_le p h hC_K_pos.le (hK p h)
  have hQnn : (0 : ℝ) ≤ 4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ) := by
    positivity
  have hBr := hB p h
  have hBrnn : (0 : ℝ) ≤ (Nat.clog 2 p.decompositionSize : ℝ) +
      (Nat.clog 2 p.gridSize : ℝ) + (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) +
      (p.n : ℝ) + 1 := by positivity
  have hQfact : (0 : ℝ) ≤ (32 * C_K) *
      ((p.d : ℝ)^2 * p.Hmax * p.T * (p.logScale / Real.log p.logScale)) :=
    mul_nonneg (by positivity) (mul_nonneg hX hLpnn)
  have hcast : (p.gateCount : ℝ)
      = (4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ)) *
        ((Nat.clog 2 p.decompositionSize : ℝ) + (Nat.clog 2 p.gridSize : ℝ) +
          (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) + (p.n : ℝ) + 1) := by
    unfold gateCount
    push_cast
    ring
  have hform : p.gateFormula
      = (p.d : ℝ)^2 * p.Hmax * p.T * (p.logScale / Real.log p.logScale) *
        (p.logScale + p.derivativeLog + (p.n : ℝ)) := rfl
  rw [hcast, hform]
  calc (4 * (p.segmentCount : ℝ) * (p.truncationOrder : ℝ)) *
        ((Nat.clog 2 p.decompositionSize : ℝ) + (Nat.clog 2 p.gridSize : ℝ) +
          (Nat.clog 2 (p.segmentPrecision + 2) : ℝ) + (p.n : ℝ) + 1)
      ≤ ((32 * C_K) * ((p.d : ℝ)^2 * p.Hmax * p.T *
            (p.logScale / Real.log p.logScale))) *
          (C_B * (p.logScale + p.derivativeLog + (p.n : ℝ))) :=
        mul_le_mul hQ hBr hBrnn hQfact
    _ = (32 * C_K * C_B) * ((p.d : ℝ)^2 * p.Hmax * p.T *
          (p.logScale / Real.log p.logScale) *
            (p.logScale + p.derivativeLog + (p.n : ℝ))) := by ring

/-! ## Combined Complexity Theorem (Eqs. (2)–(3)) -/

/-- Main result of [Kieferova, Scherer, and Berry, 2019][KieferovaSchererBerry2019] (§II, p. 2,
Eqs. (2)–(3)): there exist constants `C_q, C_g > 0` such that throughout `Regime`, the
truncated-Dyson simulator uses at most

* `C_q · d² Hmax T · log(dHmaxT/ε) / loglog(dHmaxT/ε)` oracle queries (Eq. (2)), and
* `C_g · d² Hmax T · (log(dHmaxT/ε) / loglog(dHmaxT/ε)) ·
   (log(dHmaxT/ε) + log(HdotMax T / (ε d Hmax)) + n)` additional elementary gates (Eq. (3)). -/
theorem main_result :
    (∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
        (p.queryCount : ℝ) ≤ C * p.queryFormula) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (p : SourceParameters), p.Regime →
        (p.gateCount : ℝ) ≤ C * p.gateFormula) :=
  ⟨query_complexity, gate_complexity⟩

end Qatlib.Papers.TruncDyson18.MainResults.MainResult
