/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver18.MainResults.GateComplexity.TaylorGateComplexity

Source result for Claim `c003` of QLinearSolver18, fixed arXiv:1805.10549v2
(29 Nov 2018), Subasi--Somma--Orsucci, "Gate-based implementations", p. 9.

The paper compiles the second (gap-amplified) algorithm with the truncated
Taylor-series Hamiltonian simulation of Ref. [20]:

* Eq. (48)-(49): `H~'(s) = ((d+1)/16) * sum_{l=1}^{32} V_l(s)`, a linear
  combination of 32 unitaries with total weight `O(d)`;
* truncation order `K = O(log(dT/eps) / log log (dT/eps))` (p. 9);
* `r = O(dT)` segments, hence `O(dT K)` uses of the oracle `O_A` (and of the
  controlled `U_b`, `U_b^dagger`) -- the query complexity;
* gate complexity `O(dT K (n + C_M))`, where `n = log_2 N` and `C_M` is the
  cost of the matrix-element rotation `M` (p. 9);
* substituting `T = O(kappa log kappa / eps)` (Eq. (12)) gives

  query `= O~(d kappa / eps)` and gate `= O~(d kappa (n + C_M) / eps)`,

  the `O~` hiding polylogarithmic factors in `d kappa / eps`.

Formal model. `truncationOrder x = log (x + 2)` is a valid (upper-bound)
truncation order: on the paper's asymptotic domain `x = d T / eps >= 16` the
paper's `K = log x / log log x` is at most `log x <= log (x + 2)`, as proved in
`paper_truncationOrder_le`. Larger `K` only improves the simulation accuracy,
so the resulting counts are upper bounds on the paper's `O(dTK)` count.
`queryCount d T eps = d * T * truncationOrder (d*T/eps)` and
`gateCount = queryCount * (n + C_M)` then have exactly the paper's form.

The `O~` notation is realised by the explicit envelope
`(log (d kappa / eps + 2) + 1)^2`: a constant times the base complexity times
a polynomial in the logarithm. The theorem is stated for every finite constant
`cT > 0` in the Eq. (12) bound `T <= cT * kappa log kappa / eps`; the returned
`O~` constant depends on `cT`, as it must.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver18.MainResults.GateComplexity.TaylorGateComplexity

/-- Truncation order used for the truncated Taylor series, modelled as
`log (x + 2)` (an upper bound on the paper's `K = log x / log log x` for
`x >= 16`, see `paper_truncationOrder_le`). -/
def truncationOrder (x : ℝ) : ℝ := Real.log (x + 2)

/-- Query complexity of the gate-model simulation (p. 9): `O(d T K)` uses of
the oracle `O_A` (and of the controlled `U_b`, `U_b^dagger`), with
`K = truncationOrder (d T / eps)`. -/
def queryCount (d T eps : ℝ) : ℝ := d * T * truncationOrder (d * T / eps)

/-- Gate complexity (p. 9): `O(d T K (n + C_M))` basic gates, where `n = log_2 N`
and `C_M` is the cost of the matrix-element rotation. -/
def gateCount (d n cM T eps : ℝ) : ℝ := queryCount d T eps * (n + cM)

/-- The `O~` coefficient arising from a finite Eq. (12) constant `cT > 0`:
it grows only logarithmically in `cT`, as `O~` hides. -/
def logConst (cT : ℝ) : ℝ := max 0 (Real.log (cT + 2) / Real.log 2)

/-- The paper's truncation order `K = log x / log log x` is dominated by
`truncationOrder x = log (x + 2)` on the asymptotic domain `x >= 16`
(because `log log x >= 1` there, since `e < log 16`). -/
theorem paper_truncationOrder_le {x : ℝ} (hx : 16 ≤ x) :
    Real.log x / Real.log (Real.log x) ≤ truncationOrder x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (16 : ℝ) ≤ x := hx
  -- `1 < log 16 < log x`, because `log 16 = 4 log 2 > 4 * 0.693 = 2.77 > e`.
  have hlog16_gt_exp : Real.exp 1 < Real.log 16 := by
    have h4 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hlogx_ge : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx1
  have hlog16_pos : 0 < Real.log 16 := by
    linarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hloglog : 1 ≤ Real.log (Real.log x) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (Real.log 16) :=
      Real.log_le_log (Real.exp_pos 1) hlog16_gt_exp.le
    rw [Real.log_exp] at h1
    have h2 : Real.log (Real.log 16) ≤ Real.log (Real.log x) :=
      Real.log_le_log hlog16_pos hlogx_ge
    linarith
  have hlogx_pos : 0 < Real.log x := by
    have : (0 : ℝ) < Real.log 16 := hlog16_pos
    linarith
  have hle : Real.log x ≤ truncationOrder x := by
    unfold truncationOrder
    exact Real.log_le_log hx0 (by linarith)
  have hloglog_pos : 0 < Real.log (Real.log x) := by linarith
  have hdiv : Real.log x / Real.log (Real.log x) ≤ Real.log x := by
    rw [div_le_iff₀ hloglog_pos]
    have h := mul_le_mul_of_nonneg_left hloglog hlogx_pos.le
    nlinarith [h]
  exact le_trans hdiv hle

/-- Core bound: for every finite Eq. (12) constant `cT > 0`, the query count
`d T K` is `O~(d kappa / eps)` with an explicit polylogarithmic envelope. -/
theorem query_complexity_core (cT : ℝ) (hcT : 0 < cT) :
    ∀ (d T kappa eps : ℝ), 2 ≤ kappa → 0 < eps → eps ≤ 1 → 1 ≤ d →
      T ≤ cT * kappa * Real.log kappa / eps → 16 ≤ d * T / eps →
      queryCount d T eps ≤ cT * (logConst cT + 3) * (d * kappa / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2 := by
  intro d T kappa eps hk hε0 hε1 hd hT hreg
  have hd0 : (0 : ℝ) < d := by linarith
  have hk0 : (0 : ℝ) < kappa := by linarith
  have hlogk : 0 < Real.log kappa := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Positivity of the total time and of `d * T`.
  have hxpos : 0 < d * T / eps := lt_of_lt_of_le (by norm_num) hreg
  have hdT_pos : 0 < d * T := by
    rcases (div_pos_iff.mp hxpos) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd hε0 (not_lt.mpr h2.le)
  -- Abbreviations `y = d kappa / eps`, `B = log (y + 2)`.
  set y : ℝ := d * kappa / eps with hydef
  set B : ℝ := Real.log (y + 2) with hBdef
  have hdk2 : (2 : ℝ) ≤ d * kappa := by nlinarith [hk, hd]
  have hy2 : 2 ≤ y := by
    rw [hydef, le_div_iff₀ hε0]
    nlinarith [hdk2, hε1]
  have hy0 : (0 : ℝ) < y := by linarith
  have hBpos : 0 < B := by
    rw [hBdef]
    exact Real.log_pos (by linarith)
  have hy2pos : (0 : ℝ) < y + 2 := by linarith
  -- `kappa <= y` and `log kappa <= B`.
  have hky : kappa ≤ y := by
    rw [hydef, le_div_iff₀ hε0]
    have hk1 : kappa ≤ d * kappa := by nlinarith [hd, hk0]
    nlinarith [hε1, hk1]
  have hlogky : Real.log kappa ≤ B := by
    have h1 : Real.log kappa ≤ Real.log y := Real.log_le_log hk0 hky
    have h2 : Real.log y ≤ Real.log (y + 2) := Real.log_le_log hy0 (by linarith)
    rw [hBdef]
    linarith
  -- `d T / eps <= cT * y^3`.
  have hx3 : d * T / eps ≤ cT * y ^ 3 := by
    have h1 : d * T / eps ≤ d * (cT * kappa * Real.log kappa / eps) / eps := by
      apply div_le_div_of_nonneg_right _ hε0.le
      exact mul_le_mul_of_nonneg_left hT hd0.le
    have h2 : d * (cT * kappa * Real.log kappa / eps) / eps =
        cT * y * (Real.log kappa / eps) := by
      rw [hydef]
      field_simp
    have hlogk_le : Real.log kappa ≤ kappa := Real.log_le_self hk0.le
    have h3 : Real.log kappa / eps ≤ y ^ 2 := by
      have hkeps : kappa / eps ≤ y := by
        have hmono : kappa / eps ≤ d * kappa / eps := by
          apply div_le_div_of_nonneg_right _ hε0.le
          nlinarith [hd, hk0]
        rw [hydef]
        exact hmono
      have h4 : Real.log kappa / eps ≤ kappa / eps :=
        div_le_div_of_nonneg_right hlogk_le hε0.le
      calc Real.log kappa / eps ≤ kappa / eps := h4
        _ ≤ y := hkeps
        _ ≤ y ^ 2 := by nlinarith [hy2]
    calc d * T / eps ≤ cT * y * (Real.log kappa / eps) := by
          calc d * T / eps ≤ d * (cT * kappa * Real.log kappa / eps) / eps := h1
            _ = cT * y * (Real.log kappa / eps) := h2
      _ ≤ cT * y * y ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = cT * y ^ 3 := by ring
  -- `d T / eps + 2 <= (cT + 2) (y + 2)^3`.
  have hx2 : d * T / eps + 2 ≤ (cT + 2) * (y + 2) ^ 3 := by
    have hcube : y ^ 3 ≤ (y + 2) ^ 3 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y) (by linarith : y ≤ y + 2) 3
      exact this
    have hx_le : d * T / eps ≤ cT * (y + 2) ^ 3 :=
      le_trans hx3 (mul_le_mul_of_nonneg_left hcube hcT.le)
    have hone : (1 : ℝ) ≤ (y + 2) ^ 3 := by nlinarith [hy2]
    nlinarith [hx_le, hone, hcT]
  -- Logarithmic bound.
  have hlogx : Real.log (d * T / eps + 2) ≤ (logConst cT + 3) * B := by
    have hpos : 0 < d * T / eps + 2 := by positivity
    have hle := Real.log_le_log hpos hx2
    have hcT2 : (0 : ℝ) < cT + 2 := by linarith
    have hcube_pos : (0 : ℝ) < (y + 2) ^ 3 := pow_pos hy2pos 3
    rw [Real.log_mul (ne_of_gt hcT2) (ne_of_gt hcube_pos), Real.log_pow] at hle
    push_cast at hle
    rw [hBdef]
    have hK : Real.log (cT + 2) ≤ logConst cT * Real.log (y + 2) := by
      unfold logConst
      rcases le_total (Real.log (cT + 2)) 0 with hneg | hpos'
      · have h0 : (0 : ℝ) ≤ max 0 (Real.log (cT + 2) / Real.log 2) := le_max_left _ _
        nlinarith
      · have hval : max 0 (Real.log (cT + 2) / Real.log 2) =
            Real.log (cT + 2) / Real.log 2 := by
          exact max_eq_right (div_nonneg hpos' hlog2.le)
        rw [hval]
        have hBge2 : Real.log 2 ≤ Real.log (y + 2) := by
          apply Real.log_le_log (by norm_num)
          linarith
        have h := mul_le_mul_of_nonneg_left hBge2 (div_nonneg hpos' hlog2.le)
        have hc : Real.log (cT + 2) / Real.log 2 * Real.log 2 = Real.log (cT + 2) := by
          field_simp
        linarith
    linarith
  -- `d T <= cT * y * B`.
  have hdT_le : d * T ≤ cT * y * B := by
    have h1 : d * T ≤ d * (cT * kappa * Real.log kappa / eps) :=
      mul_le_mul_of_nonneg_left hT hd0.le
    have h2 : d * (cT * kappa * Real.log kappa / eps) = cT * y * Real.log kappa := by
      rw [hydef]
      field_simp
    calc d * T ≤ d * (cT * kappa * Real.log kappa / eps) := h1
      _ = cT * y * Real.log kappa := h2
      _ ≤ cT * y * B := mul_le_mul_of_nonneg_left hlogky (by positivity)
  -- Assemble.
  have hK3 : (0 : ℝ) ≤ logConst cT + 3 := by
    have : (0 : ℝ) ≤ logConst cT := by
      unfold logConst
      exact le_max_left _ _
    linarith
  simp only [queryCount, truncationOrder]
  have hstep1 : d * T * Real.log (d * T / eps + 2) ≤
      d * T * ((logConst cT + 3) * B) :=
    mul_le_mul_of_nonneg_left hlogx hdT_pos.le
  have hstep2 : d * T * ((logConst cT + 3) * B) ≤
      (logConst cT + 3) * (cT * y * B) * B := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdT_le hK3) hBpos.le
    linarith [h]
  have hstep3 : (logConst cT + 3) * (cT * y * B) * B =
      cT * (logConst cT + 3) * y * B ^ 2 := by ring
  have hfac : (0 : ℝ) ≤ cT * (logConst cT + 3) * y := by positivity
  have hstep4 : cT * (logConst cT + 3) * y * B ^ 2 ≤
      cT * (logConst cT + 3) * y * (B + 1) ^ 2 := by
    have hBB : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith [hBpos]
    exact mul_le_mul_of_nonneg_left hBB hfac
  have hstep5 : cT * (logConst cT + 3) * y * (B + 1) ^ 2 =
      cT * (logConst cT + 3) * (d * kappa / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2 := by
    rw [← hydef, ← hBdef]
  calc d * T * Real.log (d * T / eps + 2)
      ≤ d * T * ((logConst cT + 3) * B) := hstep1
    _ ≤ (logConst cT + 3) * (cT * y * B) * B := hstep2
    _ = cT * (logConst cT + 3) * y * B ^ 2 := hstep3
    _ ≤ cT * (logConst cT + 3) * y * (B + 1) ^ 2 := hstep4
    _ = cT * (logConst cT + 3) * (d * kappa / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2 := hstep5

/-- Claim `c003`, query part (p. 9): using the truncated Taylor simulation of
Eq. (48)-(49) with `T = O(kappa log kappa / eps)` (Eq. (12)), the query
complexity (uses of `O_A` and controlled `U_b`, `U_b^dagger`) is
`O~(d kappa / eps)`.

`O~` envelope: `(log (d kappa / eps + 2) + 1)^2`; its coefficient is explicit
for every finite Eq. (12) constant. Domain `kappa >= 2`, `0 < eps <= 1`,
`d >= 1`, `d T / eps >= 16` (asymptotic regime, cf. the paper's `O~`). -/
theorem gateModel_query_complexity (cT : ℝ) (hcT : 0 < cT) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d T kappa eps : ℝ),
      2 ≤ kappa → 0 < eps → eps ≤ 1 → 1 ≤ d →
      T ≤ cT * kappa * Real.log kappa / eps → 16 ≤ d * T / eps →
      queryCount d T eps ≤ C * (d * kappa / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2 := by
  refine ⟨cT * (logConst cT + 3), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ logConst cT := by
      unfold logConst
      exact le_max_left _ _
    positivity
  · intro d T kappa eps hk hε0 hε1 hd hT hreg
    exact query_complexity_core cT hcT d T kappa eps hk hε0 hε1 hd hT hreg

/-- Claim `c003`, gate part (p. 9): the gate complexity is
`O~(d kappa (n + C_M) / eps)`, where `n = log_2 N` and `C_M` is the cost of the
matrix-element rotation. Same `O~` envelope as the query part. -/
theorem gateModel_gate_complexity (cT : ℝ) (hcT : 0 < cT) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n cM T kappa eps : ℝ),
      2 ≤ kappa → 0 < eps → eps ≤ 1 → 1 ≤ d → 1 ≤ n → 1 ≤ cM →
      T ≤ cT * kappa * Real.log kappa / eps → 16 ≤ d * T / eps →
      gateCount d n cM T eps ≤ C * (d * kappa * (n + cM) / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2 := by
  refine ⟨cT * (logConst cT + 3), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ logConst cT := by
      unfold logConst
      exact le_max_left _ _
    positivity
  · intro d n cM T kappa eps hk hε0 hε1 hd hn hcM hT hreg
    have hq := query_complexity_core cT hcT d T kappa eps hk hε0 hε1 hd hT hreg
    have hnM : (0 : ℝ) ≤ n + cM := by linarith
    unfold gateCount
    calc queryCount d T eps * (n + cM)
        ≤ (cT * (logConst cT + 3) * (d * kappa / eps) *
            (Real.log (d * kappa / eps + 2) + 1) ^ 2) * (n + cM) :=
          mul_le_mul_of_nonneg_right hq hnM
      _ = cT * (logConst cT + 3) * (d * kappa * (n + cM) / eps) *
            (Real.log (d * kappa / eps + 2) + 1) ^ 2 := by ring

/-- Claim `c003` (p. 9), conjunction form: the Taylor-simulation compilation of
the second algorithm has query complexity `O~(d kappa / eps)` and gate
complexity `O~(d kappa (n + C_M) / eps)`, for every finite Eq. (12) constant
`cT > 0`. -/
theorem taylor_gate_model_complexity (cT : ℝ) (hcT : 0 < cT) :
    (∃ C : ℝ, 0 < C ∧ ∀ (d T kappa eps : ℝ),
      2 ≤ kappa → 0 < eps → eps ≤ 1 → 1 ≤ d →
      T ≤ cT * kappa * Real.log kappa / eps → 16 ≤ d * T / eps →
      queryCount d T eps ≤ C * (d * kappa / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d n cM T kappa eps : ℝ),
      2 ≤ kappa → 0 < eps → eps ≤ 1 → 1 ≤ d → 1 ≤ n → 1 ≤ cM →
      T ≤ cT * kappa * Real.log kappa / eps → 16 ≤ d * T / eps →
      gateCount d n cM T eps ≤ C * (d * kappa * (n + cM) / eps) *
        (Real.log (d * kappa / eps + 2) + 1) ^ 2) :=
  ⟨gateModel_query_complexity cT hcT, gateModel_gate_complexity cT hcT⟩

end Qatlib.Papers.QLinearSolver18.MainResults.GateComplexity.TaylorGateComplexity
