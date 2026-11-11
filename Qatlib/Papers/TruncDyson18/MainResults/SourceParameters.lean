/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.ComputedGrid.ComputedDysonGridProgram
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveDysonParameters

set_option backward.isDefEq.respectTransparency false

/-!
# Source parameters of the truncated-Dyson-series simulator

Paper: M. Kieferová, A. Scherer, D. W. Berry, *Simulating the dynamics of
time-dependent Hamiltonians with a truncated Dyson series*, arXiv:1805.00582v1.

This module fixes the parameter notation of §II (Eqs. (1)--(3)) and the derived
algorithm parameters of §VI: the LCU coefficient `γ` of Eq. (9), the number of
summands `L` of Eq. (10), the segment weight `λ = Lγ`, the segment count `r = Θ(λT)`
(§V, p. 9), the per-segment dyadic precision `k = ⌈log₂(r/ε)⌉`, the Dyson order `K`
of Eq. (14) (instantiated with the frozen native factorial cutoff, Eq. (35)), and
the grid size `M` of Eq. (41) (instantiated with the frozen computed Dyson grid).
The query and gate ledgers are the counts of §VI, Eqs. (42) and (44).

Nothing here is a claim: the quantitative headline of the paper (Eqs. (2)--(3)) is
proved downstream in `MainResult/MainResult.lean` and `TruncationBudget/`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.TruncDyson18.MainResults

open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts

/-- Parameters of arXiv:1805.00582 §II. `d` is the sparsity of the `d`-sparse
Hamiltonian, `Hmax` bounds the spectral norm of every `H(t)` (Eq. (1)),
`HdotMax` bounds the norm of the derivative, `T` is the evolution time, `eps` the
target error `ε`, and `n` the number of system qubits. -/
structure SourceParameters where
  d : ℕ
  Hmax : ℝ
  HdotMax : ℝ
  T : ℝ
  eps : ℝ
  n : ℕ

namespace SourceParameters

/-- Admissibility of the paper's parameters: positive sparsity, bounds and time,
positive target error. -/
def Admissible (p : SourceParameters) : Prop :=
  1 ≤ p.d ∧ 0 < p.Hmax ∧ 0 ≤ p.HdotMax ∧ 0 < p.T ∧ 0 < p.eps

/-- The asymptotic regime in which Eqs. (2)--(3) are stated. Besides admissibility
this records the conditions that the `O(·)` reading of the paper makes implicit:
the evolution scale is at least one segment (`1 ≤ d² Hmax T`, so that `r ≥ 1` is
reached), the target error is below the natural `d Hmax T / e²` scale (so that
`log(dHmaxT/ε) ≥ 2` and the double logarithm is positive), the sparsity error
`d ε` does not exceed the evolution scale (so that `log d ≤ log(dHmaxT/ε)` and the
`d²` inside `log(λT/ε)` costs only a constant), and the derivative logarithm
`log(HdotMax T/(ε d Hmax))` of Eq. (3) is nonnegative. -/
structure Regime (p : SourceParameters) : Prop where
  d_pos : 1 ≤ p.d
  Hmax_pos : 0 < p.Hmax
  HdotMax_nonneg : 0 ≤ p.HdotMax
  T_pos : 0 < p.T
  eps_pos : 0 < p.eps
  scale : 1 ≤ (p.d : ℝ)^2 * p.Hmax * p.T
  error_small : Real.exp 2 ≤ (p.d : ℝ) * p.Hmax * p.T / p.eps
  sparse_regime : (p.d : ℝ) * p.eps ≤ p.Hmax * p.T
  deriv_log_nonneg : 0 ≤ Real.log (p.HdotMax * p.T / (p.eps * (p.d : ℝ) * p.Hmax))

/-- Eq. (9): the time-independent LCU coefficient `γ = Θ(ε/(d³T))`, taken at the
endpoint of the class. -/
def gamma (p : SourceParameters) : ℝ := p.eps / ((p.d : ℝ)^3 * p.T)

/-- Eq. (10): the number of one-sparse unitary summands `L = ⌈d²Hmax/γ⌉`. -/
def decompositionSize (p : SourceParameters) : ℕ := ⌈(p.d : ℝ)^2 * p.Hmax / p.gamma⌉₊

/-- `λ = Lγ`, the sum of the (time-independent) LCU weights of one segment. -/
def lcuWeight (p : SourceParameters) : ℝ := (p.decompositionSize : ℝ) * p.gamma

/-- §V p. 9: the number of time segments, `r = max 1 ⌈2λT⌉` (`r = Θ(λT)`, a power
of two in the compressed-rotation circuit). -/
def segmentCount (p : SourceParameters) : ℕ := max 1 ⌈2 * p.lcuWeight * p.T⌉₊

/-- The segment length `t = T/r`. -/
def segmentTime (p : SourceParameters) : ℝ := p.T / (p.segmentCount : ℝ)

/-- The per-segment dyadic precision `k = ⌈log₂(r/ε)⌉`, chosen so that the
truncation-plus-discretization error of one segment is at most `ε/r`. -/
def segmentPrecision (p : SourceParameters) : ℕ :=
  ⌈Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2⌉₊

/-- Eq. (14)/(35): the Dyson truncation order, instantiated with the frozen native
factorial cutoff at precision `k`. -/
def truncationOrder (p : SourceParameters) : ℕ := computedDysonCutoff (p.segmentPrecision + 8)

/-- Eq. (41): the dyadic grid size `M`, instantiated with the frozen computed Dyson
grid at precision `k` (the concrete schedule whose accumulated grid error is
bounded in the frozen layer). -/
def gridBits (p : SourceParameters) : ℕ :=
  Nat.clog 2 (computedDysonGridSize p.segmentTime p.Hmax p.HdotMax (p.segmentPrecision + 8))

/-- The grid size `M = 2^gridBits`. -/
def gridSize (p : SourceParameters) : ℕ := 2 ^ p.gridBits

/-- The main logarithmic scale `log(d Hmax T/ε)` of Eqs. (2)--(3). -/
def logScale (p : SourceParameters) : ℝ := Real.log ((p.d : ℝ) * p.Hmax * p.T / p.eps)

/-- The derivative logarithm `log(HdotMax T/(ε d Hmax))` of Eq. (3). -/
def derivativeLog (p : SourceParameters) : ℝ :=
  Real.log (p.HdotMax * p.T / (p.eps * (p.d : ℝ) * p.Hmax))

/-- Eq. (42): `O(rK)` queries. Each of the `r` segments runs `K` controlled
Hamiltonian queries inside `W`, and the oblivious amplitude amplification costs two
applications of `W` and one of `W†` (Eq. (22)); the factor `4` is a generous
constant accounting for this repetition. -/
def queryCount (p : SourceParameters) : ℕ := 4 * p.segmentCount * p.truncationOrder

/-- Eq. (44): the gate ledger `O(λT K[log L + log M + log log(λT/ε) + n])`, with
the `log log(λT/ε)` term represented by `⌈log₂(k+2)⌉` (since `2^k ≥ r/ε`). -/
def gateCount (p : SourceParameters) : ℕ :=
  4 * p.segmentCount * p.truncationOrder *
    (Nat.clog 2 p.decompositionSize + Nat.clog 2 p.gridSize +
      Nat.clog 2 (p.segmentPrecision + 2) + p.n + 1)

/-- The right-hand side of the query bound, Eq. (2). -/
def queryFormula (p : SourceParameters) : ℝ :=
  (p.d : ℝ)^2 * p.Hmax * p.T * p.logScale / Real.log p.logScale

/-- The right-hand side of the gate bound, Eq. (3). -/
def gateFormula (p : SourceParameters) : ℝ :=
  (p.d : ℝ)^2 * p.Hmax * p.T * (p.logScale / Real.log p.logScale) *
    (p.logScale + p.derivativeLog + p.n)

/-! ### Elementary facts about the derived parameters -/

/-- The `gamma_pos` result for the TruncDyson18 paper model. -/
theorem gamma_pos (p : SourceParameters) (h : p.Regime) : 0 < p.gamma := by
  have hd : (0 : ℝ) < (p.d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) h.d_pos)
  unfold gamma
  exact div_pos h.eps_pos (mul_pos (pow_pos hd 3) h.T_pos)

/-- The `one_le_d` result for the TruncDyson18 paper model. -/
theorem one_le_d (p : SourceParameters) (h : p.Regime) : (1 : ℝ) ≤ (p.d : ℝ) := by
  exact_mod_cast h.d_pos

/-- The `d_pos` result for the TruncDyson18 paper model. -/
theorem d_pos (p : SourceParameters) (h : p.Regime) : 0 < p.d :=
  lt_of_lt_of_le (by norm_num) h.d_pos

/-- The `d_cast_pos` result for the TruncDyson18 paper model. -/
theorem d_cast_pos (p : SourceParameters) (h : p.Regime) : (0 : ℝ) < (p.d : ℝ) := by
  exact_mod_cast (p.d_pos h)

/-- `d²Hmax/γ = d⁵HmaxT/ε`, the paper's `Θ(d⁵HmaxT/ε)` form of `L` (p. 11). -/
theorem ratio_eq (p : SourceParameters) (h : p.Regime) :
    (p.d : ℝ)^2 * p.Hmax / p.gamma = (p.d : ℝ)^5 * p.Hmax * p.T / p.eps := by
  have hd : (0 : ℝ) < (p.d : ℝ) := p.d_cast_pos h
  unfold gamma
  field_simp

/-- The `decompositionSize_eq_ratio` result for the TruncDyson18 paper model. -/
theorem decompositionSize_eq_ratio (p : SourceParameters) (h : p.Regime) :
    p.decompositionSize = ⌈(p.d : ℝ)^5 * p.Hmax * p.T / p.eps⌉₊ := by
  unfold decompositionSize
  rw [p.ratio_eq h]

/-- The lower endpoint of `λ = Lγ`: `d²Hmax ≤ λ` (since `L ≥ d²Hmax/γ`). -/
theorem le_lcuWeight (p : SourceParameters) (h : p.Regime) :
    (p.d : ℝ)^2 * p.Hmax ≤ p.lcuWeight := by
  have hg : 0 < p.gamma := p.gamma_pos h
  have hceil : (p.d : ℝ)^2 * p.Hmax / p.gamma ≤ (p.decompositionSize : ℝ) := by
    unfold decompositionSize
    exact Nat.le_ceil _
  calc (p.d : ℝ)^2 * p.Hmax
      = ((p.d : ℝ)^2 * p.Hmax / p.gamma) * p.gamma := by field_simp
    _ ≤ (p.decompositionSize : ℝ) * p.gamma :=
        mul_le_mul_of_nonneg_right hceil hg.le
    _ = p.lcuWeight := rfl

/-- The upper endpoint of `λ = Lγ`: `λ < 2 d²Hmax` (`L < d²Hmax/γ + 1` and
`γ ≤ d²Hmax`). -/
theorem lcuWeight_lt_two (p : SourceParameters) (h : p.Regime) :
    p.lcuWeight < 2 * ((p.d : ℝ)^2 * p.Hmax) := by
  have hg : 0 < p.gamma := p.gamma_pos h
  have hd : (0 : ℝ) < (p.d : ℝ) := p.d_cast_pos h
  have hd1 : (1 : ℝ) ≤ (p.d : ℝ) := p.one_le_d h
  have hd3 : (1 : ℝ) ≤ (p.d : ℝ)^3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (p.d : ℝ) ^ 3 := by gcongr
  have hmaxT : (0 : ℝ) ≤ p.Hmax * p.T := (mul_pos h.Hmax_pos h.T_pos).le
  have hgam_le : p.gamma ≤ (p.d : ℝ)^2 * p.Hmax := by
    unfold gamma
    rw [div_le_iff₀ (mul_pos (pow_pos hd 3) h.T_pos)]
    have h2 : p.Hmax * p.T ≤ p.Hmax * p.T * (p.d : ℝ)^3 := by
      nlinarith [hmaxT, hd3]
    nlinarith [h.sparse_regime, h.eps_pos]
  have hx : (0 : ℝ) ≤ (p.d : ℝ)^2 * p.Hmax / p.gamma :=
    (div_pos (mul_pos (pow_pos hd 2) h.Hmax_pos) hg).le
  have hceil : (p.decompositionSize : ℝ) < (p.d : ℝ)^2 * p.Hmax / p.gamma + 1 := by
    unfold decompositionSize
    exact Nat.ceil_lt_add_one hx
  have hstep : p.lcuWeight < ((p.d : ℝ)^2 * p.Hmax / p.gamma + 1) * p.gamma := by
    unfold lcuWeight
    exact mul_lt_mul_of_pos_right hceil hg
  have hsplit : ((p.d : ℝ)^2 * p.Hmax / p.gamma + 1) * p.gamma
      = (p.d : ℝ)^2 * p.Hmax + p.gamma := by
    field_simp
  rw [hsplit] at hstep
  linarith

/-- The segment count is at least `2λT`. -/
theorem segmentCount_ge (p : SourceParameters) (h : p.Regime) :
    2 * p.lcuWeight * p.T ≤ (p.segmentCount : ℝ) := by
  have hceil : 2 * p.lcuWeight * p.T ≤ (⌈2 * p.lcuWeight * p.T⌉₊ : ℝ) := Nat.le_ceil _
  have hle : (⌈2 * p.lcuWeight * p.T⌉₊ : ℝ) ≤ (p.segmentCount : ℝ) := by
    unfold segmentCount
    exact_mod_cast le_max_right 1 ⌈2 * p.lcuWeight * p.T⌉₊
  linarith

/-- The segment count is at most `3λT` in the regime of Eq. (2). -/
theorem segmentCount_le (p : SourceParameters) (h : p.Regime) :
    (p.segmentCount : ℝ) ≤ 4 * p.lcuWeight * p.T := by
  have hlam : (1 : ℝ) ≤ p.lcuWeight * p.T := by
    have h1 := p.le_lcuWeight h
    have h2 : (p.d : ℝ)^2 * p.Hmax * p.T ≤ p.lcuWeight * p.T :=
      mul_le_mul_of_nonneg_right h1 h.T_pos.le
    nlinarith [h.scale, h2]
  have hx : (0 : ℝ) ≤ 2 * p.lcuWeight * p.T := by
    have := p.gamma_pos h
    nlinarith [h.T_pos, p.le_lcuWeight h]
  have hceil : (⌈2 * p.lcuWeight * p.T⌉₊ : ℝ) < 2 * p.lcuWeight * p.T + 1 :=
    Nat.ceil_lt_add_one hx
  have hnat : p.segmentCount ≤ 1 + ⌈2 * p.lcuWeight * p.T⌉₊ := by
    unfold segmentCount
    omega
  have hcast : (p.segmentCount : ℝ) ≤ 1 + (⌈2 * p.lcuWeight * p.T⌉₊ : ℝ) := by
    calc (p.segmentCount : ℝ) ≤ ((1 + ⌈2 * p.lcuWeight * p.T⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = 1 + (⌈2 * p.lcuWeight * p.T⌉₊ : ℝ) := by push_cast; ring
  linarith

/-- The `segmentCount_pos` result for the TruncDyson18 paper model. -/
theorem segmentCount_pos (p : SourceParameters) (h : p.Regime) : 0 < p.segmentCount := by
  unfold segmentCount
  exact lt_of_lt_of_le (by norm_num) (le_max_left 1 _)

/-- The `segmentTime_pos` result for the TruncDyson18 paper model. -/
theorem segmentTime_pos (p : SourceParameters) (h : p.Regime) : 0 < p.segmentTime := by
  have hr : (0 : ℝ) < (p.segmentCount : ℝ) := by exact_mod_cast p.segmentCount_pos h
  unfold segmentTime
  exact div_pos h.T_pos hr

/-- The segment length is at most `1/(2d²Hmax)`, the scale at which the frozen
domain condition `α t ≤ 1/2` holds. -/
theorem segmentTime_le (p : SourceParameters) (h : p.Regime) :
    p.segmentTime ≤ 1 / (2 * ((p.d : ℝ)^2 * p.Hmax)) := by
  have hd : (0 : ℝ) < (p.d : ℝ) := p.d_cast_pos h
  have hr := p.segmentCount_ge h
  have hrpos : (0 : ℝ) < (p.segmentCount : ℝ) := by exact_mod_cast p.segmentCount_pos h
  have hden : (0 : ℝ) < 2 * ((p.d : ℝ)^2 * p.Hmax) :=
    mul_pos (by norm_num) (mul_pos (pow_pos hd 2) h.Hmax_pos)
  unfold segmentTime
  rw [div_le_div_iff₀ hrpos hden]
  -- goal `T * (2 * d² * Hmax) ≤ segmentCount * 1`
  nlinarith [hr, h.T_pos.le, p.le_lcuWeight h]

/-- `k ≥ log₂(r/ε)`: the ceiling bound behind the accuracy budget `ε/r`. -/
theorem le_segmentPrecision (p : SourceParameters) (h : p.Regime) :
    Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2 ≤ (p.segmentPrecision : ℝ) := by
  unfold segmentPrecision
  exact Nat.le_ceil _

/-- `k ≤ log₂(r/ε) + 1`. -/
theorem segmentPrecision_le (p : SourceParameters) (h : p.Regime) :
    (p.segmentPrecision : ℝ) ≤
      Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2 + 1 := by
  have hx : (0 : ℝ) ≤ Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2 := by
    have hone : (1 : ℝ) ≤ (p.segmentCount : ℝ) / p.eps := by
      rw [le_div_iff₀ h.eps_pos]
      have hsmall : Real.exp 2 * p.eps ≤ (p.d : ℝ) * p.Hmax * p.T :=
        (le_div_iff₀ h.eps_pos).mp h.error_small
      have hexp1 : (1 : ℝ) ≤ Real.exp 2 := by
        linarith [Real.add_one_le_exp 2]
      have hr := p.segmentCount_ge h
      have hl := p.le_lcuWeight h
      have hd1 := p.one_le_d h
      nlinarith [hsmall, hexp1, hr, hl, h.eps_pos, h.Hmax_pos, h.T_pos,
        mul_pos (mul_pos (p.d_cast_pos h) h.Hmax_pos) h.T_pos]
    have hlog : 0 ≤ Real.log ((p.segmentCount : ℝ) / p.eps) := Real.log_nonneg hone
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  unfold segmentPrecision
  exact (Nat.ceil_lt_add_one hx).le

/-- The `gridSize_pos` result for the TruncDyson18 paper model. -/
theorem gridSize_pos (p : SourceParameters) (h : p.Regime) : 0 < p.gridSize := by
  unfold gridSize
  exact pow_pos (by norm_num) _

/-- The frozen computed grid size is at most the chosen dyadic grid. -/
theorem le_gridSize (p : SourceParameters) :
    computedDysonGridSize p.segmentTime p.Hmax p.HdotMax (p.segmentPrecision + 8) ≤ p.gridSize := by
  unfold gridSize gridBits
  exact Nat.le_pow_clog (by norm_num) _

/-- The `truncationOrder_eq` result for the TruncDyson18 paper model. -/
theorem truncationOrder_eq (p : SourceParameters) :
    p.truncationOrder = computedDysonCutoff (p.segmentPrecision + 8) := rfl

end SourceParameters

end Qatlib.Papers.TruncDyson18.MainResults
