/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PrecondQLSA13.MainResults.Complexity.SourceComplexity
public import Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication.SourceScatteringApplication
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Upgrading the tilde: sub-polynomial Suzuki factor and log-only scaling

Fixed arXiv:1301.2340v4, pp. 3--4.  The frozen public module
`Qatlib.Papers.PrecondQLSA13.MainResults.Complexity` composes the paper's
component costs into `totalCost d κ N ε = 72 · d^7 κ log N / ε² · F` with the
Berry-et-al Suzuki factor `F = exp(2 ln 5 √(ln(mτ/ε)))`, `m = 6d²`,
`τ = κ/ε`. This file proves two scalar estimates for that prescribed cost:

* `suzukiFactor_subpolylog`: for every exponent `δ > 0`, once
  `ln(mτ/ε) ≥ (2 ln 5 / δ)²` the Suzuki factor is at most `(mτ/ε)^δ`; so the
  tilde in `Õ(d^7 κ log N / ε²)` can be replaced by an *explicit*
  sub-polynomial factor with any chosen exponent (`totalCost_subpolylog`).
* `preconditioned_cost_log_only` and `quantum_over_classical_tends_zero`:
  when the SPAI preconditioner bounds the condition number by a constant `K`
  independent of `N` (the frozen Eq. (12) content), every factor of the
  composed cost is `N`-independent except `log N`, and the quantum cost
  divided by any classical cost that grows at least linearly in `N` becomes
  arbitrarily small. The denominator is a chosen linear comparison cost;
  no classical lower bound or executable quantum speedup is established.

Boundary: the SPAI construction itself, the simulated Hamiltonian, and the
coupled output-error-resource proof remain the paper's standard-model
premises (as recorded in the frozen module); this file adds only the two
asymptotic steps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade

open Qatlib.Papers.PrecondQLSA13.MainResults.Complexity
open Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication

/-- For every `δ > 0`, the Suzuki factor `exp(2 ln 5 √(ln x))` is at most
`x ^ δ` once `ln x ≥ (2 ln 5 / δ)²`: the tilde hides a sub-polynomial factor
with arbitrarily small exponent. -/
theorem suzukiFactor_subpolylog (x δ : ℝ) (hδ : 0 < δ) (hx : 1 ≤ x)
    (hlog : (2 * Real.log 5 / δ) ^ 2 ≤ Real.log x) :
    Real.exp (2 * Real.log 5 * Real.sqrt (Real.log x)) ≤ x ^ δ := by
  have hlog5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have hc0 : (0 : ℝ) ≤ 2 * Real.log 5 / δ := by positivity
  have hL : (0 : ℝ) ≤ Real.log x := le_trans (sq_nonneg _) hlog
  have hsq : 2 * Real.log 5 / δ ≤ Real.sqrt (Real.log x) := by
    have h1 : (2 * Real.log 5 / δ) ^ 2 ≤ (Real.sqrt (Real.log x)) ^ 2 := by
      rw [Real.sq_sqrt hL]
      exact hlog
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg hc0, abs_of_nonneg (Real.sqrt_nonneg _)] at h2
  have hmul : 2 * Real.log 5 * Real.sqrt (Real.log x) ≤ δ * Real.log x := by
    have hinner : (2 * Real.log 5 / δ) * Real.sqrt (Real.log x)
        ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    have hstep : δ * ((2 * Real.log 5 / δ) * Real.sqrt (Real.log x))
        ≤ δ * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left hinner hδ.le
    have hrew : δ * ((2 * Real.log 5 / δ) * Real.sqrt (Real.log x))
        = 2 * Real.log 5 * Real.sqrt (Real.log x) := by
      field_simp
    have hrew2 : δ * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x))
        = δ * Real.log x := by
      rw [Real.mul_self_sqrt hL]
    rw [hrew] at hstep
    rw [hrew2] at hstep
    exact hstep
  calc Real.exp (2 * Real.log 5 * Real.sqrt (Real.log x))
      ≤ Real.exp (δ * Real.log x) := Real.exp_le_exp.mpr hmul
    _ = x ^ δ := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
        ring

/-- The composed cost of the frozen module, upgraded: once
`ln(6d²κ/ε²) ≥ (2 ln 5 / δ)²`, the `Õ(d^7 κ log N / ε²)` headline is an
explicit bound `72 · d^7 κ log N / ε² · (6d²κ/ε²)^δ`. -/
theorem totalCost_subpolylog (d κ N ε δ : ℝ)
    (hd : 0 < d) (hκ : 0 < κ) (hN : 1 < N) (hε : 0 < ε) (hδ : 0 < δ)
    (hlog : (2 * Real.log 5 / δ) ^ 2 ≤ Real.log (6 * d ^ 2 * κ / ε ^ 2)) :
    totalCost d κ N ε
      ≤ 72 * d ^ 7 * κ * Real.log N / ε ^ 2 * (6 * d ^ 2 * κ / ε ^ 2) ^ δ := by
  have heq := totalCost_eq_tilde d κ N ε (by positivity) (by positivity)
  have harg : subMatrixCount d * (κ / ε) / ε = 6 * d ^ 2 * κ / ε ^ 2 := by
    unfold subMatrixCount
    field_simp
  have hx1 : (1 : ℝ) ≤ 6 * d ^ 2 * κ / ε ^ 2 := by
    have hpos : (0 : ℝ) < 6 * d ^ 2 * κ / ε ^ 2 := by positivity
    have hexp := Real.exp_log hpos
    have hmono := Real.exp_le_exp.mpr
      (le_trans (sq_nonneg (2 * Real.log 5 / δ)) hlog)
    calc (1 : ℝ) = Real.exp 0 := by norm_num
      _ ≤ Real.exp (Real.log (6 * d ^ 2 * κ / ε ^ 2)) := hmono
      _ = 6 * d ^ 2 * κ / ε ^ 2 := hexp
  have hF : suzukiFactor (subMatrixCount d) (κ / ε) ε
      ≤ (6 * d ^ 2 * κ / ε ^ 2) ^ δ := by
    unfold suzukiFactor
    rw [harg]
    exact suzukiFactor_subpolylog _ δ hδ hx1 hlog
  rw [heq]
  refine mul_le_mul_of_nonneg_left hF ?_
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (le_of_lt (Real.log_pos hN))) (by positivity)

/-- When the preconditioner bounds the condition number by `K`, every factor
of the composed cost is `N`-independent except the single `log N`. -/
theorem preconditioned_cost_log_only (d K N ε δ : ℝ)
    (hd : 0 < d) (hK : 0 < K) (hN : 1 < N) (hε : 0 < ε) (hδ : 0 < δ)
    (hlog : (2 * Real.log 5 / δ) ^ 2 ≤ Real.log (6 * d ^ 2 * K / ε ^ 2)) :
    totalCost d K N ε
      ≤ (72 * d ^ 7 * K / ε ^ 2 * (6 * d ^ 2 * K / ε ^ 2) ^ δ) * Real.log N := by
  exact (totalCost_subpolylog d K N ε δ hd hK hN hε hδ hlog).trans_eq
    (by field_simp)

/-- The elementary decay fact used for the speedup ratios: `log N ≤ 2√N`
for `N ≥ 1`, since `log N = 2 log √N ≤ 2(√N − 1)`. -/
theorem log_le_two_sqrt (N : ℝ) (hN : 1 ≤ N) :
    Real.log N ≤ 2 * Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 :=
    Real.log_sqrt hN0.le
  have h3 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos_of_pos hN0)
  have h1 : Real.log N = 2 * Real.log (Real.sqrt N) := by
    rw [h2]
    ring
  rw [h1]
  linarith

/-- The prescribed scalar cost with fixed condition parameter `K`, divided
by a chosen positive linear comparison cost, becomes arbitrarily small.
This does not prove a classical lower bound or an executable speedup. -/
theorem quantum_over_classical_tends_zero (d K ε δ cclassical : ℝ)
    (hd : 0 < d) (hK : 0 < K) (hε : 0 < ε) (hδ : 0 < δ)
    (hcc : 0 < cclassical)
    (hlog : (2 * Real.log 5 / δ) ^ 2 ≤ Real.log (6 * d ^ 2 * K / ε ^ 2))
    (e : ℝ) (he : 0 < e) :
    ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      totalCost d K N ε / (cclassical * N) ≤ e := by
  have hcost := preconditioned_cost_log_only d K (2 : ℝ) ε δ hd hK
    (by norm_num) hε hδ hlog
  set C := 72 * d ^ 7 * K / ε ^ 2 * (6 * d ^ 2 * K / ε ^ 2) ^ δ with hCdef
  have hC0 : (0 : ℝ) ≤ C := by
    rw [hCdef]
    positivity
  refine ⟨max 2 ((2 * C / (cclassical * e)) ^ 2 + 1), by norm_num, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) < N := by
    have h2N : (2 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
    linarith
  have hcc : (0 : ℝ) < cclassical * N := by positivity
  have hcostN := preconditioned_cost_log_only d K N ε δ hd hK hN1 hε hδ hlog
  have hlogN : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt N hN1.le
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    have := Real.sqrt_le_sqrt (hN1.le)
    simpa using this
  have ht : 2 * C / (cclassical * e) ≤ Real.sqrt N := by
    have hbig : (2 * C / (cclassical * e)) ^ 2 ≤ N := by
      have hle := le_trans (le_max_right _ _) hN
      have hpos := sq_nonneg (2 * C / (cclassical * e))
      linarith
    have hroot : (2 * C / (cclassical * e)) ^ 2
        ≤ (Real.sqrt N) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
      exact hbig
    have habs := sq_le_sq.mp hroot
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * C / (cclassical * e)),
      abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  rw [div_le_iff₀ hcc]
  have hkey : 2 * C * Real.sqrt N ≤ e * (cclassical * N) := by
    have hce : (0 : ℝ) < cclassical * e := by positivity
    have h1 : 2 * C ≤ (cclassical * e) * Real.sqrt N :=
      le_trans ((div_le_iff₀ hce).mp ht) (le_of_eq (by ring))
    have hsqN : Real.sqrt N * Real.sqrt N = N :=
      Real.mul_self_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [h1, hs1, hsqN]
  calc totalCost d K N ε
      ≤ C * Real.log N := hcostN
    _ ≤ C * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left hlogN hC0
    _ = 2 * C * Real.sqrt N := by ring
    _ ≤ e * (cclassical * N) := hkey

end Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade
