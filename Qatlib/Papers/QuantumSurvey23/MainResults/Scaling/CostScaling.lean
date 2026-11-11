/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Cost-scaling vocabulary for QuantumSurvey23

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011 (PDF SHA-256
`5d026bc38957ccc4f193a6fdf4c096dcf9e202c91a56b9f1cb57cbc8df903166`).

Every "complexity assessment" claim in this survey has the same skeleton: a
quantum cost that is polynomial in the problem size versus a classical cost
that is polynomial, exponentially larger, or superpolynomial.  This module fixes
the elementary vocabulary those assessments share, so each claim file only has
to instantiate the paper's own cost model:

* `expCost n = 2^n` — a representative exponential classical cost;
* `polyCost C d n = C * (n+1)^d` — a uniform polynomial bound;
* `expCost_dominates_poly` — for every fixed `C, d`, `2^n` eventually exceeds
  `C * (n+1)^d`;
* `sqrtCost N = Nat.sqrt N + 1` — the ceiling of `√N` as a natural number,
  with the exact quadratic identities used by Grover-type assessments;
* `polySum` and `polySum_bound` — a sum of two polynomially bounded costs is
  still polynomially bounded (used for "simulation plus state preparation").

Boundary: these are arithmetic facts about the cost functions printed in the
survey.  They do not model gate-level implementations or prove any
complexity-theoretic lower bound; those remain the survey's cited results.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

open Filter Asymptotics
open scoped Topology

/-- The exponential cost `2^n`; the paper's representative cost of exact
diagonalization (`2^M` for `M` lattice sites / qubits). -/
def expCost (n : ℕ) : ℕ := 2 ^ n

/-- A uniform polynomial cost bound `C * (n+1)^d`. -/
def polyCost (C d n : ℕ) : ℕ := C * (n + 1) ^ d

/-- **Exponential dominates polynomial.**  For every constant `C` and every
fixed degree `d`, the exponential `2^n` eventually exceeds `C * (n+1)^d`.
This is the arithmetic content of every "exponential speedup over exact
diagonalization" assessment in the survey. -/
theorem expCost_dominates_poly (C d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → polyCost C d n < expCost n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Over `ℝ`, `x^(d+1) = o(2^x)`.
  have hlittle : (fun n : ℕ => (n : ℝ) ^ (d + 1)) =o[atTop]
      (fun n : ℕ => (2 : ℝ) ^ n) := by
    have h₁ : (fun x : ℝ => x ^ (d + 1)) =o[atTop]
        (fun x : ℝ => Real.exp (Real.log 2 * x)) :=
      isLittleO_pow_exp_pos_mul_atTop (d + 1) hlog
    have h₂ : (fun n : ℕ => (n : ℝ) ^ (d + 1)) =o[atTop]
        (fun n : ℕ => Real.exp (Real.log 2 * (n : ℝ))) := by
      have h₂ := h₁.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [Function.comp_def] using h₂
    have h₃ : (fun n : ℕ => Real.exp (Real.log 2 * (n : ℝ))) =
        (fun n : ℕ => (2 : ℝ) ^ n) := by
      funext n
      rw [Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [h₃] at h₂
    exact h₂
  have hpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < ‖(2 : ℝ) ^ n‖ :=
    Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs]
      exact abs_pos.mpr (by positivity)
  have hlt : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (d + 1) < (2 : ℝ) ^ n := by
    filter_upwards [hlittle.eventuallyLT_norm_of_eventually_pos hpos] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
    exact hn
  have hbig : ∀ᶠ n : ℕ in atTop, ((C * 2 ^ d : ℕ) : ℝ) ≤ n := by
    filter_upwards [eventually_ge_atTop ((C * 2 ^ d : ℕ))] with n hn
    exact_mod_cast hn
  have hev : ∀ᶠ n : ℕ in atTop, (C : ℝ) * ((n : ℝ) + 1) ^ d < (2 : ℝ) ^ n := by
    filter_upwards [hlt, hbig, eventually_ge_atTop (1 : ℕ)] with n hlt hbig hn1
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hstep : (C : ℝ) * ((n : ℝ) + 1) ^ d ≤ (C : ℝ) * ((2 : ℝ) * n) ^ d := by
      have hbase : (n : ℝ) + 1 ≤ 2 * n := by linarith
      have hpow : ((n : ℝ) + 1) ^ d ≤ ((2 : ℝ) * n) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase d
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hstep2 : (C : ℝ) * ((2 : ℝ) * n) ^ d = ((C : ℝ) * (2 : ℝ) ^ d) * (n : ℝ) ^ d := by
      ring
    have hdata : ((C : ℝ) * (2 : ℝ) ^ d) ≤ n := by
      have := hbig
      push_cast at this
      exact this
    have hstep3 : ((C : ℝ) * (2 : ℝ) ^ d) * (n : ℝ) ^ d ≤ n * (n : ℝ) ^ d := by
      exact mul_le_mul_of_nonneg_right hdata (by positivity)
    have hstep4 : n * (n : ℝ) ^ d = (n : ℝ) ^ (d + 1) := by
      rw [pow_succ]
      ring
    calc (C : ℝ) * ((n : ℝ) + 1) ^ d
        ≤ (C : ℝ) * ((2 : ℝ) * n) ^ d := hstep
      _ = ((C : ℝ) * (2 : ℝ) ^ d) * (n : ℝ) ^ d := hstep2
      _ ≤ n * (n : ℝ) ^ d := hstep3
      _ = (n : ℝ) ^ (d + 1) := hstep4
      _ < (2 : ℝ) ^ n := hlt
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  simp only [polyCost, expCost]
  exact_mod_cast h

/-- The ceiling `√N` used for quadratic (Grover-type) speedups: `Nat.sqrt N + 1`. -/
def sqrtCost (N : ℕ) : ℕ := Nat.sqrt N + 1

/-- `sqrtCost N` squares above `N`: `N < (sqrtCost N)^2` (the defining ceiling
property of `√N`). -/
theorem sqrtCost_sq_gt (N : ℕ) : N < sqrtCost N ^ 2 := by
  simpa [sqrtCost] using Nat.lt_succ_sqrt' N

/-- `sqrtCost N` is at most `N` for `N ≥ 2`, so a quadratic speedup never costs
more than the classical linear scan. -/
theorem sqrtCost_le (N : ℕ) (hN : 2 ≤ N) : sqrtCost N ≤ N := by
  have h : Nat.sqrt N < N := Nat.sqrt_lt_self (by omega)
  simp only [sqrtCost]
  omega

/-- Composition of two quadratic speedups is a quartic speedup: applying the
`√·` cost ceiling twice leaves a cost whose fourth power exceeds the original
classical scale.  This is the arithmetic content of the survey's quartic
speedups built from two independent quadratic gains. -/
theorem quartic_of_two_quadratic (N : ℕ) :
    N < (sqrtCost (sqrtCost N)) ^ 4 := by
  set q := sqrtCost N
  set c := sqrtCost q
  have hNq : N < q ^ 2 := sqrtCost_sq_gt N
  have hqc : q < c ^ 2 := sqrtCost_sq_gt q
  have hqc' : q ^ 2 < (c ^ 2) ^ 2 := by
    exact Nat.pow_lt_pow_left hqc (by norm_num : (2 : ℕ) ≠ 0)
  calc N < q ^ 2 := hNq
    _ < (c ^ 2) ^ 2 := hqc'
    _ = c ^ 4 := by ring

/-- A pair of polynomially bounded costs has a polynomially bounded sum.
Used for "simulation + initial-state preparation" assessments: if both the
simulation and the preparation are `poly(N)`, so is their total. -/
def polyBound (C d n : ℕ) : Prop := ∀ m : ℕ, m = n → m ≤ C * (n + 1) ^ d

/-- If `f` has a polynomial bound of degree `d₁` and `g` one of degree `d₂`,
then `f + g` has a polynomial bound of degree `max d₁ d₂`. -/
theorem polySum_bound {f g : ℕ → ℕ} {C₁ C₂ d₁ d₂ : ℕ}
    (hf : ∀ n, f n ≤ C₁ * (n + 1) ^ d₁) (hg : ∀ n, g n ≤ C₂ * (n + 1) ^ d₂) :
    ∀ n, f n + g n ≤ (C₁ + C₂) * (n + 1) ^ (max d₁ d₂) := by
  intro n
  have hd₁ : (n + 1) ^ d₁ ≤ (n + 1) ^ (max d₁ d₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hd₂ : (n + 1) ^ d₂ ≤ (n + 1) ^ (max d₁ d₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h1 : f n ≤ C₁ * (n + 1) ^ (max d₁ d₂) :=
    le_trans (hf n) (Nat.mul_le_mul_left _ hd₁)
  have h2 : g n ≤ C₂ * (n + 1) ^ (max d₁ d₂) :=
    le_trans (hg n) (Nat.mul_le_mul_left _ hd₂)
  calc f n + g n ≤ C₁ * (n + 1) ^ (max d₁ d₂) + C₂ * (n + 1) ^ (max d₁ d₂) :=
        Nat.add_le_add h1 h2
    _ = (C₁ + C₂) * (n + 1) ^ (max d₁ d₂) := by ring

end Qatlib.Papers.QuantumSurvey23.MainResults.Scaling
