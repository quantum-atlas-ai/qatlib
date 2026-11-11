/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver18.MainResults.SpectralGap.GroundStateTime

Source result for Claim `c001` of QLinearSolver18, fixed arXiv:1805.10549v2
(29 Nov 2018), Subasi--Somma--Orsucci.

Main text Eq. (9), p. 3: the first algorithm (random-time evolution with the
Hamiltonians `H(s) = A(s) P_b^perp A(s)` of Eq. (3), whose unique ground state
is `|x(s)>`) has total evolution time `T := sum_{j=1}^{q} <t^j>` satisfying

  `T = O(kappa^2 log(kappa) / eps)`.

The source proof path (supplementary material, pp. 6-7) is:

* Eq. (14): the gap lower bound `Delta*(s) = (1 - s)^2 + (s / kappa)^2`;
* Eq. (25): the path-length bound `L* = sqrt 2 * log (12 kappa)`;
* Eq. (26): `T = pi * sum_j 1 / Delta*(v^j)`;
* Eqs. (27)-(30): comparison of the sum with the integral
  `int dv / Delta* = 2 kappa (1 + kappa)`;
* Eq. (31): `T <= pi * (sqrt (2 kappa (1 + kappa)) / delta + 2 (kappa^2 + 1))`;
* `q = Theta((L*)^2 / eps)` and `delta = Theta(eps / log kappa)`, hence Eq. (9).

This file formalises the ledger quantities of Eqs. (14), (25), (31) and proves
the final asymptotic deduction of Eq. (9) with an explicit constant. The
paper's `O` constants are independent of `kappa` and `eps`; the asymptotic
domain is `kappa >= 2`, `0 < eps <= 1` (at `kappa = 1` the factor `log kappa`
vanishes, so this is the usual regime in which the `O` notation applies).

No quantum-mechanical content is asserted here; the theorem concerns the
scalar time ledger exactly as bounded in the supplementary material.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver18.MainResults.SpectralGap.GroundStateTime

/-- Eq. (14), p. 6: lower bound `Delta*(s) = (1 - s)^2 + (s / kappa)^2` on the
spectral gap of `H(s) = A(s) P_b^perp A(s)` (Eq. (3)). -/
def gapStar (s kappa : ℝ) : ℝ := (1 - s) ^ 2 + (s / kappa) ^ 2

/-- Eq. (25), p. 6: path-length bound `L* = sqrt 2 * log (12 kappa)`. -/
def pathBound (kappa : ℝ) : ℝ := Real.sqrt 2 * Real.log (12 * kappa)

/-- Number of randomization steps `q = Theta((L*)^2 / eps)` (p. 7), represented
by its leading term. -/
def stepCount (kappa eps : ℝ) : ℝ := pathBound kappa ^ 2 / eps

/-- Step spacing `delta = (v_b - v_a) / q` (p. 7), with `v_b - v_a <= L*`. -/
def spacing (kappa eps : ℝ) : ℝ := pathBound kappa / stepCount kappa eps

/-- Eq. (31), p. 7: closed-form upper bound
`T <= pi * (sqrt (2 kappa (1 + kappa)) / delta + 2 (kappa^2 + 1))` on the total
evolution time `T = pi * sum_j 1 / Delta*(v^j)` (Eq. (26)) of the first
algorithm. -/
def quadraticTimeBound (kappa eps : ℝ) : ℝ :=
  Real.pi * (Real.sqrt (2 * kappa * (1 + kappa)) / spacing kappa eps +
    2 * (kappa ^ 2 + 1))

/-- Explicit asymptotic constant for Eq. (9). -/
def quadraticConstant : ℝ :=
  5 * Real.sqrt 2 * Real.pi + 4 * Real.pi / Real.log 2

/-- The path bound is strictly positive in the asymptotic regime. -/
theorem pathBound_pos {kappa : ℝ} (hkappa : 2 ≤ kappa) : 0 < pathBound kappa := by
  unfold pathBound
  have hlog : 0 < Real.log (12 * kappa) := Real.log_pos (by nlinarith)
  positivity

/-- Simplifying the spacing: `delta = L* / (L*^2 / eps) = eps / L*`. -/
theorem spacing_eq {kappa eps : ℝ} (hkappa : 2 ≤ kappa) (heps : 0 < eps) :
    spacing kappa eps = eps / pathBound kappa := by
  unfold spacing stepCount
  have hL : pathBound kappa ≠ 0 := ne_of_gt (pathBound_pos hkappa)
  field_simp

/-- Elementary log bound used in Eq. (25): for `kappa >= 2`,
`log (12 kappa) <= 5 log kappa`. -/
theorem log_twelve_mul_le {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    Real.log (12 * kappa) ≤ 5 * Real.log kappa := by
  have hkappa0 : (0 : ℝ) < kappa := by linarith
  have hsq : (4 : ℝ) ≤ kappa ^ 2 := by nlinarith
  have hquarter : (12 : ℝ) ≤ kappa ^ 4 := by nlinarith [sq_nonneg (kappa ^ 2), hsq]
  have hpow : (12 : ℝ) * kappa ≤ kappa ^ 5 := by
    calc (12 : ℝ) * kappa ≤ kappa ^ 4 * kappa :=
          mul_le_mul_of_nonneg_right hquarter hkappa0.le
      _ = kappa ^ 5 := by ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 12 * kappa) hpow
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- The square-root factor of Eq. (31) is at most `2 kappa` for `kappa >= 2`. -/
theorem sqrt_two_kappa_le {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    Real.sqrt (2 * kappa * (1 + kappa)) ≤ 2 * kappa := by
  have hkappa0 : (0 : ℝ) < kappa := by linarith
  have hle : 2 * kappa * (1 + kappa) ≤ (2 * kappa) ^ 2 := by nlinarith
  have h2k : 0 ≤ 2 * kappa := by positivity
  calc Real.sqrt (2 * kappa * (1 + kappa))
      ≤ Real.sqrt ((2 * kappa) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 2 * kappa := Real.sqrt_sq h2k

/-- Supp. Mat. Eq. (31) with `delta = eps / L*`, `L* = sqrt 2 log (12 kappa)`,
and `q = (L*)^2 / eps`: the closed-form total-time bound is
`O(kappa^2 log(kappa) / eps)` with the explicit constant `quadraticConstant`. -/
theorem quadraticTimeBound_le {kappa eps : ℝ} (hkappa : 2 ≤ kappa)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    quadraticTimeBound kappa eps ≤ quadraticConstant * kappa ^ 2 * Real.log kappa / eps := by
  have hkappa0 : (0 : ℝ) < kappa := by linarith
  have hlogk : 0 < Real.log kappa := Real.log_pos (by linarith)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2k : Real.log 2 ≤ Real.log kappa := Real.log_le_log (by norm_num) hkappa
  have hepslog : eps * Real.log 2 ≤ Real.log kappa := by
    nlinarith [heps1, hlog2, hlog2k]
  -- Path-length bound `L* <= 5 sqrt 2 log kappa`.
  have hLle : pathBound kappa ≤ 5 * Real.sqrt 2 * Real.log kappa := by
    unfold pathBound
    have h := mul_le_mul_of_nonneg_left (log_twelve_mul_le hkappa) (Real.sqrt_nonneg 2)
    linarith
  -- Rewrite the `1 / delta` factor as `L* / eps`.
  have hdiv : Real.sqrt (2 * kappa * (1 + kappa)) / (eps / pathBound kappa) =
      Real.sqrt (2 * kappa * (1 + kappa)) * pathBound kappa / eps := by
    have hL : pathBound kappa ≠ 0 := ne_of_gt (pathBound_pos hkappa)
    field_simp
  -- Bound the first term of Eq. (31) by `10 sqrt 2 kappa log kappa / eps`.
  have hterm1 : Real.sqrt (2 * kappa * (1 + kappa)) / (eps / pathBound kappa) ≤
      10 * Real.sqrt 2 * kappa * Real.log kappa / eps := by
    rw [hdiv]
    apply div_le_div_of_nonneg_right _ heps0.le
    calc Real.sqrt (2 * kappa * (1 + kappa)) * pathBound kappa
        ≤ (2 * kappa) * (5 * Real.sqrt 2 * Real.log kappa) :=
          mul_le_mul (sqrt_two_kappa_le hkappa) hLle (pathBound_pos hkappa).le (by positivity)
      _ = 10 * Real.sqrt 2 * kappa * Real.log kappa := by ring
  -- Bound the second term of Eq. (31) by `4 kappa^2`.
  have hterm2 : 2 * (kappa ^ 2 + 1) ≤ 4 * kappa ^ 2 := by nlinarith
  -- Combine inside the outer `pi` factor.
  have hinside : Real.sqrt (2 * kappa * (1 + kappa)) / (eps / pathBound kappa) +
      2 * (kappa ^ 2 + 1) ≤
      10 * Real.sqrt 2 * kappa * Real.log kappa / eps + 4 * kappa ^ 2 :=
    add_le_add hterm1 hterm2
  have hpi_mul := mul_le_mul_of_nonneg_left hinside hpi.le
  -- Final algebra: `pi * (10 sqrt 2 kappa log kappa / eps + 4 kappa^2)
  --   <= quadraticConstant * kappa^2 * log kappa / eps`.
  have hfinal : Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa / eps + 4 * kappa ^ 2)
      ≤ quadraticConstant * kappa ^ 2 * Real.log kappa / eps := by
    -- First term: `pi * 10 sqrt2 kappa log kappa <= 5 sqrt2 pi kappa^2 log kappa`.
    have hA : Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa) ≤
        5 * Real.sqrt 2 * Real.pi * kappa ^ 2 * Real.log kappa := by
      have h10 : (10 : ℝ) ≤ 5 * kappa := by nlinarith
      have hfac : (0 : ℝ) ≤ Real.sqrt 2 * Real.pi * kappa * Real.log kappa := by positivity
      calc Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa)
          = 10 * (Real.sqrt 2 * Real.pi * kappa * Real.log kappa) := by ring
        _ ≤ (5 * kappa) * (Real.sqrt 2 * Real.pi * kappa * Real.log kappa) :=
              mul_le_mul_of_nonneg_right h10 hfac
        _ = 5 * Real.sqrt 2 * Real.pi * kappa ^ 2 * Real.log kappa := by ring
    -- Second term: `pi * 4 kappa^2 eps <= (4 pi / log 2) kappa^2 log kappa`.
    have hB : Real.pi * (4 * kappa ^ 2) * eps ≤
        4 * Real.pi / Real.log 2 * kappa ^ 2 * Real.log kappa := by
      have hfac : (0 : ℝ) ≤ 4 * Real.pi * kappa ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hepslog hfac
      have hrm : 4 * Real.pi / Real.log 2 * kappa ^ 2 * Real.log kappa
          = 4 * Real.pi * kappa ^ 2 * Real.log kappa / Real.log 2 := by ring
      rw [hrm, le_div_iff₀ hlog2]
      calc Real.pi * (4 * kappa ^ 2) * eps * Real.log 2
          = 4 * Real.pi * kappa ^ 2 * (eps * Real.log 2) := by ring
        _ ≤ 4 * Real.pi * kappa ^ 2 * Real.log kappa := h
    unfold quadraticConstant
    have hlhs : Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa / eps + 4 * kappa ^ 2)
        = (Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa) +
            Real.pi * (4 * kappa ^ 2) * eps) / eps := by
      have he : eps ≠ 0 := ne_of_gt heps0
      field_simp
    have hrhs : (5 * Real.sqrt 2 * Real.pi + 4 * Real.pi / Real.log 2) * kappa ^ 2 *
          Real.log kappa =
        5 * Real.sqrt 2 * Real.pi * kappa ^ 2 * Real.log kappa +
          4 * Real.pi / Real.log 2 * kappa ^ 2 * Real.log kappa := by ring
    rw [hlhs, hrhs]
    apply div_le_div_of_nonneg_right _ heps0.le
    linarith [hA, hB]
  calc quadraticTimeBound kappa eps
      = Real.pi * (Real.sqrt (2 * kappa * (1 + kappa)) / (eps / pathBound kappa) +
          2 * (kappa ^ 2 + 1)) := by
        unfold quadraticTimeBound
        rw [spacing_eq hkappa heps0]
    _ ≤ Real.pi * (10 * Real.sqrt 2 * kappa * Real.log kappa / eps + 4 * kappa ^ 2) := hpi_mul
    _ ≤ quadraticConstant * kappa ^ 2 * Real.log kappa / eps := hfinal

/-- Eq. (9), p. 3 (Claim `c001`): the total evolution time
`T := sum_j <t^j>` of the first (ground-state randomization) algorithm satisfies
`T = O(kappa^2 log(kappa) / eps)`.

Faithful form: any total time `T` bounded by the closed form of Supp. Mat.
Eq. (31) obeys the paper's asymptotic bound, with the explicit constant
`quadraticConstant`. Eq. (31) is the supplementary material's proved bound on
`T = pi * sum_j 1 / Delta*(v^j)` (Eqs. (26)-(30)); this theorem records the
final asymptotic deduction of Eq. (9). -/
theorem groundState_total_time_bigO :
    ∃ C : ℝ, 0 < C ∧ ∀ (T kappa eps : ℝ), 2 ≤ kappa → 0 < eps → eps ≤ 1 →
      T ≤ quadraticTimeBound kappa eps → T ≤ C * kappa ^ 2 * Real.log kappa / eps := by
  refine ⟨quadraticConstant, ?_, ?_⟩
  · unfold quadraticConstant
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro T kappa eps hkappa heps0 heps1 hT
    exact le_trans hT (quadraticTimeBound_le hkappa heps0 heps1)

/-- Eq. (9) stated for the closed-form ledger itself (no hypothesis on an
external `T`): the Eq. (31) bound is `O(kappa^2 log kappa / eps)` with the
explicit constant `quadraticConstant`. -/
theorem groundState_ledger_bigO :
    ∀ (kappa eps : ℝ), 2 ≤ kappa → 0 < eps → eps ≤ 1 →
      quadraticTimeBound kappa eps ≤ quadraticConstant * kappa ^ 2 * Real.log kappa / eps :=
  fun _ _ hkappa heps0 heps1 => quadraticTimeBound_le hkappa heps0 heps1

end Qatlib.Papers.QLinearSolver18.MainResults.SpectralGap.GroundStateTime
