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
# QLinearSolver18.MainResults.SpectralGap.AmplifiedGapTime

Source result for Claim `c002` of QLinearSolver18, fixed arXiv:1805.10549v2
(29 Nov 2018), Subasi--Somma--Orsucci.

Main text Eq. (12), p. 3: the second algorithm (spectral gap amplification,
using the Hamiltonians `H'(s) = sigma+ (x) A(s) P_b^perp + sigma- (x) P_b^perp A(s)`
of Eq. (10), whose zero-eigenvalue subspace contains `|0> (x) |x(s)>`) has
total evolution time `T := sum_{j=1}^{q} <t^j>` satisfying

  `T = O(kappa log(kappa) / eps)`.

Source proof path (supplementary material, p. 7):

* Eq. (32): `T = pi * sum_j 1 / sqrt (Delta*(v^j))`;
* Eq. (33): comparison of the sum with the integral
  `int dv / sqrt (Delta*) = pi kappa / sqrt 2`;
* Eq. (34)-(35): `T <= pi * (pi kappa / (sqrt 2 * delta) + 2 sqrt (kappa^2 + 1))`;
* `delta = Theta(eps / log kappa)` then gives Eq. (12).

This file formalises the Eq. (35) ledger and proves the final asymptotic
deduction of Eq. (12) with an explicit constant. Domain: `kappa >= 2`,
`0 < eps <= 1` (the `O`-notation asymptotic regime; see the c001 file).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver18.MainResults.SpectralGap.AmplifiedGapTime

/-- Eq. (25), p. 6: path-length bound `L* = sqrt 2 * log (12 kappa)`. -/
def pathBound (kappa : ℝ) : ℝ := Real.sqrt 2 * Real.log (12 * kappa)

/-- Number of randomization steps `q = Theta((L*)^2 / eps)` (p. 7). -/
def stepCount (kappa eps : ℝ) : ℝ := pathBound kappa ^ 2 / eps

/-- Step spacing `delta = (v_b - v_a) / q` (p. 7), with `v_b - v_a <= L*`. -/
def spacing (kappa eps : ℝ) : ℝ := pathBound kappa / stepCount kappa eps

/-- Eq. (35), p. 7: closed-form upper bound
`T <= pi * (pi kappa / (sqrt 2 * delta) + 2 sqrt (kappa^2 + 1))` on the total
evolution time `T = pi * sum_j 1 / sqrt (Delta*(v^j))` (Eq. (32)) of the second,
gap-amplified algorithm. -/
def linearTimeBound (kappa eps : ℝ) : ℝ :=
  Real.pi * (Real.pi * kappa / (Real.sqrt 2 * spacing kappa eps) +
    2 * Real.sqrt (kappa ^ 2 + 1))

/-- Explicit asymptotic constant for Eq. (12). -/
def linearConstant : ℝ := 5 * Real.pi ^ 2 + 2 * Real.sqrt 2 * Real.pi / Real.log 2

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

/-- Elementary log bound from Eq. (25): for `kappa >= 2`,
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

/-- `sqrt (kappa^2 + 1) <= sqrt 2 * kappa` for `kappa >= 1`. -/
theorem sqrt_sq_add_one_le {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    Real.sqrt (kappa ^ 2 + 1) ≤ Real.sqrt 2 * kappa := by
  have hkappa0 : (0 : ℝ) < kappa := by linarith
  have hle : kappa ^ 2 + 1 ≤ 2 * kappa ^ 2 := by nlinarith
  calc Real.sqrt (kappa ^ 2 + 1) ≤ Real.sqrt (2 * kappa ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 2 * kappa := by
        rw [show (2 : ℝ) * kappa ^ 2 = 2 * kappa ^ 2 from rfl,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hkappa0.le]

/-- Supp. Mat. Eq. (35) with `delta = eps / L*`: the closed-form total-time
bound is `O(kappa log kappa / eps)` with the explicit constant `linearConstant`. -/
theorem linearTimeBound_le {kappa eps : ℝ} (hkappa : 2 ≤ kappa)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    linearTimeBound kappa eps ≤ linearConstant * kappa * Real.log kappa / eps := by
  have hkappa0 : (0 : ℝ) < kappa := by linarith
  have hlogk : 0 < Real.log kappa := Real.log_pos (by linarith)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2k : Real.log 2 ≤ Real.log kappa := Real.log_le_log (by norm_num) hkappa
  have hepslog : eps * Real.log 2 ≤ Real.log kappa := by
    nlinarith [heps1, hlog2, hlog2k]
  have hLle : pathBound kappa ≤ 5 * Real.sqrt 2 * Real.log kappa := by
    unfold pathBound
    have h := mul_le_mul_of_nonneg_left (log_twelve_mul_le hkappa) (Real.sqrt_nonneg 2)
    linarith
  -- Rewrite the `1 / delta` factor: `pi kappa / (sqrt 2 * eps/L*) = pi kappa L* / (sqrt 2 eps)`.
  have hdiv : Real.pi * kappa / (Real.sqrt 2 * (eps / pathBound kappa)) =
      Real.pi * kappa * pathBound kappa / (Real.sqrt 2 * eps) := by
    have hL : pathBound kappa ≠ 0 := ne_of_gt (pathBound_pos hkappa)
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2
    have he : eps ≠ 0 := ne_of_gt heps0
    field_simp
  -- First term of Eq. (35): `pi kappa / (sqrt 2 delta) <= 5 pi kappa log kappa / eps`.
  have hterm1 : Real.pi * kappa / (Real.sqrt 2 * (eps / pathBound kappa)) ≤
      5 * Real.pi * kappa * Real.log kappa / eps := by
    rw [hdiv]
    have hrew : Real.pi * kappa * pathBound kappa / (Real.sqrt 2 * eps) =
        (Real.pi * kappa * pathBound kappa / Real.sqrt 2) / eps := by
      have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2
      have he : eps ≠ 0 := ne_of_gt heps0
      field_simp
    rw [hrew]
    apply div_le_div_of_nonneg_right _ heps0.le
    rw [div_le_iff₀ hsqrt2]
    calc Real.pi * kappa * pathBound kappa
        ≤ Real.pi * kappa * (5 * Real.sqrt 2 * Real.log kappa) :=
          mul_le_mul_of_nonneg_left hLle (by positivity)
      _ = 5 * Real.pi * kappa * Real.log kappa * Real.sqrt 2 := by ring
  -- Second term of Eq. (35): `2 sqrt (kappa^2+1) <= 2 sqrt2 kappa`.
  have hterm2 : 2 * Real.sqrt (kappa ^ 2 + 1) ≤ 2 * Real.sqrt 2 * kappa := by
    have h := sqrt_sq_add_one_le hkappa
    linarith
  -- Multiply the inner sum by the outer `pi`.
  have hinside : Real.pi * kappa / (Real.sqrt 2 * (eps / pathBound kappa)) +
      2 * Real.sqrt (kappa ^ 2 + 1) ≤
      5 * Real.pi * kappa * Real.log kappa / eps + 2 * Real.sqrt 2 * kappa :=
    add_le_add hterm1 hterm2
  have hpi_mul := mul_le_mul_of_nonneg_left hinside hpi.le
  -- Final algebra with the constant `linearConstant`.
  have hfirst : Real.pi * (5 * Real.pi * kappa * Real.log kappa / eps) =
      5 * Real.pi ^ 2 * kappa * Real.log kappa / eps := by
    have he : eps ≠ 0 := ne_of_gt heps0
    field_simp
  have hsecond : Real.pi * (2 * Real.sqrt 2 * kappa) = 2 * Real.sqrt 2 * Real.pi * kappa := by
    ring
  have hB : 2 * Real.sqrt 2 * Real.pi * kappa ≤
      2 * Real.sqrt 2 * Real.pi / Real.log 2 * kappa * Real.log kappa / eps := by
    have hrm : 2 * Real.sqrt 2 * Real.pi / Real.log 2 * kappa * Real.log kappa / eps =
        (2 * Real.sqrt 2 * Real.pi * kappa * Real.log kappa / Real.log 2) / eps := by
      have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
      have he : eps ≠ 0 := ne_of_gt heps0
      field_simp
    rw [hrm]
    rw [le_div_iff₀ heps0]
    rw [le_div_iff₀ hlog2]
    calc 2 * Real.sqrt 2 * Real.pi * kappa * eps * Real.log 2
        = 2 * Real.sqrt 2 * Real.pi * kappa * (eps * Real.log 2) := by ring
      _ ≤ 2 * Real.sqrt 2 * Real.pi * kappa * Real.log kappa :=
            mul_le_mul_of_nonneg_left hepslog (by positivity)
  have hfinal : 5 * Real.pi ^ 2 * kappa * Real.log kappa / eps +
      2 * Real.sqrt 2 * Real.pi * kappa ≤
      linearConstant * kappa * Real.log kappa / eps := by
    unfold linearConstant
    have hrhs : (5 * Real.pi ^ 2 + 2 * Real.sqrt 2 * Real.pi / Real.log 2) *
          kappa * Real.log kappa / eps =
        5 * Real.pi ^ 2 * kappa * Real.log kappa / eps +
          2 * Real.sqrt 2 * Real.pi / Real.log 2 * kappa * Real.log kappa / eps := by
      have he : eps ≠ 0 := ne_of_gt heps0
      field_simp
    rw [hrhs]
    linarith [hB]
  calc linearTimeBound kappa eps
      = Real.pi * (Real.pi * kappa / (Real.sqrt 2 * (eps / pathBound kappa)) +
          2 * Real.sqrt (kappa ^ 2 + 1)) := by
        unfold linearTimeBound
        rw [spacing_eq hkappa heps0]
    _ ≤ Real.pi * (5 * Real.pi * kappa * Real.log kappa / eps +
          2 * Real.sqrt 2 * kappa) := hpi_mul
    _ = 5 * Real.pi ^ 2 * kappa * Real.log kappa / eps +
          2 * Real.sqrt 2 * Real.pi * kappa := by
        rw [mul_add, hfirst, hsecond]
    _ ≤ linearConstant * kappa * Real.log kappa / eps := hfinal

/-- Eq. (12), p. 3 (Claim `c002`): the total evolution time
`T := sum_j <t^j>` of the second (spectral gap amplification) algorithm satisfies
`T = O(kappa log(kappa) / eps)`.

Faithful form: any total time `T` bounded by the closed form of Supp. Mat.
Eq. (35) obeys the paper's asymptotic bound, with the explicit constant
`linearConstant`. Eq. (35) is the supplementary material's proved bound on
`T = pi * sum_j 1 / sqrt (Delta*(v^j))` (Eqs. (32)-(34)). -/
theorem amplifiedGap_total_time_bigO :
    ∃ C : ℝ, 0 < C ∧ ∀ (T kappa eps : ℝ), 2 ≤ kappa → 0 < eps → eps ≤ 1 →
      T ≤ linearTimeBound kappa eps → T ≤ C * kappa * Real.log kappa / eps := by
  refine ⟨linearConstant, ?_, ?_⟩
  · unfold linearConstant
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro T kappa eps hkappa heps0 heps1 hT
    exact le_trans hT (linearTimeBound_le hkappa heps0 heps1)

/-- Eq. (12) stated for the closed-form ledger itself, with the explicit
constant `linearConstant`. -/
theorem amplifiedGap_ledger_bigO :
    ∀ (kappa eps : ℝ), 2 ≤ kappa → 0 < eps → eps ≤ 1 →
      linearTimeBound kappa eps ≤ linearConstant * kappa * Real.log kappa / eps :=
  fun _ _ hkappa heps0 heps1 => linearTimeBound_le hkappa heps0 heps1

end Qatlib.Papers.QLinearSolver18.MainResults.SpectralGap.AmplifiedGapTime
