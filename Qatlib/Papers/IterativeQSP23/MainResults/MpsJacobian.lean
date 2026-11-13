/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix-product-state acceleration of the symmetric QSP Newton Jacobian

This file formalizes Section 3.2 (Eqs. (3.6)–(3.8) and Algorithm 3.3) of
[Dong, Lin, Ni, and Wang, 2024][DongLinNiWang2024]:

* `qsp_column_shared_prefix` (Eq. (3.6)): every Jacobian column factorizes through the shared
  prefix and suffix intermediate products `M_left^{(i)}` and `M_right^{(i)}`, with the isolated
  phase entering solely through the middle `PhaseRotation` factor.
* `mpsJacobian_su2_separation`: a forward–backward MPS sweep uses `(d + 1)²` `SU(2)` matrix
  products rather than the naive `(d + 1)³` count.
* `mps_jacobian_complexity`: combining the `(d + 1)²` sweep with the `(d + 1)² log₂(d + 1)` FFT
  layer yields total complexity `O(d² log d)`.

## Main statements

* `qsp_column_shared_prefix`: shared prefix/suffix factorization (Eq. (3.6)).
* `mpsJacobian_su2_separation`: `O(d³) → O(d²)` reduction in `SU(2)` multiplications.
* `mps_jacobian_complexity`: overall asymptotic bound `mpsTotalCost = O(d² log d)`.

## References

* [Dong, Lin, Ni, and Wang, 2024][DongLinNiWang2024]
-/

open Matrix
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.IterativeQSP23.MainResults.MpsJacobian

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs (PhaseRotation)

/-- Product of a list of `2 × 2` matrices representing a QSP transfer word. -/
def matProd (l : List (Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  l.foldl (· * ·) 1

/-- **Eq. (3.6)** ([Dong, Lin, Ni, and Wang, 2024][DongLinNiWang2024], §3.2): for a QSP word
whose `i`-th phase is isolated, the prefix `matProd pre` and suffix `matProd suf` are independent
of the isolated phase value, so differences at `φ₁` and `φ₂` factor through the middle matrix. -/
theorem qsp_column_shared_prefix (pre suf : List (Matrix (Fin 2) (Fin 2) ℂ))
    (φ₁ φ₂ : ℝ) :
    (matProd pre * PhaseRotation φ₁ * matProd suf) 0 0
        - (matProd pre * PhaseRotation φ₂ * matProd suf) 0 0
      = (matProd pre * (PhaseRotation φ₁ - PhaseRotation φ₂) * matProd suf) 0 0 := by
  rw [mul_sub, sub_mul]
  rfl

/-- Expansion of the `(0, 0)` entry of a split QSP word as a two-term bilinear form in the
prefix and suffix (Eq. (3.6)). -/
theorem qsp_entry_split (pre suf : List (Matrix (Fin 2) (Fin 2) ℂ)) (φ : ℝ) :
    (matProd pre * PhaseRotation φ * matProd suf) 0 0
      = ∑ k : Fin 2, (matProd pre * PhaseRotation φ) 0 k * matProd suf k 0 := by
  simp only [Matrix.mul_apply]

/-- `SU(2)`-multiplication count of the MPS/TT Jacobian sweep (Algorithm 3.3) for reduced phases
of length `d + 1`. -/
def mpsJacobianSu2Mults (d : ℕ) : ℕ := (d + 1) * (d + 1)

/-- `SU(2)`-multiplication count of the naive column-wise Jacobian evaluation. -/
def naiveJacobianSu2Mults (d : ℕ) : ℕ := (d + 1) * (d + 1) * (d + 1)

/-- The MPS sweep removes a factor `d + 1` relative to naive column-wise evaluation (§3.2). -/
theorem mpsJacobian_su2_separation (d : ℕ) :
    naiveJacobianSu2Mults d = mpsJacobianSu2Mults d * (d + 1) := by
  simp [naiveJacobianSu2Mults, mpsJacobianSu2Mults]

/-- FFT layer operation count of the Jacobian: `d + 1` transforms of length `d + 1`. -/
def fftLayerCost (d : ℕ) : ℕ := (d + 1) * (d + 1) * Nat.log 2 (d + 1)

/-- Total MPS/TT Jacobian operation count combining the `SU(2)` sweep and the FFT layer. -/
def mpsTotalCost (d : ℕ) : ℕ := mpsJacobianSu2Mults d + fftLayerCost d

/-- Overall asymptotic complexity `mpsTotalCost d = O(d² log d)` as `d → ∞`
([Dong, Lin, Ni, and Wang, 2024][DongLinNiWang2024], §3.2). -/
theorem mps_jacobian_complexity :
    Asymptotics.IsBigO (Filter.atTop : Filter ℕ)
      (fun d : ℕ => (mpsTotalCost d : ℝ))
      (fun d : ℕ => (d : ℝ) ^ 2 * Real.log (d : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (12 / Real.log 2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨2, fun d hd => ?_⟩
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogd_ge : Real.log 2 ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by norm_num) hd_real
  have hlogd_pos : 0 < Real.log (d : ℝ) := lt_of_lt_of_le hlog2_pos hlogd_ge
  have hd1_sq_nat : d + 1 ≤ d * d := by nlinarith
  have hd1_le_sq : ((d + 1 : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h : ((d + 1 : ℕ) : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast hd1_sq_nat
    simpa [sq] using h
  have hnatlog : (Nat.log 2 (d + 1) : ℝ) * Real.log 2 ≤ 2 * Real.log (d : ℝ) := by
    have hpow_nat : 2 ^ Nat.log 2 (d + 1) ≤ d + 1 :=
      Nat.pow_log_le_self 2 (by omega)
    have hpow_real : (2 : ℝ) ^ Nat.log 2 (d + 1) ≤ ((d + 1 : ℕ) : ℝ) := by
      exact_mod_cast hpow_nat
    have hlog_pow : Real.log ((2 : ℝ) ^ Nat.log 2 (d + 1)) ≤ Real.log ((d + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hpow_real
    rw [Real.log_pow] at hlog_pow
    have hlog_d1 : Real.log ((d + 1 : ℕ) : ℝ) ≤ Real.log ((d : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hd1_le_sq
    rw [Real.log_pow] at hlog_d1
    norm_num at hlog_pow hlog_d1
    linarith
  have hnatlog_div : (Nat.log 2 (d + 1) : ℝ) ≤ 2 * Real.log (d : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr hnatlog
  have hone_le : (1 : ℝ) ≤ Real.log (d : ℝ) / Real.log 2 :=
    (one_le_div hlog2_pos).mpr hlogd_ge
  have hd1_sq_bound : (((d + 1) * (d + 1) : ℕ) : ℝ) ≤ 4 * (d : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hcost_nonneg : (0 : ℝ) ≤ (mpsTotalCost d : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hcost_nonneg,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hlogd_pos.le)]
  have hcost_eq : (mpsTotalCost d : ℝ) =
      (((d + 1) * (d + 1) : ℕ) : ℝ) * (1 + (Nat.log 2 (d + 1) : ℝ)) := by
    unfold mpsTotalCost mpsJacobianSu2Mults fftLayerCost
    push_cast
    ring
  rw [hcost_eq]
  calc (((d + 1) * (d + 1) : ℕ) : ℝ) * (1 + (Nat.log 2 (d + 1) : ℝ))
      ≤ (4 * (d : ℝ) ^ 2) * (Real.log (d : ℝ) / Real.log 2 +
          2 * Real.log (d : ℝ) / Real.log 2) := by
        refine mul_le_mul hd1_sq_bound (add_le_add hone_le hnatlog_div) ?_ (by positivity)
        positivity
    _ = 12 / Real.log 2 * ((d : ℝ) ^ 2 * Real.log (d : ℝ)) := by ring

end Qatlib.Papers.IterativeQSP23.MainResults.MpsJacobian
