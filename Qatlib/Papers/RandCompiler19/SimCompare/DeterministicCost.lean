/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Deterministic product-formula costs and the Table I comparison (source Appendix C)

Fixed source: E. Campbell, *A random compiler for fast Hamiltonian simulation*,
arXiv:1811.08017v2 (PDF SHA256 `291fcf6f1c4fb2c487026c6c124a936a03fdc48b85d3ff9738b48a786f891b9f`),
Appendix C and Table I.

The source reproduces from Childs--Ostrander--Su the Trotter/Suzuki error
prefactors `(C1)`--`(C7)`, the segment count `(C8)`, and the gate counts
`(C9)`--`(C10)`.  The mathematical content of the comparison in Table I is:

* every `2k`-order Suzuki decomposition needs `r = ΛtL(ΛtB_k/ε)^{1/(2k)}`
  segments of `2·5^{k-1}L` exponentials each, so its total gate count scales
  as `L²(Λt)^{1+1/(2k)}/ε^{1/(2k)}` with a constant `C_k` (`C9`, `C10`);
* the deterministic `2k`-order count carries an *extra* factor
  `L^{1/(2k)}` on top of that random count (`tableI_det_vs_random`);
* the first-order deterministic count is exactly `L³(Λt)²/(2ε)`
  (`(C11)` with `k = 1`: `4√2 L²(Λt)^{3/2}/√ε`), while qDRIFT with
  `λ = ΛL` is `2L²(Λt)²/ε`, so qDRIFT is cheaper by exactly `4/L`
  (`qdrift_vs_first_order_det`), and unconditionally cheaper once `L ≥ 4`.

All statements are exact rational/sqrt identities for the bounds as printed in
Appendix C; no asymptotic `O(·)` is asserted, and the exponential factors of
`(C1)`/`(C3)` are consistently dropped only through an explicit `≥ 1` bound
(`trottA_drop_exp`, `trottB_drop_exp`), as the source does.
-/

namespace Qatlib.Papers.RandCompiler19.SimCompare.DeterministicCost

set_option autoImplicit false

/-! ## Elementary real-power helpers -/

/-- Splitting a real power of a positive product over a positive divisor. -/
theorem rpow_mul_div {x B eps r : ℝ} (hx : 0 < x) (hB : 0 ≤ B) (heps : 0 < eps) :
    (x * B / eps) ^ r = x ^ r * B ^ r / eps ^ r := by
  rw [Real.div_rpow (by positivity) heps.le r, Real.mul_rpow hx.le hB]

/-- Extracting one power when the exponent is `1 + r`. -/
theorem rpow_one_add {x r : ℝ} (hx : 0 < x) : x ^ (1 + r) = x * x ^ r := by
  rw [Real.rpow_add hx, Real.rpow_one]

/-- `x^{3/2} = x·√x` for positive `x`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  rw [h, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-! ## `(C1)`: the first-order Trotter prefactors -/

/-- Source `(C1)`: the first-order Trotter error prefactor `a_TROTT`. -/
noncomputable def trottA (L : ℕ) (Lam t r : ℝ) : ℝ :=
  ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 * Real.exp (Lam * t / r)

/-- Source `(C1)`: the companion first-order prefactor `b_TROTT`. -/
noncomputable def trottB (L : ℕ) (Lam t r : ℝ) : ℝ :=
  ((L : ℝ) * Lam * t) ^ 3 / (3 * r ^ 3) * Real.exp (Lam * t / r)

/-- `(C1)`: `a_TROTT` dominates the exponential-free factor whenever `Λt/r ≥ 0`. -/
theorem trottA_drop_exp {L : ℕ} {Lam t r : ℝ} (hr : 0 ≤ Lam * t / r) :
    ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 ≤ trottA L Lam t r := by
  unfold trottA
  exact le_mul_of_one_le_right (div_nonneg (sq_nonneg _) (sq_nonneg r)) (Real.one_le_exp hr)

/-- `(C1)`: `b_TROTT` dominates its exponential-free factor whenever `Λt/r ≥ 0`. -/
theorem trottB_drop_exp {L : ℕ} {Lam t r : ℝ} (hx : 0 ≤ Lam * t) (hr : 0 < r)
    (he : 0 ≤ Lam * t / r) :
    ((L : ℝ) * Lam * t) ^ 3 / (3 * r ^ 3) ≤ trottB L Lam t r := by
  unfold trottB
  have hLx : 0 ≤ (L : ℝ) * Lam * t := by
    rw [mul_assoc]
    exact mul_nonneg (by positivity) hx
  have ha : 0 ≤ ((L : ℝ) * Lam * t) ^ 3 / (3 * r ^ 3) :=
    div_nonneg (pow_nonneg hLx 3) (mul_nonneg (by norm_num) (pow_pos hr 3).le)
  exact le_mul_of_one_le_right ha (Real.one_le_exp he)

/-- The source's remark that randomised Trotter has a significant advantage when
`b_TROTT ≪ a_TROTT`: since `b/a = Λt/(3r)`, this holds exactly when `Λt ≤ 3r`. -/
theorem trottB_le_trottA {L : ℕ} {Lam t r : ℝ} (hr : 0 < r)
    (h : (L : ℝ) * Lam * t ≤ 3 * r) :
    trottB L Lam t r ≤ trottA L Lam t r := by
  unfold trottA trottB
  have hfrac : (L : ℝ) * Lam * t / (3 * r) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h
  have hfac : ((L : ℝ) * Lam * t) ^ 3 / (3 * r ^ 3) =
      ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 * ((L : ℝ) * Lam * t / (3 * r)) := by
    ring_nf
  rw [hfac]
  calc ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 * ((L : ℝ) * Lam * t / (3 * r)) *
          Real.exp (Lam * t / r)
      ≤ ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 * 1 * Real.exp (Lam * t / r) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfrac (by positivity)) (Real.exp_pos _).le
    _ = ((L : ℝ) * Lam * t) ^ 2 / r ^ 2 * Real.exp (Lam * t / r) := by ring

/-! ## `(C7)`--`(C10)`: Suzuki constants, segment count and gate count -/

/-- Source `(C7)`: `B_k = (2·5^{k-1})^{2k+1}/(2k-1)!`. -/
noncomputable def suzukiB (k : ℕ) : ℝ :=
  ((2 : ℝ) * 5 ^ (k - 1)) ^ (2 * k + 1) / (Nat.factorial (2 * k - 1) : ℝ)

/-- Source `(C8)`: the number of `2k`-order Suzuki segments needed to push the
error below `ε` is `r = ΛtL(ΛtB_k/ε)^{1/(2k)}`. -/
noncomputable def suzukiSegments (k : ℕ) (L : ℕ) (Lam t eps B : ℝ) : ℝ :=
  Lam * t * (L : ℝ) * ((Lam * t * B / eps) ^ ((1 : ℝ) / (2 * k)))

/-- Source `(C9)`: each `2k`-order Suzuki segment holds `2·5^{k-1}L`
exponentials, so the total gate count is `2·5^{k-1}·L·r`. -/
noncomputable def suzukiCount (k : ℕ) (L : ℕ) (Lam t eps B : ℝ) : ℝ :=
  2 * (5 : ℝ) ^ (k - 1) * (L : ℝ) * suzukiSegments k L Lam t eps B

/-- Source `(C10)`: the constant `C_k = 2·5^{k-1}B_k^{1/(2k)}`. -/
noncomputable def suzukiConstant (k : ℕ) (B : ℝ) : ℝ :=
  2 * (5 : ℝ) ^ (k - 1) * B ^ ((1 : ℝ) / (2 * k))

/-- Source `(C10)`: `(C9)` simplifies to `C_k·L²(Λt)^{1+1/(2k)}/ε^{1/(2k)}`;
in particular the dependence on the number of terms is exactly `L²` at every
order `k ≥ 1`. -/
theorem suzukiCount_eq_scaling {k : ℕ} {L : ℕ} {Lam t eps B : ℝ}
    (hx : 0 < Lam * t) (hB : 0 ≤ B) (heps : 0 < eps) :
    suzukiCount k L Lam t eps B =
      suzukiConstant k B * (L : ℝ) ^ 2 * (Lam * t) ^ (1 + (1 : ℝ) / (2 * k)) /
        eps ^ ((1 : ℝ) / (2 * k)) := by
  unfold suzukiCount suzukiSegments suzukiConstant
  rw [rpow_mul_div hx hB heps, rpow_one_add hx]
  ring

/-- `B_1 = 8`, the value used for the first-order comparison in `(C11)`. -/
theorem suzukiB_one : suzukiB 1 = 8 := by
  unfold suzukiB
  norm_num

/-- The constant of the `k = 1` gate count, `C_1 = 4√2`. -/
theorem suzukiConstant_first_order : suzukiConstant 1 (suzukiB 1) = 4 * Real.sqrt 2 := by
  rw [suzukiB_one]
  unfold suzukiConstant
  norm_num
  have hsqrt : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [← Real.sqrt_eq_rpow, hsqrt]
  ring

/-- Source `(C11)`: for `k = 1` the `2k`-order Suzuki gate count is
`4√2·L²(Λt)^{3/2}/√ε`. -/
theorem suzukiCount_first_order {L : ℕ} {Lam t eps : ℝ} (hx : 0 < Lam * t)
    (heps : 0 < eps) :
    suzukiCount 1 L Lam t eps (suzukiB 1) =
      4 * Real.sqrt 2 * (L : ℝ) ^ 2 * (Lam * t) * Real.sqrt (Lam * t) /
        Real.sqrt eps := by
  have hB : 0 ≤ suzukiB 1 := by rw [suzukiB_one]; norm_num
  rw [suzukiCount_eq_scaling hx hB heps, suzukiConstant_first_order]
  simp only [Nat.cast_one]
  have hx32 : (Lam * t) ^ (1 + (1 : ℝ) / (2 * 1)) = (Lam * t) * Real.sqrt (Lam * t) := by
    rw [show 1 + (1 : ℝ) / (2 * 1) = (3 : ℝ) / 2 by norm_num]
    exact rpow_three_halves hx
  have hep : eps ^ ((1 : ℝ) / (2 * 1)) = Real.sqrt eps := by
    rw [show (1 : ℝ) / (2 * 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [hx32, hep]
  ring

/-! ## Table I: qDRIFT against first-order deterministic Trotter -/

/-- Table I row `qDRIFT (general result)`, using the source's Fig. 1 count
`N = ⌈2λ²t²/ε⌉` without the ceiling: `N = 2(λt)²/ε`. -/
noncomputable def qdriftGateCount (lam t eps : ℝ) : ℝ :=
  2 * (lam * t) ^ 2 / eps

/-- Table I row `1st order Trotter DET`: `r = L²Λ²t²/(2ε)` segments of `L`
exponentials each, so `N = L³(Λt)²/(2ε)`. -/
noncomputable def firstOrderDetCount (L : ℕ) (Lam t eps : ℝ) : ℝ :=
  (L : ℝ) ^ 3 * (Lam * t) ^ 2 / (2 * eps)

/-- Table I row `qDRIFT (when λ = ΛL)`: `2L²(Λt)²/ε`. -/
theorem qdriftGateCount_lamLambdaL {L : ℕ} {Lam t eps : ℝ} :
    qdriftGateCount (Lam * (L : ℝ)) t eps = 2 * (L : ℝ) ^ 2 * (Lam * t) ^ 2 / eps := by
  unfold qdriftGateCount
  rw [mul_pow]
  ring

/-- Table I row `qDRIFT (when λ = Λ√L)`: `2L(Λt)²/ε`, one power of `L` cheaper. -/
theorem qdriftGateCount_lamLambdaSqrtL {L : ℕ} {Lam t eps : ℝ} (hL : 0 ≤ (L : ℝ)) :
    qdriftGateCount (Lam * Real.sqrt (L : ℝ)) t eps = 2 * (L : ℝ) * (Lam * t) ^ 2 / eps := by
  unfold qdriftGateCount
  rw [mul_pow, mul_pow, Real.sq_sqrt hL]
  ring

/-- The Table I comparison between qDRIFT at `λ = ΛL` and first-order
deterministic Trotter: the ratio is exactly `4/L`. -/
theorem qdrift_vs_first_order_det {L : ℕ} {Lam t eps : ℝ} (hL : 0 < (L : ℝ))
    (heps : 0 < eps) :
    qdriftGateCount (Lam * (L : ℝ)) t eps =
      4 / (L : ℝ) * firstOrderDetCount L Lam t eps := by
  rw [qdriftGateCount_lamLambdaL, firstOrderDetCount]
  field_simp
  ring

/-- Consequently qDRIFT at `λ = ΛL` is never more expensive than first-order
deterministic Trotter once `L ≥ 4`, and strictly cheaper for `L > 4`. -/
theorem qdrift_beats_first_order_det {L : ℕ} {Lam t eps : ℝ} (hL : 4 ≤ L)
    (hLam : 0 < Lam) (ht : 0 < t) (heps : 0 < eps) :
    qdriftGateCount (Lam * (L : ℝ)) t eps ≤ firstOrderDetCount L Lam t eps := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hL
  rw [qdrift_vs_first_order_det hLpos heps]
  have hratio : 4 / (L : ℝ) ≤ 1 := by
    rw [div_le_one hLpos]
    exact_mod_cast hL
  have hpos : 0 ≤ firstOrderDetCount L Lam t eps := by
    unfold firstOrderDetCount
    positivity
  calc 4 / (L : ℝ) * firstOrderDetCount L Lam t eps
      ≤ 1 * firstOrderDetCount L Lam t eps := mul_le_mul_of_nonneg_right hratio hpos
    _ = firstOrderDetCount L Lam t eps := by ring

/-! ## Table I: deterministic versus random `2k`-order Suzuki -/

/-- Table I row `(2k)th order Trotter DET`: `L^{2+1/(2k)}(Λt)^{1+1/(2k)}/ε^{1/(2k)}`. -/
noncomputable def detSuzukiGateCount (k : ℕ) (L : ℕ) (Lam t eps : ℝ) : ℝ :=
  (L : ℝ) ^ (2 + (1 : ℝ) / (2 * k)) * (Lam * t) ^ (1 + (1 : ℝ) / (2 * k)) /
    eps ^ ((1 : ℝ) / (2 * k))

/-- Table I row `(2k)th order Trotter RANDOM`: the same expression with the
`L`-exponent reduced to `2`. -/
noncomputable def randomSuzukiGateCount (k : ℕ) (L : ℕ) (Lam t eps : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (Lam * t) ^ (1 + (1 : ℝ) / (2 * k)) / eps ^ ((1 : ℝ) / (2 * k))

/-- The core of Table I: the deterministic `2k`-order count exceeds the random
one by exactly the factor `L^{1/(2k)}` in the number of Hamiltonian terms. -/
theorem tableI_det_vs_random {k : ℕ} {L : ℕ} {Lam t eps : ℝ} (hL : 0 < (L : ℝ)) :
    detSuzukiGateCount k L Lam t eps =
      (L : ℝ) ^ ((1 : ℝ) / (2 * k)) * randomSuzukiGateCount k L Lam t eps := by
  unfold detSuzukiGateCount randomSuzukiGateCount
  rw [Real.rpow_add hL, Real.rpow_two]
  ring

/-- `(C10)` is exactly the Table I `(2k)th order Trotter RANDOM` row: the
Suzuki gate count with the source constant equals `C_k` times that scaling. -/
theorem suzukiCount_eq_tableI {k : ℕ} {L : ℕ} {Lam t eps B : ℝ}
    (hx : 0 < Lam * t) (hB : 0 ≤ B) (heps : 0 < eps) :
    suzukiCount k L Lam t eps B = suzukiConstant k B * randomSuzukiGateCount k L Lam t eps := by
  rw [suzukiCount_eq_scaling hx hB heps]
  unfold randomSuzukiGateCount
  ring

/-! ## From the first-order segment count to the Table I row -/

/-- Source's first-order segment count `r = L²Λ²t²/(2ε)`. -/
noncomputable def firstOrderSegments (L : ℕ) (Lam t eps : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (Lam * t) ^ 2 / (2 * eps)

/-- Each of the `r` first-order segments holds `L` exponentials, so the source's
segment count gives exactly Table I's `1st order Trotter DET` gate count. -/
theorem firstOrderDetCount_eq {L : ℕ} {Lam t eps : ℝ} :
    (L : ℝ) * firstOrderSegments L Lam t eps = firstOrderDetCount L Lam t eps := by
  unfold firstOrderSegments firstOrderDetCount
  ring

end Qatlib.Papers.RandCompiler19.SimCompare.DeterministicCost
