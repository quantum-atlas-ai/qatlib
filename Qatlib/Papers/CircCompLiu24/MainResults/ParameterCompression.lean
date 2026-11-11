/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircCompLiu24.MainResults.ParameterCompressionModel
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CircCompLiu24 `MainResults`: `O(polylog m)` trainable parameters

Fixed source: arXiv:2410.09846v2, §3.1, Eq. (1) and the paragraph after it
(v2 markdown lines 265--270).

The paper's main parameter-counting claim is the conjunction of two facts.
First, `N = ceil(log_2 m)` qubits provide `2^N >= m` computational-basis states,
so the circuit exposes at least `m` Born probabilities. Second, the `L`-layer
`R_Y + CNOT` ansatz has `N * L` trainable angles; if the number of layers is
polynomial in the qubit count, `L <= C * N^k`, then this is `C * N^(k+1)` —
a polynomial in `N = ceil(log_2 m)`, hence `O(polylog m)` in the target
parameter count `m`.

Nothing here asserts approximation accuracy, training convergence, or
generalization; those are outside the paper's counting claim.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CircCompLiu24.MainResults

open Qatlib.Foundations.PureStateMath

noncomputable section

/-- **Main counting claim of §3.1.** With `N = ceil(log_2 m)` qubits the
register exposes at least `m` Born outcomes; if the `L`-layer ansatz has a
polynomial layer budget `L <= C * N^k`, its trainable parameter count `N * L`
is at most `C * N^(k+1)`, and `N <= floor(log_2 m) + 1`. -/
theorem parameterCompression (m k C L : ℕ)
    (hL : L ≤ C * (qubitCount m) ^ k) :
    m ≤ basisStateCount (qubitCount m) ∧
    ansatzParameterCount (qubitCount m) L ≤ C * (qubitCount m) ^ (k + 1) ∧
    qubitCount m ≤ Nat.log2 m + 1 := by
  refine ⟨?_, ?_, qubitCount_le_log2_succ m⟩
  · rw [basisStateCount, qubitCount]
    exact Nat.le_pow_clog (by decide) m
  · unfold ansatzParameterCount
    calc
      qubitCount m * L ≤ qubitCount m * (C * (qubitCount m) ^ k) :=
        Nat.mul_le_mul_left _ hL
      _ = C * (qubitCount m) ^ (k + 1) := by
        rw [Nat.pow_succ]
        ring

/-- The paper's `L = O(N)` case: a linear layer budget leaves `O(N^2)`
trainable parameters. -/
theorem parameterCompression_linear_layers (m c L : ℕ)
    (hL : L ≤ c * qubitCount m) :
    m ≤ basisStateCount (qubitCount m) ∧
    ansatzParameterCount (qubitCount m) L ≤ c * (qubitCount m) ^ 2 := by
  have h := parameterCompression m 1 c L (by simpa using hL)
  exact ⟨h.1, by simpa using h.2.1⟩

/-- The paper's `L = O(N^2)` case: a quadratic layer budget leaves `O(N^3)`
trainable parameters. -/
theorem parameterCompression_quadratic_layers (m c L : ℕ)
    (hL : L ≤ c * (qubitCount m) ^ 2) :
    m ≤ basisStateCount (qubitCount m) ∧
    ansatzParameterCount (qubitCount m) L ≤ c * (qubitCount m) ^ 3 := by
  have h := parameterCompression m 2 c L (by simpa using hL)
  exact ⟨h.1, by simpa using h.2.1⟩

/-- `ceil(log_2 m)` is bounded by a constant multiple of `log m`: for `m >= 2`,
`ceil(log_2 m) <= (2 / log 2) * log m`. -/
theorem qubitCount_cast_le (m : ℕ) (hm : 2 ≤ m) :
    (qubitCount m : ℝ) ≤ (2 / Real.log 2) * Real.log m := by
  have hm0 : m ≠ 0 := by omega
  have hn1 : 1 ≤ Nat.log2 m := by
    rw [Nat.le_log2 hm0]
    simpa using hm
  have hN : qubitCount m ≤ 2 * Nat.log2 m := by
    have h := qubitCount_le_log2_succ m
    omega
  have hlog2 : (Nat.log2 m : ℝ) ≤ Real.logb 2 (m : ℝ) := Real.log2_le_logb m
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (qubitCount m : ℝ) ≤ (2 * Nat.log2 m : ℕ) := by exact_mod_cast hN
    _ = 2 * (Nat.log2 m : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.logb 2 (m : ℝ) := by gcongr
    _ = (2 / Real.log 2) * Real.log m := by
      rw [Real.logb]
      ring

/-- For `m >= 2`, the `m`-th ansatz parameter count under a polynomial layer
budget is bounded by an explicit constant times `(log m)^(k+1)`. -/
theorem ansatzParameterCount_cast_le (k C : ℕ) (L : ℕ → ℕ) (m : ℕ)
    (hm : 2 ≤ m) (hL : L m ≤ C * (qubitCount m) ^ k) :
    (ansatzParameterCount (qubitCount m) (L m) : ℝ) ≤
      (C : ℝ) * (2 / Real.log 2) ^ (k + 1) * (Real.log m) ^ (k + 1) := by
  have hN := qubitCount_cast_le m hm
  have hN0 : 0 ≤ (qubitCount m : ℝ) := by positivity
  have hLcast : (L m : ℝ) ≤ (C : ℝ) * (qubitCount m : ℝ) ^ k := by
    exact_mod_cast hL
  have hlog0 : 0 ≤ Real.log m :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  calc
    (ansatzParameterCount (qubitCount m) (L m) : ℝ)
        = (qubitCount m : ℝ) * (L m : ℝ) := by
          unfold ansatzParameterCount
          push_cast
          ring
    _ ≤ (qubitCount m : ℝ) * ((C : ℝ) * (qubitCount m : ℝ) ^ k) := by
      gcongr
    _ = (C : ℝ) * (qubitCount m : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      ring
    _ ≤ (C : ℝ) * (((2 / Real.log 2) * Real.log m) ^ (k + 1)) := by
      gcongr
    _ = (C : ℝ) * (2 / Real.log 2) ^ (k + 1) * (Real.log m) ^ (k + 1) := by
      rw [mul_pow]
      ring

/-- **`O(polylog m)` form of the main claim.** For any layer schedule whose
size is polynomial in the qubit count, `L m <= C * (ceil(log_2 m))^k`, the
number of trainable ansatz parameters grows at most like `(log m)^(k+1)` in
the target parameter count `m`. -/
theorem ansatzParameterCount_isBigO_polylog (k C : ℕ) (L : ℕ → ℕ)
    (hL : ∀ m, L m ≤ C * (qubitCount m) ^ k) :
    (fun m : ℕ => (ansatzParameterCount (qubitCount m) (L m) : ℝ))
      =O[Filter.atTop] (fun m : ℕ => (Real.log m) ^ (k + 1)) := by
  refine Asymptotics.IsBigO.of_bound ((C : ℝ) * (2 / Real.log 2) ^ (k + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  have hbound := ansatzParameterCount_cast_le k C L m hm (hL m)
  have hf0 : 0 ≤ (ansatzParameterCount (qubitCount m) (L m) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log m :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hg0 : 0 ≤ (Real.log m) ^ (k + 1) := pow_nonneg hlog0 _
  rw [Real.norm_eq_abs, abs_of_nonneg hf0, Real.norm_eq_abs, abs_of_nonneg hg0]
  calc
    (ansatzParameterCount (qubitCount m) (L m) : ℝ)
        ≤ (C : ℝ) * (2 / Real.log 2) ^ (k + 1) * (Real.log m) ^ (k + 1) := hbound
    _ = ((C : ℝ) * (2 / Real.log 2) ^ (k + 1)) * (Real.log m) ^ (k + 1) := by ring

end

end Qatlib.Papers.CircCompLiu24.MainResults
