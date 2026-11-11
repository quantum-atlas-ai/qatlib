/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanPrograms11.MainResults.LearningGraphStages
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DistinctnessStages — stage complexities of the distinctness learning graph

Belovs, *Span Programs for Functions with Constant-Sized 1-certificates*,
fixed arXiv:1105.4024v1 (20 May 2011), PDF SHA-256
`315b5768c635ceee578e1ed2879a53a210c73c53a43bd0d0430041f9faa4e552`.

Section 4 runs the stage construction on the distinctness function `f : [m]ⁿ → {0,1}`
(`f x = 1` iff two entries of `x` coincide). On a 1-input the 1-certificate has two marked
elements `a` and `b` with `x_a = x_b`, and the learning graph has the three stages of
Table 1: stage I loads `r - 2` elements different from `a` and `b`, stage II loads `a`,
stage III loads `b`, all transitions of unit weight, with the flow of §4 distributed evenly.

The counting underlying Eq. (2)–(4) of the paper:

* stage I: `C(n, r-2)` transitions of length `r - 2`, of which `C(n-2, r-2)` are valid,
  each carrying flow `C(n-2, r-2)⁻¹`;
* stage II: `C(n, r-2) (n - r + 2)` transitions of length `1`, `C(n-2, r-2)` of them valid;
* stage III: `C(n, r-1) (n - r + 1)` transitions of length `1`, `C(n-2, r-2)` of them valid.

This file records the resulting negative and positive complexities, their exact closed
forms (Eq. (2)–(4) after cancelling binomial coefficients), the constant-factor bounds
`C₁ ≤ 2r`, `C₂ ≤ 2√n`, `C₃ ≤ 2n/√r` under `r ≤ n/2`, and the optimisation
`r + √n + n/√r = Θ(n^{2/3})` at `r = n^{2/3}`.

Boundary: the identification of the stage complexities with an actual span-program
witness size (Theorem 3) and the Grover/non-Boolean variants are outside this file; here
only the counting of §4 and the optimisation of §4–§5 are covered.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanPrograms11.MainResults

/-! ### Binomial identities -/

/-- `C(n,k) (n-k)(n-k-1) = C(n-2,k) n (n-1)`: the binomial-coefficient cancellation behind
Eq. (2)–(4) of the paper. -/
theorem choose_mul_sub_mul_sub (n k : ℕ) (h2 : k + 2 ≤ n) :
    n.choose k * (n - k) * (n - k - 1) = (n - 2).choose k * (n * (n - 1)) := by
  have hk2 : k ≤ n - 2 := Nat.le_sub_of_add_le h2
  have hdesc1 : n.descFactorial 2 = n * (n - 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
    ring
  have hmul := Nat.descFactorial_mul_descFactorial (n := n) (k := 2) (m := k + 2)
    (by omega : (2 : ℕ) ≤ k + 2)
  rw [show k + 2 - 2 = k by omega, hdesc1] at hmul
  have hdesc2 : n.descFactorial (k + 2) = n.descFactorial k * (n - k) * (n - k - 1) := by
    have h1 : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
      Nat.descFactorial_succ n k
    have h2' : n.descFactorial (k + 1 + 1) = (n - (k + 1)) * n.descFactorial (k + 1) :=
      Nat.descFactorial_succ n (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega] at h2'
    rw [h2', h1, show n - (k + 1) = n - k - 1 by omega]
    ring
  have hfac : n.descFactorial k = k.factorial * n.choose k :=
    Nat.descFactorial_eq_factorial_mul_choose n k
  have hfac2 : (n - 2).descFactorial k = k.factorial * (n - 2).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose (n - 2) k
  refine Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) ?_
  calc k.factorial * (n.choose k * (n - k) * (n - k - 1))
      = (k.factorial * n.choose k) * (n - k) * (n - k - 1) := by ring
    _ = n.descFactorial k * (n - k) * (n - k - 1) := by rw [hfac]
    _ = n.descFactorial (k + 2) := hdesc2.symm
    _ = (n - 2).descFactorial k * (n * (n - 1)) := hmul.symm
    _ = (k.factorial * (n - 2).choose k) * (n * (n - 1)) := by rw [hfac2]
    _ = k.factorial * ((n - 2).choose k * (n * (n - 1))) := by ring

/-- Real form of `choose_mul_sub_mul_sub`. -/
theorem choose_ratio_mul (n k : ℕ) (h2 : k + 2 ≤ n) :
    (n.choose k : ℝ) * ((n : ℝ) - k) * ((n : ℝ) - k - 1)
      = ((n - 2).choose k : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hk : k ≤ n := by omega
  have e1 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub hk
  have e2 : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - k), e1, Nat.cast_one]
  have e3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hcast : ((n.choose k * (n - k) * (n - k - 1) : ℕ) : ℝ)
      = (((n - 2).choose k * (n * (n - 1)) : ℕ) : ℝ) := by
    rw [choose_mul_sub_mul_sub n k h2]
  push_cast at hcast
  rw [e1, e2, e3] at hcast
  exact hcast

/-- The quotient form of `choose_ratio_mul`: `C(n,k) / C(n-2,k) = n(n-1)/((n-k)(n-k-1))`. -/
theorem choose_div_choose (n k : ℕ) (h2 : k + 2 ≤ n) :
    (n.choose k : ℝ) / ((n - 2).choose k : ℝ)
      = ((n : ℝ) * ((n : ℝ) - 1)) / (((n : ℝ) - k) * ((n : ℝ) - k - 1)) := by
  have hk1 : ((n : ℝ) - k) ≠ 0 := by
    have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
    linarith
  have hk2 : ((n : ℝ) - k - 1) ≠ 0 := by
    have : (k : ℝ) + 1 < n := by exact_mod_cast (by omega : k + 1 < n)
    linarith
  have hpos : (0 : ℝ) < ((n - 2).choose k : ℝ) := by
    have := Nat.choose_pos (by omega : k ≤ n - 2)
    exact_mod_cast this
  rw [div_eq_div_iff (ne_of_gt hpos) (mul_ne_zero hk1 hk2)]
  have := choose_ratio_mul n k h2
  linarith [this]

/-- `C(n, r-1) (r-1) = C(n, r-2) (n - r + 2)`, the step that turns stage III into a
multiple of `C(n-2, r-2)` in Eq. (4). -/
theorem choose_pred_mul (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    (n.choose (r - 1) : ℝ) * ((r : ℝ) - 1)
      = (n.choose (r - 2) : ℝ) * ((n : ℝ) - (r : ℝ) + 2) := by
  have h := Nat.choose_succ_right_eq n (r - 2)
  rw [show r - 2 + 1 = r - 1 by omega] at h
  have hcast : ((n.choose (r - 1) * (r - 1) : ℕ) : ℝ)
      = ((n.choose (r - 2) * (n - (r - 2)) : ℕ) : ℝ) := by rw [h]
  push_cast at hcast
  have er1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have ek : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub hr, Nat.cast_ofNat]
  have e : ((n - (r - 2) : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) + 2 := by
    rw [Nat.cast_sub (by omega : r - 2 ≤ n), ek]
    ring
  rw [er1, e] at hcast
  exact hcast

/-- `sqrt (a² X) = a * sqrt X` for `a, X ≥ 0`. -/
theorem sqrt_sq_mul (a X : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a ^ 2 * X) = a * Real.sqrt X := by
  rw [Real.sqrt_mul (sq_nonneg a) X, Real.sqrt_sq ha]

/-! ### Stage data of the distinctness learning graph (Table 1 of §4) -/

/-- Negative complexity of stage I: `C(n, r-2)` transitions of length `r - 2`, unit weight. -/
def dNeg1 (n r : ℕ) : ℝ := (n.choose (r - 2) : ℝ) * ((r - 2 : ℕ) : ℝ)

/-- Positive complexity of stage I: `C(n-2, r-2)` valid transitions, each of flow
`C(n-2, r-2)⁻¹`, of length `r - 2`. -/
def dPos1 (n r : ℕ) : ℝ := ((r - 2 : ℕ) : ℝ) / ((n - 2).choose (r - 2) : ℝ)

/-- Negative complexity of stage II: `C(n, r-2) (n - r + 2)` transitions of length `1`. -/
def dNeg2 (n r : ℕ) : ℝ := (n.choose (r - 2) : ℝ) * ((n - r + 2 : ℕ) : ℝ)

/-- Negative complexity of stage III: `C(n, r-1) (n - r + 1)` transitions of length `1`. -/
def dNeg3 (n r : ℕ) : ℝ := (n.choose (r - 1) : ℝ) * ((n - r + 1 : ℕ) : ℝ)

/-- Positive complexity of stages II and III: `C(n-2, r-2)` valid transitions of flow
`C(n-2, r-2)⁻¹` and length `1`. -/
def dPos23 (n r : ℕ) : ℝ := 1 / ((n - 2).choose (r - 2) : ℝ)

/-- Complexity `C₁ = sqrt(N₁ P₁)` of stage I. -/
def dC1 (n r : ℕ) : ℝ := stageComplexity (dNeg1 n r) (dPos1 n r)

/-- Complexity `C₂ = sqrt(N₂ P₂)` of stage II. -/
def dC2 (n r : ℕ) : ℝ := stageComplexity (dNeg2 n r) (dPos23 n r)

/-- Complexity `C₃ = sqrt(N₃ P₃)` of stage III. -/
def dC3 (n r : ℕ) : ℝ := stageComplexity (dNeg3 n r) (dPos23 n r)

/-- Total complexity `C₁ + C₂ + C₃` of the three stages (§4, after Eq. (4)). -/
def dTotal (n r : ℕ) : ℝ := dC1 n r + dC2 n r + dC3 n r

section StageSquares

/-- The binomial ratio `C(n,r-2)/C(n-2,r-2) = n(n-1)/((n-r+2)(n-r+1))` that cancels both
stage I and stage II of Eq. (2)–(3). -/
theorem choose_dRatio {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    (n.choose (r - 2) : ℝ) / ((n - 2).choose (r - 2) : ℝ)
      = ((n : ℝ) * ((n : ℝ) - 1)) / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1)) := by
  have hk2 : r - 2 + 2 ≤ n := by omega
  have h := choose_div_choose n (r - 2) hk2
  have ek : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by rw [Nat.cast_sub h2, Nat.cast_ofNat]
  have e2 : ((n : ℝ) - ((r - 2 : ℕ) : ℝ) - 1) = (n : ℝ) - (r : ℝ) + 1 := by rw [ek]; ring
  have e1 : ((n : ℝ) - ((r - 2 : ℕ) : ℝ)) = (n : ℝ) - (r : ℝ) + 2 := by rw [ek]; ring
  rw [e2, e1] at h
  exact h

/-- `C(n-2,r-2)` is nonzero under `2 ≤ r ≤ n`. -/
theorem choose_pos_sub {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    ((n - 2).choose (r - 2) : ℝ) ≠ 0 := by
  have := Nat.choose_pos (by omega : r - 2 ≤ n - 2)
  exact_mod_cast (ne_of_gt this)

/-- Eq. (2) before taking the square root: `N₁ P₁ = k² C(n,r-2)/C(n-2,r-2)` with
`k = r - 2`, which equals `k² n(n-1)/((n-r+2)(n-r+1))`. -/
theorem dStage1_sq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dNeg1 n r * dPos1 n r
      = ((r : ℝ) - 2) ^ 2 * (((n : ℝ) * ((n : ℝ) - 1))
        / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1))) := by
  have hratio := choose_dRatio h2 hrn
  have hD := choose_pos_sub (n := n) h2 hrn
  have ek : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by rw [Nat.cast_sub h2, Nat.cast_ofNat]
  unfold dNeg1 dPos1
  rw [ek]
  rw [show (n.choose (r - 2) : ℝ) * ((r : ℝ) - 2)
        * (((r : ℝ) - 2) / ((n - 2).choose (r - 2) : ℝ))
      = ((r : ℝ) - 2) ^ 2
        * ((n.choose (r - 2) : ℝ) / ((n - 2).choose (r - 2) : ℝ)) by
    field_simp [hD]]
  rw [hratio]

/-- Eq. (3) before taking the square root: `N₂ P₂ = C(n,r-2)(n-r+2)/C(n-2,r-2)
= n(n-1)/(n-r+1)`. -/
theorem dStage2_sq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dNeg2 n r * dPos23 n r
      = ((n : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) - (r : ℝ) + 1) := by
  have hratio := choose_dRatio h2 hrn
  have hD := choose_pos_sub (n := n) h2 hrn
  have enr : ((n - r + 2 : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) + 2 := by
    push_cast [Nat.cast_sub hrn]
    ring
  unfold dNeg2 dPos23
  rw [enr]
  rw [show (n.choose (r - 2) : ℝ) * ((n : ℝ) - (r : ℝ) + 2)
        * (1 / ((n - 2).choose (r - 2) : ℝ))
      = ((n : ℝ) - (r : ℝ) + 2)
        * ((n.choose (r - 2) : ℝ) / ((n - 2).choose (r - 2) : ℝ)) by
    field_simp [hD]]
  rw [hratio]
  have hnr : ((n : ℝ) - (r : ℝ) + 2) ≠ 0 := by
    have : (r : ℝ) ≤ n := by exact_mod_cast hrn
    linarith
  have hnr1 : ((n : ℝ) - (r : ℝ) + 1) ≠ 0 := by
    have : (r : ℝ) ≤ n := by exact_mod_cast hrn
    linarith
  field_simp

/-- Eq. (4) before taking the square root: `N₃ P₃ = C(n,r-1)(n-r+1)/C(n-2,r-2)
= n(n-1)/(r-1)`. -/
theorem dStage3_sq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dNeg3 n r * dPos23 n r
      = ((n : ℝ) * ((n : ℝ) - 1)) / ((r : ℝ) - 1) := by
  have hratio := choose_dRatio h2 hrn
  have hD := choose_pos_sub (n := n) h2 hrn
  have hstep := choose_pred_mul n r h2 hrn
  have enr : ((n - r + 1 : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) + 1 := by
    push_cast [Nat.cast_sub hrn]
    ring
  have hr1 : ((r : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
    linarith
  have hprev : (n.choose (r - 1) : ℝ)
      = (n.choose (r - 2) : ℝ) * ((n : ℝ) - (r : ℝ) + 2) / ((r : ℝ) - 1) := by
    field_simp
    linarith [hstep]
  unfold dNeg3 dPos23
  rw [enr, hprev]
  rw [show (n.choose (r - 2) : ℝ) * ((n : ℝ) - (r : ℝ) + 2) / ((r : ℝ) - 1)
        * ((n : ℝ) - (r : ℝ) + 1) * (1 / ((n - 2).choose (r - 2) : ℝ))
      = ((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1) / ((r : ℝ) - 1)
        * ((n.choose (r - 2) : ℝ) / ((n - 2).choose (r - 2) : ℝ)) by
    field_simp [hD, hr1]]
  rw [hratio]
  have hnr : ((n : ℝ) - (r : ℝ) + 2) ≠ 0 := by
    have : (r : ℝ) ≤ n := by exact_mod_cast hrn
    linarith
  have hnr1 : ((n : ℝ) - (r : ℝ) + 1) ≠ 0 := by
    have : (r : ℝ) ≤ n := by exact_mod_cast hrn
    linarith
  field_simp

end StageSquares

/-! ### Closed forms of Eq. (2)–(4) -/

/-- Eq. (2) of §4: `C₁ = (r-2) sqrt(n(n-1)/((n-r+2)(n-r+1)))`, hence `C₁ = O(r)`. -/
theorem dC1_eq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dC1 n r = ((r : ℝ) - 2)
      * Real.sqrt (((n : ℝ) * ((n : ℝ) - 1))
        / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1))) := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast h2
  unfold dC1 stageComplexity
  rw [dStage1_sq h2 hrn]
  exact sqrt_sq_mul _ _ (by linarith)

/-- Eq. (3) of §4: `C₂ = sqrt(n(n-1)/(n-r+1))`, hence `C₂ = O(sqrt n)`. -/
theorem dC2_eq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dC2 n r = Real.sqrt (((n : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) - (r : ℝ) + 1)) := by
  unfold dC2 stageComplexity
  rw [dStage2_sq h2 hrn]

/-- Eq. (4) of §4: `C₃ = sqrt(n(n-1)/(r-1))`, hence `C₃ = O(n/sqrt r)`. -/
theorem dC3_eq {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dC3 n r = Real.sqrt (((n : ℝ) * ((n : ℝ) - 1)) / ((r : ℝ) - 1)) := by
  unfold dC3 stageComplexity
  rw [dStage3_sq h2 hrn]

/-! ### Constant-factor bounds -/

/-- Stage I is `O(r)`: under `2r ≤ n`, `C₁ ≤ 2r`. -/
theorem dC1_le {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) (hsmall : 2 * r ≤ n) :
    dC1 n r ≤ 2 * r := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast h2
  have hn : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hhalf : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have : (2 : ℝ) * r ≤ n := by exact_mod_cast hsmall
    linarith
  have hDpos : (0 : ℝ) < ((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1) := by
    have h1 : (0 : ℝ) < (n : ℝ) - (r : ℝ) + 2 := by linarith
    have h2' : (0 : ℝ) < (n : ℝ) - (r : ℝ) + 1 := by linarith
    exact mul_pos h1 h2'
  have hD : ((n : ℝ) / 2) * ((n : ℝ) / 2)
      ≤ ((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1) := by
    have h3 : (0:ℝ) < (n:ℝ)/2 := by linarith
    nlinarith
  have hX : ((n : ℝ) * ((n : ℝ) - 1))
      / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1)) ≤ 4 := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  rw [dC1_eq h2 hrn]
  have hsqrt : Real.sqrt (((n : ℝ) * ((n : ℝ) - 1))
      / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1))) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num)).2 (by nlinarith)
  calc ((r : ℝ) - 2) * Real.sqrt (((n : ℝ) * ((n : ℝ) - 1))
        / (((n : ℝ) - (r : ℝ) + 2) * ((n : ℝ) - (r : ℝ) + 1)))
      ≤ ((r : ℝ) - 2) * 2 := by
        exact mul_le_mul_of_nonneg_left hsqrt (by linarith)
    _ ≤ 2 * r := by linarith

/-- Stage II is `O(sqrt n)`: under `2r ≤ n`, `C₂ ≤ 2 sqrt n`. -/
theorem dC2_le {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) (hsmall : 2 * r ≤ n) :
    dC2 n r ≤ 2 * Real.sqrt n := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast h2
  have hn : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hhalf : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have : (2 : ℝ) * r ≤ n := by exact_mod_cast hsmall
    linarith
  have hden : (0 : ℝ) < (n : ℝ) - (r : ℝ) + 1 := by linarith
  have hX : ((n : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) - (r : ℝ) + 1) ≤ 2 * n := by
    rw [div_le_iff₀ hden]
    nlinarith
  rw [dC2_eq h2 hrn]
  have h1 : Real.sqrt (((n : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) - (r : ℝ) + 1))
      ≤ Real.sqrt (2 * n) := Real.sqrt_le_sqrt hX
  have h2' : Real.sqrt (2 * n) ≤ 2 * Real.sqrt n := by
    have : Real.sqrt (2 * n) ≤ Real.sqrt (4 * n) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    rwa [show Real.sqrt (4 * n) = 2 * Real.sqrt n by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by norm_num]] at this
  linarith

/-- Stage III is `O(n/sqrt r)`: `C₃ ≤ 2n/sqrt r`. -/
theorem dC3_le {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) :
    dC3 n r ≤ 2 * n / Real.sqrt r := by
  have hr : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hn : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast h2
    linarith
  have hsq : (2 * (n : ℝ) / Real.sqrt r) ^ 2 = 4 * (n : ℝ) ^ 2 / (r : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hr)]
    norm_num
  have hX : ((n : ℝ) * ((n : ℝ) - 1)) / ((r : ℝ) - 1) ≤ 4 * (n : ℝ) ^ 2 / (r : ℝ) := by
    rw [div_le_div_iff₀ hr1 hr]
    have hle : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast h2
    have hkey : (0 : ℝ) ≤ (r - 2) * (3 * (n : ℝ)) := by
      apply mul_nonneg (by linarith) (by linarith)
    nlinarith [hkey]
  have hnn : (0 : ℝ) ≤ 2 * n / Real.sqrt r := by positivity
  rw [dC3_eq h2 hrn]
  refine (Real.sqrt_le_left hnn).2 ?_
  rw [hsq]
  exact hX

/-- §4, after Eq. (4): the three stages together cost at most
`2(r + sqrt n + n/sqrt r)`. -/
theorem dTotal_le {n r : ℕ} (h2 : 2 ≤ r) (hrn : r ≤ n) (hsmall : 2 * r ≤ n) :
    dTotal n r ≤ 2 * ((r : ℝ) + Real.sqrt n + (n : ℝ) / Real.sqrt r) := by
  unfold dTotal
  have h1 := dC1_le h2 hrn hsmall
  have h2' := dC2_le h2 hrn hsmall
  have h3 := dC3_le h2 hrn
  calc dC1 n r + dC2 n r + dC3 n r
      ≤ 2 * (r : ℝ) + 2 * Real.sqrt n + 2 * (n : ℝ) / Real.sqrt r := by linarith
    _ = 2 * ((r : ℝ) + Real.sqrt n + (n : ℝ) / Real.sqrt r) := by ring

/-! ### Optimisation: `r + sqrt n + n/sqrt r = Θ(n^{2/3})` at `r = n^{2/3}` -/

/-- `sqrt (n^{2/3}) = n^{1/3}`. -/
theorem sqrt_rpow_two_thirds (N : ℝ) (hN : 0 < N) :
    Real.sqrt (N ^ (2 / 3 : ℝ)) = N ^ (1 / 3 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hN)]
  norm_num

/-- `N / N^{1/3} = N^{2/3}`. -/
theorem div_rpow_third (N : ℝ) (hN : 0 < N) : N / N ^ (1 / 3 : ℝ) = N ^ (2 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < N ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hN _
  have hsplit : N ^ (1 / 3 : ℝ) * N ^ (2 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hN]
    norm_num
  field_simp
  linarith [hsplit]

/-- For every stage parameter `r > 0` the total complexity bound already exceeds
`n^{2/3}`: `r + n/sqrt r ≥ n^{2/3}`. -/
theorem rpow_two_thirds_le_add (N r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    N ^ (2 / 3 : ℝ) ≤ r + N / Real.sqrt r := by
  by_cases hle : N ^ (2 / 3 : ℝ) ≤ r
  · have : (0 : ℝ) ≤ N / Real.sqrt r := by positivity
    linarith
  · push Not at hle
    have hsqrt : Real.sqrt r ≤ N ^ (1 / 3 : ℝ) := by
      calc Real.sqrt r ≤ Real.sqrt (N ^ (2 / 3 : ℝ)) := Real.sqrt_le_sqrt (le_of_lt hle)
        _ = N ^ (1 / 3 : ℝ) := sqrt_rpow_two_thirds N hN
    have hmono : N / N ^ (1 / 3 : ℝ) ≤ N / Real.sqrt r :=
      div_le_div_of_nonneg_left (le_of_lt hN) (Real.sqrt_pos.mpr hr) hsqrt
    have hval : N / N ^ (1 / 3 : ℝ) = N ^ (2 / 3 : ℝ) := div_rpow_third N hN
    linarith [hmono, hval, le_of_lt hr]

/-- At `r = n^{2/3}` the bound reads `n^{2/3} + sqrt n + n^{2/3} ≤ 3 n^{2/3}`. -/
theorem total_at_optimum (N : ℝ) (hN : 1 ≤ N) :
    N ^ (2 / 3 : ℝ) + Real.sqrt N + N / Real.sqrt (N ^ (2 / 3 : ℝ))
      ≤ 3 * N ^ (2 / 3 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hval : N / Real.sqrt (N ^ (2 / 3 : ℝ)) = N ^ (2 / 3 : ℝ) := by
    rw [sqrt_rpow_two_thirds N hNpos, div_rpow_third N hNpos]
  have hsqrt : Real.sqrt N ≤ N ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  rw [hval]
  linarith

/-- The stage bound of §4 at the optimum value `r = n^{2/3}` is at most `6 n^{2/3}`: the
learning graph for distinctness has complexity `O(n^{2/3})`. -/
theorem distinctness_stage_bound_two_thirds (N : ℝ) (hN : 1 ≤ N) :
    2 * (N ^ (2 / 3 : ℝ) + Real.sqrt N + N / Real.sqrt (N ^ (2 / 3 : ℝ)))
      ≤ 6 * N ^ (2 / 3 : ℝ) := by
  have h := total_at_optimum N hN
  linarith

/-- Proposition 5 applied to the three distinctness stages: after normalising the weights of
stage `i` by `N_i`, the resulting learning graph has complexity at most `sqrt 3 * (C₁+C₂+C₃)`.
The hypothesis `3 ≤ r` keeps stage I nonempty; for `r = 2` stage I is empty and `C₁ = 0`, so
the estimate is trivial. -/
theorem dTotal_via_stage_decomposition {n r : ℕ} (h3r : 3 ≤ r) (hrn : r ≤ n) :
    Real.sqrt ((3 : ℝ) * (dNeg1 n r * dPos1 n r + dNeg2 n r * dPos23 n r
        + dNeg3 n r * dPos23 n r)) ≤ Real.sqrt 3 * dTotal n r := by
  have hD : (0 : ℝ) < ((n - 2).choose (r - 2) : ℝ) := by
    have := Nat.choose_pos (by omega : r - 2 ≤ n - 2)
    exact_mod_cast this
  have hkN : (0 : ℝ) < (n.choose (r - 2) : ℝ) := by
    have := Nat.choose_pos (by omega : r - 2 ≤ n)
    exact_mod_cast this
  have hkN3 : (0 : ℝ) < (n.choose (r - 1) : ℝ) := by
    have := Nat.choose_pos (by omega : r - 1 ≤ n)
    exact_mod_cast this
  have hk : (0 : ℝ) < ((r - 2 : ℕ) : ℝ) := by
    have : 0 < r - 2 := by omega
    exact_mod_cast this
  have hnr2 : (0 : ℝ) < ((n - r + 2 : ℕ) : ℝ) := by
    have : 0 < n - r + 2 := by omega
    exact_mod_cast this
  have hnr1 : (0 : ℝ) < ((n - r + 1 : ℕ) : ℝ) := by
    have : 0 < n - r + 1 := by omega
    exact_mod_cast this
  have key := stage_decomposition 3
    (fun i : Fin 3 => ![dNeg1 n r, dNeg2 n r, dNeg3 n r] i)
    (fun i : Fin 3 => ![dPos1 n r, dPos23 n r, dPos23 n r] i)
    (fun i => by
      fin_cases i
      · simpa [dNeg1] using mul_pos hkN hk
      · simpa [dNeg2] using mul_pos hkN hnr2
      · simpa [dNeg3] using mul_pos hkN3 hnr1)
    (fun i => by
      fin_cases i
      · simpa [dPos1] using le_of_lt (div_pos hk hD)
      · simp only [dPos23]
        exact (one_div_pos.2 hD).le
      · simp only [dPos23]
        exact (one_div_pos.2 hD).le)
  have hsum : (∑ i : Fin 3,
      ![dNeg1 n r, dNeg2 n r, dNeg3 n r] i * ![dPos1 n r, dPos23 n r, dPos23 n r] i)
      = dNeg1 n r * dPos1 n r + dNeg2 n r * dPos23 n r + dNeg3 n r * dPos23 n r := by
    simp [Fin.sum_univ_three]
  have hsqrt : (∑ i : Fin 3, Real.sqrt
      (![dNeg1 n r, dNeg2 n r, dNeg3 n r] i * ![dPos1 n r, dPos23 n r, dPos23 n r] i))
      = dTotal n r := by
    simp only [Fin.sum_univ_three]
    simp [dTotal, dC1, dC2, dC3, stageComplexity]
  rw [hsum, hsqrt] at key
  exact key

end Qatlib.Papers.SpanPrograms11.MainResults
