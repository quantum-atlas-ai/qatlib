/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.GevreyTools.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / GevreyTools — Lemma 3.1 (Eq. (3.1), p. 11)

Fixed source: arXiv:2608.17653v1.  The combinatorial estimate

`l! · k^{n-k-l} ≤ eⁿ · (n-k)!`   for `1 ≤ k ≤ n`, `0 ≤ l ≤ n-k`,

used in the proof of the Gevrey cutoff estimate (Eq. (3.11)).  The paper
proves it by setting `m = n-k`, forming `φ(l) = l! k^{m-l}/m!`, observing that
`φ(l)/φ(l-1) = l/k`, so that the maximum over `0 ≤ l ≤ m` is attained at an
endpoint and equals `max(k^m/m!, 1) ≤ e^k`.

The Lean proof follows that route: the decreasing branch (`l ≤ k`) is bounded
by `k^m`, the increasing branch (`l ≥ k`) is bounded by `m!`, and both
endpoints are bounded using `Real.pow_div_factorial_le_exp`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.GevreyTools

/-- Decreasing branch of the paper's proof of Lemma 3.1: for `l ≤ min k m`,
`l! · k^{m-l} ≤ k^m` (the ratio `φ(l)/φ(l-1) = l/k` is at most one). -/
private lemma factorial_pow_down (l k m : ℕ) (hk : 1 ≤ k) (hl : l ≤ min k m) :
    (l.factorial : ℝ) * (k : ℝ) ^ (m - l) ≤ (k : ℝ) ^ m := by
  induction l with
  | zero => simp
  | succ j ih =>
      obtain ⟨hjk, hjm⟩ := le_min_iff.mp hl
      have hjmin : j ≤ min k m := le_trans (Nat.le_succ j) hl
      have ih' := ih hjmin
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hmj : m - j = (m - (j + 1)) + 1 := by omega
      have hA : (j.factorial : ℝ) * (k : ℝ) ^ (m - (j + 1)) ≤
          (k : ℝ) ^ m / (k : ℝ) := by
        rw [le_div_iff₀ hkpos]
        calc (j.factorial : ℝ) * (k : ℝ) ^ (m - (j + 1)) * (k : ℝ)
            = (j.factorial : ℝ) * (k : ℝ) ^ (m - j) := by
              rw [hmj, pow_succ]; ring
          _ ≤ (k : ℝ) ^ m := ih'
      calc ((j + 1).factorial : ℝ) * (k : ℝ) ^ (m - (j + 1))
          = ((j + 1 : ℕ) : ℝ) * ((j.factorial : ℝ) * (k : ℝ) ^ (m - (j + 1))) := by
            rw [Nat.factorial_succ]; push_cast; ring
        _ ≤ ((j + 1 : ℕ) : ℝ) * ((k : ℝ) ^ m / (k : ℝ)) := by gcongr
        _ = (((j + 1 : ℕ) : ℝ) / (k : ℝ)) * (k : ℝ) ^ m := by ring
        _ ≤ 1 * (k : ℝ) ^ m := by
            gcongr
            exact div_le_one_of_le₀ (by exact_mod_cast hjk) (le_of_lt hkpos)
        _ = (k : ℝ) ^ m := one_mul _

/-- Increasing branch of the paper's proof of Lemma 3.1: for `k ≤ j ≤ m`,
`j! · k^{m-j} ≤ m!` (the ratio `φ(l)/φ(l-1) = l/k` is at least one, so the
value at `j` is bounded by the right endpoint `φ(m) = 1`). -/
private lemma factorial_pow_up (k m : ℕ) (hk : 1 ≤ k) :
    ∀ d j : ℕ, m - j = d → k ≤ j → j ≤ m →
      (j.factorial : ℝ) * (k : ℝ) ^ (m - j) ≤ (m.factorial : ℝ) := by
  intro d
  induction d with
  | zero =>
      intro j hd hkj hjm
      have : j = m := by omega
      subst this
      simp
  | succ d ih =>
      intro j hd hkj hjm
      have hjm' : j < m := by omega
      have hstep : ((j + 1).factorial : ℝ) * (k : ℝ) ^ (m - (j + 1)) ≤
          (m.factorial : ℝ) :=
        ih (j + 1) (by omega) (by omega) (by omega)
      have hpow : (k : ℝ) ^ (m - j) = (k : ℝ) ^ (m - (j + 1)) * (k : ℝ) := by
        rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]
      calc (j.factorial : ℝ) * (k : ℝ) ^ (m - j)
          = ((k : ℝ) / ((j + 1 : ℕ) : ℝ)) *
              (((j + 1).factorial : ℝ) * (k : ℝ) ^ (m - (j + 1))) := by
            rw [hpow, Nat.factorial_succ]
            push_cast
            field_simp
        _ ≤ 1 * (m.factorial : ℝ) := by
            have hdiv : (k : ℝ) / ((j + 1 : ℕ) : ℝ) ≤ 1 :=
              div_le_one_of_le₀ (by exact_mod_cast Nat.le_succ_of_le hkj) (by positivity)
            exact mul_le_mul hdiv hstep (by positivity) (by norm_num)
        _ = (m.factorial : ℝ) := one_mul _

/-- Fixed arXiv:2608.17653v1, Lemma 3.1, Eq. (3.1), p. 11.
For integers `1 ≤ k ≤ n` and `0 ≤ l ≤ n-k`: `l! · k^{n-k-l} ≤ eⁿ · (n-k)!`. -/
theorem lemma_three_one_factorial_power_bound
    (l k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hl : l ≤ n - k) :
    (l.factorial : ℝ) * (k : ℝ) ^ (n - k - l) ≤
      Real.exp (n : ℝ) * ((n - k).factorial : ℝ) := by
  set m : ℕ := n - k with hm
  have hl' : l ≤ m := hl
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hexp_k : (k : ℝ) ^ m ≤ Real.exp (k : ℝ) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) hk0 m
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hfacpos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hfacpos)] at hmul
  have hexpmono : Real.exp (k : ℝ) ≤ Real.exp (n : ℝ) :=
    Real.exp_le_exp.mpr (by exact_mod_cast hkn)
  have hmn : (n - k - l) = (m - l) := rfl
  rw [hmn, hm]
  by_cases hlk : l ≤ k
  · have hlmin : l ≤ min k m := le_min hlk hl'
    have hdown := factorial_pow_down l k m hk hlmin
    have hleft : (l.factorial : ℝ) * (k : ℝ) ^ (m - l) ≤
        Real.exp (k : ℝ) * (m.factorial : ℝ) := hdown.trans hexp_k
    calc (l.factorial : ℝ) * (k : ℝ) ^ (m - l)
        ≤ Real.exp (k : ℝ) * (m.factorial : ℝ) := hleft
      _ ≤ Real.exp (n : ℝ) * (m.factorial : ℝ) := by gcongr
  · have hkl : k ≤ l := le_of_lt (Nat.lt_of_not_le hlk)
    have hup := factorial_pow_up k m hk (m - l) l rfl hkl hl'
    have hone : (1 : ℝ) ≤ Real.exp (k : ℝ) := Real.one_le_exp hk0
    have hstep : (m.factorial : ℝ) ≤ Real.exp (k : ℝ) * (m.factorial : ℝ) := by
      calc (m.factorial : ℝ) = 1 * (m.factorial : ℝ) := (one_mul _).symm
        _ ≤ Real.exp (k : ℝ) * (m.factorial : ℝ) := by gcongr
    calc (l.factorial : ℝ) * (k : ℝ) ^ (m - l)
        ≤ (m.factorial : ℝ) := hup
      _ ≤ Real.exp (k : ℝ) * (m.factorial : ℝ) := hstep
      _ ≤ Real.exp (n : ℝ) * (m.factorial : ℝ) := by gcongr

/-- Fixed arXiv:2608.17653v1, Lemma 3.1, Eq. (3.1), p. 11 (claim c001, same
result as `lemma_three_one_factorial_power_bound`). -/
theorem claim_c001_lemma_three_one
    (l k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hl : l ≤ n - k) :
    (l.factorial : ℝ) * (k : ℝ) ^ (n - k - l) ≤
      Real.exp (n : ℝ) * ((n - k).factorial : ℝ) :=
  lemma_three_one_factorial_power_bound l k n hk hkn hl

end Qatlib.Papers.SlowHamSim26.GevreyTools
