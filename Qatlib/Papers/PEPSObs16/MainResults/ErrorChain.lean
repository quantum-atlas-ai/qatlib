/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PEPSObs16.MainResults.SourceMainResults
import Mathlib.Tactic

/-!
# PEPSObs16 — error chain of Theorem 1, eqs. (11)–(15), and the quasi-polynomial cost

Fixed source: arXiv:1606.06301v2, Appendix "Proof of Theorem 1", eqs. (11)–(15),
and p. 6 ("for `ℓ = O(log N)` in quasi-polynomial time").

Two steps of the paper's proof are formalised here on top of
`SourceMainResults`:

* **Eq. (11) → (13).** The clustering bound controls
  `|⟨O_X ⊗ M⟩ − ⟨O_X⟩⟨M⟩|` by `e^{-O(ℓΔ*)} ‖O_X‖ ‖M‖`. Dividing by
  `⟨M⟩ = ⟨ω|M|ω⟩ ≥ ‖M‖ κ(A)^{-2}` and using `κ(A) = κ(A^{-1})` turns it into
  the per-step error `e^{-O(ℓΔ*)} ‖O_X‖ κ(A)²`. `ratio_error_bound` performs the
  division; `cond_ratio_bound` performs the `‖M‖/⟨M⟩ ≤ κ²` bound; the paper's
  own `κ_* = max_i κ(A_i)` is handled by `sum_stepError_le`.

* **Quasi-polynomial classical time.** `classicalCost D d ell` counts
  `(Dd)^{3 d ℓ^d}` contraction terms. With `ℓ ≤ C log N` its logarithm is
  `O((log N)^d)`, so the cost is `exp(O((log N)^d))`, the paper's
  quasi-polynomial `O(2^{(log N)^{O(1)}})`. `classicalCost_log_le` proves the
  logarithmic bound and `classicalCost_quasipoly` states it in exponential form.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators

/-! ## Eq. (11) → (13): from the clustering bound to the per-step error -/

/-- **The `‖M‖ / ⟨M⟩ ≤ κ(A)²` step of eq. (13).** For a positive matrix
`M = (A⁻¹)†A⁻¹` acting on a normalised state, the paper bounds the Rayleigh
quotient below by `‖M‖ κ(A)^{-2}` (the denominator in eq. (11) is at least
`σ_min(M)` and `σ_max(M)/σ_min(M) = κ(A)²`). Consequently
`‖M‖ / ⟨ω|M|ω⟩ ≤ κ(A)²`. -/
theorem cond_ratio_bound (Mnorm q κ : ℝ) (hκ : 0 < κ) (hM : 0 < Mnorm)
    (hq : Mnorm / κ ^ 2 ≤ q) : Mnorm / q ≤ κ ^ 2 := by
  have hκ2 : 0 < κ ^ 2 := pow_pos hκ 2
  have hMle : Mnorm ≤ q * κ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hq (le_of_lt hκ2)
    rwa [div_mul_cancel₀ Mnorm (ne_of_gt hκ2)] at h
  have hqpos : 0 < q := lt_of_lt_of_le (div_pos hM hκ2) hq
  rw [div_le_iff₀ hqpos]
  linarith

/-- **Eq. (11) → (13), division step.** If the clustering bound
`|⟨O_X ⊗ M⟩ − ⟨O_X⟩⟨M⟩| ≤ e ‖O_X‖ ‖M‖` holds and `⟨M⟩ ≥ ‖M‖ κ^{-2}`, then the
normalised discrepancy `|⟨O_X ⊗ M⟩/⟨M⟩ − ⟨O_X⟩|` is at most `e ‖O_X‖ κ²`, which
is the paper's per-step error `e^{-O(ℓΔ*)} ‖O_X‖ κ(A)^2`. -/
theorem ratio_error_bound (cross prod q Om M e κ : ℝ)
    (hq : 0 < q) (he : 0 ≤ e * Om) (hM : 0 < M) (hκ : 0 < κ)
    (hnorm : M / κ ^ 2 ≤ q)
    (h : |cross - prod * q| ≤ e * Om * M) :
    |cross / q - prod| ≤ e * Om * κ ^ 2 := by
  have hκ2 : 0 < κ ^ 2 := pow_pos hκ 2
  have hMle : M ≤ q * κ ^ 2 := by
    have h' := mul_le_mul_of_nonneg_right hnorm (le_of_lt hκ2)
    rwa [div_mul_cancel₀ M (ne_of_gt hκ2)] at h'
  have hqne : q ≠ 0 := ne_of_gt hq
  have hrewrite : cross / q - prod = (cross - prod * q) / q := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  calc
    |cross - prod * q| ≤ e * Om * M := h
    _ ≤ e * Om * (q * κ ^ 2) := mul_le_mul_of_nonneg_left hMle he
    _ = e * Om * κ ^ 2 * q := by ring

/-- **The per-step error is monotone in the condition number.** A larger bound
on `κ` never decreases the step error, which lets the paper replace every
`κ(A_i)` by `κ_* = max_i κ(A_i)`. -/
theorem stepError_mono_kappa (c Δ ell Onorm κ₁ κ₂ : ℝ)
    (hO : 0 ≤ Onorm) (h1 : 0 ≤ κ₁) (h12 : κ₁ ≤ κ₂) :
    stepError c Δ ell κ₁ Onorm ≤ stepError c Δ ell κ₂ Onorm := by
  unfold stepError
  have he : 0 ≤ Real.exp (-(c * ell * Δ)) := (Real.exp_pos _).le
  have hsq : κ₁ ^ 2 ≤ κ₂ ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq he) hO

/-- **The paper's `κ_* = max_i κ(A_i)` (eq. (15), definition of `κ_*`).** The
sum of the per-step errors over the at most `n` boundary tensors is at most
`n` times the step error at `κ_*`. This is the passage from eq. (13) to eq. (14)
with a single condition-number bound. -/
theorem sum_stepError_le (n : ℕ) (c Δ ell Onorm κstar : ℝ) (κ : ℕ → ℝ)
    (hO : 0 ≤ Onorm)
    (h : ∀ i, i < n → 0 ≤ κ i ∧ κ i ≤ κstar) :
    (∑ i ∈ Finset.range n, stepError c Δ ell (κ i) Onorm) ≤
      (n : ℝ) * stepError c Δ ell κstar Onorm := by
  have hsingle : ∀ i ∈ Finset.range n,
      stepError c Δ ell (κ i) Onorm ≤ stepError c Δ ell κstar Onorm := by
    intro i hi
    exact stepError_mono_kappa c Δ ell Onorm (κ i) κstar hO
      (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2
  calc
    (∑ i ∈ Finset.range n, stepError c Δ ell (κ i) Onorm)
        ≤ ∑ _i ∈ Finset.range n, stepError c Δ ell κstar Onorm :=
          Finset.sum_le_sum hsingle
    _ = (n : ℝ) * stepError c Δ ell κstar Onorm := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Quasi-polynomial classical time (p. 6) -/

/-- **Logarithm of the contraction count.** `classicalCost D d ell` is
`(Dd)^{3 d ℓ^d}`, so its logarithm is `3 d ℓ^d log(Dd)` (eq. (18) discussion,
p. 6). -/
theorem classicalCost_log (D d ell : ℕ) :
    Real.log ((classicalCost D d ell : ℕ) : ℝ) =
      (3 * d * ell ^ d : ℕ) * Real.log (((D * d : ℕ)) : ℝ) := by
  unfold classicalCost
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- **Quasi-polynomial bound on the classical time.** If the radius obeys
`ℓ ≤ C log N`, then the logarithm of the contraction count is at most
`3 d (C log N)^d log(Dd)`, i.e. `O((log N)^d)` for constant `d, D`. This is the
paper's statement that for `ℓ = O(log N)` the cost `(Dd)^{O(ℓ^d)}` is
quasi-polynomial in `N`. -/
theorem classicalCost_log_le (D d ell : ℕ) (N C : ℝ)
    (hlog : 0 < Real.log (((D * d : ℕ)) : ℝ))
    (hell : (ell : ℝ) ≤ C * Real.log N) (hC : 0 ≤ C) (hN : 0 ≤ Real.log N) :
    Real.log ((classicalCost D d ell : ℕ) : ℝ) ≤
      3 * (d : ℝ) * (C * Real.log N) ^ d * Real.log (((D * d : ℕ)) : ℝ) := by
  rw [classicalCost_log]
  have hClog : 0 ≤ C * Real.log N := mul_nonneg hC hN
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hpow : (ell : ℝ) ^ d ≤ (C * Real.log N) ^ d :=
    pow_le_pow_left₀ hell0 hell d
  have hexp : ((3 * d * ell ^ d : ℕ) : ℝ) ≤ 3 * (d : ℝ) * (C * Real.log N) ^ d := by
    push_cast
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hpow)]
  have hlog0 : 0 ≤ Real.log (((D * d : ℕ)) : ℝ) := hlog.le
  exact mul_le_mul_of_nonneg_right hexp hlog0

/-- **Exponential form of the quasi-polynomial classical time.** Under the
same radius bound, `(Dd)^{3 d ℓ^d} ≤ exp(3 d (C log N)^d log(Dd))`, an
`exp(O((log N)^d))` bound — the paper's `O(2^{(log N)^{O(1)}})` quasi-polynomial
time. -/
theorem classicalCost_quasipoly (D d ell : ℕ) (N C : ℝ)
    (hlog : 0 < Real.log (((D * d : ℕ)) : ℝ))
    (hell : (ell : ℝ) ≤ C * Real.log N) (hC : 0 ≤ C) (hN : 0 ≤ Real.log N) :
    ((classicalCost D d ell : ℕ) : ℝ) ≤
      Real.exp (3 * (d : ℝ) * (C * Real.log N) ^ d *
        Real.log (((D * d : ℕ)) : ℝ)) := by
  have hbase : (1 : ℝ) < ((D * d : ℕ) : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg (D * d))).mp hlog
  have hbase' : (1 : ℝ) < (D : ℝ) * (d : ℝ) := by
    push_cast at hbase ⊢
    exact hbase
  have hpos : 0 < ((classicalCost D d ell : ℕ) : ℝ) := by
    unfold classicalCost
    push_cast
    exact pow_pos (by linarith) _
  calc
    ((classicalCost D d ell : ℕ) : ℝ)
        = Real.exp (Real.log ((classicalCost D d ell : ℕ) : ℝ)) :=
          (Real.exp_log hpos).symm
    _ ≤ Real.exp (3 * (d : ℝ) * (C * Real.log N) ^ d *
          Real.log (((D * d : ℕ)) : ℝ)) :=
          Real.exp_le_exp_of_le (classicalCost_log_le D d ell N C hlog hell hC hN)

end Qatlib.Papers.PEPSObs16.MainResults
