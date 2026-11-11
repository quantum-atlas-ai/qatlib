/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Error analysis for the truncated Taylor flow (DiagMatEig19)

Source: *Computing eigenvalues of diagonalizable matrices in a quantum computer*,
fixed arXiv:1912.08015.  This file formalizes the numerical core of §2.2:

* eq. (10), p.6: the `(k+1)`-term exponential truncation `T_k`;
* eq. (19)-(20), Lemma 5, p.7: after `p` Euler/Taylor steps of the discretized
  ODE (3), the state error and the norm deviation are at most
  `(1 + e/(k+1)!)^p - 1`;
* eq. (21), Proposition 6, p.8: the normalized superposition of the exact
  solution differs from the normalized superposition of the truncated states
  by at most `2√(m+1)·A·(1-A)^(-1/2)`, where `A = (1+e/(k+1)!)^m - 1`.

The paper's quantum states along the eigenvector `|E_j⟩` reduce to scalar
powers of `e^z` and `T_k(z)` with `z = 2π i λ_j Δt` (eqs. (4), (16)-(18)),
so the statements below are stated for that scalar reduction and for general
Hilbert-space vectors at the superposition step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Qatlib.Papers.DiagMatEig19.MainResults

open scoped BigOperators

/-- arXiv:1912.08015, eq. (10), p.6: the `(k+1)`-term truncation
`T_k(z) = ∑_{j=0}^{k} z^j / j!` of the exponential. -/
def taylorTrunc (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), z ^ j / (j.factorial : ℂ)

/-- arXiv:1912.08015, §2.2, p.6: for `‖z‖ ≤ 1` the truncation error of
`T_k` is at most `e/(k+1)!`.  This is the scalar estimate quoted before
eq. (11) and used in the proof of Lemma 5. -/
theorem taylorTrunc_error (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - taylorTrunc k z‖ ≤ Real.exp 1 / ((k + 1).factorial : ℝ) := by
  have hn : 0 < k + 1 := Nat.succ_pos k
  have h := Complex.exp_bound hz hn
  have hzpow : ‖z‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcoef :
      ((k + 1).succ : ℝ) * (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹
        ≤ Real.exp 1 / ((k + 1).factorial : ℝ) := by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hsucc : ((k + 1).succ : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast, hsucc]
    have hr : ((k : ℝ) + 2) / ((k : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hk1]
      linarith
    have he : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    have hfacne : ((k + 1).factorial : ℝ) ≠ 0 := ne_of_gt hfac
    have hkey : ((k : ℝ) + 2) * (((k + 1).factorial : ℝ) * ((k : ℝ) + 1))⁻¹
        = (((k : ℝ) + 2) / ((k : ℝ) + 1)) / ((k + 1).factorial : ℝ) := by
      field_simp
    rw [hkey]
    exact div_le_div_of_nonneg_right (hr.trans he) hfac.le
  calc
    ‖Complex.exp z - taylorTrunc k z‖
        = ‖Complex.exp z - ∑ m ∈ Finset.range (k + 1), z ^ m / (m.factorial : ℂ)‖ := by
          rw [taylorTrunc]
    _ ≤ ‖z‖ ^ (k + 1) *
          (((k + 1).succ : ℝ) * (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹) := h
    _ ≤ 1 * (((k + 1).succ : ℝ) *
          (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹) := by
          gcongr
    _ = ((k + 1).succ : ℝ) * (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹ := one_mul _
    _ ≤ Real.exp 1 / ((k + 1).factorial : ℝ) := hcoef

/-- arXiv:1912.08015, Lemma 5, eq. (19), p.7: along an eigenvector with
`z = 2π i λ_j Δt` (purely imaginary, `‖z‖ < 1`), the `p`-step truncation error
is at most `(1 + e/(k+1)!)^p - 1`. -/
theorem lemma5_error_bound (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (hre : z.re = 0)
    (p : ℕ) :
    ‖Complex.exp z ^ p - taylorTrunc k z ^ p‖
      ≤ (1 + Real.exp 1 / ((k + 1).factorial : ℝ)) ^ p - 1 := by
  set r : ℝ := Real.exp 1 / ((k + 1).factorial : ℝ) with hr
  have hr_nonneg : 0 ≤ r := by positivity
  have hexp : ‖Complex.exp z‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hT : ‖taylorTrunc k z‖ ≤ 1 + r := by
    have h1 : ‖taylorTrunc k z‖ ≤ ‖Complex.exp z‖ + ‖Complex.exp z - taylorTrunc k z‖ := by
      calc
        ‖taylorTrunc k z‖
            = ‖Complex.exp z - (Complex.exp z - taylorTrunc k z)‖ := by ring_nf
        _ ≤ ‖Complex.exp z‖ + ‖Complex.exp z - taylorTrunc k z‖ := norm_sub_le _ _
    have h2 : ‖Complex.exp z - taylorTrunc k z‖ ≤ r := taylorTrunc_error k z hz
    linarith
  have hstep : ∀ n : ℕ,
      ‖Complex.exp z ^ (n + 1) - taylorTrunc k z ^ (n + 1)‖
        ≤ ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖ + r * (1 + r) ^ n := by
    intro n
    have hdec : Complex.exp z ^ (n + 1) - taylorTrunc k z ^ (n + 1)
        = Complex.exp z * (Complex.exp z ^ n - taylorTrunc k z ^ n)
          + (Complex.exp z - taylorTrunc k z) * taylorTrunc k z ^ n := by
      ring
    rw [hdec]
    have h1 : ‖Complex.exp z * (Complex.exp z ^ n - taylorTrunc k z ^ n)
        + (Complex.exp z - taylorTrunc k z) * taylorTrunc k z ^ n‖
        ≤ ‖Complex.exp z‖ * ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖
          + ‖Complex.exp z - taylorTrunc k z‖ * ‖taylorTrunc k z ^ n‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h2 : ‖taylorTrunc k z ^ n‖ ≤ (1 + r) ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hT n
    have h3 : ‖Complex.exp z - taylorTrunc k z‖ ≤ r := taylorTrunc_error k z hz
    calc
      ‖Complex.exp z * (Complex.exp z ^ n - taylorTrunc k z ^ n)
          + (Complex.exp z - taylorTrunc k z) * taylorTrunc k z ^ n‖
          ≤ ‖Complex.exp z‖ * ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖
            + ‖Complex.exp z - taylorTrunc k z‖ * ‖taylorTrunc k z ^ n‖ := h1
      _ ≤ 1 * ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖ + r * (1 + r) ^ n := by
          have hmul : ‖Complex.exp z - taylorTrunc k z‖ * ‖taylorTrunc k z ^ n‖
              ≤ r * (1 + r) ^ n :=
            mul_le_mul h3 h2 (norm_nonneg _) hr_nonneg
          rw [hexp]
          linarith
      _ = ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖ + r * (1 + r) ^ n := by ring
  induction p with
  | zero => simp
  | succ n ih =>
      have h1 : ‖Complex.exp z ^ (n + 1) - taylorTrunc k z ^ (n + 1)‖
          ≤ ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖ + r * (1 + r) ^ n := hstep n
      have h2 : ‖Complex.exp z ^ n - taylorTrunc k z ^ n‖ + r * (1 + r) ^ n
          ≤ ((1 + r) ^ n - 1) + r * (1 + r) ^ n := by
        gcongr
      have h3 : ((1 + r) ^ n - 1) + r * (1 + r) ^ n = (1 + r) ^ (n + 1) - 1 := by
        rw [pow_succ]
        ring
      linarith [h1, h2, h3.le, h3.ge]

/-- arXiv:1912.08015, Lemma 5, eq. (20), p.7: the norm of the truncated state
deviates from `1` by at most `(1 + e/(k+1)!)^p - 1`. -/
theorem lemma5_norm_deviation (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (hre : z.re = 0)
    (p : ℕ) :
    |‖taylorTrunc k z ^ p‖ - 1|
      ≤ (1 + Real.exp 1 / ((k + 1).factorial : ℝ)) ^ p - 1 := by
  have herr := lemma5_error_bound k z hz hre p
  have hexp : ‖Complex.exp z ^ p‖ = 1 := by
    rw [norm_pow, Complex.norm_exp, hre, Real.exp_zero, one_pow]
  calc
    |‖taylorTrunc k z ^ p‖ - 1| = |‖taylorTrunc k z ^ p‖ - ‖Complex.exp z ^ p‖| := by
      rw [hexp]
    _ ≤ ‖taylorTrunc k z ^ p - Complex.exp z ^ p‖ := abs_norm_sub_norm_le _ _
    _ = ‖Complex.exp z ^ p - taylorTrunc k z ^ p‖ := norm_sub_rev _ _
    _ ≤ _ := herr

/-- arXiv:1912.08015, Lemma 5, eq. (19)-(20), p.7, packaged: for
`z = 2π i λ_j Δt` with `‖z‖ ≤ 1`, both the state error and the norm deviation
after `p` steps are bounded by `(1 + e/(k+1)!)^p - 1`. -/
theorem lemma5_taylor_evolution_error (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (hre : z.re = 0)
    (p : ℕ) :
    ‖Complex.exp z ^ p - taylorTrunc k z ^ p‖
        ≤ (1 + Real.exp 1 / ((k + 1).factorial : ℝ)) ^ p - 1 ∧
      |‖taylorTrunc k z ^ p‖ - 1|
        ≤ (1 + Real.exp 1 / ((k + 1).factorial : ℝ)) ^ p - 1 :=
  ⟨lemma5_error_bound k z hz hre p, lemma5_norm_deviation k z hz hre p⟩

end Qatlib.Papers.DiagMatEig19.MainResults

namespace Qatlib.Papers.DiagMatEig19.MainResults.SuperpositionAux

/-- Scalar inequality used in the proof of Proposition 6 (arXiv:1912.08015, p.8):
if `a > 0`, `b > 0`, `‖a² - b²‖ ≤ a² A` and `0 ≤ A < 1`, then the two
normalization differences are at most `A/(a√(1-A))`. -/
theorem normalization_bounds {a b A : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA0 : 0 ≤ A) (hA1 : A < 1)
    (hab : |a ^ 2 - b ^ 2| ≤ a ^ 2 * A) :
    |1 / a - 1 / b| ≤ A / (a * Real.sqrt (1 - A)) ∧
      1 / b ≤ 1 / (a * Real.sqrt (1 - A)) := by
  have hs : 0 < Real.sqrt (1 - A) := Real.sqrt_pos.2 (by linarith)
  have ha2pos : 0 < a ^ 2 := by positivity
  have hbsq : a ^ 2 * (1 - A) ≤ b ^ 2 := by
    have := abs_le.1 hab
    nlinarith
  have hb_ge : a * Real.sqrt (1 - A) ≤ b := by
    have h1 : Real.sqrt (a ^ 2 * (1 - A)) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hbsq
    have h2 : Real.sqrt (a ^ 2 * (1 - A)) = a * Real.sqrt (1 - A) := by
      rw [Real.sqrt_mul ha2pos.le, Real.sqrt_sq ha.le]
    have h3 : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
    linarith [h1, h2.symm, h3.symm]
  have hdiff : |a - b| ≤ a * A := by
    have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [hfactor, abs_mul] at hab
    have habs : |a + b| = a + b := abs_of_pos (by linarith)
    rw [habs] at hab
    have hpos : 0 < a + b := by linarith
    rw [mul_comm] at hab
    have hle : |a - b| ≤ a ^ 2 * A / (a + b) := by
      rw [le_div_iff₀ hpos]
      linarith
    have hdiv : a ^ 2 * A / (a + b) ≤ a * A := by
      rw [div_le_iff₀ hpos]
      nlinarith [mul_nonneg hA0 ha.le]
    linarith
  constructor
  · have h1 : |1 / a - 1 / b| = |a - b| / (a * b) := by
      have h : 1 / a - 1 / b = (b - a) / (a * b) := by
        field_simp
      rw [h, abs_div, abs_of_pos (by positivity : 0 < a * b), abs_sub_comm]
    rw [h1]
    have h2 : |a - b| / (a * b) ≤ (a * A) / (a * b) := by gcongr
    have h3 : (a * A) / (a * b) = A / b := by
      field_simp [ne_of_gt ha]
    have h4 : A / b ≤ A / (a * Real.sqrt (1 - A)) := by
      gcongr
    linarith
  · exact one_div_le_one_div_of_le (by positivity) hb_ge

end Qatlib.Papers.DiagMatEig19.MainResults.SuperpositionAux

namespace Qatlib.Papers.DiagMatEig19.MainResults

open scoped ComplexOrder

/-- The embedding of a state `x : H` into the `p`-th slot of the time register,
i.e. `|p⟩|x⟩` in the paper's notation (arXiv:1912.08015, Proposition 6). -/
def timeEmbed {H : Type*} [Zero H] (m : ℕ) (p : Fin (m + 1)) (x : H) :
    PiLp 2 (fun _ : Fin (m + 1) => H) :=
  PiLp.single 2 p x

/-- arXiv:1912.08015, Proposition 6, eq. (21), p.8.  Let `u p = |x(t_p)⟩` be
the exact unit-norm solution states and `v p = |x_{p,0}⟩` the truncated states,
with `L = ∑_p ‖v p‖²` and `|L - (m+1)| ≤ (m+1) A`.  Then the normalized
superposition of the exact states and that of the truncated states differ in
`ℓ²` norm by at most `2√(m+1)·A·(1-A)^(-1/2)`.

The tensor product with the time register is realized as `PiLp 2`, i.e. the
direct sum of `m+1` copies of the state space with the `ℓ²` norm; the paper's
`∑_p |p⟩|·⟩` is exactly `∑_p PiLp.single p (·)`. -/
theorem proposition6_superposition_norm_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (m : ℕ) (u v : Fin (m + 1) → H) (A : ℝ)
    (hu : ∀ p, ‖u p‖ = 1)
    (hδ : ∀ p, ‖u p - v p‖ ≤ A)
    (hA0 : 0 ≤ A) (hA1 : A < 1)
    (L : ℝ) (hLpos : 0 < L)
    (hLdef : L = ∑ p : Fin (m + 1), ‖v p‖ ^ 2)
    (hL : |L - ((m + 1 : ℕ) : ℝ)| ≤ ((m + 1 : ℕ) : ℝ) * A) :
    ‖∑ p : Fin (m + 1), timeEmbed m p
        (((1 / Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) • u p
          - ((1 / Real.sqrt L : ℝ) : ℂ) • v p)‖
      ≤ 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) * A / Real.sqrt (1 - A) := by
  set a : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ)
  set b : ℝ := Real.sqrt L
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < a := Real.sqrt_pos.2 hNpos
  have hb : 0 < b := Real.sqrt_pos.2 hLpos
  have ha2 : a ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt hNpos.le
  have hb2 : b ^ 2 = L := Real.sq_sqrt hLpos.le
  have hs : 0 < Real.sqrt (1 - A) := Real.sqrt_pos.2 (by linarith)
  have hL' : |a ^ 2 - b ^ 2| ≤ a ^ 2 * A := by
    rw [ha2, hb2, abs_sub_comm]; exact hL
  obtain ⟨hfirst, hsecond⟩ :=
    SuperpositionAux.normalization_bounds ha hb hA0 hA1 hL'
  -- triangle inequality over the time register
  have htri : ‖∑ p : Fin (m + 1), timeEmbed m p
        (((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p)‖
      ≤ ∑ p : Fin (m + 1),
          ‖((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p‖ := by
    calc
      ‖∑ p : Fin (m + 1), timeEmbed m p
          (((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p)‖
          ≤ ∑ p : Fin (m + 1),
              ‖timeEmbed m p (((1 / a : ℝ) : ℂ) • u p
                - ((1 / b : ℝ) : ℂ) • v p)‖ := norm_sum_le _ _
      _ = ∑ p : Fin (m + 1),
            ‖((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p‖ := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          simp only [timeEmbed, PiLp.norm_single]
  -- componentwise bound
  have hcomp : ∀ p : Fin (m + 1),
      ‖((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p‖
        ≤ |1 / a - 1 / b| + (1 / b) * A := by
    intro p
    have hdecomp : ((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p
        = (((1 / a - 1 / b : ℝ)) : ℂ) • u p
          + ((1 / b : ℝ) : ℂ) • (u p - v p) := by
      module
    rw [hdecomp]
    calc
      ‖((((1 / a - 1 / b : ℝ)) : ℂ) • u p
          + ((1 / b : ℝ) : ℂ) • (u p - v p))‖
          ≤ ‖(((1 / a - 1 / b : ℝ)) : ℂ) • u p‖
            + ‖((1 / b : ℝ) : ℂ) • (u p - v p)‖ := norm_add_le _ _
      _ = |1 / a - 1 / b| * ‖u p‖ + (1 / b) * ‖u p - v p‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / b)]
      _ = |1 / a - 1 / b| + (1 / b) * ‖u p - v p‖ := by
          rw [hu p, mul_one]
      _ ≤ |1 / a - 1 / b| + (1 / b) * A := by
          gcongr
          exact hδ p
  have hsum : ∑ p : Fin (m + 1),
      ‖((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p‖
        ≤ ((m + 1 : ℕ) : ℝ) * (|1 / a - 1 / b| + (1 / b) * A) := by
    calc
      ∑ p : Fin (m + 1),
          ‖((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p‖
          ≤ ∑ _p : Fin (m + 1), (|1 / a - 1 / b| + (1 / b) * A) := by
            refine Finset.sum_le_sum (fun p _ => hcomp p)
      _ = ((m + 1 : ℕ) : ℝ) * (|1 / a - 1 / b| + (1 / b) * A) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfinal : ((m + 1 : ℕ) : ℝ) * (|1 / a - 1 / b| + (1 / b) * A)
      ≤ 2 * a * A / Real.sqrt (1 - A) := by
    have hbA : (1 / b) * A ≤ A / (a * Real.sqrt (1 - A)) := by
      have h1 : (1 / b) * A ≤ (1 / (a * Real.sqrt (1 - A))) * A :=
        mul_le_mul_of_nonneg_right hsecond hA0
      have h2 : (1 / (a * Real.sqrt (1 - A))) * A
          = A / (a * Real.sqrt (1 - A)) := by ring
      linarith [h1, h2.le, h2.ge]
    have hstep : ((m + 1 : ℕ) : ℝ) * (|1 / a - 1 / b| + (1 / b) * A)
        ≤ ((m + 1 : ℕ) : ℝ) *
            (A / (a * Real.sqrt (1 - A)) + A / (a * Real.sqrt (1 - A))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hfirst hbA
    have hcalc : ((m + 1 : ℕ) : ℝ) *
        (A / (a * Real.sqrt (1 - A)) + A / (a * Real.sqrt (1 - A)))
          = 2 * a * A / Real.sqrt (1 - A) := by
      rw [← ha2]
      field_simp [ne_of_gt ha, ne_of_gt hs]
      ring
    linarith [hcalc.le, hcalc.ge, hstep]
  have hmain : ‖∑ p : Fin (m + 1), timeEmbed m p
        (((1 / a : ℝ) : ℂ) • u p - ((1 / b : ℝ) : ℂ) • v p)‖
      ≤ 2 * a * A / Real.sqrt (1 - A) := le_trans htri (le_trans hsum hfinal)
  simpa [a, b] using hmain

end Qatlib.Papers.DiagMatEig19.MainResults
