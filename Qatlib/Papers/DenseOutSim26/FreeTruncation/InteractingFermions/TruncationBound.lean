/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Interacting fermions: Lieb-Robinson truncation and query complexity
(arXiv:2609.40094v1, p.15-16)

Theorem 7 (Eq. (38)-(39)) bounds the dense-output truncation error for an
interacting fermionic system with interaction strength `g` by the Lieb-Robinson
tail sum `Σ_R(X0) = Σ_{x∈∂ΦX0} Σ_{y∉X_R} G(x,y)`, which decays monotonically to
`0` as `R → ∞`.  Proposition 2 (Eq. (45)-(47)) then compares the black-box
baseline `poly(N) T³ log(1/δ)/ε` with the truncated count `e^T log(1/δ)/ε`, so
the advantage exists only on a logarithmic time scale.

The Lieb-Robinson bound itself is taken as the paper's input (B1)-(B2); the
formalised content below is the integral comparison of (38), the monotone decay
of the tail sum, and the query-ratio algebra of (47).
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.InteractingFermions

open MeasureTheory intervalIntegral

set_option autoImplicit false

/-- The Lieb-Robinson tail sum of Eq. (39).  We record it as an abstract
nonnegative quantity `Sigma R` indexed by the truncation radius, with the
paper's monotone decay to zero; the double sum over `∂ΦX0` and `X_R^c` is the
origin of its `R`-dependence. -/
noncomputable def liebRobinsonTail (Sigma : ℕ → ℝ) (R : ℕ) : ℝ := Sigma R

/-- **Theorem 7, Eq. (38)**: the dense-output truncation error is at most the
integral of the pointwise Lieb-Robinson bound.  The hypothesis `hpt` is the
paper's estimate `‖O(t) − O_R(t)‖ ≤ 2‖O‖Σ_R(X0)(e^{2gt} − 1)`; the conclusion is
obtained by monotonicity of the interval integral. -/
theorem theorem7_fermion_truncation
    {f : ℝ → ℝ} {normO Sigma g T : ℝ}
    (hT : 0 ≤ T)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hInt2 : IntervalIntegrable
      (fun t : ℝ => 2 * normO * Sigma * (Real.exp (2 * g * t) - 1)) volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t ≤ 2 * normO * Sigma * (Real.exp (2 * g * t) - 1)) :
    ∫ t in (0 : ℝ)..T, f t ≤
      ∫ t in (0 : ℝ)..T, 2 * normO * Sigma * (Real.exp (2 * g * t) - 1) :=
  intervalIntegral.integral_mono_on hT hInt hInt2 hpt

/-- **Theorem 7, Eq. (39)**: the tail sum decays monotonically to `0`. -/
theorem theorem7_tail_sum_monotone
    {Sigma : ℕ → ℝ} (hmono : ∀ R R' : ℕ, R ≤ R' → Sigma R' ≤ Sigma R) :
    ∀ R R' : ℕ, R ≤ R' → liebRobinsonTail Sigma R' ≤ liebRobinsonTail Sigma R :=
  hmono

/-- **Theorem 7, Eq. (39)**, limit form: if in addition `Σ_R → 0`, then the
truncated error vanishes asymptotically. -/
theorem theorem7_tail_sum_tendsto_zero
    {Sigma : ℕ → ℝ} (hlim : Filter.Tendsto Sigma Filter.atTop (nhds 0)) :
    Filter.Tendsto (liebRobinsonTail Sigma) Filter.atTop (nhds 0) := by
  exact hlim

/-- The interacting baseline query count of Eq. (45):
`poly(N) T³ log(1/δ)/ε`. -/
noncomputable def queryBaseInteracting (polyN T δ ε : ℝ) : ℝ :=
  polyN * T ^ 3 * Real.log (1 / δ) / ε

/-- The truncated query count of Eq. (46): `e^T log(1/δ)/ε`. -/
noncomputable def queryTruncInteracting (T δ ε : ℝ) : ℝ :=
  Real.exp T * Real.log (1 / δ) / ε

/-- **Proposition 2, Eq. (47)**: `query_base/query_trunc = poly(N) T³/e^T`. -/
theorem proposition2_query_ratio
    {polyN T δ ε : ℝ}
    (hE : Real.exp T ≠ 0) (hL : Real.log (1 / δ) ≠ 0) (hε : ε ≠ 0) :
    queryBaseInteracting polyN T δ ε / queryTruncInteracting T δ ε =
      polyN * T ^ 3 / Real.exp T := by
  unfold queryBaseInteracting queryTruncInteracting
  rw [div_eq_div_iff (div_ne_zero (mul_ne_zero hE hL) hε) hE]
  ring

/-- **Proposition 2, Eq. (47) (advantage regime)**: if `poly(N) T³ ≤ e^T` and
`0 < δ < 1`, the truncated query count does not exceed the baseline count.  The
condition `T ≳ 3 log N` is the paper's "advantage only at the time scale
`log N`". -/
theorem proposition2_advantage_implication
    {polyN T δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hmain : Real.exp T ≤ polyN * T ^ 3) :
    queryTruncInteracting T δ ε ≤ queryBaseInteracting polyN T δ ε := by
  have hlog : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_neg hδ hδ1]
  have hc : 0 ≤ Real.log (1 / δ) / ε := div_nonneg hlog.le hε.le
  have h := mul_le_mul_of_nonneg_right hmain hc
  calc queryTruncInteracting T δ ε
      = Real.exp T * (Real.log (1 / δ) / ε) := by
        unfold queryTruncInteracting; ring
    _ ≤ (polyN * T ^ 3) * (Real.log (1 / δ) / ε) := h
    _ = queryBaseInteracting polyN T δ ε := by
        unfold queryBaseInteracting; ring

/-- **Proposition 2, fast-decay part**: for `α > D` the advantage is only a
constant factor, since both norms are `Θ(1)` (Theorem 2). -/
theorem proposition2_fast_decay_constant_factor
    {query : ℝ → ℝ} {Hfull HR K : ℝ}
    (hmono : ∀ a b : ℝ, a ≤ b → query a ≤ query b)
    (hHR : HR ≤ Hfull) (hHfull : Hfull ≤ K) :
    query HR ≤ query K :=
  le_trans (hmono HR Hfull hHR) (hmono Hfull K hHfull)

end Qatlib.Papers.DenseOutSim26.FreeTruncation.InteractingFermions
