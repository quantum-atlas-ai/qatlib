/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Asymptotic query complexity for free systems (arXiv:2609.40094v1, p.11-12)

This file formalises Theorem 2 (Eq. (28)), Theorem 4 (Eq. (31)-(33)), Theorem 5
(Eq. (34)), Theorem 3 (Eq. (29)) and Proposition 1 (Eq. (30)) of the paper.

The generic black-box complexity formula, Theorem 3.3 of [29], used throughout
is (paper Eq. (8))

`query(H, T, ε) = O(‖H‖ T³ log(1/δ) / ε)`,

i.e. linear in the Hamiltonian norm.  We model an abstract query-count function
of the Hamiltonian norm and derive the paper's asymptotic statements from it.
The genuinely analytic inputs are the norm estimates of Lemma 1
(`NormBoundIntegral.lean`): `‖H‖ = Θ(1)`, `Θ(log L)` or `Θ(L^{D−α})`.

Claims covered:
* `theorem2_leading_order` (c002(i), proved from monotonicity of the cost bound);
* `theorem2_finite_size_reduction` (c002(ii), proved from monotonicity);
* `theorem3_free_fermion_error` and `theorem3_sufficient_radius` (c015);
* `proposition1_baseline_query` (c016, proved from the norm bound);
* `theorem4_ratio_identity`, `theorem4_ratio_diverges` (c003, proved);
* `theorem5_ratio_identity`, `theorem5_log_ratio_diverges` (c004, proved).
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- The paper's truncated slow-decay query count, Eq. (32):
`(T²/ε)^{(1−α/D)/(α−D/2)} · T³ log(1/δ)/ε`. -/
noncomputable def queryTruncSlow (T ε δ α D : ℝ) : ℝ :=
  (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) * (T ^ 3 * Real.log (1 / δ) / ε)

/-- The paper's baseline slow-decay query count, Eq. (30):
`N^{1−α/D} · T³ log(1/δ)/ε`. -/
noncomputable def queryBaseSlow (N T ε δ α D : ℝ) : ℝ :=
  N ^ (1 - α / D) * (T ^ 3 * Real.log (1 / δ) / ε)

/-- The `α = D` baseline query count underlying Eq. (34), with the logarithmic
norm dependence `‖H‖ = Θ(log N)`. -/
noncomputable def queryBaseLog (N T ε δ : ℝ) : ℝ :=
  Real.log N * (T ^ 3 * Real.log (1 / δ) / ε)

/-- The `α = D` truncated query count underlying Eq. (34). -/
noncomputable def queryTruncLog (T ε δ : ℝ) : ℝ :=
  Real.log T * (T ^ 3 * Real.log (1 / δ) / ε)

/-- **Theorem 2(i), Eq. (28)**: when both the full and the truncated Hamiltonian
norms are bounded by a constant `K` (`Θ(1)` in `N` and `R`), the generic
complexity formula yields `query_base = query_trunc = O(T³ log(1/δ)/ε)`, with
`O`-constant `C·K`. -/
theorem theorem2_leading_order
    {queryBase queryTrunc : ℝ → ℝ} {K C T ε δ Hb Ht : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hHb0 : 0 ≤ Hb) (hHb : Hb ≤ K) (hHt0 : 0 ≤ Ht) (hHt : Ht ≤ K)
    (hlog : 0 ≤ Real.log (1 / δ))
    (hbase : ∀ H, 0 ≤ H → H ≤ K →
      queryBase H ≤ C * (H * T ^ 3 * Real.log (1 / δ) / ε))
    (htrunc : ∀ H, 0 ≤ H → H ≤ K →
      queryTrunc H ≤ C * (H * T ^ 3 * Real.log (1 / δ) / ε)) :
    queryBase Hb ≤ C * K * (T ^ 3 * Real.log (1 / δ) / ε) ∧
      queryTrunc Ht ≤ C * K * (T ^ 3 * Real.log (1 / δ) / ε) := by
  constructor
  · have h1 : Hb * T ^ 3 * Real.log (1 / δ) / ε ≤ K * T ^ 3 * Real.log (1 / δ) / ε := by
      have hT3 : 0 ≤ T ^ 3 := pow_nonneg hT 3
      have hnum : Hb * T ^ 3 * Real.log (1 / δ) ≤ K * T ^ 3 * Real.log (1 / δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHb hT3) hlog
      exact div_le_div_of_nonneg_right hnum hε.le
    calc queryBase Hb ≤ C * (Hb * T ^ 3 * Real.log (1 / δ) / ε) := hbase Hb hHb0 hHb
      _ ≤ C * (K * T ^ 3 * Real.log (1 / δ) / ε) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = C * K * (T ^ 3 * Real.log (1 / δ) / ε) := by ring
  · have h1 : Ht * T ^ 3 * Real.log (1 / δ) / ε ≤ K * T ^ 3 * Real.log (1 / δ) / ε := by
      have hT3 : 0 ≤ T ^ 3 := pow_nonneg hT 3
      have hnum : Ht * T ^ 3 * Real.log (1 / δ) ≤ K * T ^ 3 * Real.log (1 / δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHt hT3) hlog
      exact div_le_div_of_nonneg_right hnum hε.le
    calc queryTrunc Ht ≤ C * (Ht * T ^ 3 * Real.log (1 / δ) / ε) := htrunc Ht hHt0 hHt
      _ ≤ C * (K * T ^ 3 * Real.log (1 / δ) / ε) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = C * K * (T ^ 3 * Real.log (1 / δ) / ε) := by ring

/-- **Theorem 2(ii)**: finite-size reduction.  If the truncated normalization
`H_R` is no larger than the full-system normalization `‖H‖` and the query count
is monotone in the Hamiltonian norm, then the truncated query count is at most
the baseline count; the gain is an `N`-independent constant factor whenever `R`
is independent of `N` (Corollary 2). -/
theorem theorem2_finite_size_reduction
    {query : ℝ → ℝ} {Hfull HR : ℝ}
    (hmono : ∀ a b : ℝ, a ≤ b → query a ≤ query b)
    (hHR : HR ≤ Hfull) :
    query HR ≤ query Hfull :=
  hmono HR Hfull hHR

/-- **Theorem 3, Eq. (29) (integration step)**: for slow decay `D > α > D/2`,
the pointwise light-cone estimate `‖O(t) − O_R(t)‖ ≤ t/R^{α−D/2}` integrates to
`∫₀^T ‖O(t) − O_R(t)‖ dt ≤ T²/R^{α−D/2}`.  This is the paper's derivation of
Eq. (29) from the state-independent estimate of Eq. (52). -/
theorem theorem3_free_fermion_error
    {f : ℝ → ℝ} {T α D R : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ t / R ^ (α - D / 2)) :
    ∫ t in (0 : ℝ)..T, f t ≤ T ^ 2 / R ^ (α - D / 2) := by
  simpa using integral_div_rpow_bound hT zero_le_one hR hInt (by simpa using hpt)

/-- **Theorem 3, Eq. (29)**: the state-independent dense-output truncation error
bound `|J_H(O) − J_{H_R}(O)| ≤ T²/R^{α−D/2}`, obtained from
`|J_H(O) − J_{H_R}(O)| ≤ ∫₀^T ‖O(t) − O_R(t)‖ dt` (normalised initial state)
and the integrated pointwise estimate. -/
theorem theorem3_dense_output_error
    {f : ℝ → ℝ} {JH JHR T α D R : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ t / R ^ (α - D / 2))
    (hgap : |JH - JHR| ≤ ∫ t in (0 : ℝ)..T, f t) :
    |JH - JHR| ≤ T ^ 2 / R ^ (α - D / 2) :=
  le_trans hgap (theorem3_free_fermion_error hT hR hInt hpt)

/-- **Theorem 3, radius choice**: if the error obeys the bound `T²/R^{α−D/2}`
and `R ≥ (T²/ε)^{1/(α−D/2)}`, then the error is at most `ε`.  This is the
paper's statement that a radius of order `(T²/ε)^{1/(α−D/2)}` suffices. -/
theorem theorem3_sufficient_radius
    {JH JHR T ε α D R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hα : 0 < α - D / 2)
    (herr : |JH - JHR| ≤ T ^ 2 / R ^ (α - D / 2))
    (hRbig : (T ^ 2 / ε) ^ (1 / (α - D / 2)) ≤ R) :
    |JH - JHR| ≤ ε := by
  have hq : (0 : ℝ) < α - D / 2 := hα
  have hbase0 : 0 ≤ T ^ 2 / ε := div_nonneg (sq_nonneg T) hε.le
  have hpow : T ^ 2 / ε ≤ R ^ (α - D / 2) := by
    have hmono : ((T ^ 2 / ε) ^ (1 / (α - D / 2))) ^ (α - D / 2) ≤
        R ^ (α - D / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase0 _) hRbig hq.le
    rwa [← Real.rpow_mul hbase0, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one] at hmono
  have hRq : (0 : ℝ) < R ^ (α - D / 2) := Real.rpow_pos_of_pos hR _
  have hle : T ^ 2 / R ^ (α - D / 2) ≤ ε := by
    rw [div_le_iff₀ hRq]
    have := (div_le_iff₀ hε).mp hpow
    linarith
  linarith [herr]

/-- **Proposition 1, Eq. (30)**: applying the generic formula (8) to the full
`N`-site Hamiltonian and using `‖H‖ = Θ(N^{1−α/D})` (Lemma 1, regime `α < D`,
with `L = Θ(N^{1/D})`) gives
`query_base(N,T,ε) = O(N^{1−α/D} T³ log(1/δ)/ε)`. -/
theorem proposition1_baseline_query
    {queryBase : ℝ → ℝ} {C n T ε δ α D : ℝ}
    (hn : 0 ≤ n ^ (1 - α / D))
    (hbase : ∀ H, 0 ≤ H → H ≤ n ^ (1 - α / D) →
      queryBase H ≤ C * (H * T ^ 3 * Real.log (1 / δ) / ε)) :
    queryBase (n ^ (1 - α / D)) ≤
      C * (n ^ (1 - α / D) * (T ^ 3 * Real.log (1 / δ) / ε)) := by
  calc queryBase (n ^ (1 - α / D))
      ≤ C * (n ^ (1 - α / D) * T ^ 3 * Real.log (1 / δ) / ε) :=
        hbase _ hn (le_refl _)
    _ = C * (n ^ (1 - α / D) * (T ^ 3 * Real.log (1 / δ) / ε)) := by ring

/-- **Theorem 4, Eq. (33), ratio identity**: the baseline-to-truncated query
ratio equals `N^{1−α/D} / (T²/ε)^{(1−α/D)/(α−D/2)}`. -/
theorem theorem4_ratio_identity
    {N T ε δ α D : ℝ}
    (hQ : (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) ≠ 0)
    (hL : T ^ 3 * Real.log (1 / δ) / ε ≠ 0) :
    queryBaseSlow N T ε δ α D / queryTruncSlow T ε δ α D =
      N ^ (1 - α / D) / (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) := by
  unfold queryBaseSlow queryTruncSlow
  rw [div_eq_div_iff (mul_ne_zero hQ hL) hQ]
  ring

/-- **Theorem 4, Eq. (33)**: for `D/2 < α < D` and fixed `T, ε, δ`, the query
ratio diverges as `N → ∞` (given positive normalization factors). -/
theorem theorem4_ratio_diverges
    {α D T ε δ : ℝ} (hD : 0 < D) (hαD : α < D) (_hα : D / 2 < α)
    (hQ : 0 < T ^ 2 / ε) (hL : 0 < T ^ 3 * Real.log (1 / δ) / ε) :
    Filter.Tendsto
      (fun N : ℝ => queryBaseSlow N T ε δ α D / queryTruncSlow T ε δ α D)
      Filter.atTop Filter.atTop := by
  have hp : 0 < 1 - α / D := by
    rw [sub_pos]
    exact (div_lt_one hD).mpr hαD
  have hQpos : 0 < (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) :=
    Real.rpow_pos_of_pos hQ _
  have hQne : (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) ≠ 0 := hQpos.ne'
  have hLne : T ^ 3 * Real.log (1 / δ) / ε ≠ 0 := hL.ne'
  have hcongr : (fun N : ℝ => queryBaseSlow N T ε δ α D / queryTruncSlow T ε δ α D)
      = fun N : ℝ => N ^ (1 - α / D) /
          (T ^ 2 / ε) ^ ((1 - α / D) / (α - D / 2)) := by
    funext N
    exact theorem4_ratio_identity hQne hLne
  rw [hcongr]
  exact (tendsto_rpow_atTop hp).atTop_div_const hQpos

/-- **Theorem 5, Eq. (34), ratio identity**: for `α = D` the ratio equals
`log N / log T`. -/
theorem theorem5_ratio_identity
    {N T ε δ : ℝ} (hT : Real.log T ≠ 0)
    (hL : T ^ 3 * Real.log (1 / δ) / ε ≠ 0) :
    queryBaseLog N T ε δ / queryTruncLog T ε δ = Real.log N / Real.log T := by
  unfold queryBaseLog queryTruncLog
  rw [div_eq_div_iff (mul_ne_zero hT hL) hT]
  ring

/-- **Theorem 5, Eq. (34)**: for fixed `T > 1`, the ratio `log N / log T` diverges
as `N → ∞`. -/
theorem theorem5_log_ratio_diverges
    {T : ℝ} (hT : 1 < T) :
    Filter.Tendsto (fun N : ℝ => Real.log N / Real.log T) Filter.atTop Filter.atTop := by
  have hlogT : 0 < Real.log T := Real.log_pos hT
  exact Real.tendsto_log_atTop.atTop_div_const hlogT

end Qatlib.Papers.DenseOutSim26.FreeTruncation.FreeLightCone
