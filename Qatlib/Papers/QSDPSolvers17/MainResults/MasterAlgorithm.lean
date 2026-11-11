/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QSDPSolvers17.MainResults.Model.SdpInstance
import Qatlib.Concepts.MatrixWeights.LambdaMin

set_option backward.isDefEq.respectTransparency false

/-!
# Master algorithm for SDP feasibility (paper QSDPSolvers17, Theorem 3, App. A)

Source: arXiv:1710.02581, Appendix A, pp. 15–16.  Algorithm 2 is the matrix
multiplicative weights (MMW) algorithm of [19] applied to the zero-sum game defined by
Oracle A.1.  Its analysis rests on Proposition 2 (Corollary 4 of [19]) with learning
rate `δ = ε/4`, which gives, for every density matrix `ρ`,

`(1 + ε/4) ∑_t Tr(M_t ρ_t) ≥ ∑_t Tr(M_t ρ) - 4 ln n / ε`   (equation (A.5)),

where `M_t = (I - A_{j(t)})/2`.  Assuming that `S_0 ≠ ∅` and that Oracle A.1 returns a
violating index in every round, (A.6)–(A.8) turn this into `T < 16 ln n / ε²`, a
contradiction with `T = ⌈16 ln n / ε²⌉`.  Hence within `16 ln n / ε²` rounds the
algorithm either finds a violated constraint or outputs a state in `S_ε`.

The key analytic input, the chord/comparator inequality at a *negative* learning rate
`η = -ε/4`, is provided by the frozen development
`QuantumAlgorithm.Concepts.MatrixWeights.LambdaMin.matrix_mw_chord_comparator`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.MasterAlgorithm

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.MatrixWeights.LambdaMin
open Qatlib.Papers.QSDPSolvers17.MainResults.Model
open scoped ComplexOrder MatrixOrder BigOperators

/-- Elementary exponential bound used in the passage from Proposition 2 to (A.5):
for `0 ≤ x ≤ 1/2`, `exp x ≤ 1 + x + x²`.  Proof by the truncated Taylor expansion
(three terms) with the Lagrange-type remainder of `Real.exp_bound'`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound' hx0 (by linarith) (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h
  nlinarith [hx0, hx1, sq_nonneg x, pow_nonneg hx0 3]

/-- Equation (A.5) of App. A, derived from Proposition 2 at learning rate `η = -ε/4`.
For every density matrix `σ` and every family `0 ≤ M_t ≤ I`,

`(1 + ε/4) ∑_t Tr(M_t ρ_t) ≥ ∑_t Tr(M_t σ) - 4 ln D / ε`,

where `ρ_t = mmwState D M (-ε/4) t`.  The constants `1 + ε/4` and `4/ε` are exactly
those of (A.5); they follow from `(e^{ε/4} - 1)/(ε/4) ≤ 1 + ε/4` (proved via
`exp_le_one_add_add_sq`). -/
theorem chord_comparator_lower (D T : ℕ) (M : ℕ → Operator D) (ε : ℝ)
    (hD : 0 < D) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1)
    (σ : Operator D) (hσ : IsDensityOperator σ) :
    (1 + ε / 4) *
        (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M (-(ε / 4)) t)).re) ≥
      (∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re) - 4 * Real.log D / ε := by
  have hδ : 0 < ε / 4 := by linarith
  have hδ_le : ε / 4 ≤ 1 / 2 := by linarith
  have hchord := matrix_mw_chord_comparator D T M (-(ε / 4)) σ hD hM hσ
  -- hchord : (1 - exp (ε/4)) * A ≤ log D - (ε/4) * C
  set A : ℝ := ∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M (-(ε / 4)) t)).re
    with hA_def
  set C : ℝ := ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re with hC_def
  have hexp_le : Real.exp (ε / 4) ≤ 1 + ε / 4 + (ε / 4) ^ 2 :=
    exp_le_one_add_add_sq hδ.le hδ_le
  have hexp_ge : 1 ≤ Real.exp (ε / 4) := Real.one_le_exp hδ.le
  -- The actual gains are nonnegative, so we may multiply the chord inequality by a
  -- factor dominating `(exp (ε/4) - 1) / (ε/4)`.
  have hA_nonneg : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro t _
    have hρ : IsDensityOperator (mmwState D M (-(ε / 4)) t) :=
      (matrix_mw_actual_gibbs_iterates_density D M (-(ε / 4)) t hD
        (fun s => (hM s).1.isHermitian)).2
    have hmono := mmw_trace_mul_mono D (mmwState D M (-(ε / 4)) t) (0 : Operator D) (M t)
      hρ.1 (by rw [Matrix.le_iff]; simpa using (hM t).1)
    rw [Matrix.mul_zero, Matrix.trace_zero, Matrix.trace_mul_comm (mmwState D M (-(ε / 4)) t)
      (M t)] at hmono
    exact hmono
  have hkey : (Real.exp (ε / 4) - 1) * A ≥ (ε / 4) * C - Real.log D := by
    have := hchord
    have hexpε : Real.exp (-(-(ε / 4))) = Real.exp (ε / 4) := by ring_nf
    rw [hexpε] at this
    linarith
  have hfactor : Real.exp (ε / 4) - 1 ≤ (ε / 4) * (1 + ε / 4) := by
    nlinarith [hexp_le]
  have hscaled : (ε / 4) * (1 + ε / 4) * A ≥ (ε / 4) * C - Real.log D := by
    nlinarith [mul_le_mul_of_nonneg_right hfactor hA_nonneg, hkey]
  -- Divide by `ε/4`.
  have hfinal : (1 + ε / 4) * A ≥ C - 4 * Real.log D / ε := by
    have hδne : ε / 4 ≠ 0 := ne_of_gt hδ
    field_simp [hδne] at hscaled ⊢
    nlinarith [hscaled]
  simpa [hA_def, hC_def] using hfinal

/-- **Theorem 3 (Master Algorithm)**, arXiv:1710.02581 App. A, pp. 15–16.
Let `P` be an SDP feasibility instance with `-I ≤ A_j ≤ I` and let `σ ∈ S_0` be an
exactly feasible density matrix.  For `0 < ε ≤ 1/2` and any horizon
`T ≥ 16 ln D / ε²`, Algorithm 2 cannot receive a violating index from Oracle A.1 in
*every* round: there is some round `t < T` in which the current MMW state
`ρ_t = mmwState D (fun s => gain (j s)) (-ε/4) t` satisfies all relaxed constraints
`Tr(A_{j(t)} ρ_t) ≤ a_{j(t)} + ε`, i.e. lies in `S_ε`.

This is the soundness half of Theorem 3; the query bound is the statement that the
horizon is `T = ⌈16 ln D / ε²⌉` (see `master_algorithm_query_bound`). -/
theorem master_algorithm_soundness
    {m D : ℕ} (P : SdpInstance m D) (ε : ℝ) (T : ℕ) (j : ℕ → Fin m)
    (hD2 : 2 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hT : 16 * Real.log D / ε ^ 2 ≤ (T : ℝ))
    (hAspec : ∀ i, (-1 : Operator D) ≤ P.A i ∧ P.A i ≤ 1)
    (hσ : ∃ σ, FeasibleAt P σ) :
    ¬ ∀ t, t < T →
      P.a (j t) + ε <
        (Matrix.trace (P.A (j t) * mmwState D (fun s => P.gain (j s)) (-(ε / 4)) t)).re := by
  intro hviol
  obtain ⟨σ, hσfeas⟩ := hσ
  have hD : 0 < D := by omega
  have hlog : 0 < Real.log D := Real.log_pos (by exact_mod_cast hD2)
  have hεpos : 0 < 16 * Real.log D / ε ^ 2 := by positivity
  have hT0R : (0 : ℝ) < T := lt_of_lt_of_le hεpos hT
  have hT0 : 0 < T := by exact_mod_cast hT0R
  let M : ℕ → Operator D := fun s => P.gain (j s)
  let ρ : ℕ → Operator D := fun t => mmwState D M (-(ε / 4)) t
  have hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1 := fun s =>
    ⟨gain_posSemidef P (hAspec (j s)).2, gain_le_one P (hAspec (j s)).1⟩
  have hdensity : ∀ t, IsDensityOperator (ρ t) := fun t =>
    (matrix_mw_actual_gibbs_iterates_density D M (-(ε / 4)) t hD
      (fun s => (hM s).1.isHermitian)).2
  -- (A.5)
  have hA5 := chord_comparator_lower D T M ε hD hε0 hε1 hM σ hσfeas.1
  -- Termwise upper bound for the actual gains from the oracle violations.
  have hactual : ∀ t, t < T →
      (Matrix.trace (M t * ρ t)).re < (1 - P.a (j t) - ε) / 2 := by
    intro t ht
    have htr := trace_gain_mul P (j t) (ρ t)
    have hρtr : (Matrix.trace (ρ t)).re = 1 := by
      rw [(hdensity t).2]; norm_num
    have hv := hviol t ht
    dsimp [M, ρ] at htr hv ⊢
    rw [htr, hρtr]
    linarith
  -- Termwise lower bound for the comparator `σ`.
  have hcomp : ∀ t, t < T →
      (1 - P.a (j t)) / 2 ≤ (Matrix.trace (M t * σ)).re := by
    intro t _
    have htr := trace_gain_mul P (j t) σ
    have hσtr : (Matrix.trace σ).re = 1 := by
      rw [hσfeas.1.2]; norm_num
    have hle := hσfeas.2 (j t)
    dsimp [M] at htr ⊢
    rw [htr, hσtr]
    linarith
  -- `a_{j(t)} ≥ -1`, derived as in App. A from `Tr(M_j σ) ≤ 1`.
  have hage : ∀ t, t < T → -1 ≤ P.a (j t) := by
    intro t ht
    have hupper := trace_gain_mul_le_one P (hAspec (j t)).1 hσfeas.1
    have hlower := hcomp t ht
    linarith
  -- Sum the two termwise families.
  have hsum_actual : (∑ t ∈ Finset.range T, (Matrix.trace (M t * ρ t)).re) <
      ∑ t ∈ Finset.range T, (1 - P.a (j t) - ε) / 2 := by
    refine Finset.sum_lt_sum (fun t ht => le_of_lt (hactual t (Finset.mem_range.mp ht))) ?_
    exact ⟨0, Finset.mem_range.mpr hT0, hactual 0 hT0⟩
  have hsum_comp : (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2) ≤
      ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re := by
    refine Finset.sum_le_sum (fun t ht => hcomp t (Finset.mem_range.mp ht))
  -- Combine with (A.5) and rearrange to (A.6)–(A.7).
  have hε4pos : 0 < 1 + ε / 4 := by positivity
  have hsum_actual_scaled :
      (1 + ε / 4) * (∑ t ∈ Finset.range T, (Matrix.trace (M t * ρ t)).re) <
        (1 + ε / 4) * (∑ t ∈ Finset.range T, (1 - P.a (j t) - ε) / 2) :=
    mul_lt_mul_of_pos_left hsum_actual hε4pos
  have hA7 : 4 * Real.log D / ε >
      (ε / 8) * (∑ t ∈ Finset.range T, (3 + ε + P.a (j t))) := by
    have h1 : (1 + ε / 4) * (∑ t ∈ Finset.range T, (Matrix.trace (M t * ρ t)).re) ≥
        (∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re) - 4 * Real.log D / ε :=
      hA5
    have h2 : (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2) ≤
        ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re := hsum_comp
    have h3 : (1 + ε / 4) * (∑ t ∈ Finset.range T, (1 - P.a (j t) - ε) / 2) >
        (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2) - 4 * Real.log D / ε := by
      linarith
    -- Expand the difference of the two sums.
    have hexpand :
        (1 + ε / 4) * (∑ t ∈ Finset.range T, (1 - P.a (j t) - ε) / 2) -
            (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2) =
          -((ε / 8) * (∑ t ∈ Finset.range T, (3 + ε + P.a (j t)))) := by
      have hterm : ∀ t,
          (1 + ε / 4) * ((1 - P.a (j t) - ε) / 2) - (1 - P.a (j t)) / 2 =
            -((ε / 8) * (3 + ε + P.a (j t))) := by
        intro t; ring
      calc (1 + ε / 4) * (∑ t ∈ Finset.range T, (1 - P.a (j t) - ε) / 2) -
            (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2)
          = (∑ t ∈ Finset.range T, (1 + ε / 4) * ((1 - P.a (j t) - ε) / 2)) -
              (∑ t ∈ Finset.range T, (1 - P.a (j t)) / 2) := by
            rw [Finset.mul_sum]
        _ = ∑ t ∈ Finset.range T,
              ((1 + ε / 4) * ((1 - P.a (j t) - ε) / 2) - (1 - P.a (j t)) / 2) := by
            rw [← Finset.sum_sub_distrib]
        _ = ∑ t ∈ Finset.range T, -((ε / 8) * (3 + ε + P.a (j t))) :=
            Finset.sum_congr rfl (fun t _ => hterm t)
        _ = -((ε / 8) * (∑ t ∈ Finset.range T, (3 + ε + P.a (j t)))) := by
            rw [Finset.mul_sum, Finset.sum_neg_distrib]
    linarith
  -- (A.8): `T (2 + ε) < 32 ln D / ε²`.
  have hsum_ge : (T : ℝ) * (2 + ε) ≤ ∑ t ∈ Finset.range T, (3 + ε + P.a (j t)) := by
    calc (T : ℝ) * (2 + ε) = ∑ _t ∈ Finset.range T, (2 + ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range T, (3 + ε + P.a (j t)) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          have := hage t (Finset.mem_range.mp ht)
          linarith
  have hTgt : (T : ℝ) * (2 + ε) < 32 * Real.log D / ε ^ 2 := by
    have hpos8 : 0 < ε / 8 := by positivity
    have h := mul_le_mul_of_nonneg_left hsum_ge hpos8.le
    -- `h : (ε/8) * (T * (2+ε)) < (ε/8) * Σ ...`
    have h' : (ε / 8) * (∑ t ∈ Finset.range T, (3 + ε + P.a (j t))) <
        4 * Real.log D / ε := hA7
    have hεne : ε ≠ 0 := ne_of_gt hε0
    have : (ε / 8) * ((T : ℝ) * (2 + ε)) < 4 * Real.log D / ε := lt_of_le_of_lt h h'
    field_simp [hεne] at this ⊢
    nlinarith [this]
  -- But `T ≥ 16 ln D / ε²` gives the opposite inequality.
  have hTge : 32 * Real.log D / ε ^ 2 ≤ (T : ℝ) * (2 + ε) := by
    have h2T : 32 * Real.log D / ε ^ 2 ≤ 2 * (T : ℝ) := by
      have h' := mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 2)
      convert h' using 1 <;> ring
    nlinarith [h2T, hε0, hT0R]
  linarith

/-- The stated query bound of Theorem 3: the horizon `⌈16 ln D / ε²⌉` is at most
`16 ln D / ε² + 1`, matching "at most `16 ln n / ε²` queries" up to the usual ceiling
convention (App. A, p. 16). -/
theorem master_algorithm_query_bound (D : ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    ((Nat.ceil (16 * Real.log D / ε ^ 2) : ℕ) : ℝ) < 16 * Real.log D / ε ^ 2 + 1 := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 16 * Real.log D / ε ^ 2 by positivity)
  simpa using h

end Qatlib.Papers.QSDPSolvers17.MainResults.MasterAlgorithm
