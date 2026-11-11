/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SpectralTrace — the filter/trace lemmas of BettiNumber25 (Lemmas 4.1 and 5.1)

Akhalwaya–Bhayat–Connolly–Herbert–Horesh–Sorci–Ubaru,
*Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes*, fixed arXiv:2408.16934v3
(Quantum 9, 1901, 2025), PDF SHA-256
`dcf534a47e98fb6bb6bc34039e64bac6e7ba07fdb7d9b17f781dae1a01fe7848`.

* Source Lemma 4.1 (p. 9): if `p` is a real polynomial with `p(0) = 1` and
  `|p(x)| < ε` on `[δ,1]`, and `δ` is the smallest positive eigenvalue of the
  normalised Laplacian `Δ̃_k`, then
  `|tr p(Δ̃_k)/|S_k| − β_k/|S_k|| < ε`.
* Source Lemma 5.1 (p. 13): if `d ≥ log(1/ε)/δ` then
  `β_k ≤ tr(H^d) ≤ β_k + ε|S_k|`, where `H = I − Δ̃_k`.

Both are stated for the eigenvalue list of the matrix (`λ : Fin N → ℝ`), which is
exactly the form in which the paper's proofs use them ("the trace of a
diagonalisable matrix is the sum of its eigenvalues", eq. (12)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.SpectralTrace

/-- **Auxiliary trace comparison.**  For a function `f` of the eigenvalues with
`f z = 1` on the kernel and `|f| < ε` away from the kernel, the normalised trace
of `f` is within `ε` of the normalised kernel dimension. -/
theorem filter_trace_close {N : ℕ} (f : ℝ → ℝ) (ε z : ℝ) (hε : 0 < ε)
    (hz : f z = 1) (μ : Fin N → ℝ) (h : ∀ i, μ i ≠ z → |f (μ i)| < ε) :
    |(∑ i, f (μ i)) / (N : ℝ)
      - ((Finset.univ.filter (fun i => μ i = z)).card : ℝ) / (N : ℝ)| < ε := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simpa using hε
  set S := Finset.univ.filter (fun i => μ i = z) with hS
  set T := Finset.univ.filter (fun i => μ i ≠ z) with hT
  have hsplit : ∑ i, f (μ i) = S.sum (fun i => f (μ i)) + T.sum (fun i => f (μ i)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => μ i = z) (f := fun i => f (μ i)), ← hS, ← hT]
  have hSval : S.sum (fun i => f (μ i)) = (S.card : ℝ) := by
    have h1 : ∀ i ∈ S, f (μ i) = 1 := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2, hz]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hTcard : T.card ≤ N := by
    rw [hT]
    simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => μ i ≠ z)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have key : |∑ i, f (μ i) - (S.card : ℝ)| < (N : ℝ) * ε := by
    rw [hsplit, hSval]
    have e : (S.card : ℝ) + T.sum (fun i => f (μ i)) - (S.card : ℝ)
        = T.sum (fun i => f (μ i)) := by ring
    rw [e]
    rcases Nat.eq_zero_or_pos T.card with hT0 | hTpos
    · have hTempty : T = ∅ := Finset.card_eq_zero.mp hT0
      rw [hTempty]
      simp only [Finset.sum_empty, abs_zero]
      positivity
    · have hne : T.Nonempty := Finset.card_pos.mp hTpos
      calc |T.sum (fun i => f (μ i))| ≤ T.sum (fun i => |f (μ i)|) :=
            Finset.abs_sum_le_sum_abs _ _
        _ < T.sum (fun _ => ε) :=
            Finset.sum_lt_sum_of_nonempty hne
              (fun i hi => h i (Finset.mem_filter.mp hi).2)
        _ = (T.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * ε := by
            have hc : (T.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTcard
            nlinarith [hε]
  have hdiv : |(∑ i, f (μ i)) / (N : ℝ) - (S.card : ℝ) / (N : ℝ)|
      = |∑ i, f (μ i) - (S.card : ℝ)| / (N : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
  rw [hdiv]
  rw [div_lt_iff₀ hNpos]
  linarith [key]

/-- **Source Lemma 4.1** (eq. (4), p. 9).  If `p(0) = 1` and `|p(x)| < ε` on
`[δ,1]`, and every nonzero eigenvalue `λ i` of the normalised Laplacian lies in
`[δ,1]`, then the normalised trace of `p(Δ̃_k)` differs from the normalised Betti
number `β/|S_k|` by less than `ε`. -/
theorem lemma_4_1_filter_trace {N : ℕ} (p : Polynomial ℝ) (ε δ : ℝ) (hε : 0 < ε)
    (hp0 : p.eval 0 = 1)
    (hp : ∀ x ∈ Set.Icc δ 1, |p.eval x| < ε)
    (lam : Fin N → ℝ) (hspec : ∀ i, lam i ≠ 0 → lam i ∈ Set.Icc δ 1) :
    |(∑ i, p.eval (lam i)) / (N : ℝ)
      - ((Finset.univ.filter (fun i => lam i = 0)).card : ℝ) / (N : ℝ)| < ε := by
  refine filter_trace_close (fun x => p.eval x) ε 0 hε hp0 lam ?_
  intro i hi
  exact hp (lam i) (hspec i hi)

/-- From `d ≥ log(1/ε)/δ` with `0 < δ ≤ 1` we get `(1 − δ)^d ≤ ε`.  This is the
elementary step in the proof of source Lemma 5.1 ("choosing `d ≥ log(1/ε)/δ`
ensures that `(1−δ)^d ≤ ε`"). -/
theorem one_sub_pow_le_of_log_le (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (d : ℕ) (hd : Real.log (1 / ε) / δ ≤ (d : ℝ)) : (1 - δ) ^ d ≤ ε := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    simp only [pow_zero]
    have hlog : Real.log (1 / ε) ≤ 0 := by
      have h := mul_le_mul_of_nonneg_right hd (le_of_lt hδ0)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ0)] at h
      simpa using h
    have hε1 : 1 ≤ ε := by
      rw [Real.log_nonpos_iff (by positivity)] at hlog
      have : 1 / ε ≤ 1 := hlog
      rw [div_le_one (by positivity)] at this
      linarith
    exact hε1
  · rcases lt_or_eq_of_le hδ1 with hδlt | hδeq
    · have hpos : 0 < 1 - δ := by linarith
      have hlog : Real.log (1 - δ) ≤ -δ := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      have hdδ : Real.log (1 / ε) ≤ (d : ℝ) * δ := by
        have h := mul_le_mul_of_nonneg_right hd (le_of_lt hδ0)
        rwa [div_mul_cancel₀ _ (ne_of_gt hδ0)] at h
      have hexp : (d : ℝ) * Real.log (1 - δ) ≤ -Real.log (1 / ε) := by
        have h1 : (d : ℝ) * Real.log (1 - δ) ≤ (d : ℝ) * (-δ) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)
        nlinarith
      calc (1 - δ) ^ d = Real.exp ((d : ℝ) * Real.log (1 - δ)) := by
            rw [← Real.exp_log (pow_pos hpos d), Real.log_pow]
        _ ≤ Real.exp (-Real.log (1 / ε)) := Real.exp_le_exp.mpr hexp
        _ = ε := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]
            rw [one_div, inv_inv]
    · subst hδeq
      rw [show (1 - 1 : ℝ) = 0 by norm_num, zero_pow (Nat.ne_of_gt hdpos)]
      exact le_of_lt hε

/-- **Source Lemma 5.1** (eq. (11), p. 13).  `H = I − Δ̃_k` has eigenvalues
`ν i ∈ [0,1]`, equal to `1` exactly on the kernel and at most `1 − δ` on the
positive spectrum.  For `d ≥ log(1/ε)/δ` the normalised power trace is squeezed
between the normalised Betti number and that number plus `ε`. -/
theorem lemma_5_1_power_trace {N : ℕ} (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (d : ℕ) (hd : Real.log (1 / ε) / δ ≤ (d : ℝ))
    (ν : Fin N → ℝ) (hν0 : ∀ i, 0 ≤ ν i) (hν1 : ∀ i, ν i ≤ 1)
    (hνgap : ∀ i, ν i ≠ 1 → ν i ≤ 1 - δ) :
    (((Finset.univ.filter (fun i => ν i = 1)).card : ℝ) ≤ ∑ i, (ν i) ^ d) ∧
    (∑ i, (ν i) ^ d
      ≤ ((Finset.univ.filter (fun i => ν i = 1)).card : ℝ) + ε * (N : ℝ)) := by
  classical
  set S := Finset.univ.filter (fun i => ν i = 1) with hS
  set T := Finset.univ.filter (fun i => ν i ≠ 1) with hT
  have hεd : (1 - δ) ^ d ≤ ε := one_sub_pow_le_of_log_le δ ε hδ0 hδ1 hε d hd
  have hsplit : ∑ i, (ν i) ^ d = S.sum (fun i => (ν i) ^ d) + T.sum (fun i => (ν i) ^ d) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => ν i = 1) (f := fun i => (ν i) ^ d), ← hS, ← hT]
  have hSval : S.sum (fun i => (ν i) ^ d) = (S.card : ℝ) := by
    have h1 : ∀ i ∈ S, (ν i) ^ d = 1 := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2, one_pow]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hnonneg : ∀ i, 0 ≤ (ν i) ^ d := fun i => pow_nonneg (hν0 i) d
  constructor
  · calc (S.card : ℝ) = S.sum (fun i => (ν i) ^ d) := hSval.symm
      _ ≤ ∑ i, (ν i) ^ d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _
          exact hnonneg i
  · have hTbound : T.sum (fun i => (ν i) ^ d) ≤ (N : ℝ) * ε := by
      have hterm : ∀ i ∈ T, (ν i) ^ d ≤ ε := by
        intro i hi
        have hne : ν i ≠ 1 := (Finset.mem_filter.mp hi).2
        have hle : ν i ≤ 1 - δ := hνgap i hne
        have : (ν i) ^ d ≤ (1 - δ) ^ d := pow_le_pow_left₀ (hν0 i) hle d
        exact this.trans hεd
      calc T.sum (fun i => (ν i) ^ d) ≤ T.sum (fun _ => ε) := Finset.sum_le_sum hterm
        _ = (T.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * ε := by
            have hc : T.card ≤ N := by
              rw [hT]
              simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
                (p := fun i => ν i ≠ 1)
            have hc' : (T.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hc
            nlinarith [hε]
    rw [hsplit, hSval]
    nlinarith [hTbound]

end Qatlib.Papers.BettiNumber25.MainResults.SpectralTrace
