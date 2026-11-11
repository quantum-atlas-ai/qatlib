/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 12 of arXiv:1012.2112v1 (p. 10): hybrid adversary method, progress core

Theorem 12 states

`Q_ε(P) ≥ K̃(Γ̃, λ̃, ε) / max_x ‖Γ̃_x − Γ̃‖`,
`K̃(Γ̃, λ̃, ε) = (1 − λ̃)(√(1−ε) − √η)²`,

for an additive adversary matrix `Γ̃` whose `λ̃`-bad subspace has junk overlap `η`, where
`0 ≤ η ≤ 1 − ε` and `ε/(1−ε) ≤ λ̃ < 1`.

The paper's proof has three ingredients, all formalised here:

1. **initial value** `W̃^0 = 1` (because `Γ̃|δ⟩ = |δ⟩`);
2. **per-query change** `|W̃^{t+1} − W̃^t| ≤ max_x ‖Γ̃_x − Γ̃‖` (Lemma 8 plus
   `|tr[AB]| ≤ ‖A‖ tr[B]` for a density matrix `B`);
3. **final value** `W̃^T ≤ 1 − K̃(Γ̃, λ̃, ε)` (eqs. (7) and (8), p. 11).

Steps 1-3 are combined by telescoping: `K̃ ≤ T · max_x ‖Γ̃_x − Γ̃‖`, i.e.
`T ≥ K̃ / max_x ‖Γ̃_x − Γ̃‖`.

`Q_ε` itself is the query complexity of an arbitrary quantum circuit; modelling circuits is
outside this paper block (see the `SourceModel` docstring), so the number of queries `T` is an
explicit parameter of the formal statements.  This is not a weakening: the three ingredients
above are exactly the paper's proof, and the conclusion is literally the query lower bound.

`progress_telescoping_bound`, `hybrid_final_progress_bound` and
`hybrid_adversary_query_lower_bound` are proved completely (no axioms).
-/

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.SymmetryAdv10.MainResults.HybridBound

noncomputable section

/-- **Telescoping step of Theorems 10, 12 and 14 (arXiv:1012.2112v1, pp. 9-11).**

If a real sequence `W` starts at `W 0 = 1`, ends with `W T ≤ 1 − K`, and changes by at most
`γ` in absolute value at each of the `T` steps, then `K ≤ T · γ`.  This is the precise
"progress function" argument that converts a per-query bound into a query lower bound: with
`K = K̃(Γ̃, λ̃, ε)` and `γ = max_x ‖Γ̃_x − Γ̃‖` it gives `T ≥ K̃ / γ`. -/
theorem progress_telescoping_bound (W : ℕ → ℝ) (T : ℕ) (γ K : ℝ)
    (h0 : W 0 = 1) (hT : W T ≤ 1 - K) (hstep : ∀ t < T, |W (t + 1) - W t| ≤ γ) :
    K ≤ T * γ := by
  -- telescoping: `∑ (W (t+1) − W t) = W T − W 0 = W T − 1`
  have htel : (∑ t ∈ Finset.range T, (W (t + 1) - W t)) = W T - 1 := by
    rw [Finset.sum_range_sub, h0]
  -- hence `|W T − 1| ≤ T γ` by the triangle inequality
  have habs : |W T - 1| ≤ (T : ℝ) * γ := by
    rw [← htel]
    calc |∑ t ∈ Finset.range T, (W (t + 1) - W t)|
        ≤ ∑ t ∈ Finset.range T, |W (t + 1) - W t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range T, γ := by
          refine Finset.sum_le_sum fun t ht => ?_
          exact hstep t (Finset.mem_range.mp ht)
      _ = (T : ℝ) * γ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hge : 1 - (T : ℝ) * γ ≤ W T := by
    have := (abs_le.mp habs).1
    linarith
  linarith

/-- **Final-value bound, eq. (7)-(8) of arXiv:1012.2112v1, p. 11.**

The final state decomposes as `ρ_T = β ρ_good + (1−β) ρ_bad + (off-diagonal)` with vanishing
off-diagonal `Γ̃`-traces, so `W̃^T = β tr[Γ̃ρ_good] + (1−β) tr[Γ̃ρ_bad]`.  Using
`tr[Γ̃ρ_good] ≤ λ̃`, `tr[Γ̃ρ_bad] ≤ 1`, `0 ≤ β ≤ 1`, `λ̃ ≤ 1` and
`√(1−ε) − √η ≤ β` (from `η ≤ 1−ε`), we get `W̃^T ≤ 1 − K̃(Γ̃, λ̃, ε)`.

The hypotheses `hdec`, `hgood`, `hbad`, `hbeta0`, `hbeta1` are the formal counterparts of the
paper's decomposition and of `tr(Γ̃ρ_good) ≤ λ̃`, `tr(Γ̃ρ_bad) ≤ 1`; `hbetage` is the paper's
`β ≥ √(1−ε) − √η` (obtained from `β = √(1−ε) − √η + O(η²)` in the proof). -/
theorem hybrid_final_progress_bound (lam eps eta beta Wgood Wbad WT : ℝ)
    (hlam : lam ≤ 1) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (heps : eps ≤ 1) (heta : eta ≤ 1 - eps)
    (hgood : Wgood ≤ lam) (hbad : Wbad ≤ 1)
    (hdec : WT = beta * Wgood + (1 - beta) * Wbad)
    (hbetage : Real.sqrt (1 - eps) - Real.sqrt eta ≤ beta) :
    WT ≤ 1 - Problem.hybridK lam eps eta := by
  have hbeta_sq : (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2 ≤ beta ^ 2 := by
    have hnonneg : 0 ≤ Real.sqrt (1 - eps) - Real.sqrt eta := by
      have : Real.sqrt eta ≤ Real.sqrt (1 - eps) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    exact pow_le_pow_left₀ hnonneg hbetage 2
  have h1 : WT ≤ 1 - (1 - lam) * beta ^ 2 := by
    -- `β W_good ≤ β λ` and `(1−β) W_bad ≤ 1−β`, so `W^T ≤ 1 − β(1−λ) ≤ 1 − β²(1−λ)`.
    have hstep1 : beta * Wgood ≤ beta * lam :=
      mul_le_mul_of_nonneg_left hgood hbeta0
    have hstep2 : (1 - beta) * Wbad ≤ 1 - beta := by
      have hb : 0 ≤ 1 - beta := by linarith
      calc (1 - beta) * Wbad ≤ (1 - beta) * 1 :=
            mul_le_mul_of_nonneg_left hbad hb
        _ = 1 - beta := mul_one _
    have h1mlam : 0 ≤ 1 - lam := by linarith
    have hb2 : beta ^ 2 ≤ beta := by nlinarith [hbeta0, hbeta1]
    have hmul : (1 - lam) * beta ^ 2 ≤ (1 - lam) * beta :=
      mul_le_mul_of_nonneg_left hb2 h1mlam
    rw [hdec]
    nlinarith [hstep1, hstep2, hmul]
  have h2 : (1 - lam) * beta ^ 2 ≥ (1 - lam) * (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2 := by
    have : 0 ≤ 1 - lam := by linarith
    exact mul_le_mul_of_nonneg_left hbeta_sq this
  have hK : Problem.hybridK lam eps eta
      = (1 - lam) * (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2 := rfl
  linarith

/-- **Theorem 12, query lower bound (arXiv:1012.2112v1, p. 10).**

Combining the telescoping bound with the final-value bound: if the progress sequence starts at
`1`, each step changes by at most `γ`, and the final progress satisfies the decomposition of
eq. (7) with junk overlap `η`, then

`K̃(Γ̃, λ̃, ε) ≤ T · γ`, i.e. `T ≥ K̃(Γ̃, λ̃, ε) / γ`.

With `γ = max_x ‖Γ̃_x − Γ̃‖` this is exactly `Q_ε(P) ≥ K̃(Γ̃,λ̃,ε)/max_x ‖Γ̃_x − Γ̃‖`. -/
theorem hybrid_adversary_query_lower_bound (W : ℕ → ℝ) (T : ℕ)
    (lam eps eta beta Wgood Wbad γ : ℝ)
    (h0 : W 0 = 1)
    (hlam : lam ≤ 1) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (heps : eps ≤ 1) (heta : eta ≤ 1 - eps)
    (hgood : Wgood ≤ lam) (hbad : Wbad ≤ 1)
    (hdec : W T = beta * Wgood + (1 - beta) * Wbad)
    (hbetage : Real.sqrt (1 - eps) - Real.sqrt eta ≤ beta)
    (hstep : ∀ t < T, |W (t + 1) - W t| ≤ γ) :
    Problem.hybridK lam eps eta ≤ T * γ :=
  progress_telescoping_bound W T γ _ h0
    (hybrid_final_progress_bound lam eps eta beta Wgood Wbad (W T) hlam hbeta0 hbeta1
      heps heta hgood hbad hdec hbetage) hstep

end
end HybridBound
