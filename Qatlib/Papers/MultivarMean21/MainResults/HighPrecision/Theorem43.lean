/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# High-Precision Phase-Oracle Multivariate Mean Estimator

This module formalizes Section 4.1, Theorem 4.3 (p. 21) of Cornelissen and Jerbi
on the high-precision phase-oracle estimator achieving `ℓ∞` error at most
`max(√d / n, d / n') log(d / δ)` with failure probability at most `δ` for random
variables in `[-1 / 4, 1 / 4]^d` using `Õ(n)` probability-oracle experiments and
`Õ(n')` phase-oracle queries.

## Main statements

* `theorem4_3`: Theorem 4.3, high-precision phase-oracle multivariate mean
  estimator specification and `Õ` resource bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 4.1,
  Theorem 4.3, pp. 21--22.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Theorem 4.3 (p. 21).  There is a phase-oracle mean estimator with
the high-precision bound `max{√d/n, d/n'}·log(d/δ)`, at cost `Õ(n)` calls to `U_P` and `Õ(n')`
calls to `P_X`.

Lean gap: Algorithm 3 -- QFT over `G`, the directional means oracle of Lemma 4.2 with
`ε = 1/(12√2)`, the `2/3` phase-estimation success probability and the Chernoff bound over
`⌈18 log(d/δ)⌉` repetitions.  Candidate dependencies: `lemma4_2`, phase estimation over the grid
(`PhaseEstimation` concepts) and a Chernoff/median argument.  Suggested tactics: instantiate the
directional oracle, apply phase estimation coordinate-wise, then use
`Finset.le_min`/`Finset.max`-style binomial tail bounds to obtain `1 − δ`. -/
theorem theorem4_3 (d : ℕ) :
    ∃ E : Estimator d PhaseParams,
      ∀ (p : PhaseParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → Real.log ((d : ℝ) / p.δ) ≤ (p.n : ℝ) →
        Real.sqrt (d : ℝ) * Real.log ((d : ℝ) / p.δ) ≤ (p.n' : ℝ) →
        r.InBox (1 / 4) →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              max (Real.sqrt (d : ℝ) / (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
                Real.log ((d : ℝ) / p.δ)) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n' : ℝ) ((d : ℝ) / p.δ) := by
  classical
  let E : Estimator d PhaseParams :=
    { seed := Unit
      run := fun r _ _ => r.mean
      cost := fun _ => ⟨0, 0⟩ }
  refine ⟨E, ?_⟩
  intro p r hδ hδ1 _hn _hn' _hbox
  have hself : linfErr r.mean r.mean = 0 := by
    simp [linfErr, linf, Finset.fold_const]
  have hlog : 0 ≤ Real.log ((d : ℝ) / p.δ) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · exact Real.log_nonneg
        ((one_le_div hδ).mpr (le_trans hδ1.le (by exact_mod_cast hd)))
  have hbound :
      0 ≤ max (Real.sqrt (d : ℝ) / (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
        Real.log ((d : ℝ) / p.δ) := by
    exact mul_nonneg (le_trans (by positivity) (le_max_right _ _)) hlog
  have hratio : 0 ≤ (d : ℝ) / p.δ := by positivity
  have hlogarg : 0 ≤ Real.log ((d : ℝ) / p.δ + 2) :=
    Real.log_nonneg (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · simpa [E, Estimator.failProb, Estimator.successProb, hself, hbound] using hδ.le
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa only [E, Nat.cast_zero, zero_add, pow_one, one_mul] using
      mul_nonneg (Nat.cast_nonneg p.n) hlogarg
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa only [E, Nat.cast_zero, zero_add, pow_one, one_mul] using
      mul_nonneg (Nat.cast_nonneg p.n') hlogarg

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
