/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticNP01.MainResults.SourceGroundState
import Qatlib.Papers.AdiabaticNP01.MainResults.SourceRepetition

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabaticNP01 — minimising violated clauses at the quadratic runtime (Claim `c002`)

Source: E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, D. Preda,
arXiv:quant-ph/0104129v1 (2001), §11 "Instances with the number of clauses fixed
in advance", pp. 9–10, and Figure 5.

Claim `c002`: *"The quantum adiabatic algorithm is designed to find the ground
state of `H_P`, which corresponds to the minimum of the classical energy cost
`h`, whether the instance has satisfying assignments or not.  The data in Figures
4 and 5 show that the algorithm does at least as well on the general problem of
minimizing the number of unsatisfied clauses as it does on finding a usa."*

The model-level content is proved in `SourceGroundState.lean` (ground state of the
diagonal `H_P` is supported on minimum-violation assignments, and measuring it
outputs such an assignment with probability one).  This file adds the semantic
comparison with the USA problem and the §11/§10 runtime statement:

* `isMinViolation_iff_satisfying_of_min_zero`: on a satisfiable instance the
  minimum-violation assignments are exactly the satisfying assignments; so the
  general minimisation problem contains the original USA problem;
* `worst_case_repetition_200`: the Figure 5 worst-case bound `p ≥ 0.04` at the
  quadratic runtime `T(16)`, `T(17)` combined with the §10 repetition argument
  gives confidence `> 0.9997` after 200 repetitions, for any such `p`;
* `minimum_violation_success_at_quadratic_runtime`: for the 16- and 17-bit
  no-satisfying-assignment families with median success probability above `1/8`
  and worst case at least `0.04` (Figure 5), a repetition count independent of the
  clause count and of `n` reaches any target confidence.

No `sorry`, no `admit`, no additional axioms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticNP01.MainResults

variable {n : ℕ}

/-- On a satisfiable instance (`minViolation = 0`) the minimum-violation
assignments are exactly the satisfying assignments.  Hence the general
minimisation problem of §11 (p. 9) contains the original USA problem. -/
theorem isMinViolation_iff_satisfying_of_min_zero (I : ExactCoverInstance n)
    (hmin : I.minViolation = 0) (z : Bitstring n) :
    I.IsMinViolation z ↔ ∀ C ∈ I.clauses, exactlyOneTrue z C := by
  constructor
  · intro h
    exact satisfies_of_minViolation_eq_zero I hmin z h
  · intro hsat
    unfold ExactCoverInstance.IsMinViolation
    rw [(violationCount_eq_zero_iff I z).mpr hsat, hmin]

/-- Figure 5 (§11, p. 10): the worst-case success probability at the quadratic
runtime is never below `0.04`.  Therefore, for any per-run success probability
`p ≥ 0.04` (and `p ≤ 1`), 200 repetitions — the paper's worked example of §10,
p. 8 — already give confidence strictly better than `0.9997`. -/
theorem worst_case_repetition_200 (p : ℝ) (hp : 0.04 ≤ p) (hp1 : p ≤ 1) :
    (0.9997 : ℝ) < repetitionSuccessProbability p 200 := by
  have hfail : failureProbability p 200 ≤ failureProbability (0.04 : ℝ) 200 :=
    failureProbability_anti (by norm_num) hp hp1 200
  have hnum := two_hundred_repetitions_numeric
  unfold repetitionSuccessProbability at hnum ⊢
  linarith

/-- **Claim `c002` — minimum-violation success at the quadratic runtime.**  On the
16- and 17-bit families without satisfying assignments, the paper reports a median
success probability above `1/8` and a worst case at least `0.04` at `T(n)`
(Figure 5, §11 p. 10).  For any procedure whose success probability at `T(n)`
satisfies those bounds, a fixed number of repetitions — independent of the number
of clauses and of `n` — achieves any target confidence `1 − ε`. -/
theorem minimum_violation_success_at_quadratic_runtime
    (p : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hworst : ∀ n ∈ ({16, 17} : Finset ℕ), (0.04 : ℝ) ≤ p n)
    (hp_hi : ∀ n ∈ ({16, 17} : Finset ℕ), p n ≤ 1) :
    ∃ k : ℕ, ∀ n ∈ ({16, 17} : Finset ℕ),
      1 - ε ≤ repetitionSuccessProbability (p n) k := by
  obtain ⟨k, hk⟩ := exists_repetitions_meeting_target
    (p := 0.04) (by norm_num) (by norm_num) hε
  refine ⟨k, ?_⟩
  intro n hn
  have hlo := hworst n hn
  have hhi := hp_hi n hn
  have hfail : failureProbability (p n) k ≤ failureProbability (0.04 : ℝ) k :=
    failureProbability_anti (by linarith) hlo hhi k
  unfold repetitionSuccessProbability
  linarith [hk, hfail]

end Qatlib.Papers.AdiabaticNP01.MainResults
