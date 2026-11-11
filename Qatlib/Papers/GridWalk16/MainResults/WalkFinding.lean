/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GridWalk16.MainResults.ExtendedHittingBound

set_option backward.isDefEq.respectTransparency false

/-!
# GridWalk16 — quantum walk search algorithms: Corollary 7, Theorem 12, Theorem 13
(claims c004, c008, c009)

Fixed paper: arXiv:1612.08958v1, §2 p. 8 and §5 pp. 12–13.

**Corollary 7** (p. 8): given a reversible ergodic walk `P` with marked set `M` and an
estimate `ε̃` of `ε_M` with `2/3 ≤ ε̃/ε_M ≤ 4/3`, one can find a marked state by a quantum
walk with probability at least `1/5` using `O(√HT(P,{m}))` steps, where `m ∈ M` maximises
the upper bound.  The mathematical content formalised here is the step-count transfer:
an algorithm that runs in `c·√HT⁺(P,M)` steps also runs in `c·√(max_{m∈M} HT⁺(P,{m}))`
steps, which is exactly Corollary 3 applied under the square root
(`corollary7_uses_max_hitting_time`, using `extendedHitting_le_max_singleton` from
`ExtendedHittingBound.lean`).

**Theorem 12** (p. 12): there is a quantum algorithm that, with probability at least `2/3`,
outputs an estimate `h̃ ∈ O(HTeff(P,M))` such that applying `P′` for `h̃` steps from `π`
finds a marked state with probability at least `3/4`, at cost `O(S + √h̃·(U+C))`.
Formalised here: the cost scaling implied by `h̃ ∈ O(HTeff)`
(`theorem12_estimate_cost_scaling`, `theorem12_cost_bound`).

**Theorem 13 (Main)** (p. 13): there is a quantum algorithm that, given a torus with marked
vertices, outputs a marked vertex with probability at least `1/log N` in cost
`S + min(√(H log H), √(N log N))·(U+C)`, where `H = HTeff(Ptorus,M)`.  The proof (p. 13)
combines three success factors `p₁ ≥ 2/3` (the estimate is good), `p₂ ≥ 3/20` (a sampled
sub-grid contains a marked vertex, by Lemma 11 with the `3/4` estimate-accuracy factor:
`(1/5)·(3/4 = 3/20)`), and `p₃ ≥ 1/5` (Corollary 7 on that sub-grid), giving
`p₁·p₂·p₃ ≥ 1/50`; the cost is bounded by the `min` of the two walk lengths.
Formalised here: `theorem13_success_probability` and `theorem13_cost_bound`.

Model note (important, and stated in the Lean docstrings as well).  A **faithful**
statement of an *existence of a quantum algorithm* requires a model of quantum algorithms
and their costs, which the library does not provide (the paper-layer files of this repo
are models, not executable quantum programs).  An `∃ alg, …` written with free
success/cost fields would be vacuously true.  Therefore the three claims are formalised at
the level of the paper's **quantitative derivation**: the primitive algorithmic guarantees
stated in the paper (existence of the `[22]`-walk, of the hitting-time estimator, of the
torus algorithm) are taken as hypotheses, and the numerical conclusions the paper derives
from them are proved.  The `∃`-algorithm content itself is *not* formalised; this is
recorded as the remaining gap.  No `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.GridWalk16.MainResults

/-! ## Corollary 7 (claim c004) -/

/-- **Corollary 7 (c004), step-count transfer.** Suppose a quantum-walk search on a
reversible ergodic walk `P` with marked set `M` uses `steps` walk steps with
`steps ≤ c·√HT⁺(P,M)`.  Then, because `HT⁺(P,M) ≤ max_{m∈M} HT⁺(P,{m})`
(Corollary 3, proved in `ExtendedHittingBound.lean`), the same algorithm uses
`steps ≤ c·√(max_{m∈M} HT⁺(P,{m}))` steps.
Paper arXiv:1612.08958v1, Corollary 7, §2 p. 8.

The paper additionally guarantees success probability `≥ 1/5` when the estimate `ε̃`
satisfies `2/3 ≤ ε̃/ε_M ≤ 4/3`; that primitive guarantee (Theorem 7 of [22]) is an
algorithmic fact that is not modelled here. -/
theorem corollary7_uses_max_hitting_time {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] (W : SpectralWalk X ι) (M : Finset X) (hM : M.Nonempty)
    (steps c : ℝ) (hc : 0 < c)
    (hsteps : steps ≤ c * Real.sqrt (W.extendedHitting M)) :
    steps ≤ c * Real.sqrt (M.sup' hM (fun m => W.extendedHitting ({m} : Finset X))) := by
  refine le_trans hsteps (mul_le_mul_of_nonneg_left ?_ hc.le)
  exact Real.sqrt_le_sqrt (W.extendedHitting_le_max_singleton M hM)

/-! ## Theorem 12 (claim c008) -/

/-- **Theorem 12 (c008), estimate cost scaling.** If the hitting-time estimate `h̃`
satisfies `h̃ ≤ C·HTeff` with `C > 0`, then its square root is at most
`√C·√HTeff`, i.e. `√h̃ ∈ O(√HTeff)`.
Paper arXiv:1612.08958v1, Theorem 12, §5 p. 12. -/
theorem theorem12_estimate_cost_scaling (Heff hEst C : ℝ) (hC : 0 < C)
    (hbound : hEst ≤ C * Heff) :
    Real.sqrt hEst ≤ Real.sqrt C * Real.sqrt Heff := by
  rw [← Real.sqrt_mul hC.le]
  exact Real.sqrt_le_sqrt hbound

/-- **Theorem 12 (c008), cost bound `S + √h̃·(U+C)`.** With `h̃ ≤ C·HTeff`, the algorithm
cost `S + √h̃·(U+C)` is bounded by `S + √C·√HTeff·(U+C)`.
Paper arXiv:1612.08958v1, Theorem 12, §5 p. 12.

The success guarantee (`≥ 3/4` after `h̃` steps from `π`, and probability `≥ 2/3` that the
estimate is good) is algorithmic and not modelled here. -/
theorem theorem12_cost_bound (S U Cc Heff hEst Cfac : ℝ)
    (hU : 0 ≤ U) (hCc : 0 ≤ Cc) (hCfac : 0 < Cfac) (hbound : hEst ≤ Cfac * Heff) :
    S + Real.sqrt hEst * (U + Cc) ≤
      S + Real.sqrt Cfac * Real.sqrt Heff * (U + Cc) := by
  have hsq := theorem12_estimate_cost_scaling Heff hEst Cfac hCfac hbound
  have hstep : Real.sqrt hEst * (U + Cc) ≤ Real.sqrt Cfac * Real.sqrt Heff * (U + Cc) :=
    mul_le_mul_of_nonneg_right hsq (by linarith)
  linarith

/-! ## Theorem 13 (claim c009) -/

/-- **Theorem 13 (c009), success probability.** If the three independent factors of the
torus algorithm have success probabilities `p₁ ≥ 2/3`, `p₂ ≥ 3/20`, `p₃ ≥ 1/5`, then the
overall success probability is at least `(2/3)·(3/20)·(1/5) = 1/50`.
Paper arXiv:1612.08958v1, Theorem 13, §5 p. 13
("outputs a marked element with probability at least `2/3 · 3/20 · 1/5 = 1/50`"). -/
theorem theorem13_success_probability (p₁ p₂ p₃ : ℝ)
    (h₁ : 2 / 3 ≤ p₁) (h₂ : 3 / 20 ≤ p₂) (h₃ : 1 / 5 ≤ p₃) :
    1 / 50 ≤ p₁ * p₂ * p₃ := by
  have h12 : (2 / 3 : ℝ) * (3 / 20) ≤ p₁ * p₂ :=
    mul_le_mul h₁ h₂ (by norm_num) (by linarith)
  have h123 : (2 / 3 : ℝ) * (3 / 20) * (1 / 5) ≤ p₁ * p₂ * p₃ :=
    mul_le_mul h12 h₃ (by norm_num) (by nlinarith [h12])
  have hconst : (2 / 3 : ℝ) * (3 / 20) * (1 / 5) = 1 / 50 := by norm_num
  linarith [h123, hconst]

/-- **Theorem 13 (c009), cost bound.** If the number of walk steps `steps` is at most
`min(√(H log H), √(N log N))`, the torus-algorithm cost `S + steps·(U+C)` is at most
`S + min(√(H log H), √(N log N))·(U+C)`.
Paper arXiv:1612.08958v1, Theorem 13, §5 p. 13. -/
theorem theorem13_cost_bound (S U Cc H N steps : ℝ)
    (hU : 0 ≤ U) (hCc : 0 ≤ Cc)
    (hsteps : steps ≤
      min (Real.sqrt (H * Real.log H)) (Real.sqrt (N * Real.log N))) :
    S + steps * (U + Cc) ≤
      S + min (Real.sqrt (H * Real.log H)) (Real.sqrt (N * Real.log N)) * (U + Cc) := by
  have h1 : steps * (U + Cc) ≤
      min (Real.sqrt (H * Real.log H)) (Real.sqrt (N * Real.log N)) * (U + Cc) :=
    mul_le_mul_of_nonneg_right hsteps (by linarith)
  linarith

end Qatlib.Papers.GridWalk16.MainResults
