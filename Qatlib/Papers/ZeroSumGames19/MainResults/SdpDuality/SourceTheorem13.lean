/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel

set_option backward.isDefEq.respectTransparency false


/-!
# ZeroSumGames19 — Theorem 13 (quantum LP solvers from the game reduction)

Fixed source: arXiv:1904.03180v1, Theorem 13, p.15.

Paper statement: given quantum query access to an LP of the form (4), an
`ε`-optimal and `ε`-feasible `y` can be found with probability `1−δ` using either

* `Õ((√n+√m)(R(r+1)/ε)³)` quantum queries to a dense matrix oracle and the same
  number of other gates, or
* `Õ(√s (R(r+1)/ε)^{3.5})` quantum queries to a sparse matrix oracle and the same
  number of other gates.

Proof (p.15): Lemma 12 (tolerance `ε''' = ε/(6R(r+1))`) combined with Theorem 9
(dense) or Theorem 11 (sparse), after padding the constraints with the two
all-one rows of (6) and adding `log(R/ε)` binary-search steps.

Boundary: cost contract; the reduction itself (construction of `A⁰⁰⁰` in (6))
is the content of `SourceLemma12`, whose two case-yields are hypotheses
(`hcase1`/`hcase2`) because game (6) is not constructed here.  The cost
re-parameterisation `ε' = ε/(6R(r+1))` for both access models is proved below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.SdpDuality

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-- Theorem 13, p.15 (cost composition).  The paper invokes Lemma 12 with
    tolerance `eps' = eps/(6R(r+1))` and plugs it into the dense Theorem 9
    cost `O~(sqrt(n+m)/eps'^3)` and the sparse Theorem 11 cost
    `O~(sqrt(s)/eps'^3.5)`.  The two `SoftOIn` transfers below are the exact
    re-parameterisations `eps' = eps/(6R(r+1))` (both access models), with
    the paper's stated `sqrt(n)+sqrt(m)` form for the dense bound.  The
    optimisation statements of Theorems 9/11 themselves are the content of
    those claims; the data of Lemma 12 is the `LPGameReduction` record. -/
theorem source_theorem13_cost_composition
    {n m s : ℕ} (hn : 0 < n) (hm : 0 < m) (hs : 0 < s)
    (data : LPGameReduction n m) {ε δ : ℝ}
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hR : 0 < data.R) (hr : 0 ≤ data.r)
    (implD implS : QuantumImplementation n m)
    (hsuccD : 1 - δ ≤ implD.successProb) (hsuccS : 1 - δ ≤ implS.successProb)
    (hhD : SoftOIn ((n : ℝ) + m + data.R * (data.r + 1) / ε)
      (Real.sqrt ((n : ℝ) + m) / (ε / (6 * data.R * (data.r + 1))) ^ 3) implD.totalTime)
    (hhS : SoftOIn ((n : ℝ) + m + data.R * (data.r + 1) / ε)
      (Real.sqrt s / (ε / (6 * data.R * (data.r + 1))) ^ (3.5 : ℝ)) implS.totalTime) :
    (1 - δ ≤ implD.successProb ∧
      SoftOIn ((n : ℝ) + m + data.R * (data.r + 1) / ε)
        (Real.sqrt ((n : ℝ) + m) * (6 * data.R * (data.r + 1) / ε) ^ 3) implD.totalTime) ∧
    (1 - δ ≤ implS.successProb ∧
      SoftOIn ((n : ℝ) + m + data.R * (data.r + 1) / ε)
        (Real.sqrt s * (6 * data.R * (data.r + 1) / ε) ^ (3.5 : ℝ)) implS.totalTime) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcpos : (0 : ℝ) < 6 * data.R * (data.r + 1) := by positivity
  refine ⟨⟨hsuccD, ?_⟩, ⟨hsuccS, ?_⟩⟩
  · obtain ⟨k, C, hC, hle⟩ := hhD
    refine ⟨k, C, hC, ?_⟩
    have hg : Real.sqrt ((n : ℝ) + m) / (ε / (6 * data.R * (data.r + 1))) ^ 3
        = Real.sqrt ((n : ℝ) + m) * (6 * data.R * (data.r + 1) / ε) ^ 3 := by
      rw [div_pow, div_pow]
      field_simp
    rwa [hg] at hle
  · obtain ⟨k, C, hC, hle⟩ := hhS
    refine ⟨k, C, hC, ?_⟩
    have hg : Real.sqrt s / (ε / (6 * data.R * (data.r + 1))) ^ (3.5 : ℝ)
        = Real.sqrt s * (6 * data.R * (data.r + 1) / ε) ^ (3.5 : ℝ) := by
      rw [Real.div_rpow (le_of_lt hε) hcpos.le,
        Real.div_rpow hcpos.le (le_of_lt hε)]
      field_simp
    rwa [hg] at hle

end Qatlib.Papers.ZeroSumGames19.MainResults.SdpDuality
