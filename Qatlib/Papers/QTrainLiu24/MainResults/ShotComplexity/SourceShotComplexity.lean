/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QTrainLiu24.MainResults.ShotComplexity — source layer

Paper: Chen-Yu Liu et al., *Quantum-Train: Rethinking Hybrid Quantum-Classical
Machine Learning in the Model Compression Perspective*, fixed arXiv:2405.11304v2.
PDF `prove/assets/2405.11304v2.pdf`.

Claim c002: the shot-complexity paragraph of §III (p.8). The source, citing
Ref. [64] (Haah–Harrow–Ji–Wu–Yu, *Sample-optimal tomography of quantum states*),
reports that a *sufficient* number of measurement shots for fidelity
tomography with infidelity `ε` is

  `N_shot = O( (2^N / ε) · log(2^N / ε) )`   (§III, p.8).

This is an upper bound under the cited estimator/error regime. The claim has a
negative half: it does **not** yield a necessary lower bound such as `Ω̃(M/ε)`,
and it cannot unconditionally replace the repository's i.i.d. empirical-frequency
`ℓ₁` contract (ProbabilityCore.Concentration's Hoeffding/Chernoff entropy, a
different `O(log(·)/ε²)` regime).

This module formalises:

* `hilbertDim N = 2^N` and `shotBound C N ε = C·(2^N/ε)·log(2^N/ε)` (the cited
  sufficient count with the big-O constant absorbed into `C`);
* `hilbertDim_div_le_shotBound`: the cited count is at least linear in the
  Hilbert dimension `2^N` (the source's "exponential increase ... with system
  size `N`");
* `no_necessary_lower_bound_above_sufficient`: from a sufficient sample size
  `B` one cannot infer a lower bound `L > B` valid at every sufficient sample
  size — exactly the source's caveat that an upper bound does not give an
  `Ω̃(M/ε)` necessary lower bound.

No `sorry`, no extra axiom, no `unsafe`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QTrainLiu24.MainResults.ShotComplexity

/-- The Hilbert-space dimension `2^N` of an `N`-qubit state (§II-A, p.2). -/
def hilbertDim (N : ℕ) : ℝ := (2 : ℝ) ^ N

/-- The cited sufficient shot count `N_shot = O((2^N/ε) log(2^N/ε))` of §III
(p.8, citing [64]); `C` absorbs the big-O constant. -/
def shotBound (C : ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  C * (hilbertDim N / ε) * Real.log (hilbertDim N / ε)

/-- `2^N > 0`. -/
theorem hilbertDim_pos (N : ℕ) : 0 < hilbertDim N := by
  unfold hilbertDim
  positivity

/-- The cited sufficient count is at least linear in the Hilbert dimension
`2^N` (`C ≥ 1` and the logarithmic factor `≥ 1`): this is the exponential
growth in `N` that the source highlights at the end of §III. -/
theorem hilbertDim_div_le_shotBound (C : ℝ) (hC : 1 ≤ C) (N : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hlog : 1 ≤ Real.log (hilbertDim N / ε)) :
    hilbertDim N / ε ≤ shotBound C N ε := by
  have hApos : 0 < hilbertDim N / ε := div_pos (hilbertDim_pos N) hε
  have h1 : hilbertDim N / ε ≤ (hilbertDim N / ε) * Real.log (hilbertDim N / ε) := by
    nlinarith [hApos, hlog]
  have hlogpos : 0 < Real.log (hilbertDim N / ε) := by linarith
  have h2 : (hilbertDim N / ε) * Real.log (hilbertDim N / ε)
      ≤ C * ((hilbertDim N / ε) * Real.log (hilbertDim N / ε)) := by
    nlinarith [hC, mul_pos hApos hlogpos]
  unfold shotBound
  calc hilbertDim N / ε
      ≤ (hilbertDim N / ε) * Real.log (hilbertDim N / ε) := h1
    _ ≤ C * ((hilbertDim N / ε) * Real.log (hilbertDim N / ε)) := h2
    _ = C * (hilbertDim N / ε) * Real.log (hilbertDim N / ε) := by ring

/-- A lower bound that is asserted to hold at every sufficient sample size must
already hold at the cited sufficient size `B`. Hence a claimed necessary lower
bound strictly above `B` (for instance an `Ω̃(M/ε)` bound exceeding the cited
`O((2^N/ε) log(2^N/ε))` count) cannot be derived from the sufficient-count
result alone. This is the negative half of claim c002. -/
theorem no_necessary_lower_bound_above_sufficient
    (Sufficient : ℝ → Prop) (B L : ℝ)
    (hB : Sufficient B) (hgt : B < L) :
    ¬ (∀ n : ℝ, Sufficient n → L ≤ n) := by
  intro h
  have hBL : L ≤ B := h B hB
  linarith

/-- Acquiring more shots than a sufficient number remains sufficient: a
sufficient-sample predicate is upward closed. -/
theorem sufficient_mono (Sufficient : ℝ → Prop)
    (hmono : ∀ ⦃a b : ℝ⦄, a ≤ b → Sufficient a → Sufficient b)
    {a b : ℝ} (hab : a ≤ b) (ha : Sufficient a) : Sufficient b :=
  hmono hab ha

end Qatlib.Papers.QTrainLiu24.MainResults.ShotComplexity
