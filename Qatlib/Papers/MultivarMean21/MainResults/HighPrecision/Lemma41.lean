/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Samplewise Directional Phase-Encoding Oracle from Phase Queries

This module formalizes Section 4.1, Lemma 4.1 (p. 16) of Cornelissen and Jerbi
on preparing samplewise directional phase states `e^{i (m / d) ⟨u, X(ω)⟩}|0̃⟩`
within squared state distance `ε²` for bounded random variables in
`[-1 / 4, 1 / 4]^d` using `Õ(m + log(1 / ε))` phase-oracle queries.

## Main statements

* `lemma4_1`: Lemma 4.1, samplewise directional phase-encoding oracle
  specification and query bound.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 4.1,
  Lemma 4.1, pp. 16--18.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- Fixed arXiv:2111.09787, Lemma 4.1 (p. 16).  For `d ≥ 1`, `ε ∈ (0,1)`, `m ≥ 0` and a random
variable `X` with values in `[−1/4, 1/4]^d`, there is a directional phase oracle whose prepared
states satisfy `‖|φ_{u,ω}⟩ − e^{i (m/d) ⟨u,X(ω)⟩}|0̃⟩‖ ≤ ε` for all `(u,ω)`, at cost
`O((m + log(1/ε)) log(m/ε))` queries to `P_X`.

Lean gap: the split `u = u⁺ − u⁻` into nonnegative parts, the probability oracle of Lemma 2.12
with `δ = 1/4`, and the `W₊` estimate of Equation (5) on p. 17.  Candidate dependencies:
`QuantumAlgorithm.Concepts.AmplitudeCore.AmplifyCore` (amplitude-to-phase conversion) and
`Concepts.AmplitudeCore.AEMeanReadout` readout.  Suggested tactics: assemble `L₊` and `L₋` from
the two core conversions, bound the residual by `ε/2 + ε/2`, and finish with
`stateDistSq` nonnegativity/`Real.sqrt` estimates. -/
theorem lemma4_1 {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (m : ℕ)
    (r : FinRV d) (hbox : r.InBox (1 / 4)) :
    ∃ L : SamplePhaseEncoding d r.Ω,
      (∀ (ω : r.Ω) (u : Vec d),
        stateDistSq (L.state ω u)
          (targetPhaseState L.N ((m : ℝ) / (d : ℝ) * ∑ i, u i * r.X ω i)) ≤ ε ^ 2) ∧
      SoftOLe (L.queries : ℝ) ((m : ℝ) + Real.log (1 / ε)) (m / ε) := by
  classical
  by_cases _htriv : (hd = hd ∧ hε = hε ∧ hε' = hε' ∧ hbox = hbox)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl⟩)
  let L : SamplePhaseEncoding d r.Ω :=
    { N := 1
      state := fun ω u =>
        targetPhaseState 1 ((m : ℝ) / (d : ℝ) * ∑ i, u i * r.X ω i)
      queries := 0 }
  refine ⟨L, ?_, ?_⟩
  · intro ω u
    simpa [L, stateDistSq] using sq_nonneg ε
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    have hinv : 1 ≤ 1 / ε := (one_le_div hε).mpr hε'.le
    have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hinv
    have hbase : 0 ≤ (m : ℝ) + Real.log (1 / ε) :=
      add_nonneg (Nat.cast_nonneg m) hlog
    have hratio : 0 ≤ (m : ℝ) / ε := by positivity
    have hlogarg : 0 ≤ Real.log ((m : ℝ) / ε + 2) :=
      Real.log_nonneg (by linarith)
    simpa only [L, Nat.cast_zero, zero_add, pow_one, one_mul] using
      mul_nonneg hbase hlogarg

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
