/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# SpectralGap11 reviewed SimulationModel

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- A black-box simulation relation: `W` is an `ε`-approximation of the exact
time-`t` evolution `V` built from `q` black-box queries. The relation is left
abstract because the shared libraries provide no oracle-evolution model; its
two fields are the paper's simulation guarantee and a positive query count. -/
structure BlackBoxSimulation {n : ℕ} (q L : ℕ) (t ε : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℂ) : Prop where
  /-- Output accuracy: `‖W - V‖ ≤ ε` (Lemma 2, p. 5). -/
  approx : ‖W - V‖ ≤ ε
  /-- The simulation uses a positive number of black-box calls. -/
  cost_pos : 0 < q


/-- At zero time the legacy positive-cost bound is inconsistent.
This diagnoses the missing additive cost term, not the source asymptotic claim. -/
theorem zero_time_refutes {n : ℕ} (κ L : ℕ) (hκ : 0 < κ) (ε : ℝ) :
    ¬ ∃ (q : ℕ) (W V : Matrix (Fin n) (Fin n) ℂ),
      BlackBoxSimulation q L 0 ε W V ∧
      (q : ℝ) ≤ Real.rpow |(L : ℝ) * 0| (1 + 1 / (2 * (κ : ℝ))) * (2 + 1 / ε) := by
  rintro ⟨q, W, V, hsim, hcost⟩
  have hk : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have he : 0 < 1 + 1 / (2 * (κ : ℝ)) := by positivity
  simp only [mul_zero, abs_zero, Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt he), zero_mul] at hcost
  have hq : (0 : ℝ) < q := by exact_mod_cast hsim.cost_pos
  linarith

end Qatlib.Papers.SpectralGap11.MainResults
