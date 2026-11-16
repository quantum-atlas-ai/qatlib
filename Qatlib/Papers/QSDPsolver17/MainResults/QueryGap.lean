/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # The legacy query records do not connect their outputs to their resource fields.
These counterinstances refute the old lower-bound contracts, not oracle query lower bounds.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QSDPsolver17.MainResults
open Qatlib.Papers.QSDPsolver17.MainResults

/-- The old majority solver records a correct output independently of its declared query count. -/
structure MajOrMajSolver where
  /-- An unconstrained resource report. -/
  queries : ℕ → ℕ → ℕ → ℝ
  /-- A total Boolean function of the full input. -/
  correct : ∀ {a b c : ℕ}, (Fin a → Fin b → Fin c → Bool) → Bool
  /-- Correctness imposes no condition on queries. -/
  hcorrect : ∀ {a b c : ℕ} (Z : Fin a → Fin b → Fin c → Bool),
    MajOrMajPromise a b c Z → correct Z = MajOrMaj a b c Z

/-- The majority interface admits an exact answer with a zero resource report. -/
theorem majority_counterexample :
    ∃ solver : MajOrMajSolver,
      ¬ BigOmegaAt (solver.queries 1 1 1) ((1 : ℝ) * Real.sqrt 1 * 1) := by
  refine ⟨⟨fun _ _ _ => 0, fun {a b c} Z => MajOrMaj a b c Z, fun _ _ => rfl⟩, ?_⟩
  rintro ⟨c, hc, h⟩
  norm_num at h
  linarith

/-- The old LP record similarly separates a Boolean response from its resource report. -/
structure LpSolver where
  /-- Reported calls to the input. -/
  queries : ℕ → ℕ → ℝ
  /-- A response on two complete SDP descriptions. -/
  distinguishes : ∀ {n m : ℕ}, SdpData n m → SdpData n m → Bool

/-- The old one-sided LP correctness predicate accepts a constant response at zero queries. -/
theorem lp_counterexample :
    ∃ solver : LpSolver,
      (∀ {n m : ℕ} (P Q : SdpData n m) (v w : ℤ),
        P.dualL1Bound (v : ℝ) → Q.dualL1Bound (w : ℝ) → v ≠ w →
          solver.distinguishes P Q = true) ∧
      ¬ BigOmegaAt (solver.queries 1 1) (Real.sqrt 1 * Real.sqrt ((1 : ℝ) ^ 3)) := by
  refine ⟨⟨fun _ _ => 0, fun _ _ => true⟩, ?_, ?_⟩
  · intros
    rfl
  · rintro ⟨c, hc, h⟩
    norm_num at h
    linarith

/-- The old sparse-sum interface records the entry function and cost independently. -/
structure SumOracle (d k : ℕ) where
  /-- Reported oracle calls. -/
  queries : ℕ
  /-- A value returned on complete input matrices. -/
  entry : (Fin k → Matrix (Fin d) (Fin d) ℂ) → Fin d → Fin d → ℂ
  /-- The exact sum identity. -/
  hcorrect : ∀ (M : Fin k → Matrix (Fin d) (Fin d) ℂ) (i j : Fin d),
    entry M i j = ∑ t, M t i j

/-- Exact summation with a zero resource field refutes the old sparse-sum lower bound. -/
theorem sum_counterexample :
    ∃ impl : SumOracle 1 1,
      ∀ c : ℝ, 0 < c → ¬ c * (1 : ℝ) * 1 ≤ (impl.queries : ℝ) := by
  refine ⟨⟨0, fun M i j => ∑ t, M t i j, fun _ _ _ => rfl⟩, ?_⟩
  intro c hc
  simpa using (not_le.mpr hc)

/-- Negative probabilities permitted by the old estimator hypotheses make its error target impossible. -/
theorem amplitude_counterexample (est : AmplitudeEstimator) :
    ¬ ∀ p pmin μ : ℝ, pmin ≤ p → p ≤ 1 → 0 < μ → μ ≤ 1 →
      |p - est.estimate p μ| ≤ μ * p := by
  intro h
  have hneg := h (-1) (-1) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpos := abs_nonneg ((-1 : ℝ) - est.estimate (-1) 1)
  linarith

end Qatlib.Papers.QSDPsolver17.MainResults
