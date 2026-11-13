/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# DiagonalTrace

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QSDPsolver17.MainResults

/-- Real-matrix trace-estimation procedure, used for the diagonal claims
(Lemma 11 and Corollary 12 work over real diagonal matrices). -/
structure RealTraceEstimator where
  estimate : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  successProbability : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  queryCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  gateCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma11_diagonal_flag`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma11_diagonal_flag_statement (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (hμ : 0 < μ) (hA : IsDiagonal A) (hH : IsDiagonal H) (hAnorm : OpNormLE_R A 1)
    (hHpsd : ∀ i, 0 ≤ H i i) : Prop :=
    ∃ F : RealProbabilityCircuit n,
      |F.prob - (Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExpR H))| ≤ μ ∧
      F.queries = 1 ∧
      ∃ k : ℕ, F.gates ≤ (Real.log (2 + 1 / μ)) ^ k + Real.log (2 + (n : ℝ))

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `cor12_diagonal_trace`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def cor12_diagonal_trace_statement : Prop :=
    ∃ E : RealTraceEstimator,
      ∀ {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ),
        IsDiagonal A → IsDiagonal H → OpNormLE_R A 1 → (∀ i, 0 ≤ H i i) →
        0 < θ → θ ≤ 1 →
        |E.estimate A H θ -
            Matrix.trace (A * matExpR H) / Matrix.trace (matExpR H)| ≤ θ ∧
        (2 : ℝ) / 3 ≤ E.successProbability A H θ ∧
        BigOAt (E.queryCost A H θ) (Real.sqrt (n : ℝ) / θ) ∧
        IsSoftO (E.gateCost A H θ) (Real.sqrt (n : ℝ) / θ) ((n : ℝ) + 1 / θ)

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
