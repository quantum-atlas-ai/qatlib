/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# SparseTrace

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

/-- `I ⪯ H` in quadratic-form form. -/
def PSDMinusOne {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, ‖x‖ ^ 2 ≤ (∑ i, star (x i) * (H.mulVec x) i).re

/-- `K I - H ⪰ 0` in quadratic-form form, i.e. `H ⪯ K I`. -/
def LeScalarIdentity {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) : Prop :=
  ∀ x : Fin n → ℂ, 0 ≤ (∑ i, star (x i) * ((K • (1 : Matrix (Fin n) (Fin n) ℂ) - H).mulVec x) i).re

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma13_sparse_flag`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma13_sparse_flag_statement (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ)
    (K μ : ℝ) (s d : ℕ)
    (hμ : 0 < μ) (hK : 0 < K) (hA : OpNormLE A 1)
    (hHmin : PSDMinusOne H) (hHmax : LeScalarIdentity H K)
    (hAs : RowSparse A s) (hHd : RowSparse H d) (hsd : s ≤ d) : Prop :=
    ∃ F : ProbabilityCircuit,
      |F.prob - (Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExp H)).re| ≤ μ ∧
      IsSoftO F.queries ((K : ℝ) * (d : ℝ)) ((n : ℝ) + K + 1 / μ) ∧
      IsSoftO F.gates ((K : ℝ) * (d : ℝ)) ((n : ℝ) + K + 1 / μ)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `cor14_sparse_trace`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def cor14_sparse_trace_statement : Prop :=
    ∃ T : TraceEstimationProcedure,
      ∀ {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℂ) (K θ : ℝ) (s d : ℕ),
        OpNormLE A 1 → OpNormLE H K → 0 < K → RowSparse A s → RowSparse H d → s ≤ d →
        0 < θ → θ ≤ 1 →
        |T.estimate A H θ -
            (Matrix.trace (A * matExp H)).re / (Matrix.trace (matExp H)).re| ≤ θ ∧
        (2 : ℝ) / 3 ≤ T.successProbability A H θ ∧
        IsSoftO (T.queryCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ) ∧
        IsSoftO (T.gateCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ)

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
