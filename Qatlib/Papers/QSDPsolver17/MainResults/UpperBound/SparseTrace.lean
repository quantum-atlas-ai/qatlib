/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

@[expose] public section

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
open Matrix

/-- `I ⪯ H`: the difference `H - I` is Hermitian positive semidefinite. -/
def PSDMinusOne {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  PSD (H - 1)

/-- For Hermitian `H`, the quadratic-form inequality expressing `H ⪯ K I`. -/
def LeScalarIdentity {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) : Prop :=
  ∀ x : Fin n → ℂ,
    0 ≤ (∑ i, star (x i) * ((K • (1 : Matrix (Fin n) (Fin n) ℂ) - H).mulVec x) i).re

/-- The lower PSD bound forces `H` to be Hermitian. -/
theorem PSDMinusOne.isHermitian {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (h : PSDMinusOne H) : H.IsHermitian := by
  have hd : (H - 1).IsHermitian := h.1
  simpa only [sub_add_cancel] using hd.add Matrix.isHermitian_one

/-- For Hermitian `H`, the lower PSD bound is equivalent to bounding its
quadratic form below by the squared Euclidean norm. -/
theorem psdMinusOne_iff_quadratic_form {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) :
    PSDMinusOne H ↔ ∀ x : Fin n → ℂ,
      (∑ i, ‖x i‖ ^ 2) ≤ (∑ i, star (x i) * (H.mulVec x) i).re := by
  have hform (x : Fin n → ℂ) :
      (∑ i, star (x i) * ((H - 1).mulVec x) i).re =
        (∑ i, star (x i) * (H.mulVec x) i).re - ∑ i, ‖x i‖ ^ 2 := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib, Complex.sub_re]
    congr 1
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  refine ⟨fun h x => ?_, fun h => ⟨hH.sub Matrix.isHermitian_one, fun x => ?_⟩⟩
  · exact sub_nonneg.mp (hform x ▸ h.2 x)
  · rw [hform]
    exact sub_nonneg.mpr (h x)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma13_sparse_flag`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma13_sparse_flag_statement (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ)
    (K μ : ℝ) (s d : ℕ) : Prop :=
  0 < n → A.IsHermitian → OpNormLE A 1 → PSDMinusOne H → LeScalarIdentity H K →
    0 < K → RowSparse A s → RowSparse H d → s ≤ d → 0 < μ →
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
        0 < n → A.IsHermitian → H.IsHermitian → OpNormLE A 1 → OpNormLE H K →
        0 < K → RowSparse A s → RowSparse H d → s ≤ d →
        0 < θ → θ ≤ 1 →
        |T.estimate A H θ -
            (Matrix.trace (A * matExp H)).re / (Matrix.trace (matExp H)).re| ≤ θ ∧
        (2 : ℝ) / 3 ≤ T.successProbability A H θ ∧
        IsSoftO (T.queryCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ) ∧
        IsSoftO (T.gateCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ)

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
