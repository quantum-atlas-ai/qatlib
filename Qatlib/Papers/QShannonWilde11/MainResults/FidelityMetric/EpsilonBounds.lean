/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.ProvedMath

@[expose] public section

/-!
# Epsilon forms of the Fuchs--van de Graaf inequalities

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Corollaries 9.3.1--9.3.2, fixed
PDF p. 276.
<https://arxiv.org/abs/1106.1445>

The public theorem
`Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.fidelity_traceDist_bounds`
already proves the two-sided Fuchs--van de Graaf inequality in root-fidelity and
normalized trace-distance form.  This file converts those bounds to the epsilon
conventions used by the two corollaries, while retaining the unnormalized trace
norm `‖ρ - σ‖₁` appearing in the source. The inputs are positive semidefinite
matrices of trace one, so their dimension is necessarily positive.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric

open Qatlib.Papers.QShannonWilde11.MainResults.Model

noncomputable section

/-- **Corollary 9.3.1** — [Wilde2017], arXiv:1106.1445v8, fixed PDF p. 276.  If two states have
unnormalized trace-norm distance at most `ε ∈ [0, 1]`, then their fidelity is at least `1 - ε`. -/
theorem fidelity_ge_one_sub_of_traceNormDiff_le {d : ℕ} (ρ σ : Dens (Fin d)) {ε : ℝ}
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdist : traceNormDiff ρ.val σ.val ≤ ε) :
    1 - ε ≤ fidelity ρ.val σ.val := by
  have hbounds :=
    Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.fidelity_traceDist_bounds ρ σ
  have hT : traceDist ρ.val σ.val ≤ ε / 2 := by
    unfold traceNormDiff at hdist
    unfold traceDist
    linarith
  have hlower : 1 - Real.sqrt (fidelity ρ.val σ.val) ≤ ε / 2 :=
    le_trans hbounds.1 hT
  have hrootnonneg : 0 ≤ Real.sqrt (fidelity ρ.val σ.val) :=
    Real.sqrt_nonneg _
  have hfidelitynonneg : 0 ≤ fidelity ρ.val σ.val := by
    unfold fidelity
    positivity
  have hbase : 1 - ε / 2 ≤ Real.sqrt (fidelity ρ.val σ.val) := by linarith
  have hsq : (1 - ε / 2) ^ 2 ≤
      (Real.sqrt (fidelity ρ.val σ.val)) ^ 2 :=
    sq_le_sq' (by linarith) hbase
  calc 1 - ε ≤ (1 - ε / 2) ^ 2 := by nlinarith [sq_nonneg ε]
    _ ≤ (Real.sqrt (fidelity ρ.val σ.val)) ^ 2 := hsq
    _ = fidelity ρ.val σ.val := Real.sq_sqrt hfidelitynonneg

/-- **Corollary 9.3.2** — [Wilde2017], arXiv:1106.1445v8, fixed PDF p. 276.  If two states have
fidelity at least `1 - ε`, then their unnormalized trace-norm distance is at most `2√ε`. -/
theorem traceNormDiff_le_of_fidelity_ge_one_sub {d : ℕ} (ρ σ : Dens (Fin d)) {ε : ℝ}
    (_hε : 0 ≤ ε) (_hε1 : ε ≤ 1) (hfidelity : 1 - ε ≤ fidelity ρ.val σ.val) :
    traceNormDiff ρ.val σ.val ≤ 2 * Real.sqrt ε := by
  have hbounds :=
    Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.fidelity_traceDist_bounds ρ σ
  have hle : 1 - fidelity ρ.val σ.val ≤ ε := by linarith
  have hroot : Real.sqrt (1 - fidelity ρ.val σ.val) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hle
  have hT := le_trans hbounds.2 hroot
  unfold traceDist at hT
  unfold traceNormDiff
  linarith

end

end Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric
