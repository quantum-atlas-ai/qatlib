/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

@[expose] public section


/-! # Trace-norm identities in the actual matrix model -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open scoped BigOperators

/-- The legacy singular-value sum is definitionally the matrix trace norm. -/
theorem traceNorm_eq_singularValueSum {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.traceNorm M = singularValueSum M := by
  rfl

/-- Trace distance satisfies the triangle inequality. -/
theorem traceDist_triangle {d : ℕ} (ρ σ τ : Dens (Fin d)) :
    traceDist ρ.val τ.val ≤ traceDist ρ.val σ.val + traceDist σ.val τ.val := by
  have h := Matrix.traceNorm_add_le (ρ.val - σ.val) (σ.val - τ.val)
  rw [sub_add_sub_cancel] at h
  unfold traceDist
  linarith

/-- The legacy entanglement-fidelity identity unfolds its Kraus-sum definition.
It does not identify this sum with a purification overlap. -/
theorem entanglementFidelity_eq_kraus_trace_sum {d : ℕ} {ι : Type} [Fintype ι]
    (ρ : Dens (Fin d)) (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hK : (∑ m, (K m).conjTranspose * K m) = 1) :
    entanglementFidelity K ρ.val = ∑ m, ‖Matrix.trace (ρ.val * K m)‖ ^ 2 := by
  rfl

/-- The Fuchs--van de Graaf inequalities in Wilde's squared-fidelity convention,
with the explicit root-fidelity and half-trace-norm representation bridge. -/
theorem fidelity_traceDist_bounds {d : ℕ} (ρ σ : Dens (Fin d)) :
    1 - Real.sqrt (fidelity ρ.val σ.val) ≤ traceDist ρ.val σ.val ∧
      traceDist ρ.val σ.val ≤ Real.sqrt (1 - fidelity ρ.val σ.val) := by
  have h := (Qatlib.Concepts.MixedFidelity.FidelityMetric.g3 d ρ.val σ.val
    ρ.property σ.property).1
  have hf : fidelity ρ.val σ.val =
      (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot ρ.val σ.val) ^ 2 := rfl
  have htrace : traceDist ρ.val σ.val =
      Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance ρ.val σ.val := by
    unfold traceDist Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance
    ring
  rw [hf, Real.sqrt_sq (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot_nonneg _ _),
    htrace]
  exact h

end Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric
