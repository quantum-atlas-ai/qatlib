/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Appendix

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- **Lemma A.0.1** — arXiv:1106.1445v8, fixed PDF p. 739. If `M` and `N` are positive
semidefinite, then so are `M+N`, `MNM` and `NMN`.
Deps: `Matrix.PosSemidef.add`, `Matrix.PosSemidef.conjTranspose_mul_mul_same`. -/
theorem posSemidef_add_and_sandwich {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (M + N).PosSemidef ∧ (M * N * M).PosSemidef ∧ (N * M * N).PosSemidef := by
  refine ⟨hM.add hN, ?_, ?_⟩
  · have h := hN.conjTranspose_mul_mul_same M
    rwa [hM.isHermitian.eq] at h
  · have h := hM.conjTranspose_mul_mul_same N
    rwa [hN.isHermitian.eq] at h

/-- Complex inner product `⟨x|y⟩ = Σ_i x_i conj(y_i)`. -/
def iprod {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ i, x i * star (y i)

/-- Normalised averaged vector `|χ̂⟩ = (1/√d) Σ_j γ_j |χ_j⟩` with phases `γ`. -/
def avgVec {d : ℕ} (χ : Fin d → Fin d → ℂ) (γ : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ((1 / Real.sqrt (d : ℝ) : ℝ) : ℂ) * ∑ j, γ j * χ j i

end

end Qatlib.Papers.QShannonWilde11.MainResults.Appendix
