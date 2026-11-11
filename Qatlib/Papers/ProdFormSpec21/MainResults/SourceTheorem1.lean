/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 (leakage rate) — paper-layer Lean

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v2, **Theorem 1**, p.3 (Eq after (13)); proof in Appendix D
(p.11–12), resting on the projector-distance identity Eq (46).

Paper statement.  `T(δt)^L` is the Trotterized evolution; if the initial state `ρ`
belongs to the subregion `A` spanned by `m` eigenstates,
`P = Σ_{j=1}^m P_j`, `Tr(ρP) = 1`, then, provided `‖P − P̃‖ < 1`,
the leakage satisfies

  `1 − Tr(T(δt)^L ρ T(δt)^{†L} P) = O(‖P − P̃‖²) = O(m h² δt² / λ²)`.

Appendix D proves the exact inequality `1 − Tr(ρ U†PU) ≤ ‖U†PU − P‖²` by applying
Eq (46), `min_{ρ_a∈H_A} tr(P_B ρ_a) = 1 − ‖P_A − P_B‖²`, twice, and
`‖U†PU − P‖ ≤ ‖U†PU − P̃‖ + ‖P̃ − P‖ = 2δp` (using `[U, P̃] = 0` and unitarity).

We model the leakage on finite matrices with `Matrix.trace`; the remaining
residual is the rank-`m` min-trace identity Eq (46), stated as a hypothesis in
the bridging lemma `theorem1_leakage`.  The unitary conjugation invariance
`‖U† MU‖ = ‖M‖` is proved in this file from `U†U = 1`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The **leakage rate** `1 − Tr(T ρ T† P)` of the paper, written via cyclicity of
the trace as `1 − Tr(ρ U† P U)` with `U` the Trotterized evolution and using the
real part (the trace of a density-weighted projector is real). -/
noncomputable def leakageRate (ρ P U : Matrix I I ℂ) : ℝ :=
  1 - (Matrix.trace (ρ * (Uᴴ * P * U))).re

/-- **Theorem 1 (Leakage rate), paper p.3 / Appendix D.**  Let `P` and `P̃` be
idempotent projectors (`P² = P`, `P̃² = P̃`), `U` the Trotterized evolution with
`U†U = 1` and `[U, P̃] = 0`, and `ρ` a density supported on `P` (`Tr(ρP) = 1`).
If `‖P − P̃‖ < 1`, the leakage is `O(‖P − P̃‖²)`; concretely
`1 − Tr(ρ U† P U) ≤ 4‖P − P̃‖²` (Appendix D, Eq (46) applied twice).

Residual: the rank-`m` min-trace identity Eq (46) for general `m`, carried as the
hypothesis `hEq46`.  The unitary-conjugation norm identity
`‖U† M U‖ = ‖M‖` is proved below from `U†U = 1`; the assembly
(`‖U†PU − P‖ ≤ 2δp` and the final squaring) is also derived. -/
theorem theorem1_leakage
    (ρ P Pt U : Matrix I I ℂ)
    (hP : P * P = P) (hPt : Pt * Pt = Pt)
    (hU : Uᴴ * U = 1) (hcomm : U * Pt = Pt * U)
    (hρ : Matrix.trace (ρ * P) = 1)
    (hδ : ‖P - Pt‖ < 1)
    -- Appendix D, Eq (46) (rank-m min-trace identity, applied to `U†PU` and `P`):
    (hEq46 : 1 - (Matrix.trace (ρ * (Uᴴ * P * U))).re ≤ ‖Uᴴ * P * U - P‖ ^ 2) :
    leakageRate ρ P U ≤ 4 * ‖P - Pt‖ ^ 2 := by
  -- `‖U†PU − P‖ ≤ ‖U†PU − P̃‖ + ‖P̃ − P‖ = 2‖P − P̃‖`.
  unfold leakageRate
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hmem : U ∈ unitary (Matrix I I ℂ) := by
    rw [Unitary.mem_iff]
    exact ⟨by simpa [Matrix.star_eq_conjTranspose] using hU,
           by simpa [Matrix.star_eq_conjTranspose] using hUU⟩
  have hmemstar : Uᴴ ∈ unitary (Matrix I I ℂ) := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hmem
  have hconj : ‖Uᴴ * P * U - Pt‖ = ‖P - Pt‖ := by
    have hPtU : Uᴴ * Pt * U = Pt := by
      rw [mul_assoc, ← hcomm, ← mul_assoc, hU, one_mul]
    calc ‖Uᴴ * P * U - Pt‖ = ‖Uᴴ * (P - Pt) * U‖ := by
          rw [mul_sub, sub_mul, hPtU]
      _ = ‖(P - Pt) * U‖ := by
          simpa only [mul_assoc] using
            CStarRing.norm_mem_unitary_mul ((P - Pt) * U) hmemstar
      _ = ‖P - Pt‖ := CStarRing.norm_mul_mem_unitary (P - Pt) hmem
  have htri : ‖Uᴴ * P * U - P‖ ≤ 2 * ‖P - Pt‖ := by
    have hsplit : Uᴴ * P * U - P = (Uᴴ * P * U - Pt) + (Pt - P) := by abel
    rw [hsplit]
    calc ‖(Uᴴ * P * U - Pt) + (Pt - P)‖
        ≤ ‖Uᴴ * P * U - Pt‖ + ‖Pt - P‖ := norm_add_le _ _
      _ = ‖P - Pt‖ + ‖P - Pt‖ := by rw [hconj, norm_sub_rev]
      _ = 2 * ‖P - Pt‖ := by ring
  have hsq : ‖Uᴴ * P * U - P‖ ^ 2 ≤ (2 * ‖P - Pt‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) htri
  nlinarith [hEq46, hsq]

end Qatlib.Papers.ProdFormSpec21.MainResults
