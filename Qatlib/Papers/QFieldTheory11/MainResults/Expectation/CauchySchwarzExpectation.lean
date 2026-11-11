/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Expectation — Hermitian expectation Cauchy–Schwarz bound

Source: Jordan–Lee–Preskill, *Quantum Algorithms for Quantum Field Theories*,
fixed arXiv:1111.3633v1 (2011). PDF SHA-256 recorded in the paper README block.

Proposition 2 (pp.24–25): for a Hermitian operator `M` and a quantum state `|ψ⟩`,
`|⟨ψ|M|ψ⟩| ≤ √⟨ψ|M²|ψ⟩`. The paper's proof (Eqs.35–37) observes that
`(M − ⟨M⟩1)² ⪰ 0` gives `0 ≤ ⟨M²⟩ − ⟨M⟩²`, which is the Cauchy–Schwarz inequality
on the Hermitian form.

The formal statement below is the operator-theoretic core: on a complex inner
product space (the quantum Hilbert space) with `M` a symmetric (`IsSymmetric`,
i.e. Hermitian) linear operator and `‖ψ‖ = 1`, the real expectation value obeys the
bound with `M²ψ = M(Mψ)`. This is exactly the inequality the paper uses in Eqs.42–44
to bound `μ_{φ(x)}, σ_{φ(x)}, μ_{π(x)}, σ_{π(x)}`.

Boundary: no claim about unbounded operators; only the finite-expectation inequality.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace ComplexOrder
open RCLike

namespace Qatlib.Papers.QFieldTheory11.MainResults.Expectation

/-- Fixed arXiv:1111.3633v1, Proposition 2 (pp.24–25, Eqs.35–37): for a Hermitian
operator `M` (modelled as a symmetric complex-linear endomorphism) and a normalized
state `ψ` (`‖ψ‖ = 1`), the modulus of the expectation `⟨ψ|M|ψ⟩` is at most the square
root of the expectation `⟨ψ|M²|ψ⟩` of the square `M²ψ = M(Mψ)`.

Proof: Cauchy–Schwarz gives `|⟨ψ|Mψ⟩| ≤ ‖ψ‖‖Mψ‖ = ‖Mψ‖`; Hermiticity gives
`⟨ψ|M(Mψ)⟩ = ⟨Mψ|Mψ⟩ = ‖Mψ‖²`, so `‖Mψ‖ = √⟨ψ|M²ψ⟩`. -/
theorem prop2_cauchy_schwarz_expectation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : E →ₗ[ℂ] E) (hM : M.IsSymmetric) (ψ : E) (hψ : ‖ψ‖ = 1) :
    |re ⟪ψ, M ψ⟫| ≤ Real.sqrt (re ⟪ψ, M (M ψ)⟫) := by
  -- Hermiticity: `⟪ψ, M(Mψ)⟫ = ⟪Mψ, Mψ⟫`.
  have hsymm : ⟪M ψ, M ψ⟫ = ⟪ψ, M (M ψ)⟫ := hM ψ (M ψ)
  -- Hence the radicand is `‖Mψ‖²`.
  have hnorm : re ⟪ψ, M (M ψ)⟫ = ‖M ψ‖ ^ 2 := by
    rw [← hsymm, inner_self_eq_norm_sq]
  -- Cauchy–Schwarz bound `‖⟪ψ, Mψ⟫‖ ≤ ‖Mψ‖`.
  have hcs : ‖⟪ψ, M ψ⟫‖ ≤ ‖M ψ‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) ψ (M ψ)
    rwa [hψ, one_mul] at h
  calc
    |re ⟪ψ, M ψ⟫| ≤ ‖⟪ψ, M ψ⟫‖ := abs_re_le_norm _
    _ ≤ ‖M ψ‖ := hcs
    _ = Real.sqrt (‖M ψ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (re ⟪ψ, M (M ψ)⟫) := by rw [hnorm]

end Qatlib.Papers.QFieldTheory11.MainResults.Expectation
