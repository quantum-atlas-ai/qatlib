/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EigTransform26.Representation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# EigTransform26 — Representation block, normalization (Proposition 2.5)

Paper-layer Lean statement and proof for claim `c003`:

* `c003` Proposition 2.5 — normalization of a standard vanilla LCHM realization,
  eqs. (2.12) and (2.13), p.12.

The monomial value (2.12) is recorded definitionally as `alphaMono`; the polynomial
bound (2.13) is then the coefficientwise composition of the monomial normalizations,
which is proved here by distributivity of the finite sum.  The circuit-level step
"the coefficientwise implementation has normalization at most the sum of the monomial
normalizations" is the implementation hypothesis `hα`; in absence of a circuit model in
Lean it is recorded as a hypothesis (see the docstring).
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

namespace Qatlib.Papers.EigTransform26.Representation

/-- The monomial block-encoding normalization of eq. (2.12):
`α_{vanilla,m} = s_K^m · ∑_j |a_j|`, where `a : Fin M → ℂ` are the LCU coefficients and
`s_K` is the signal-oracle scale. -/
noncomputable def alphaMono {M : ℕ} (sK : ℝ) (a : Fin M → ℂ) (m : ℕ) : ℝ :=
  sK ^ m * ∑ j, ‖a j‖

/-- **Proposition 2.5 (Normalization in a standard vanilla LCHM implementation).**
arXiv:2607.25812v1, §2, eqs. (2.12)-(2.13), p.12.

For the monomial `g(z) = z^m`, the standard QSVT–LCU realization of eq. (2.10) has
block-encoding normalization `α_{vanilla,m} = s_K^m ∑_j |a_j|` (eq. (2.12)).  For a
polynomial `p(z) = ∑_{ℓ=0}^d b_ℓ z^ℓ`, the coefficientwise implementation obeys
`α_{vanilla,p} ≤ (∑_{ℓ=0}^d |b_ℓ| s_K^ℓ) ∑_j |a_j|` (eq. (2.13)).

`αvanillaP` denotes the normalization of the direct coefficientwise implementation; the
hypothesis `hα` records the standard QSVT–LCU composition fact that it is at most the sum
of the monomial normalizations `∑_ℓ |b_ℓ| α_{vanilla,ℓ}` (the LCU block-encoding
normalization of a sum of block encodings is bounded by the sum of the normalizations). -/
theorem proposition_2_5 {M : ℕ}
    (sK : ℝ) (a : Fin M → ℂ) (b : ℕ → ℂ) (d : ℕ) (αvanillaP : ℝ)
    (hα : αvanillaP ≤ ∑ ℓ ∈ Finset.range (d + 1), ‖b ℓ‖ * alphaMono sK a ℓ) :
    (∀ m : ℕ, alphaMono sK a m = sK ^ m * ∑ j, ‖a j‖)
      ∧ αvanillaP ≤ (∑ ℓ ∈ Finset.range (d + 1), ‖b ℓ‖ * sK ^ ℓ) * (∑ j, ‖a j‖) := by
  refine ⟨fun m => rfl, ?_⟩
  -- Eq. (2.13): pull the common factor `∑_j |a_j|` out of the coefficientwise sum.
  have hsum : (∑ ℓ ∈ Finset.range (d + 1), ‖b ℓ‖ * alphaMono sK a ℓ)
      = (∑ ℓ ∈ Finset.range (d + 1), ‖b ℓ‖ * sK ^ ℓ) * (∑ j, ‖a j‖) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [alphaMono]
    ring
  exact le_trans hα (le_of_eq hsum)

end Qatlib.Papers.EigTransform26.Representation
