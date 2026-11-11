/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace.KroneckerTraceFormula

set_option backward.isDefEq.respectTransparency false

/-!
# ApproxKronReduction — Corollary 1 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Corollary 1 and its proof, p. 4.

Corollary 1: the function `(μ,ν,λ) ↦ d_μ d_ν d_λ g_{μνλ}` is in `#BQP`, and the
problem `ApproxKron` (approximating Kronecker coefficients to a given relative error)
is polynomial-time reducible to `QXC`.

The proof (p. 4) observes that Theorem 1 gives a polynomial-size verification circuit
measuring the projector `P_{μνλ}`; since `P_{μνλ}` is a projector its eigenvalues are
`0` or `1`, and by Lemma 1 the number of `+1` eigenvalues is `d_μ d_ν d_λ g_{μνλ}`.
Exact counting of `+1` eigenvalues is a `#BQP` problem, and relative-error
approximation of this count is a `QXC` problem; the dimensional factor `d_μ d_ν d_λ`
is efficiently computable via the hook-length formula.

The library (both `QuantumAlgorithmDev` and Frozen) has no `#BQP`/`QXC` complexity-class
framework and no hook-length formula, so the class-membership statement itself is not
expressible.  What is formalised here is its mathematical core, the *counting* form of
the identity: the map `(μ,ν,λ) ↦ d_μ d_ν d_λ g_{μνλ}` is the trace of a family of
idempotent matrices, i.e. it is a projector counting function (number of `+1`
eigenvalues).  The two missing layers are exactly (i) uniformity/poly-size of the
circuit family of Theorem 1 and (ii) the definition of `#BQP`/`QXC`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.CharacterSums

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A complex-valued function on an index type is a *projector counting function* if it
is the trace of a family of idempotent matrices.  For a projector the trace is the number
of `+1` eigenvalues, which is the counting quantity of a `#BQP` function (paper p. 4,
proof of Corollary 1). -/
def IsProjectorCountingFunction {ι V : Type*} [Fintype V] [DecidableEq V]
    (f : ι → ℂ) : Prop :=
  ∃ P : ι → Matrix V V ℂ, (∀ i, P i * P i = P i) ∧ ∀ i, f i = Matrix.trace (P i)

/-- **Corollary 1, counting core** (fixed arXiv:2302.11454v3, p. 4): for any indexed
family of triples of characters, the map
`i ↦ d_{μ_i} d_{ν_i} d_{λ_i} g_{μ_i ν_i λ_i}` is the trace of the family of idempotent
Kronecker projectors `P_{μ_i ν_i λ_i}`, hence a projector counting function.  This is the
`#BQP` content of Corollary 1 (the number of `+1` eigenvalues of `P_{μνλ}` is
`d_μ d_ν d_λ g_{μνλ}` by Lemma 1). -/
theorem corollary1_dmu_dnu_dlam_kronCoeff_is_counting
    {ι : Type*} (χμ χν χl : ι → G → ℂ)
    (hμ : ∀ i, ∀ σ : G, χμ i σ⁻¹ = χμ i σ)
    (hν : ∀ i, ∀ σ : G, χν i σ⁻¹ = χν i σ)
    (hl : ∀ i, ∀ σ : G, χl i σ⁻¹ = χl i σ)
    (hproj : ∀ i, kronProjector (χμ i) (χν i) (χl i) *
        kronProjector (χμ i) (χν i) (χl i) = kronProjector (χμ i) (χν i) (χl i)) :
    IsProjectorCountingFunction (V := G × G × G)
      (fun i => charDim (χμ i) * charDim (χν i) * charDim (χl i) *
        kronCoeff (χμ i) (χν i) (χl i)) :=
  ⟨fun i => kronProjector (χμ i) (χν i) (χl i), hproj,
    fun i => (trace_kronProjector (χμ i) (χν i) (χl i) (hμ i) (hν i) (hl i)).symm⟩

/-- **Corollary 1, `ApproxKron` reduction core** (fixed arXiv:2302.11454v3, p. 4): a
relative-error approximation of the eigenvalue count `k = d_μ d_ν d_λ g_{μνλ}` transfers
to the same relative-error approximation of the normalized Kronecker coefficient
`g_{μνλ} = k / (d_μ d_ν d_λ)`.  This is the elementary step of the polynomial-time
reduction `ApproxKron ≤_p QXC` (the `QXC` side being the relative-error counting of
`+1` eigenvalues). -/
theorem approxKron_from_relative_count_error (D k k' : ℝ) (hD : D ≠ 0)
    (δ : ℝ) (hδ : |k - k'| ≤ δ * |k|) :
    |D⁻¹ * k - D⁻¹ * k'| ≤ δ * |D⁻¹ * k| := by
  have habs : |D⁻¹| = |D|⁻¹ := abs_inv D
  have hk : 0 ≤ |k| := abs_nonneg k
  calc |D⁻¹ * k - D⁻¹ * k'| = |D⁻¹ * (k - k')| := by rw [mul_sub]
    _ = |D⁻¹| * |k - k'| := abs_mul _ _
    _ = |D|⁻¹ * |k - k'| := by rw [habs]
    _ ≤ |D|⁻¹ * (δ * |k|) := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity)
    _ = δ * (|D|⁻¹ * |k|) := by ring
    _ = δ * |D⁻¹ * k| := by rw [abs_mul, habs]

end Qatlib.Papers.KroneckerCoef23.MainResults.CharacterSums
