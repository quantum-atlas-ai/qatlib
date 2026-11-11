/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ScatteringQFT11.MainResults.ExpectationCore

set_option backward.isDefEq.respectTransparency false

/-!
# The finite-dimensional Weyl relation behind Proposition 1

Jordan–Lee–Preskill, *Quantum Computation of Scattering in Scalar Quantum Field
Theories* (arXiv:1112.4833v1), Proposition 1 (p. 21) states that for Hermitian
operators `p̂, q̂` on `L²(ℝ)` obeying the canonical commutation relation
`[q̂, p̂] = i𝟙`, the eigenbasis of `p̂` is the Fourier transform of the eigenbasis
of `q̂`.

The paper's proof (equations (57)–(61)) uses exactly one mechanism: the
conjugation `f̂(δ) = e^{−iq̂δ} p̂ e^{iq̂δ}` satisfies `f̂(δ) = p̂ + δ𝟙`, hence
`p̂ e^{iq̂δ} = e^{iq̂δ}(p̂ + δ𝟙)` (59), so `e^{iq̂δ}` shifts a `p̂`-eigenvector to
the eigenvector of the shifted eigenvalue (60); the Fourier transform is then the
operator that implements this shift on the `q̂`-eigenbasis.

This module formalises that algebraic mechanism in the finite-dimensional model
used throughout the repository: a unitary pair `U, V` obeying the Weyl form
`U V = ω (V U)` of the canonical commutation relation (the discrete analogue of
`[q̂, p̂] = i𝟙`, with `ω` a root of unity). The main theorem is the finite analogue
of (59)–(60): conjugating by `U` multiplies the `V`-eigenvalue by `ω⁻¹`, so `U`
carries the `V`-eigenbasis onto the eigenbasis of the conjugate operator.

**Coverage status (partial).** The operator statement of Proposition 1 lives on
`L²(ℝ)` and needs the unbounded self-adjoint realisation of `p̂` and `q̂` and the
Fourier transform as a unitary on `L²(ℝ)`; Mathlib has no spectral theory for
unbounded operators, so that statement is not reconstructed here. What is proved
is the finite-dimensional Weyl mechanism that the paper's proof uses, including
the explicit eigen-relation. The discrete Fourier identification of the two
eigenbases is not formalised.
-/

namespace Qatlib.Papers.ScatteringQFT11.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Weyl form of the canonical commutation relation.** Two operators satisfy the
finite-dimensional Weyl relation with phase `ω` when `U V = ω (V U)`; for a
`d`-level system with `ω = e^{2πi/d}` this is the discrete counterpart of
`[q̂, p̂] = i𝟙`. -/
def WeylPair (U V : Matrix n n ℂ) (ω : ℂ) : Prop := U * V = ω • (V * U)

/-- **Finite analogue of equations (59)–(60).** If `U, V` obey the Weyl relation
`U V = ω (V U)` with `ω ≠ 0`, then conjugating by `U` sends a `V`-eigenvector with
eigenvalue `ζ` to a `V`-eigenvector with eigenvalue `ω⁻¹ ζ`. This is precisely the
mechanism by which the paper's `e^{iq̂δ}` shifts the eigenvalue of `p̂`:

`p̂ e^{iq̂δ} = e^{iq̂δ}(p̂ + δ𝟙)` (59) ⟹ `p̂ (e^{iq̂δ}|p⟩) = (p + δ)(e^{iq̂δ}|p⟩)` (60). -/
theorem weyl_conj_shifts_eigenvalue {U V : Matrix n n ℂ} {ω ζ : ℂ}
    (hWeyl : WeylPair U V ω) (hω : ω ≠ 0) (v : QState n)
    (hv : V *ᵥ v = ζ • v) :
    V *ᵥ (U *ᵥ v) = (ω⁻¹ * ζ) • (U *ᵥ v) := by
  have hVU : V * U = ω⁻¹ • (U * V) := by
    have h := hWeyl
    unfold WeylPair at h
    have : (ω⁻¹ : ℂ) • (U * V) = ω⁻¹ • (ω • (V * U)) := by rw [h]
    rw [this, smul_smul, inv_mul_cancel₀ hω, one_smul]
  calc V *ᵥ (U *ᵥ v) = (V * U) *ᵥ v := Matrix.mulVec_mulVec v V U
    _ = (ω⁻¹ • (U * V)) *ᵥ v := by rw [hVU]
    _ = ω⁻¹ • ((U * V) *ᵥ v) := Matrix.smul_mulVec _ _ _
    _ = ω⁻¹ • (U *ᵥ (V *ᵥ v)) := by rw [Matrix.mulVec_mulVec v U V]
    _ = ω⁻¹ • (U *ᵥ (ζ • v)) := by rw [hv]
    _ = ω⁻¹ • (ζ • (U *ᵥ v)) := by rw [Matrix.mulVec_smul]
    _ = (ω⁻¹ * ζ) • (U *ᵥ v) := smul_smul _ _ _

/-- **Equation (60) read as a statement about the eigenbasis.** The conjugate
operator `U` maps every `ζ`-eigenvector of `V` into the `(ω⁻¹ζ)`-eigenspace of `V`;
in the paper's continuous setting the map `U = e^{iq̂δ}` is the Fourier/shift
transformation that carries the `q̂`-eigenbasis to the `p̂`-eigenbasis. -/
theorem weyl_eigenbasis_image {U V : Matrix n n ℂ} {ω ζ : ℂ}
    (hWeyl : WeylPair U V ω) (hω : ω ≠ 0) :
    ∀ v : QState n, V *ᵥ v = ζ • v → V *ᵥ (U *ᵥ v) = (ω⁻¹ * ζ) • (U *ᵥ v) :=
  fun v hv => weyl_conj_shifts_eigenvalue hWeyl hω v hv

end Qatlib.Papers.ScatteringQFT11.MainResults
