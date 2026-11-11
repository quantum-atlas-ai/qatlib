/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace.KroneckerTraceFormula

set_option backward.isDefEq.respectTransparency false

/-!
# PositivityQMA — Corollary 2 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Corollary 2 and its proof, p. 5.

Corollary 2: the problem of deciding positivity of Kronecker coefficients — given
`μ,ν,λ ⊢ n`, decide whether `g_{μνλ} > 0` — is contained in `QMA`.

The proof (p. 5) uses the projective measurement `{P_{μνλ}, I − P_{μνλ}}` of Theorem 1:

* `P_{μνλ}` has nonzero rank if and only if `g_{μνλ} > 0`;
* if `g_{μνλ} > 0` there is a quantum state giving outcome `+1`;
* if `g_{μνλ} = 0` then all states give outcome `0`.

Since `g_{μνλ}` is a nonnegative integer, deciding positivity is deciding `g_{μνλ} ≠ 0`,
and by Lemma 1 (`g_{μνλ} = (d_μd_νd_λ)⁻¹ Tr(P_{μνλ})`) this is equivalent to
`Tr(P_{μνλ}) ≠ 0`, i.e. to the projector having nonzero rank.  This is the criterion a
`QMA` verifier checks (with perfect completeness and soundness).

The library has no `QMA` class and no spectral theorem packaged for the witness-state
step (`g > 0 ⇒ ∃ state with outcome +1`, `g = 0 ⇒ all states give 0`), so the
class-membership and witness-existence layers are documented as the gap of this partial
formalisation.  The decision criterion `g_{μνλ} ≠ 0 ↔ Tr(P_{μνλ}) ≠ 0` is proved in full.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.CharacterSums

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Corollary 2, positivity criterion** (fixed arXiv:2302.11454v3, p. 5): the
Kronecker coefficient is nonzero if and only if the Kronecker projector has nonzero
trace (nonzero rank).  Since `g_{μνλ}` is a nonnegative integer, this is the decision
criterion of the `QMA` protocol of Corollary 2.  The hypotheses are the reality of the
characters (Eq. (54)) and nonzero dimensions, as in Lemma 1. -/
theorem corollary2_positivity_iff_nonzero_trace (χμ χν χl : G → ℂ)
    (hμ : ∀ σ : G, χμ σ⁻¹ = χμ σ) (hν : ∀ σ : G, χν σ⁻¹ = χν σ)
    (hl : ∀ σ : G, χl σ⁻¹ = χl σ)
    (hdμ : charDim χμ ≠ 0) (hdν : charDim χν ≠ 0) (hdl : charDim χl ≠ 0) :
    kronCoeff χμ χν χl ≠ 0 ↔ Matrix.trace (kronProjector χμ χν χl) ≠ 0 := by
  have hD : charDim χμ * charDim χν * charDim χl ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdμ hdν) hdl
  rw [lemma1_kronecker_coeff_eq_normalized_trace χμ χν χl hμ hν hl hdμ hdν hdl]
  constructor
  · intro h htr
    exact h (by rw [htr, mul_zero])
  · intro htr h
    apply htr
    have hmul : (charDim χμ * charDim χν * charDim χl) *
        ((charDim χμ * charDim χν * charDim χl)⁻¹ *
          Matrix.trace (kronProjector χμ χν χl)) = 0 := by
      rw [h, mul_zero]
    calc Matrix.trace (kronProjector χμ χν χl)
        = 1 * Matrix.trace (kronProjector χμ χν χl) := (one_mul _).symm
      _ = ((charDim χμ * charDim χν * charDim χl) *
            (charDim χμ * charDim χν * charDim χl)⁻¹) *
            Matrix.trace (kronProjector χμ χν χl) := by
          rw [mul_inv_cancel₀ hD]
      _ = (charDim χμ * charDim χν * charDim χl) *
            ((charDim χμ * charDim χν * charDim χl)⁻¹ *
              Matrix.trace (kronProjector χμ χν χl)) := by
          rw [mul_assoc]
      _ = 0 := hmul

end Qatlib.Papers.KroneckerCoef23.MainResults.CharacterSums
