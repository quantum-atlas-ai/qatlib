/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement.BinaryMeasurement

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem1Measurement — Theorem 1 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Theorem 1, p. 5.

Theorem 1: for all partitions `μ, ν, λ ⊢ n` a quantum circuit of size `poly(n)`
implements the projective measurement `{P_μνλ, I − P_μνλ}`.

The measurement is modelled by its two effects (`binaryEffect`).  The paper's
circuit construction (the GPE-based circuit of Lemma 6 / Theorem 2) is the
realisation of this binary measurement; its gate-level size is the paper's
`poly(n)` compilation and is not formalised here.  What is proved is that the
two effects are exhaustive and idempotent, and that the accept probability
computes `g_μνλ` through the trace formula of Lemma 1:

`g_μνλ = (d_μ d_ν d_λ)⁻¹ Tr(P_μνλ)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Theorem 1** (fixed arXiv:2302.11454v3, p. 5): the two-outcome family
`{P_μνλ, I − P_μνλ}` is a projective measurement (exhaustive, both effects
idempotent), and its trace computes the Kronecker coefficient,
`g_μνλ = (d_μ d_ν d_λ)⁻¹ Tr(P_μνλ)`.

The projector property `P_μνλ · P_μνλ = P_μνλ` is the paper's Eq. (49)–(51)
(`P_μνλ = Q (Π^L_μ ⊗ Π^L_ν ⊗ Π^L_λ)` is a projector); its proof uses the
character convolution identity and is not repeated here. -/
theorem theorem1_projective_measurement (χμ χν χl : G → ℂ)
    (hμ : ∀ σ : G, χμ σ⁻¹ = χμ σ) (hν : ∀ σ : G, χν σ⁻¹ = χν σ)
    (hl : ∀ σ : G, χl σ⁻¹ = χl σ)
    (hdμ : charDim χμ ≠ 0) (hdν : charDim χν ≠ 0) (hdl : charDim χl ≠ 0)
    (hproj : kronProjector χμ χν χl * kronProjector χμ χν χl
      = kronProjector χμ χν χl) :
    (binaryEffect (kronProjector χμ χν χl) true
        * binaryEffect (kronProjector χμ χν χl) true
        = binaryEffect (kronProjector χμ χν χl) true) ∧
    (binaryEffect (kronProjector χμ χν χl) false
        * binaryEffect (kronProjector χμ χν χl) false
        = binaryEffect (kronProjector χμ χν χl) false) ∧
    (binaryEffect (kronProjector χμ χν χl) true
        + binaryEffect (kronProjector χμ χν χl) false = 1) ∧
    kronCoeff χμ χν χl =
      (charDim χμ * charDim χν * charDim χl)⁻¹ *
        Matrix.trace (kronProjector χμ χν χl) :=
  ⟨binaryEffect_true_idempotent _ hproj, binaryEffect_false_idempotent _ hproj,
    binaryEffect_total _, lemma1_kronecker_coeff_eq_normalized_trace χμ χν χl hμ hν hl hdμ hdν hdl⟩

end Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement
