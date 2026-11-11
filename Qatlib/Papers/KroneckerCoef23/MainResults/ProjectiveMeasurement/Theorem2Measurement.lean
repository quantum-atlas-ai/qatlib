/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement.BinaryMeasurement
import Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation.ConjugationRowSum

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem2Measurement — Theorem 2 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Theorem 2, p. 6.

Theorem 2: for any `λ ⊢ n` a quantum circuit of size `poly(n)` implements the
projective measurement `{Π^c_λ, I − Π^c_λ}`, where `d_λ R_λ = Tr(Π^c_λ)`.

As for Theorem 1, the two-outcome measurement is modelled by its effects and the
gate-level circuit (Generalized Phase Estimation on the conjugation
representation) is the paper's construction, not formalised here.  The trace
identity `d_λ R_λ = Tr(Π^c_λ)` is proved in full from Lemma 8:

`Tr(Π^c_χ) = d_χ · R_χ`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace
open Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Theorem 2** (fixed arXiv:2302.11454v3, p. 6): the two-outcome family
`{Π^c_χ, I − Π^c_χ}` is a projective measurement and satisfies the trace
identity `d_χ R_χ = Tr(Π^c_χ)` used for the QMA containment of Corollary 2.

The projector property `Π^c_χ · Π^c_χ = Π^c_χ` is the paper's Eq. (49)–(51)
(evaluated for the conjugation representation) and is taken as hypothesis. -/
theorem theorem2_projective_measurement (χ : G → ℂ) (hd : charDim χ ≠ 0)
    (hproj : conjProjector χ * conjProjector χ = conjProjector χ) :
    (binaryEffect (conjProjector χ) true * binaryEffect (conjProjector χ) true
        = binaryEffect (conjProjector χ) true) ∧
    (binaryEffect (conjProjector χ) false * binaryEffect (conjProjector χ) false
        = binaryEffect (conjProjector χ) false) ∧
    (binaryEffect (conjProjector χ) true + binaryEffect (conjProjector χ) false = 1) ∧
    charDim χ * rowSum χ = Matrix.trace (conjProjector χ) :=
  ⟨binaryEffect_true_idempotent _ hproj, binaryEffect_false_idempotent _ hproj,
    binaryEffect_total _, (trace_conjProjector χ).symm⟩

end Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement
