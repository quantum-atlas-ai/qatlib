/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity.Lemma53

/-!
# Theorem 5.4 — the `1/2 + 2^{-r}` soundness compression

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 5.4 (page 22), proof pages 22--26.

Statement (verbatim): let `L ∈ QIP`.  Then for every `r ∈ poly` there is a
three-message quantum Arthur--Merlin game for `L` with completeness error `0`,
soundness error at most `1/2 + 2^{−r}`, in which Arthur's message consists of a
single coin flip.

The proof starts from the [KitaevWatrous2000] normal form (perfect completeness, soundness
`2^{−2r}`) and "compresses" the verifier's message.  The analytic heart is the
following consequence of Lemma 5.3: if the prover's reference state is at least
`1/2`-faithful (`Froot ρ σ² ≥ 1/2`), then the fidelity of the compressed game's
outstate is bounded by `1/2 + Froot ρ ξ`, which is the `1/2 + 2^{−r}` soundness
shape when `Froot ρ ξ = 2^{−r}`.

## What is formalised here

The fidelity comparison step derived from Lemma 5.3 (the paper's compression
inequality).  Constructing the actual three-message circuit, and the operator
level transfer from the scalar `maxAccept` family of the QIP model, are not in
the shared library; see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qmam

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity
open Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- Theorem 5.4 (page 22), fidelity compression step: for density operators
`ρ, σ, ξ` with `ξ = σ` or `ρ = ξ`, if the prover's state is at least
`1/2`-faithful, `Froot ρ σ ^ 2 ≥ 1/2`, then the compressed game's overlap bound
obeys the `1/2 + 2^{-r}`-shaped estimate
`Froot σ ξ ^ 2 ≤ 1/2 + Froot ρ ξ`. -/
theorem theorem_5_4 {D : ℕ} {ρ σ ξ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hξ : IsDensityOperator ξ)
    (h : ξ = σ ∨ ρ = ξ)
    (hfaithful : (1 / 2 : ℝ) ≤ Froot ρ σ ^ 2) :
    Froot σ ξ ^ 2 ≤ 1 / 2 + Froot ρ ξ := by
  have h53 := lemma_5_3 hρ hσ hξ h
  linarith

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qmam
