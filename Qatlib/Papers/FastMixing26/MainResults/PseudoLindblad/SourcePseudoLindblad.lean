/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastMixing26.MainResults.Definitions.SourceDefinitions
import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# FastMixing26.MainResults.PseudoLindblad — Section 4

Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*,
fixed arXiv:2606.26090v2 (PDF SHA-256 70f1cf62dfec60d72f2d721539a6ffc9447afb15b950de72411b8b3b06ed2b7a).

Source moments (Section 4):

* Definition 4.2 (63), p. 18: the KMS oscillator norm `|||X|||_ρ = Σ_i ‖δ_i[X]‖_ρ`
  (vocabulary below).

The Section 4 analytic statements (Lemma 4.3, Lemma 4.7, Lemma 4.10, Lemma 4.11,
Lemma 4.12, Corollary 4.13, Theorem 4.1 — claims c008–c014) are not formalized; their
statements are preserved in this branch's history.  This module retains the oscillator
norm, operator norm, supercommutator and Dobrushin vocabulary.

The auxiliary generator of Definition 1.10 (8) is the frozen
`GibbsSampling.KmsDirichlet.kmsGenerator`; the summed
generator `K = Σ_i K_i` is the frozen `kmsGeneratorFam`, and `KmsGapAtLeast` is the
paper's `gap(K) ≥ γ` (Definition 2.8).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators MatrixOrder ComplexOrder
open Finset Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.FastMixing26.MainResults.PseudoLindblad

open Qatlib.Papers.FastMixing26.MainResults
open Qatlib.Foundations.DirichletForm.KmsDirichlet

/-- Definition 4.2 (63): the KMS oscillator norm `|||X|||_ρ = Σ_{i∈[n]} ‖δ_i[X]‖_ρ`.
`δ_i[X] = X − 2^{-q} tr_i X` is kept as the abstract superoperator `δ i`. -/
def kmsOscillatorNorm {D : ℕ} {n : ℕ} (ρ : Operator D)
    (δ : Fin n → Operator D →ₗ[ℂ] Operator D) (X : Operator D) : ℝ :=
  ∑ i, kmsNorm ρ (δ i X)

/-- The KMS-induced superoperator norm `‖N‖_ρ = sup_{O} ‖N[O]‖_ρ / ‖O‖_ρ` (Definition 2.4). -/
def kmsOpNorm {D : ℕ} (ρ : Operator D) (N : Operator D →ₗ[ℂ] Operator D) : ℝ :=
  sSup {r : ℝ | ∀ X : Operator D, kmsNorm ρ (N X) ≤ r * kmsNorm ρ X}

/-- The superoperator commutator `[M, N] = M∘N − N∘M`. -/
def superComm {D : ℕ} (M N : Operator D →ₗ[ℂ] Operator D) : Operator D →ₗ[ℂ] Operator D :=
  M.comp N - N.comp M

/-- The Dobrushin constant `γ := max_i (‖δ_i‖_ρ·η_i + Σ_{j≠i} κ_{ij})` of (70). -/
def dobrushinGamma {n : ℕ} [NeZero n] (δnorm η : Fin n → ℝ)
    (κ : Fin n → Fin n → ℝ) : ℝ :=
  supOver (fun i =>
    δnorm i * η i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), κ i j)

end Qatlib.Papers.FastMixing26.MainResults.PseudoLindblad
