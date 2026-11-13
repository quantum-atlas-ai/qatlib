/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastMixing26.MainResults.Definitions.SourceDefinitions
import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# FastMixing26.MainResults.MainConclusions — Section 1 main results

Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*,
fixed arXiv:2606.26090v2 (PDF SHA-256 70f1cf62dfec60d72f2d721539a6ffc9447afb15b950de72411b8b3b06ed2b7a).

* Theorem 1.3, p. 2: the CKG Lindbladian `L` has a system-size independent spectral gap
  at high temperature (conditional bridge, fully proved).

Corollary 1.4 (c002) is not formalized (no quantum-algorithm/block-encoding model in
the library). The legacy estimator records below contain independent numerical
annotations, not runtime certificates. In particular, the partition-function record
has no accuracy condition; the expectation map receives the target scalar itself.
Neither record supplies execution, gates, or a sampling process, and neither is used
by `source_theorem_1_3`.

Theorem 1.3 is the composition of Theorem 4.1 (gap of the Pauli generator `K`) with
Theorem 5.1 (Dirichlet-form comparison `𝓔^L ≥ c₂^{qk} 𝓔^K`) through the frozen gap-transfer
lemma `kmsGap_transfer`. The two ingredients are supplied as hypotheses here; their own
statements live in `PseudoLindblad` and `DirichletComparison`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators MatrixOrder ComplexOrder
open Finset Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.FastMixing26.MainResults.MainConclusions

open Qatlib.Papers.FastMixing26.MainResults
open Qatlib.Foundations.DirichletForm.KmsDirichlet

/-- Theorem 1.3, p. 2, fixed arXiv:2606.26090v2. High-temperature spectral gap of the CKG
Lindbladian, stated as the composition of its two proven inputs.

For universal `c ≥ 1` (from Corollary 4.13) and any `β < [c^{qk} d J]^{-1}`: if the Pauli
generator `K` satisfies `gap(K) ≥ γ` (Theorem 4.1) and the Dirichlet forms compare as
`𝓔_ρ^L(O) ≥ γ·𝓔_ρ^K(O)` (Theorem 5.1), then `gap(L) ≥ γ²` — a bound independent of the
system size `n`. This is exactly the chain `Theorem 5.1 + Theorem 4.1 + kmsGap_transfer`.

The body is fully proved (bridge); the two hypotheses are the statements of Theorems 4.1
and 5.1, whose deep proofs are statement-only in this development. -/
theorem source_theorem_1_3 {D : ℕ} (q k : ℕ) (d J c : ℝ) (hc : 1 ≤ c) :
    ∀ (β : ℝ) (_hβ : 0 < β) (_hβc : β < (c ^ (q * k) * d * J)⁻¹)
      (ρ : Operator D) (L K : Operator D →ₗ[ℂ] Operator D) (γ : ℝ) (hγ : 0 < γ),
      KmsGapAtLeast ρ K γ →
      (∀ O : Operator D, kmsDirichlet ρ L O ≥ γ * kmsDirichlet ρ K O) →
      KmsGapAtLeast ρ L (γ * γ) := by
  intro β _hβ _hβc ρ L K γ hγ hKgap hcmp
  -- The Dirichlet comparison `𝓔^L ≥ γ·𝓔^K` is `𝓔^K ≤ γ⁻¹·𝓔^L`, the form required by
  -- `kmsGap_transfer` with `α = γ⁻¹`; the transferred gap is `γ / γ⁻¹ = γ²`.
  have hα : 0 < (1 : ℝ) / γ := one_div_pos.mpr hγ
  have hcmp' : ∀ O : Operator D,
      kmsDirichlet ρ K O ≤ (1 / γ) * kmsDirichlet ρ L O := by
    intro O
    have h : γ * kmsDirichlet ρ K O ≤ kmsDirichlet ρ L O := hcmp O
    have hinv : 0 ≤ (1 : ℝ) / γ := le_of_lt hα
    calc kmsDirichlet ρ K O
        = (1 / γ) * (γ * kmsDirichlet ρ K O) := by
          rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hγ)]
      _ ≤ (1 / γ) * kmsDirichlet ρ L O :=
          mul_le_mul_of_nonneg_left h hinv
  have hres := kmsGap_transfer (ρ := ρ) (M := L) (N := K) (α := 1 / γ) hα hcmp' hKgap
  have hconst : γ / (1 / γ) = γ * γ := by
    have hγ' : γ ≠ 0 := ne_of_gt hγ
    field_simp [hγ']
  rw [hconst] at hres
  exact hres

/-- Legacy numerical specification associated with Corollary 1.4, retained for
compatibility. It has no target partition function or accuracy condition and no
execution model. Its scalar bound is not a computational runtime guarantee. -/
structure PartitionFunctionEstimator (n : ℕ) (ε : ℝ) where
  /-- Independent numerical annotation; not a measured gate or sample count. -/
  runtime : ℕ
  /-- An arbitrary real number, with no specified target or accuracy. -/
  estimate : ℝ
  /-- The numerical annotation is positive. -/
  runtime_pos : 0 < runtime
  /-- A scalar upper bound, with no connection to execution. -/
  runtime_poly : (runtime : ℝ) ≤ ((n : ℝ) + 1 / ε) ^ 2

/-- Legacy scalar approximation specification associated with Corollary 1.4.
The map receives the target expectation directly, so its error bound does not
certify estimation from physical input. No computational runtime is certified. -/
structure ExpectationEstimator (n : ℕ) (ε : ℝ) where
  /-- Independent numerical annotation; not a measured gate or sample count. -/
  runtime : ℕ
  /-- An unrestricted scalar map receiving the target itself. -/
  est : ℝ → ℝ
  /-- The numerical annotation is positive. -/
  runtime_pos : 0 < runtime
  /-- A scalar upper bound, with no connection to execution. -/
  runtime_poly : (runtime : ℝ) ≤ ((n : ℝ) + 1 / ε) ^ 2
  /-- Additive error `ε` on every expectation. -/
  err : ∀ M : ℝ, |est M - M| ≤ ε

end Qatlib.Papers.FastMixing26.MainResults.MainConclusions
