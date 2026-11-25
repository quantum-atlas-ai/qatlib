/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabPEPS15.MainResults.ClusterExpansion

@[expose] public section

/-!
# AdiabPEPS15 — scope of the cluster norm bound

Source: "Rapid adiabatic preparation of injective PEPS and Gibbs states",
fixed arXiv:1508.00570v2, Lemma 13 / Eq. (99), Supplemental p. 15:
`‖fˇ_μ(Ω)‖ ≤ (e^{4β} − 1)^{|Ω|}` for every `Ω ⊆ Λ` and every edge `μ`.

The printed statement lives inside the cluster-expansion setting of §"Cluster
expansion" (arXiv:1508.00570v2, p. 15), which fixes two ambient assumptions
before Theorem 10 and Lemma 13:

* every interaction is bounded, `‖h_λ‖ ≤ 1`;
* `P_μ` is the orthogonal projector onto the ground space of `G_μ`, so
  `P_μ * P_μ = P_μ` and `‖P_μ‖ = 1`.

This module records the two elementary facts about the model of
`Qatlib.Papers.AdiabPEPS15.MainResults` that delimit the formal statement:

* `fCheck_empty_eq_mul` — at `Ω = ∅` the Möbius transform is `P * P`, and since
  `clusterBound β 0 = 1`, Eq. (99) at `|Ω| = 0` is exactly the norm bound
  `‖P‖ ≤ 1` (`fCheck_empty_norm_le_clusterBound`);
* `lemma13_literal_claim_fails` — the literal statement without a norm
  hypothesis on `P` is false.

The estimate for nonempty `Ω` is not proved here. Its source proof expands the
three exponentials (100) into monomials `h_{w₁} P_μ h_{w₂} P_μ h_{w₃}`, bounds
each monomial by one using the two assumptions above, and evaluates the
resulting Möbius sum (102). Carrying that out needs a norm bound for
`NormedSpace.exp` and the interchange of the exponential series with the finite
Möbius sum; neither is available in the current library.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open Qatlib.Papers.AdiabPEPS15.MainResults

namespace Qatlib.Papers.AdiabPEPS15.MainResults

/-- The Möbius transform at the empty cluster is the single cluster term
`f_μ(∅)`, and `e^{0} = 1` collapses its three conjugating exponentials:
`fˇ_μ(∅) = P_μ * P_μ`. -/
theorem fCheck_empty_eq_mul {d : ℕ} {ι : Type*} [DecidableEq ι]
    (h : ι → Matrix (Fin d) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (β : ℝ) :
    fCheck h P β ∅ = P * P := by
  simp [fCheck, mobiusCheck, fμ, Hsum]

/-- Eq. (99) at `|Ω| = 0`: under the paper's projector norm bound `‖P_μ‖ ≤ 1`,
`‖fˇ_μ(∅)‖ ≤ (e^{4β} − 1)^0 = 1`.  Idempotence of `P` is not needed, only the
norm bound. -/
theorem fCheck_empty_norm_le_clusterBound {d : ℕ} {ι : Type*} [DecidableEq ι]
    (h : ι → Matrix (Fin d) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (β : ℝ) (hP : ‖P‖ ≤ 1) :
    ‖fCheck h P β ∅‖ ≤ clusterBound β (∅ : Finset ι).card := by
  rw [fCheck_empty_eq_mul, clusterBound, Finset.card_empty, pow_zero]
  calc ‖P * P‖ ≤ ‖P‖ * ‖P‖ := norm_mul_le P P
    _ ≤ 1 := by nlinarith [norm_nonneg P, hP]

/-- The literal claim with an unconstrained `P` is false.  On `ℂ¹`, the choice
`P = 2 • 1` and `Ω = ∅` gives `fˇ_μ(∅) = P * P = 4 • 1`, whose operator norm is
`4`, while `clusterBound 0 0 = (e^0 − 1)^0 = 1`.  The paper's Lemma 13 is stated
for the orthogonal ground-space projectors `P_μ`, whose operator norm is `1`, so
the norm hypothesis on `P` is not redundant. -/
theorem lemma13_literal_claim_fails :
    ¬ (∀ (P : Matrix (Fin 1) (Fin 1) ℂ) (β : ℝ) (Ω : Finset Unit),
        ‖fCheck (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)) P β Ω‖ ≤
          clusterBound β Ω.card) := by
  intro hclaim
  have h0 := hclaim ((2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 ∅
  rw [fCheck_empty_eq_mul, clusterBound, Finset.card_empty, mul_zero, Real.exp_zero,
    sub_self, pow_zero] at h0
  have hsq : ((2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((2 : ℂ) • 1) = (4 : ℂ) • 1 := by
    rw [smul_mul_smul, mul_one]
    norm_num
  have hnorm : ‖(4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 4 := by
    rw [norm_smul, norm_one, mul_one]
    norm_num
  rw [hsq, hnorm] at h0
  norm_num at h0

end Qatlib.Papers.AdiabPEPS15.MainResults
