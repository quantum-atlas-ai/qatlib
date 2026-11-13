/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 5 — the output state of Algorithm 4 is close to `|ψ′⟩`

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Lemma 5 is printed on p.11 (§4.2),
proved on p.16–18 (§4.3).

Source statement.  Let `|ψ⟩` be the output state of Algorithm 4 and `P₁` the
projector onto the subspace where the outcome register `O` is in `|1⟩`.  Then

  `‖P₁|ψ⟩ − |ψ′⟩‖ ≤ ((2m+37)ε + 30δ)·‖ψ′‖`.

The source's proof (p.16) decomposes `|ψ⟩ = ∑_i α_i|v_i⟩|φ_i⟩` and applies two
claims:

* **Claim 2** (good branches, p.17): for every good `i`,
  `‖|φ′_i⟩ − (1/(κλ̃_i))|1⟩|2^{j_i}⟩|0⟩‖ ≤ (2m+37)ε·‖(1/(κλ̃_i))|1⟩|2^{j_i}⟩|0⟩‖`;
* **Claim 5** (bad branches, p.18): the bad-branch contribution to
  `‖P₁|ψ⟩ − |ψ′⟩‖` is at most `30δ·‖ψ′‖`, using that the total mass of the bad
  `|α_i|²` is `δ`.

The source text then says: "The Lemma follows by combining these two claims and
the fact that the sum of `|α_i|²` over all bad `i` is equal to `δ`."

The Lean statement below is that assembly step in ℓ² form: the good part of
`P₁|ψ⟩` is `(2m+37)ε`-close to `|ψ′⟩`, the bad part is `30δ‖ψ′‖`-controlled,
and the two parts are added before the triangle inequality is applied.  The two
source claims are hypotheses; the file proves the Lemma from them, so this is a
faithful partial formalisation (the good/bad branch analyses themselves are
Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.MedianEstimate and the
per-stage estimation-error accumulation, which remain frozen partial support).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

/-- Fixed arXiv:1010.4458v2, Lemma 5 (printed p.11, proved p.16–18).

Let `P₁|ψ⟩ = ψ_g + ψ_b` be the decomposition of the good-outcome projection of
Algorithm 4's output into the good-branch and bad-branch contributions.  If
Claim 2 bounds `‖ψ_g − ψ′‖ ≤ (2m+37)ε‖ψ′‖` and Claim 5 bounds
`‖ψ_b‖ ≤ 30δ‖ψ′‖`, then

  `‖P₁|ψ⟩ − |ψ′⟩‖ = ‖(ψ_g + ψ_b) − ψ′‖ ≤ ((2m+37)ε + 30δ)·‖ψ′‖`,

which is the source's Lemma 5.  The statement is made in the `ℓ²` norm
(`EuclideanSpace ℂ ι`) over a finite orthonormal branch basis `ι`. -/
theorem source_lemma5 {ι : Type} [Fintype ι]
    (ψg ψb target : EuclideanSpace ℂ ι) (m : ℕ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hgood : ‖ψg - target‖ ≤ ((2 * (m : ℝ) + 37) * ε) * ‖target‖)
    (hbad : ‖ψb‖ ≤ (30 * δ) * ‖target‖) :
    ‖(ψg + ψb) - target‖ ≤ ((2 * (m : ℝ) + 37) * ε + 30 * δ) * ‖target‖ := by
  have hsplit : (ψg + ψb) - target = (ψg - target) + ψb := by abel
  rw [hsplit]
  calc ‖(ψg - target) + ψb‖
      ≤ ‖ψg - target‖ + ‖ψb‖ := norm_add_le _ _
    _ ≤ ((2 * (m : ℝ) + 37) * ε) * ‖target‖ + (30 * δ) * ‖target‖ :=
        add_le_add hgood hbad
    _ = ((2 * (m : ℝ) + 37) * ε + 30 * δ) * ‖target‖ := by ring

end Qatlib.Papers.VarTimeAmpAmp10.Estimate
