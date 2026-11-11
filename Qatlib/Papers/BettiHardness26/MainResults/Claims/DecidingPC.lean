/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Qatlib.Papers.BettiHardness26.MainResults.Model.BettiProblem

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.3 (Deciding PC via Betti number)

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11). Source: Lemma 4.3, §4, p.10.

`For k ≥ (2+ε) log₂ n, w.h.p. over the distribution defining PLANTEDCLIQUE(n,k):
 β_{k−2}(skel_{k−2} X(G)) ≥ 1 ⇔ [G is from the planted case],
 β_{k−2}(skel_{k−2} X(G)) = 0 ⇔ [G is from the null case].`

This is the conjunction of Lemma 4.1 (null value `β = 0`, `NullValue.lean`) and Lemma 4.2
(planted value `β ≥ 1`, `PlantedValue.lean`). Modelling the input distributions by a `Setup`
with null weights `mu0` and planted weights `mu1`, the decision rule "planted iff `β ≥ 1`"
classifies every graph in the null support as null and every graph in the planted support as
planted. The statement below records exactly this separation; it is *proved* here as the
two support-wise implications, taking the planted lower bound `β ≥ 1` (Lemma 4.2) as hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims

open Qatlib.Papers.BettiHardness26.MainResults.Model
open Qatlib.Papers.BettiHardness26.MainResults.Reduction

variable {Γ : Type*} [Fintype Γ]

/-- The Betti-number decision rule for planted clique: output `true` (planted) iff the Betti
value is at least `1`. -/
def decidePlanted (s : Setup Γ) (g : Γ) : Bool := decide (1 ≤ s.beta g)

/-- **Lemma 4.3 (Deciding PC via Betti number)** (§4, p.10). Given the planted lower value
`β ≥ 1` (Lemma 4.2), the threshold-`1` decision rule classifies every null-support graph as null
(`β = 0 ⇒ false`, Lemma 4.1) and every planted-support graph as planted (`β ≥ 1 ⇒ true`). -/
theorem lemma_4_3 (s : Setup Γ) (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g) :
    (∀ g, s.mu0 g ≠ 0 → decidePlanted s g = false) ∧
      (∀ g, s.mu1 g ≠ 0 → decidePlanted s g = true) := by
  constructor
  · intro g hg
    unfold decidePlanted
    rw [s.null_zero g hg]
    norm_num
  · intro g hg
    unfold decidePlanted
    exact decide_eq_true (hPlanted g hg)

end Qatlib.Papers.BettiHardness26.MainResults.Claims
