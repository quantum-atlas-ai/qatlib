/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Success probability as coupling vanishes (Corollary 3)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Corollary 3, pp.30-31
(eqs. G4-G5) and its proof in Appendix G.

Corollary 3: "The success probability in Lemma 2 approaches 1 as
`max_{i,j}|w_{ij}| → 0`." The proof shows that as the weights vanish the Gibbs
distribution factorises (eq. G5), the mean-field solution becomes exact so that
`KL(Q‖P) → 0`, and hence (eq. G4) `Z_Q → Z` and one may take `κ = 1`, so the
Lemma-2 success probability `Z/(κ Z_Q)` tends to `1`.

We model the coupling strength by a parameter `ε → 0` and prove the limit from
its two ingredients supplied by the paper's proof: `Z ε / Z_Q ε → 1` (from
`Z_Q → Z`) and `κ ε → 1`. -/
set_option autoImplicit false
noncomputable section

open Filter Topology

namespace Qatlib.Papers.QDeepLearn14.MainResults.VanishingCoupling

/-- **Corollary 3** of arXiv:1412.3489 (pp.30-31): if, as the coupling strength
`ε → 0`, the mean-field partition ratio `Z/Z_Q → 1` and the bound `κ → 1`, then
the Lemma-2 success probability `Z/(κ Z_Q) → 1`. -/
theorem corollary3_successTendstoOne
    (Z ZQ κ : ℝ → ℝ)
    (hZQ : ∀ᶠ ε in nhds (0 : ℝ), ZQ ε ≠ 0)
    (hκ : ∀ᶠ ε in nhds (0 : ℝ), κ ε ≠ 0)
    (hratio : Tendsto (fun ε => Z ε / ZQ ε) (nhds 0) (nhds 1))
    (hk : Tendsto κ (nhds 0) (nhds 1)) :
    Tendsto (fun ε => Z ε / (κ ε * ZQ ε)) (nhds 0) (nhds 1) := by
  -- Rewrite `Z/(κ Z_Q)` as `(Z/Z_Q)/κ` near `0`.
  have hfun : (fun ε => Z ε / (κ ε * ZQ ε))
      =ᶠ[nhds (0 : ℝ)] (fun ε => (Z ε / ZQ ε) / κ ε) := by
    filter_upwards [hZQ, hκ] with ε hz hk'
    field_simp [hz, hk']
  -- The rewritten function tends to `1/1 = 1`.
  have hlim : Tendsto (fun ε => (Z ε / ZQ ε) / κ ε) (nhds (0 : ℝ)) (nhds (1 / 1)) :=
    hratio.div hk (by norm_num)
  rw [one_div_one] at hlim
  exact Tendsto.congr' hfun.symm hlim

end Qatlib.Papers.QDeepLearn14.MainResults.VanishingCoupling
