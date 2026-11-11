/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Claim 5.1.1 (arXiv:2408.07764v2, p.38, Eqs (223)–(226))

`|P₀| = M ≤ g`, where `P₀ = {P_ij ∈ P'' : ν_{P_ij}((ω₀)) ≥ 0}` is the set of places
of `P''` at which the Weil differential `ω₀` has no pole, and `g` is the genus of
the function field.

The paper's proof: from `(ω₀) ≥ 7A + E − D'' + ∑_{j=1}^M P_ij` (Eq (224)) take
degrees, using `deg((ω₀)) = 2g − 2` (canonical divisor) and
`deg(7A + E − D'') = 7a + (n'' − 2 + g − 7a) − n''`, to obtain
`2g − 2 ≥ 7a + (n'' − 2 + g − 7a) − n'' + M` (Eq (225)) and hence `M ≤ g`
(Eq (226)).

Formalisation boundary: Mathlib has no algebraic-function-field / Weil-differential
/ divisor-degree theory, so the divisor-theoretic derivation of Eq (225) from
Eq (224) is not formalised. What *is* captured and proved here is the arithmetic
heart, Eqs (225) ⟹ (226), with Eq (225) taken as the paper's established
intermediate inequality. This is a restricted (conditional) formalisation of the
claim, not the divisor derivation.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Claim511

/-- Fixed arXiv:2408.07764v2, Claim 5.1.1 (p.38, Eqs (225)–(226)): the arithmetic
step `2g − 2 ≥ 7a + (n'' − 2 + g − 7a) − n'' + M ⟹ M ≤ g` that yields `|P₀| ≤ g`.
The divisor-theoretic derivation of the hypothesis from Eq (224) is abstracted
(no AG function-field theory in Mathlib). -/
theorem source_claim_5_1_1
    (g a n'' M : ℕ)
    -- Eq (225): `2g - 2 ≥ deg(7A + E - D'') + M`, expanded with `deg(7A+E-D'') = g - 2`.
    (hdeg : 2 * (g : ℤ) - 2
        ≥ (7 * (a : ℤ) + ((n'' : ℤ) - 2 + (g : ℤ) - 7 * (a : ℤ)) - (n'' : ℤ)) + (M : ℤ)) :
    M ≤ g := by
  omega

end Qatlib.Papers.MagicDistill24.MainResults.Claim511
