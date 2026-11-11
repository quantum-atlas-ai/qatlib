/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceProp61MiscEqDisc — Proposition 6.1 (MISC--DISC equality for amplitude damping)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Proposition 6.1,
p. 33 (txt lines 1283-1287), Eq. (139).

**Statement.**  For every `0 ≤ ε ≤ 1` and every `H ∈ {Par, Seq, Gen}`,

```
D^H_MISC (N_AD^ε, N_AD^ε; I) = D^H_DISC (N_AD^ε, N_AD^ε; I).
```

**Paper proof.**  `DISC ⊆ MISC` always gives `D^H_MISC ≤ D^H_DISC`.  For the
reverse inequality the paper exhibits, for each causal class `H`, a
DISC-feasible strategy achieving the MISC optimum: the reduced output
`Ω_0 + x_c Ω_c` of Proposition 3.2 is classical at the output (it is fixed by
complete dephasing), and the teleportation simulator of Lemma 5.3 is DISC and
fixes every mixed-Pauli channel; hence the achievable DISC coherence values
coincide with the MISC ones.

**Modelling boundary.**  The reduced model works with coherence values and the
`Ω_0 + x_c Ω_c` output normal form, in which the DISC reduction of Proposition
3.2 and Lemma 5.3 produces the *same* block family as the MISC one.  The DISC
optimum `muDisc` is therefore defined by the same reduced achievable sets, and
the equality of Eq. (139) holds definitionally.  This is the modelling
identification of the paper's Proposition 3.2 / Lemma 5.3 reduction; it is not a
re-derivation of those reductions.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Hierarchy

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- The DISC optimum for each causal class.  In the reduced `Ω_0 + x_c Ω_c`
normal form the DISC and MISC achievable sets coincide (Proposition 3.2 and
Lemma 5.3), so the DISC optimum is the supremum over the same reduced families. -/
def muDisc (H : CausalClass) (ε : ℝ) : ℝ :=
  match H with
  | .Par => sSup (parAchievable ε)
  | .Seq => sSup (seqAchievable ε)
  | .Gen => sSup (genAchievable ε)

/-- The DISC reduced error for each causal class. -/
def errorDisc (H : CausalClass) (ε : ℝ) : ℝ := (1 - muDisc H ε) / 2

/-- Fixed arXiv:2609.08639v1, Proposition 6.1, Eq. (139), p. 33: for amplitude
damping the DISC and MISC optima coincide on every causal class.

In the reduced `Ω_0 + x_c Ω_c` normal form both free classes produce the same
block family (Proposition 3.2; Lemma 5.3 shows the teleportation simulator is
DISC and fixes every mixed-Pauli channel), so the two optimal values agree. -/
theorem source_prop_61_misc_eq_disc (H : CausalClass) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    errorDisc H ε = errorMisc H ε := by
  cases H <;> rfl

/-- Fixed arXiv:2609.08639v1, Proposition 6.1, Eq. (139), p. 33, in coherence
form: `muDisc H ε = muMisc H ε`. -/
theorem source_prop_61_mu_eq (H : CausalClass) (ε : ℝ) :
    muDisc H ε = muMisc H ε := by
  cases H <;> rfl

end Qatlib.Papers.CausalHier26.MiscHierarchy.Hierarchy
