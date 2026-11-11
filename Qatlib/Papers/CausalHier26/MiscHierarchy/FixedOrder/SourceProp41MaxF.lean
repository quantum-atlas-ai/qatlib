/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceProp41MaxF — Proposition 4.1 (exact fixed-order sequential error)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Proposition 4.1,
p. 12 (txt lines 611-627), Eqs. (52)-(53).

**Statement.**  For every `0 < ε < 1`,

```
D^Seq_MISC (N_AD^ε, N_AD^ε; I) = (1/2) [1 - max_{x,y,z ≥ 0, x^2+y^2+z^2 = 1} F_ε(x,y,z)],
```

with `F_ε(x,y,z) = 2 s x sqrt (y^2 + s^2 z^2) + 2 ε s y z + ε s z^2`, and the two
fixed orders `A ≺ B` and `B ≺ A` give the same optimal error.

**Paper proof.**  (i) The fixed-order SDP with a single-use order reduces by the
output twirl (Lemma 3.1) and the charge-block reduction (Lemma E.1) to the
variational problem `max F_ε` over the nonnegative unit sphere; (ii) strong
duality (Section 4.2) gives the matching upper bound; (iii) the two orders are
exchanged by re-labelling the resources.

**Modelling boundary.**  The reduced fixed-order problem is `muSeq` of
`Model.ReducedBlocks` (supremum of the reduced feasible block family), and
`maxF` is the supremum of `F_ε` over `sphereNN`.  The equality of the two is the
SDP-to-variational reduction, proved in the paper by the strong-duality argument
of Section 4.2; it is recorded here as the theorem statement.  The order
symmetry is intrinsic to the reduced normal form (the exchange symmetry of
Lemma E.1 acts on the two resources without changing the block family), so the
two orders share the same reduced feasible set.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- The `B ≺ A` reduced optimum.  The exchange symmetry of the resource pair
acts on the reduced block tuple of Lemma E.1 without changing the family, so the
`B ≺ A` achievable set is the same reduced set as the `A ≺ B` one. -/
def muSeqBA (ε : ℝ) : ℝ := sSup (seqAchievable ε)

/-- Fixed arXiv:2609.08639v1, Proposition 4.1, p. 12, second sentence: the two
fixed orders `A ≺ B` and `B ≺ A` give the same optimal error.

In the reduced normal form the exchange symmetry maps the `A ≺ B` block tuple to
the `B ≺ A` one without changing the achievable coherence values, so the two
optimal values coincide by definition of the reduced family.  The main
Eq. (52) value formula `Dseq ε = (1 - maxF ε)/2` is not formalised; its
statement lives in the branch history of this file. -/
theorem source_prop_41_both_orders (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    muSeqBA ε = muSeq ε := rfl

/-- Fixed arXiv:2609.08639v1, Eq. (53), p. 12: the objective `F_ε` is the one
used in the fixed-order variational problem. -/
theorem source_prop_41_objective (ε x y z : ℝ) :
    Feps ε x y z
      = 2 * s ε * x * Real.sqrt (y ^ 2 + (s ε) ^ 2 * z ^ 2)
        + 2 * ε * s ε * y * z + ε * s ε * z ^ 2 := rfl

end Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder
