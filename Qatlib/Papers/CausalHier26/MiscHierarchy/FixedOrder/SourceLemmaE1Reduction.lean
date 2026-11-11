/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.ReducedBlocks

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemmaE1Reduction — Lemma E.1 (fixed-order charge-block reduction)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma E.1, p. 35
(txt lines 1836-1866), Eqs. (171)-(175).

**Statement.**  Every reduced `A ≺ B` MISC feasible point can be averaged, without
changing `x_c`, over the independent phase rotations of the two resource channels
and over entrywise complex conjugation.  In the bases
`B00 = (|1⟩,|4⟩,|13⟩,|16⟩)`, `B_{0,-1} = (|3⟩,|15⟩)`, `B_{-1,0} = (|9⟩,|12⟩)` the
resulting blocks are

```
S00 = [[a,0,u,0],[0,b,0,-u],[u,0,g,0],[0,-u,0,h]],
S_{0,-1} = [[b,-u],[-u,h]],   S_{-1,0} = diag(m0,n0),
```

with `g + h = m0 + n0`, `a + b + m0 + n0 = 1`, the corresponding `T_c` blocks
symmetric with `diag C00 = 0`, `C_{0,-1} = K(r)`, `C_{-1,0} = K(t)`, and

```
x_c = v^T C00 v + 2 ε s (r + t),   v = (1, s, s, s^2)^T.
```

All matrices appearing as the second arguments of the certificate overlaps in
Eq. (200) are principal blocks of `S ± T_c` and are therefore positive
semidefinite.

**Modelling boundary.**  The reduced block tuple `SeqBlock` of
`Model/ReducedBlocks.lean` *is* this normal form; the finite linear system (176)
that produces it, and the averaging argument, are the paper's reduction and are
not re-derived.  What the present file records is the exact content of the block
data: the normalization equations (173), the coherence formula (175), and the
positive semidefiniteness of the six displayed principal blocks (the paper's
final sentence).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- Fixed arXiv:2609.08639v1, Lemma E.1, Eq. (172)-(175) and final sentence,
p. 36: a reduced `A ≺ B` MISC feasible block tuple has the normalization (173),
the coherence formula (175), and all six principal blocks of `S ± T_c` positive
semidefinite.

This is the exact block data used downstream by the certificate identity
(Lemma E.4, Eq. (200)) and by the equality analysis (Eq. (201)-(202)). -/
theorem source_lemma_E1_block_data (ε : ℝ) (B : SeqBlock) (h : SeqFeasible ε B) :
    B.g + B.h = B.m0 + B.n0 ∧
    B.a + B.b + B.m0 + B.n0 = 1 ∧
    seqXc ε B = quadForm (vvec ε) (seqC00 B) + 2 * ε * s ε * (B.r + B.t) ∧
    (seqS00 B + seqC00 B).PosSemidef ∧ (seqS00 B - seqC00 B).PosSemidef ∧
    (seqS0m1 B + Kmat B.r).PosSemidef ∧ (seqS0m1 B - Kmat B.r).PosSemidef ∧
    (seqSm10 B + Kmat B.t).PosSemidef ∧ (seqSm10 B - Kmat B.t).PosSemidef := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, rfl, h8, h9, h4, h5, h6, h7⟩

/-- Fixed arXiv:2609.08639v1, Lemma E.1, Eq. (175), p. 36: the coherence formula
`x_c = v^T C00 v + 2 ε s (r + t)`. -/
theorem source_lemma_E1_xc_formula (ε : ℝ) (B : SeqBlock) :
    seqXc ε B = quadForm (vvec ε) (seqC00 B) + 2 * ε * s ε * (B.r + B.t) := rfl

end Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder
