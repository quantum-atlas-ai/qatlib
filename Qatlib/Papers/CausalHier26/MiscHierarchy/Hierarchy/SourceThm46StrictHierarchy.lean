/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder.SourceProp41MaxF

set_option backward.isDefEq.respectTransparency false

/-!
# SourceThm46StrictHierarchy — Theorem 4.6 (strict MISC causal hierarchy)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Theorem 4.6,
p. 18 (txt lines 932-936), Eq. (92).

**Statement.**  For every `0 < ε < 1`,

```
D^Par_MISC (N^ε, N^ε; I) > D^Seq_MISC (N^ε, N^ε; I) > D^Gen_MISC (N^ε, N^ε; I),
```

and the two fixed orders `A ≺ B` and `B ≺ A` give the same sequential value.

**Modelling boundary.**  The strict separation half combines Lemma 4.3
(`muPar < muSeq`) and Lemma 4.5 (`muSeq < muGen`) through `D^H = (1 - μ^H)/2`;
those two analytic separation lemmas are not formalised (their statements live
in the branch history of this file), so only the order-independence half is
recorded here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Hierarchy

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model
open Qatlib.Papers.CausalHier26.MiscHierarchy.FixedOrder

/-- Fixed arXiv:2609.08639v1, Theorem 4.6, p. 18, second sentence: the two fixed
orders `A ≺ B` and `B ≺ A` give the same sequential error, via Proposition 4.1's
order symmetry (definitional in the reduced normal form). -/
theorem source_thm_46_order_independent (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    (1 - muSeqBA ε) / 2 = (1 - muSeq ε) / 2 := by
  rw [source_prop_41_both_orders ε h0 h1]

end Qatlib.Papers.CausalHier26.MiscHierarchy.Hierarchy
