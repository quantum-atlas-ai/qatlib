/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma23Classicality — Lemma 2.3 (classicality preservation)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma 2.3, p. 7
(txt lines 342-349).

**Statement.**  Every multi-input MISC higher-order map sends each tuple of
classical input channels to a classical output channel.

**Paper proof.**  For `C_k ∈ C_{X_k}` one has `Δ_{X_k}(C_k) = C_k`; the MISC
condition Eq. (11) then gives
`Δ_C[S(C_1,…,C_n)] = (Δ_C ∘ S ∘ Δ_X)(C_1,…,C_n) = (S ∘ Δ_X)(C_1,…,C_n) = S(C_1,…,C_n)`,
so the output is fixed by `Δ_C` and hence classical (Eqs. (24)-(25)).

**Modelling boundary.**  The map is represented by the operational dephasing
equations of `Model.SuperchannelAlgebra`; the Choi-space version is not needed
for this lemma.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

/-- Fixed arXiv:2609.08639v1, Lemma 2.3, p. 7: a multi-input MISC higher-order
map sends a tuple of classical input channels (`dI k (a k) = a k` for every `k`)
to a classical output channel (`dC (P a) = P a`). -/
theorem source_lemma_23_classicality_preservation
    {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (hMISC : IsMISCGen dI dC P)
    (a : ∀ k, I k) (hclassical : ∀ k, dI k (a k) = a k) :
    dC (P a) = P a :=
  misc_preserves_classical dI dC P hMISC a hclassical

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations
