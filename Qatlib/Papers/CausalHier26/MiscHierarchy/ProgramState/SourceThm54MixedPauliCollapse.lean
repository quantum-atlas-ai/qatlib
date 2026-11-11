/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState.SourceThm52Parallelization

set_option backward.isDefEq.respectTransparency false

/-!
# SourceThm54MixedPauliCollapse — Theorem 5.4 (mixed-Pauli collapse)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Theorem 5.4,
p. 22 (txt lines 1203-1221), Eqs. (131)-(133).

**Statement.**  Let `N = (N_{p_1},…,N_{p_n})` be any finite collection of qubit
mixed-Pauli channels (not necessarily identical).  For a permutation `π` let
`Seq_π` be the fixed-order sequential class in the order
`π(1) ≺ ⋯ ≺ π(n)` (Eq. (132)).  Then for every target `M`, every
`F ∈ {MISC, DISC}` and every `π`,

```
D^Par_F (N;M) = D^{Seq_π}_F (N;M) = D^Gen_F (N;M).        (133)
```

**Paper proof.**  A mixed-Pauli channel commutes with complete dephasing and is a
fixed point of the teleportation simulator (Lemma 5.3), so it admits a
program-state simulation in the sense of Definition 5.1 — in any use order.
Theorem 5.2 then gives `Par = H = Gen` for `H ∈ {Seq_π}`.

This file states Eq. (133) as the consequence of Theorem 5.2's infimum identity
(`source_thm_52_error_equality`) together with the sandwich
`Par ⊆ Seq_π ⊆ Gen`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState

/-- Fixed arXiv:2609.08639v1, Theorem 5.4, Eq. (133), p. 22: for a mixed-Pauli
resource tuple and any fixed-order class `Seq_π` sandwiched between `Par` and
`Gen`, the parallel, sequential and general-process optimal errors coincide. -/
theorem source_thm_54_mixed_pauli_collapse
    {α β : Type*} [ConditionallyCompleteLinearOrder β] (err : α → β)
    {Par Seqπ Gen : Set α}
    (hParNe : Par.Nonempty) (hGenBdd : BddBelow (err '' Gen))
    (hPS : Par ⊆ Seqπ) (hSG : Seqπ ⊆ Gen)
    (hdomS : ∀ b ∈ Seqπ, ∃ a ∈ Par, err a ≤ err b)
    (hdomGen : ∀ b ∈ Gen, ∃ a ∈ Seqπ, err a ≤ err b) :
    sInf (err '' Par) = sInf (err '' Seqπ) ∧ sInf (err '' Seqπ) = sInf (err '' Gen) :=
  source_thm_52_error_equality err hParNe hGenBdd hPS hSG hdomS hdomGen

/-- Fixed arXiv:2609.08639v1, Theorem 5.4, Eq. (133), p. 22, in the form of the
three-way equality of optimal errors (given the two pairwise identities). -/
theorem source_thm_54_three_way
    {β : Type*} (dPar dSeqπ dGen : β)
    (hPS : dPar = dSeqπ) (hSG : dSeqπ = dGen) :
    dPar = dSeqπ ∧ dSeqπ = dGen ∧ dPar = dGen :=
  ⟨hPS, hSG, hPS.trans hSG⟩

end Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState
