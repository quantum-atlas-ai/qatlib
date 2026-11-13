/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.ObliviousAmplificationSubgoalHami

set_option backward.isDefEq.respectTransparency false

/-!
# c015 — repo-only `ObliviousAmplificationSubgoal` cross-reference

This claim has **no source counterpart** in arXiv:1202.5822v1 (paper metadata marks
it `provenance_uncertain`, `lines = null`, and the source-extracted claim text says
so explicitly).  The repo contract and `Foundations/Projected/Qubitization.lean:303-305`
attribute a quadratic-walk fiber identity to this paper; that attribution is
incorrect, and the frozen contract already documents the corrected reading.  There
is therefore no source obligation to prove here.

The paper-layer entry re-exports the frozen declaration so the paper block has a
named anchor for the claim, and records that it is not a Childs-Wiebe result.
Reuses frozen
`Qatlib.Papers.HamLCUSim12.Multiproduct.obliviousAmplificationSubgoal`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.ObliviousAmplification

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Cross-reference (no source counterpart): the historical quadratic-walk fiber
identity `FiberProjector j0 * QubitizationWalk * Ket j0 ⊗ psi = (2x^2-1) * Ket j0 ⊗ psi`
for a Hermitian LCU input with `sum_j w_j U_j` acting as the scalar `x` on `psi`.
Not a Childs-Wiebe 2012 result; retained only for compatibility. -/
theorem oblivious_amplification_subgoal_crossref : ObliviousAmplificationSubgoal :=
  obliviousAmplificationSubgoal

end Qatlib.Papers.HamLCUSim12.Multiproduct.ObliviousAmplification
