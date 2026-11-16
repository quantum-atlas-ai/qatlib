/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.U1SeventhExactThirdLevelCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Lemma 3.1.1 (arXiv:2408.07764v2, pp.23–24, Eqs (120), (139)–(141))

With `q = p^s`, `p = 2`, `s ≥ 5`, the diagonal gate
`U_1^{(7)} = ∑_γ exp[iπ tr(γ⁷)] |γ⟩⟨γ|` is non-Clifford and lies in the third
level of the Clifford hierarchy: it conjugates every Pauli to a Clifford, but is
itself not Clifford.

The frozen result `triorthogonal..u1SeventhExactThirdLevel` is stated for the
fixed field `q = 2^10` (i.e. `s = 10`), which is the field used in Theorem 5.1
(`s = 10`, `s ≢ 0 mod 3`); it does **not** claim the general `s ≥ 5` instance.

This is the frozen result
`MagicDistill.Triorthogonal.u1SeventhExactThirdLevel`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Lemma311

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Fixed arXiv:2408.07764v2, Lemma 3.1.1 (pp.23–24, Eqs (139)–(141)), at the
field `q = 2^10`: `U_1^{(7)}` conjugates every Pauli to a Clifford (third level)
but is not itself Clifford.
Reuses `MagicDistill.Triorthogonal.u1SeventhExactThirdLevel`
(restricted to `s = 10`; the paper's general `s ≥ 5` is not separately formalised). -/
theorem source_lemma_3_1_1 :
    InQuditThirdLevel u1Seventh ∧ ¬ IsQuditClifford u1Seventh :=
  u1SeventhExactThirdLevel

end Qatlib.Papers.MagicDistill24.MainResults.Lemma311
