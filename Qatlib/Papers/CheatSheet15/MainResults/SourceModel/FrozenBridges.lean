/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.MainResults.SourceModel.Measures
public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetRandomizedLowerBoundKfor
public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetQuantumUpperBoundKfor

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Bridges to the frozen cheat-sheet results

Two of the paper's claims already have a committed counterpart in the frozen
library, and the paper-layer statements reuse them rather than re-proving them:

* `CheatSheetRandomizedLowerBound`
  (`RQSeparation.BornBaseline.CheatSheetRandomizedLowerBoundStat.CheatSheetRandomizedLowerBound`)
  is the distributional core of ABK16 Lemma 6 (p. 12): any bounded-error randomised
  program of depth `T` solving the total cheat-sheet function needs at least `t`
  queries whenever `t` beats the hard distribution within `1/(12c)` advantage and
  `6t ≤ 2^c`.  It is proved in
  `RQSeparation.BornBaseline.CheatSheetRandomizedLowerBoundKfor.CheatSheetRandomizedLowerBound`
  (theorem `cheatSheetRandomizedLowerBound`).
* `CheatSheetQuantumUpperBound`
  (`...CheatSheetQuantumUpperBoundStat.CheatSheetQuantumUpperBound`) is the
  constructive half of ABK16 Lemma 17 (p. 21): from circuits for `g` and `φ` on the
  complete-subroutine workspace it builds a circuit of `c (q_g + q_φ)` standard
  oracle calls solving `f_CS`.  It is proved in
  `...CheatSheetQuantumUpperBoundKfor.CheatSheetQuantumUpperBound`
  (theorem `cheatSheetQuantumUpperBound`).

The two theorems below are pure bridges: they restate the frozen contracts in this
file so that the claim files can cite a single paper-layer name, and they are proved
by `exact` of the frozen theorem (no hidden axioms).
-/

set_option autoImplicit false

open scoped Classical ENNReal
open Qatlib.Papers.CheatSheet15.BornBaseline
open Qatlib.Papers.CheatSheet15.MainResults.SourceModel

namespace Qatlib.Papers.CheatSheet15.MainResults.SourceModel

/-- ABK16 Lemma 6 (distributional core), frozen contract.  Frozen FQN:
`RQSeparation.BornBaseline.cheatSheetRandomizedLowerBound`. -/
theorem frozenCheatSheetRandomizedLowerBound :
    CheatSheetRandomizedLowerBound :=
  cheatSheetRandomizedLowerBound

/-- ABK16 Lemma 17 (quantum upper bound), frozen contract.  Frozen FQN:
`RQSeparation.BornBaseline.cheatSheetQuantumUpperBound`. -/
theorem frozenCheatSheetQuantumUpperBound :
    CheatSheetQuantumUpperBound :=
  cheatSheetQuantumUpperBound

/-- On a total function `g`, the frozen `cheatSheetFun` is exactly the paper's
`f_CS`: `cheatSheet` applied to the totalisation of `g` is `cheatSheetFun g`. -/
theorem cheatSheet_total_eq_cheatSheetFun {c M κ : ℕ} (hκ : 0 < κ) (g : BitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) :
    cheatSheet (c := c) hκ (PartialBitFun.total g) φ = cheatSheetFun (c := c) g φ := by
  have hg : (PartialBitFun.total g).totalize = g := by
    funext x
    simp [PartialBitFun.totalize]
  funext z
  show cheatSheetFun (c := c) ((PartialBitFun.total g).totalize) φ z = cheatSheetFun (c := c) g φ z
  rw [hg]

/-- The certifying promise for a total function is the paper's Definition 14 with
`dom = Set.univ`. -/
theorem isCertifyingFun_total_iff {M κ : ℕ} (hκ : 0 < κ) (g : BitFun (Fin M))
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) :
    IsCertifyingFun M κ hκ (PartialBitFun.total g) φ ↔ IsCertifying M κ hκ Set.univ g φ := by
  have hg : (PartialBitFun.total g).totalize = g := by
    funext x
    simp [PartialBitFun.totalize]
  simp [IsCertifyingFun, PartialBitFun.total_dom, hg]

end Qatlib.Papers.CheatSheet15.MainResults.SourceModel
