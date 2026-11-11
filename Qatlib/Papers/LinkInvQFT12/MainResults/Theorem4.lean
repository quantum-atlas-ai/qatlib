/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults.Theorem4 — complexity of the plat closure (c003)

Krovi--Russell, arXiv:1210.1550 (v2 PDF, §5, p.16–17, Theorem 4; extraction line 638).

The source theorem is registered here as a `Prop`-valued contract of the abstract model
in `SourceModel`; this layer does not prove it.  The model supplies only the abstract
predicate `CompleteFor`; there is no formal reduction framework, no promise-BPP/promise-SBP
class, and no counting-class completeness theorem in this layer.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- **Theorem 4** (arXiv:1210.1550, p.16–17, §5).  Let `Pl(b)` be the plat closure of a
braid whose strands are colored by any conjugacy class of the alternating group `Aₘ`,
`m ≥ 5`, having at least four fixed points.  Then additively approximating the plat
closure is `BPP`-complete, multiplicatively approximating it is `SBP`-complete, and
exact evaluation is `#P`-complete.

The group is `G = ↥(alternatingGroup (Fin m))`; the conjugacy class is the one of the
fluxon `Λ` (`Λ.chargeDim = 1`), and its representative `Λ.flux.val` has at least four
fixed points (`FourFixedPoints`).  `CompleteFor` is the model's abstract completeness
predicate (see `SourceModel`).

This is a statement registration, not a proof: the reduction framework and the complexity
classes named in the source are not formalised, and Lemma 5 — the source of `BPP`-hardness
— is itself only a registered contract in this layer. -/
def theorem4_plat_closure_completeness
    (m : ℕ) (hm : 5 ≤ m)
    (I : ClosureInvariants ↥(alternatingGroup (Fin m)))
    (Λ : DGIrrep ↥(alternatingGroup (Fin m)))
    (hfluxon : Λ.chargeDim = 1)
    (hfix : FourFixedPoints Λ.flux.val) :
    Prop :=
  CompleteFor ComplexityClass.BPP
      (fun x : BraidInstance => I.platClosure Λ x.word) ∧
    CompleteFor ComplexityClass.SBP
      (fun x : BraidInstance => I.platClosure Λ x.word) ∧
    CompleteFor ComplexityClass.SharpP
      (fun x : BraidInstance => I.platClosure Λ x.word)

end Qatlib.Papers.LinkInvQFT12.MainResults
