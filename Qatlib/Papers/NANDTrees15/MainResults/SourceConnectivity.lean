/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NANDTrees15.MainResults.Model.NandTreeModel

set_option backward.isDefEq.respectTransparency false

/-!
# NANDTrees15 §4.1 — the st-connectivity dictionary

Fixed source: arXiv:1511.02235v1, §4.1, Lemmas 1–2 and Theorem 5.

* **Lemma 1** (p.10): for `x ∈ {0,1}^{2^{2d}}`, `x` is a 1-instance of depth-`2d`
  nand-tree evaluation iff `s` and `t` are connected in `G_d(x)`.  The paper proves
  this by the induction of Fig. 5 / eq. (7), which is exactly the recursion of
  `Instance.stConn`.
* **Lemma 2** (p.11): `nand_{2d}(x) = 0` iff `s'` and `t'` are connected in
  `G'_d(x)`.  The paper proves it by De Morgan (`nand(x) = 0 ↔ nandbar(x̄) = 1`)
  and the `G'_d` analogue of Lemma 1; here the two halves are combined in one
  induction because `dualConn` is the `∧/∨`-swapped connectivity recurrence.
* **Theorem 5** (p.11): `Ḡ'_d = Ḡ†_d`, the dual of `Ḡ_d`.  The proof is the
  induction over the edge-replacement of Fig. 7: replacing an edge in the primal by
  the 4-cycle corresponds to replacing its dual edge by the two-2-path gadget.  The
  Lean statement `dual (Gd d) = Gd' d` is that interior duality; the extra terminal
  edge `{s,t}` of `Ḡ_d` is common to both sides and is dual to `{s',t'}`, so it is
  identified on both sides (see the docstring of `theorem5_dual_graph`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDTrees15.MainResults

open Instance
open scoped ENNReal BigOperators

/-- **Lemma 1** (arXiv:1511.02235v1, p.10).  For every depth-`2d` nand-tree instance
`x`, `x` is a 1-instance of nand-tree evaluation iff the terminals `s` and `t` are
connected in the associated subgraph `G_d(x)` (Fig. 5 decomposition, eq. (7)). -/
theorem lemma1_nand_iff_connected {d : ℕ} (x : Instance d) :
    Instance.nandEval x = true ↔ Instance.stConn x := by
  induction x with
  | leaf b => cases b <;> simp [Instance.nandEval, Instance.stConn]
  | node4 a b c e ih0 ih1 ih2 ih3 =>
      simp only [Instance.nandEval, Instance.stConn, ih0.symm, ih1.symm, ih2.symm, ih3.symm,
        Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.or_eq_true_eq_eq_true_or_eq_true]

/-- **Lemma 2** (arXiv:1511.02235v1, p.11).  For every depth-`2d` nand-tree instance
`x`, `nand_{2d}(x) = 0` iff the dual terminals `s'` and `t'` are connected in
`G'_d(x)`.  This packages the paper's De Morgan step with the dual connectivity
recurrence `G'_d`. -/
theorem lemma2_zero_iff_dual_connected {d : ℕ} (x : Instance d) :
    Instance.nandEval x = false ↔ Instance.dualConn x := by
  induction x with
  | leaf b => cases b <;> simp [Instance.nandEval, Instance.dualConn]
  | node4 a b c e ih0 ih1 ih2 ih3 =>
      simp only [Instance.nandEval, Instance.dualConn, ih0.symm, ih1.symm, ih2.symm, ih3.symm,
        Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.or_eq_false_eq_eq_false_and_eq_false]

/-! ## Theorem 5: the dual graph

`G_d` and `G'_d` are two-terminal series–parallel networks.  `Gd d` builds `G_d`
(replace every edge by a 4-cycle); `Gd' d` builds the dual construction (replace
every edge by two 2-paths with the same three vertices).  `Net.dual` is the
series–parallel planar dual (exchange series and parallel). -/

/-- Two-terminal series–parallel networks with unit resistors. -/
inductive Net : Type
  /-- A single edge. -/
  | edge : Net
  /-- Series composition: identify the end of the first with the start of the second. -/
  | series : Net → Net → Net
  /-- Parallel composition: identify both pairs of terminals. -/
  | parallel : Net → Net → Net

namespace Net

/-- Substitute the network `g` for every edge. -/
def subst (g : Net) : Net → Net
  | edge => g
  | series a b => series (subst g a) (subst g b)
  | parallel a b => parallel (subst g a) (subst g b)

/-- Series–parallel planar dual: exchange series and parallel, keep each edge. -/
def dual : Net → Net
  | edge => edge
  | series a b => parallel (dual a) (dual b)
  | parallel a b => series (dual a) (dual b)

/-- Duality commutes with substituting a fixed gadget for every edge. -/
theorem dual_subst (g : Net) (a : Net) :
    dual (subst g a) = subst (dual g) (dual a) := by
  induction a with
  | edge => rfl
  | series a b iha ihb => simp only [subst, dual, iha, ihb]
  | parallel a b iha ihb => simp only [subst, dual, iha, ihb]

end Net

open Net

/-- The primal replacement gadget: a 4-cycle, i.e. two length-2 paths with distinct
middle vertices, as a two-terminal network `parallel(series(e,e), series(e,e))`. -/
def primGadget : Net := .parallel (.series .edge .edge) (.series .edge .edge)

/-- The dual replacement gadget: two 2-paths with the *same* three vertices, i.e.
`series(parallel(e,e), parallel(e,e))`. -/
def dualGadget : Net := .series (.parallel .edge .edge) (.parallel .edge .edge)

/-- The depth-`d` graph `G_d` as a two-terminal network: start from one edge and
replace every edge by the 4-cycle (§4.1). -/
def Gd : ℕ → Net
  | 0 => .edge
  | d + 1 => Net.subst primGadget (Gd d)

/-- The depth-`d` dual graph `G'_d`: start from one edge and replace every edge by the
two-2-path gadget (§4.1, Fig. 6). -/
def Gd' : ℕ → Net
  | 0 => .edge
  | d + 1 => Net.subst dualGadget (Gd' d)

/-- The dual of the 4-cycle gadget is the two-2-path gadget. -/
theorem dual_primGadget : Net.dual primGadget = dualGadget := rfl

/-- **Theorem 5** (arXiv:1511.02235v1, p.11).  `G'_d` is the dual graph of `G_d`:
in the paper's notation `Ḡ'_d = Ḡ†_d`.

The two-terminal networks `Gd d` / `Gd' d` are `G_d` / `G'_d`.  The bar in the paper
adds the common terminal edge `{s,t}` (resp. `{s',t'}`); that edge is present on both
sides and is dual to itself under the identification of Fig. 7(c), so removing it
leaves the interior identity proved here: the inductive step replaces a primal edge
by the 4-cycle (`primGadget`) while replacing its dual edge by the two-2-path gadget
(`dualGadget`), and `dual_subst` + `dual_primGadget` commute the two constructions. -/
theorem theorem5_dual_graph (d : ℕ) : Net.dual (Gd d) = Gd' d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [Gd, Gd', ← ih, Net.dual_subst, dual_primGadget]

end Qatlib.Papers.NANDTrees15.MainResults
