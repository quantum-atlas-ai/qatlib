/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# NANDTrees15 — the object layer of arXiv:1511.02235

Fixed source: *NAND-Trees, Average Choice Complexity, and Effective Resistance*,
arXiv:1511.02235 (2015).  Everything in this module is a formal rendering of the
paper's definitions, not a new mathematical assumption.

## Instances

A depth-`2d` nand-tree instance is an element of `{0,1}^{2^{2d}}`, i.e. one input
bit for each of the `4^d = 2^{2d}` leaves.  `Instance d` is the complete quaternary
leaf tree of depth `d`; it is exactly the indexed family of leaves used in §4.1
(Fig. 4).  `nandEval` is the recurrence of eq. (7),

`nand_{2(d+1)}(x) = (nand_{2d}(x00) ∧ nand_{2d}(x01)) ∨ (nand_{2d}(x10) ∧ nand_{2d}(x11))`,

with the depth-0 tree equal to the identity.

## Graphs and connectivity

`G_d` is defined in §4.1 by replacing every edge with a 4-cycle.  Written as a
two-terminal network this is `G_{d+1}(x) = parallel(series(G_d(x00),G_d(x01)),
series(G_d(x10),G_d(x11)))` (Fig. 5), so s–t connectivity satisfies

`connected (node4 x00 x01 x10 x11) ↔ (connected x00 ∧ connected x01) ∨ (connected x10 ∧ connected x11)`.

`stConn` is the s–t connectivity relation *computed through this recursive graph
decomposition*; `dualConn` is the corresponding relation for `G'_d(x)`, whose edges
are present on the complement bits and whose series/parallel structure is dual:
`(connected x00 ∨ connected x01) ∧ (connected x10 ∨ connected x11)`.

## Effective resistance

For series–parallel networks with unit resistors the effective resistance is fixed by
two recursions: resistances add in series, conductances add in parallel.  `resA` is
this quantity for `G_d(x)`; `resB` is the same for the dual graph `G'_d(x)`.  Values
live in `ℝ≥0∞` so that `⊤` records disconnectedness (paper: `R_{s,t}(G)=∞` when s,t are
not connected, Definition 7).

## Average choice complexity

`avgChoiceA`/`avgChoiceB` implement the recursion that the paper derives from
Definition 9 and eqs. (4), (8): at a node with child branch sums `s0,s1` the value is
`(1/2)·c(r)·min{s0,s1}` with `c(r)` the criticality of eq. (4); for the series–parallel
structure this is exactly the parallel/series resistance recursion.  `choiceComplexity`
is Definition 9's `C(x) = min{C_A(x), C_B(x)}` (eq. (5)).

The identity `s0·s1/(s0+s1)` between the criticality form (eq. (11)) and the parallel
resistance is recorded separately (`parallelRes_eq_criticalityForm`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDTrees15.MainResults

open scoped ENNReal BigOperators

/-- A depth-`2d` nand-tree instance: one `Bool` per leaf of a complete quaternary
tree of depth `d` (the `2^{2d}` input bits, §4.1 Fig. 4). -/
inductive Instance : ℕ → Type
  /-- A single leaf bit (depth-0 instance, `nand_0 = id`). -/
  | leaf : Bool → Instance 0
  /-- Combine four depth-`d` subinstances into a depth-`(d+1)` instance. -/
  | node4 : {d : ℕ} → Instance d → Instance d → Instance d → Instance d → Instance (d + 1)

namespace Instance

/-- Nand-tree evaluation, eq. (7) of §4.1:
`nand_{2(d+1)}(x) = (nand_{2d}(x00) ∧ nand_{2d}(x01)) ∨ (nand_{2d}(x10) ∧ nand_{2d}(x11))`,
with the depth-0 tree the identity. -/
def nandEval : {d : ℕ} → Instance d → Bool
  | _, .leaf b => b
  | _, .node4 x00 x01 x10 x11 =>
      (nandEval x00 && nandEval x01) || (nandEval x10 && nandEval x11)

/-- Bitwise complement of an instance (used in Lemma 2's De Morgan reduction). -/
def neg : {d : ℕ} → Instance d → Instance d
  | _, .leaf b => .leaf (!b)
  | _, .node4 x00 x01 x10 x11 => .node4 (neg x00) (neg x01) (neg x10) (neg x11)

/-- The De Morgan dual formula `nandbar` of §4.1: same leaves, `∧` and `∨` exchanged,
which makes the top connective `∨` become `∧`.  The paper uses it because the dual
graph's connectivity is the `∧/∨`-swapped recurrence. -/
def dualEval : {d : ℕ} → Instance d → Bool
  | _, .leaf b => b
  | _, .node4 x00 x01 x10 x11 =>
      (dualEval x00 || dualEval x01) && (dualEval x10 || dualEval x11)

/-- s–t connectivity of the subgraph `G_d(x)` of §4.1, computed through the recursive
graph decomposition of Fig. 5 (edge present at a leaf iff the bit is `1`). -/
def stConn : {d : ℕ} → Instance d → Prop
  | _, .leaf b => b = true
  | _, .node4 x00 x01 x10 x11 =>
      (stConn x00 ∧ stConn x01) ∨ (stConn x10 ∧ stConn x11)

/-- s'–t' connectivity of the dual subgraph `G'_d(x)`: the edges are present on the
complement bits, and the series/parallel decomposition is swapped (planar dual of
Fig. 5). -/
def dualConn : {d : ℕ} → Instance d → Prop
  | _, .leaf b => b = false
  | _, .node4 x00 x01 x10 x11 =>
      (dualConn x00 ∨ dualConn x01) ∧ (dualConn x10 ∨ dualConn x11)

/-- The leaf bits of an instance, left to right (the `2^{2d}` input bits of §4.1). -/
def leaves : {d : ℕ} → Instance d → List Bool
  | _, .leaf b => [b]
  | _, .node4 x00 x01 x10 x11 => leaves x00 ++ leaves x01 ++ leaves x10 ++ leaves x11

/-- An instance has exactly `4^d = 2^{2d}` leaves. -/
theorem leaves_length {d : ℕ} (x : Instance d) : (leaves x).length = 4 ^ d := by
  induction x with
  | leaf b => rfl
  | node4 a b c e ih0 ih1 ih2 ih3 =>
      simp only [leaves, List.length_append, ih0, ih1, ih2, ih3, pow_succ]
      ring

/-- The instance viewed as a Boolean function on the leaf index set `Fin (4^d)`; this
is the oracle input to a query algorithm evaluating the nand-tree (§4.1, Fig. 4). -/
def leafFun {d : ℕ} (x : Instance d) (i : Fin (4 ^ d)) : Bool :=
  (leaves x).get ⟨i.1, by rw [leaves_length]; exact i.2⟩

end Instance

open Instance

/-- Parallel composition of two unit-resistance networks: conductances add, so
`R = (R₁⁻¹ + R₂⁻¹)⁻¹` with the conventions `∞⁻¹ = 0` and `0⁻¹ = ∞`. -/
def parallelRes (p q : ℝ≥0∞) : ℝ≥0∞ := (p⁻¹ + q⁻¹)⁻¹

/-- Effective resistance `R_{s,t}(G_d(x))` (Definition 7), via the series–parallel
recursions: series adds resistances, parallel is `parallelRes`.  `⊤` means the
terminals are not connected. -/
def resA : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then 1 else ⊤
  | _, .node4 x00 x01 x10 x11 => parallelRes (resA x00 + resA x01) (resA x10 + resA x11)

/-- Effective resistance `R_{s',t'}(G'_d(x))` of the dual graph (Definition 7 applied
to the dual edge set: an edge of `G'_d` is present iff its primal variable is `0`,
and the series/parallel structure is swapped). -/
def resB : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then ⊤ else 1
  | _, .node4 x00 x01 x10 x11 => parallelRes (resB x00) (resB x01) + parallelRes (resB x10) (resB x11)

/-- Average choice complexity `C_A(x)` (Definition 9) at the recursion of eqs. (4), (8):
at a node with branch sums `s0 = C_A(x00)+C_A(x01)`, `s1 = C_A(x10)+C_A(x11)`,
`C_A = (1/2)·c(r)·min{s0,s1}`, which is the parallel-resistance recursion. -/
def avgChoiceA : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then 1 else ⊤
  | _, .node4 x00 x01 x10 x11 => parallelRes (avgChoiceA x00 + avgChoiceA x01) (avgChoiceA x10 + avgChoiceA x11)

/-- Average choice complexity `C_B(x)` (Definition 9, player-B recursion). -/
def avgChoiceB : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then ⊤ else 1
  | _, .node4 x00 x01 x10 x11 => parallelRes (avgChoiceB x00) (avgChoiceB x01) + parallelRes (avgChoiceB x10) (avgChoiceB x11)

/-- The paper's `C(x) = min{C_A(x), C_B(x)}` (eq. (5)). -/
def choiceComplexity {d : ℕ} (x : Instance d) : ℝ≥0∞ := min (avgChoiceA x) (avgChoiceB x)

/-- `C_Z(x)` for `Z ∈ {A,B}`: `Z = true` is Player A, `Z = false` is Player B. -/
def choiceZ (Z : Bool) {d : ℕ} (x : Instance d) : ℝ≥0∞ :=
  if Z then avgChoiceA x else avgChoiceB x

/-- Fault complexity `F_A(x)` of eq. (6): the maximum over A-winning paths of
`2^{#faults}`.  The root of an A-winnable subtree is a fault exactly when exactly one
of the two branches `{x00,x01}` / `{x10,x11}` is winnable (one branch sum finite), in
which case it contributes a factor `2`; the value is the max over the children. -/
def faultA : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then 1 else ⊤
  | _, .node4 x00 x01 x10 x11 =>
      (if (resA x00 + resA x01 = ⊤) = (resA x10 + resA x11 = ⊤) then 1 else 2) *
        max (max (faultA x00) (faultA x01)) (max (faultA x10) (faultA x11))

/-- Fault complexity `F_B(x)` of eq. (6), player-B version. -/
def faultB : {d : ℕ} → Instance d → ℝ≥0∞
  | _, .leaf b => if b then ⊤ else 1
  | _, .node4 x00 x01 x10 x11 =>
      (if (parallelRes (resB x00) (resB x01) = ⊤) =
          (parallelRes (resB x10) (resB x11) = ⊤) then 1 else 2) *
        max (max (faultB x00) (faultB x01)) (max (faultB x10) (faultB x11))

/-- The paper's fault complexity `F(x) = min{F_A(x), F_B(x)}` (eq. (6)). -/
def faultComplexity {d : ℕ} (x : Instance d) : ℝ≥0∞ := min (faultA x) (faultB x)

end Qatlib.Papers.NANDTrees15.MainResults
