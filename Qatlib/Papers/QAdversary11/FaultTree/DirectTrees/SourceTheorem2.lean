/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration.SourceLemma1
import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan

set_option backward.isDefEq.respectTransparency false

/-!
# DirectTrees — paper Theorem 2 (k-Fault Direct Trees need `O(w^k)` queries)

Kimmel, *Quantum Adversary (Upper) Bound*, fixed arXiv:1101.0797v5 (16 May 2013).
Definition 2 (p. 6) and Theorem 2 (p. 6; proof pp. 7–8, Eq. (11)–(12)).

The paper models a *Direct Tree* for a direct Boolean function `f` with `n`
inputs as a depth-`d`, `n`-partite complete evaluation tree; each internal node
has `n` children, each labelled fault/trivial, and a designated set of *strong*
children (Definition 2). Its `κ` label is

* `κ(leaf) = 0`;
* `κ(node)` = `max` of `κ` over strong children when the node is trivial;
* `κ(node)` = `1 + max` of `κ` over strong children when the node is a fault.

A tree is `k`-fault when `κ(root) ≤ k`. Theorem 2 proves that such a tree can be
evaluated with `O(w^k)` queries for a constant `w` depending only on `f`.

Contents of this file:

* the inductive tree model `DirectTree` with `kappa` (Definition 2) and the
  recursive witness-size upper bound `wsize` (Eq. (11)–(12));
* `wsize_le_pow_kappa`: the core induction `wsize v ≤ w ^ kappa v` for `w ≥ 1`,
  which is exactly the "inductive proof on `k`" of Theorem 2 specialised to the
  recursion laws (11)/(12);
* `kFault_witnessSize_le_pow`: the `k`-fault corollary `wsize root ≤ w^k`;
* `directTree_query_bound`: the final algorithmic step — if the span-program
  witness size (equivalently, by span-program duality, the adversary) of the
  tree function is at most `w^k`, then bounded-error quantum query complexity is
  `O(w^k)`, via the tightness package `Q = Θ(ADV)` and Theorem 1.

Gap: the library has no span-program object, so the bridge "witness size
`≤ w^k` ⟹ adversary `≤ w^k`" (Eq. (8) of the paper, from [9]) is supplied as
the explicit hypothesis `hAdv` of `directTree_query_bound`; see
`SpanProgramComposition/SourceLemma3.lean` for the span-program model.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.QAdversary11.FaultTree.DirectTrees

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration

/-- A depth-indexed `n`-ary direct evaluation tree (paper Section 4, before
Definition 2). `leaf` is a depth-`0` tree. `node ch fault strong` is an internal
node with `n` children `ch`, a fault/trivial label `fault`, and the finite set
`strong` of indices of its strong children (Definition 2). -/
inductive DirectTree (n : ℕ) : Type
  | leaf : DirectTree n
  | node : (Fin n → DirectTree n) → Bool → Finset (Fin n) → DirectTree n

namespace DirectTree

/-- Paper Definition 2: the `κ` label of a node. Leaves get `0`; a trivial node
gets the max of `κ` over its strong children; a fault node gets `1` plus that
max. On an empty strong set the max is read as `0` (the `Finset.sup` bottom). -/
def kappa {n : ℕ} : DirectTree n → ℕ
  | leaf => 0
  | node ch fault strong =>
      (if fault then 1 else 0) + strong.sup (fun i => (ch i).kappa)

/-- The recursive span-program witness-size upper bound of Eq. (11)–(12): leaves
have size `1`, a trivial node multiplies by `1`, a fault node by `w`, and the
child maximum is taken over the strong children only. -/
def wsize {n : ℕ} (w : ℝ≥0∞) : DirectTree n → ℝ≥0∞
  | leaf => 1
  | node ch fault strong =>
      (if fault then w else 1) * strong.sup (fun i => (ch i).wsize w)

/-- **Core induction of Theorem 2** (Eq. (11)–(12), pp. 7–8): for any weight
`w ≥ 1`, the recursive witness size of a tree is at most `w` to the power of its
`κ` label. This is the "inductive proof on `k`" with the fault/trivial step
folding the factor `w` (fault) or `1` (trivial) into the `κ` increment. -/
theorem wsize_le_pow_kappa {n : ℕ} (w : ℝ≥0∞) (hw : 1 ≤ w) :
    ∀ v : DirectTree n, v.wsize w ≤ w ^ v.kappa := by
  intro v
  induction v with
  | leaf => simp [wsize, kappa]
  | node ch fault strong ih =>
      have h1 : strong.sup (fun i => (ch i).wsize w) ≤
          w ^ strong.sup (fun i => (ch i).kappa) := by
        have hsup1 : strong.sup (fun i => (ch i).wsize w) ≤
            strong.sup (fun i => w ^ (ch i).kappa) := by
          refine Finset.sup_le ?_
          intro i hi
          exact (ih i).trans (Finset.le_sup (s := strong) (f := fun i => w ^ (ch i).kappa) hi)
        have hsup2 : strong.sup (fun i => w ^ (ch i).kappa) ≤
            w ^ strong.sup (fun i => (ch i).kappa) := by
          refine Finset.sup_le ?_
          intro i hi
          exact pow_le_pow_right₀ hw (Finset.le_sup (s := strong)
            (f := fun i => (ch i).kappa) hi)
        exact hsup1.trans hsup2
      cases fault
      · simp only [wsize, kappa, Bool.false_eq_true, if_false, Nat.cast_zero, zero_add,
          one_mul]
        exact h1
      · simp only [wsize, kappa, if_true, Nat.cast_one]
        calc w * strong.sup (fun i => (ch i).wsize w)
            ≤ w * w ^ strong.sup (fun i => (ch i).kappa) := by gcongr
          _ = w ^ (1 + strong.sup (fun i => (ch i).kappa)) := by rw [pow_add, pow_one]

/-- Theorem 2, witness-size form: a `k`-fault tree (`κ(root) ≤ k`) has recursive
witness size at most `w^k`. -/
theorem kFault_witnessSize_le_pow {n : ℕ} (w : ℝ≥0∞) (hw : 1 ≤ w)
    (v : DirectTree n) (k : ℕ) (hk : v.kappa ≤ k) : v.wsize w ≤ w ^ k :=
  (wsize_le_pow_kappa w hw v).trans (pow_le_pow_right₀ hw hk)

/-- Corollary "constant-fault ⇒ `O(1)` queries" (Theorem 2, last sentence) in
the weight model: a tree with `κ(root) = 0` has witness size `1`. -/
theorem constFault_witnessSize_eq_one {n : ℕ} (w : ℝ≥0∞) (hw : 1 ≤ w)
    (v : DirectTree n) (hk : v.kappa = 0) : v.wsize w ≤ 1 := by
  have h := kFault_witnessSize_le_pow w hw v 0 (le_of_eq hk)
  simpa using h

/-- **The final algorithmic step of Theorem 2**: once the adversary of the
tree's Boolean function is bounded by `w^k` (which the paper obtains from the
span-program witness size `≤ w^k` via Eq. (8) of [9]), bounded-error quantum
query complexity is `O(w^k)`: there is a universal constant `C` with
`Q(tree) ≤ C · w^k`. Uses the tightness package `Q = Θ(ADV)` (Lemma 2). -/
theorem directTree_query_bound {L : ℕ} (F : (Fin L → Bool) → Bool) (w : ℝ≥0∞) (k : ℕ)
    (hAdv : sourceAdversary (sourceAlphabetDelta (booleanInput (n := L))) F ≤ w ^ k) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧
      sourceFunctionQ (booleanInput (n := L)) F ≤ C * w ^ k := by
  obtain ⟨c, hc0, hspec⟩ := functionEvaluationAdversaryAlgorithm
  refine ⟨(c : ℝ≥0∞), ?_, ?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0.ne'
  · have hQ := (hspec (Fin L → Bool) Bool L 1 (booleanInput (n := L)) F).2.1
    exact hQ.trans (mul_le_mul_right hAdv _)

end DirectTree

end Qatlib.Papers.QAdversary11.FaultTree.DirectTrees
