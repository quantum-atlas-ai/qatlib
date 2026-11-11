/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CarlemanSim26.MainResults.Core.CarlemanObjects

set_option backward.isDefEq.respectTransparency false

/-!
# Block matrices, binary forests, and the Poincaré–Dulac diagonalizer

Jennings--Korzekwa--Lostaglio--Sornborger--Subasi--Wang,
*Quantum algorithms for general nonlinear dynamics based on the Carleman embedding*,
fixed arXiv:2509.07155v2.

This module formalizes, for the statements of Section 5 and Appendices F/G/I:

* the level-`(i,j)` block matrices `V_{i,j} : (ℂ^N)^{⊗j} → (ℂ^N)^{⊗i}`
  (the blocks of the order-`k` Carleman similarity `Ṽ` of Eq. (5.28));
* the level-`j` tensor diagonal `Λ_j = Λ^{⊗j}` of Eq. (5.30);
* the binary-tree operators `f̃(t)` of Definition 5.2, Eq. (5.62), including the
  Hadamard (entrywise) weight `N_l` of Eq. (5.61) with entries
  `1/(λ_{i_1}+...+λ_{i_l} − λ_i)`;
* the forest operators `f̃(T)` of Eq. (5.63), the forest sums
  `Ṽ_{i,j} = Σ_{T ∈ T_j^i} f̃(T)` of Eq. (5.64), and the corresponding
  "inverse" forest series of Proposition 5.4, Eq. (5.103);
* blockwise composition/inversion of a family of blocks.

As in the paper, a tensor of order `j` is indexed by `Fin j → Fin n`; block
composition is ordinary matrix multiplication, which typechecks because the
middle index set is literally `(Fin j → Fin n)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.CarlemanSim26.MainResults

/-- The block of a level-`i ← level-`j` operator (source Eq. (5.28)). -/
abbrev BlockMat (n i j : ℕ) : Type := Matrix (Fin i → Fin n) (Fin j → Fin n) ℂ

/-- Identity block on level `i`. -/
def identityBlock (n i : ℕ) : BlockMat n i i :=
  fun a b => if a = b then (1 : ℂ) else 0

/-- The tensor diagonal `Λ_j = Λ^{⊗j}` of Eq. (5.30), with diagonal entries the
products `λ_{a_1}⋯λ_{a_j}`. -/
def tensorDiag {n : ℕ} (lam : Fin n → ℂ) (j : ℕ) : BlockMat n j j :=
  fun a b => if a = b then ∏ l : Fin j, lam (a l) else 0

/-- The entrywise Hadamard weight `N_l` of Eq. (5.61):
`(N_l)[i, (i_1,…,i_l)] = 1/(λ_{i_1}+⋯+λ_{i_l} − λ_i)`. -/
def nWeight {n : ℕ} (lam : Fin n → ℂ) (l : ℕ) : BlockMat n 1 l :=
  fun a b => ((∑ k : Fin l, lam (b k)) - lam (a 0))⁻¹

/-- Binary trees with leaves, the objects of Definition 5.2. -/
inductive BinaryTree : Type
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
  deriving DecidableEq, Repr

namespace BinaryTree

/-- Number of leaves of a binary tree. -/
def leaves : BinaryTree → ℕ
  | leaf => 1
  | node l r => l.leaves + r.leaves

end BinaryTree

/-- The operator `f̃(t)` assigned to a binary tree by Definition 5.2, Eq. (5.62):
`f̃(t) = N_{v(t)} ⊙ (F̃2 (f̃(t_left) ⊗ f̃(t_right)))`, with identity on leaves. -/
def treeOp {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) :
    (t : BinaryTree) → BlockMat n 1 t.leaves
  | .leaf => fun a b => if a = b then (1 : ℂ) else 0
  | .node l r =>
      fun a c =>
        nWeight lam (l.leaves + r.leaves) a c *
          (∑ p : Fin n × Fin n,
            F2t a (fun i : Fin 2 => if (i : ℕ) = 0 then p.1 else p.2) *
              treeOp lam F2t l (fun _ => p.1)
                (fun k : Fin l.leaves => c (Fin.castAdd r.leaves k)) *
              treeOp lam F2t r (fun _ => p.2)
                (fun k : Fin r.leaves => c (Fin.natAdd l.leaves k)))

/-- The total number of leaves of a forest. -/
def forestLeaves (F : List BinaryTree) : ℕ := (F.map BinaryTree.leaves).sum

/-- The operator `f̃(T)` of a forest, Eq. (5.63): the tensor product of the
operators of its constituent trees. -/
def forestOp {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) :
    (F : List BinaryTree) → BlockMat n F.length (forestLeaves F)
  | [] => fun _ _ => 1
  | t :: ts =>
      fun a c =>
        treeOp lam F2t t (fun _ => a 0)
            (fun k : Fin t.leaves =>
              c (Fin.cast (by simp [forestLeaves, List.map_cons, List.sum_cons])
                (Fin.castAdd (forestLeaves ts) k))) *
          forestOp lam F2t ts (Fin.tail a)
            (fun k : Fin (forestLeaves ts) =>
              c (Fin.cast (by simp [forestLeaves, List.map_cons, List.sum_cons])
                (Fin.natAdd t.leaves k)))

/-- The set `T_l` of binary trees with exactly `l` leaves (Definition 5.2). -/
def treeFinset (l : ℕ) : Finset BinaryTree :=
  Nat.strongRecOn (motive := fun _ => Finset BinaryTree) l fun l ih =>
    match l with
    | 0 => ∅
    | 1 => {BinaryTree.leaf}
    | m + 2 =>
        ((Finset.range (m + 1)).attach).biUnion fun a =>
          ((ih (a.1 + 1) (Nat.succ_lt_succ (Finset.mem_range.mp a.2))).product
            (ih (m + 1 - a.1) (Nat.lt_succ_of_le (Nat.sub_le (m + 1) a.1)))).image
            fun p => BinaryTree.node p.1 p.2

/-- The set `T_j^i` of binary forests with `i` trees and `j` leaves total. -/
def forestFinset : ℕ → ℕ → Finset (List BinaryTree)
  | 0, 0 => {[]}
  | 0, _ + 1 => ∅
  | _ + 1, 0 => ∅
  | i + 1, j + 1 =>
      ((Finset.range (j + 1)).attach).biUnion fun m =>
        ((treeFinset (m.1 + 1)).product (forestFinset i (j - m.1))).image
          fun p => p.1 :: p.2
termination_by i j => i

/-- Coerce a forest operator to the block type `(i,j)` fixed by the forest's tree
and leaf counts (`h1`, `h2`). -/
def forestOpAt {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) (i j : ℕ)
    (F : List BinaryTree) : BlockMat n i j :=
  if h1 : F.length = i then
    if h2 : forestLeaves F = j then
      fun a b => forestOp lam F2t F
        (fun k : Fin F.length => a (Fin.cast h1 k))
        (fun k : Fin (forestLeaves F) => b (Fin.cast h2 k))
    else 0
  else 0

/-- The diagonalizing blocks `Ṽ_{i,j} = Σ_{T ∈ T_j^i} f̃(T)` of Definition 5.2,
Eq. (5.64). -/
def forestSum {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) (i j : ℕ) :
    BlockMat n i j :=
  ∑ F ∈ forestFinset i j, forestOpAt lam F2t i j F

/-- The operator `g̃(t)` of the inverse forest series (Proposition 5.4, Eq. (5.103)):
the same tree recursion with the denominator `λ_i − (λ_{i_1}+⋯+λ_{i_l})` instead of
`(λ_{i_1}+⋯+λ_{i_l}) − λ_i`. -/
def invTreeOp {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) :
    (t : BinaryTree) → BlockMat n 1 t.leaves
  | .leaf => fun a b => if a = b then (1 : ℂ) else 0
  | .node l r =>
      fun a c =>
        ((lam (a 0) - ∑ k : Fin (l.leaves + r.leaves), lam (c k))⁻¹) *
          (∑ p : Fin n × Fin n,
            F2t a (fun i : Fin 2 => if (i : ℕ) = 0 then p.1 else p.2) *
              invTreeOp lam F2t l (fun _ => p.1)
                (fun k : Fin l.leaves => c (Fin.castAdd r.leaves k)) *
              invTreeOp lam F2t r (fun _ => p.2)
                (fun k : Fin r.leaves => c (Fin.natAdd l.leaves k)))

/-- The inverse-forest operator `g̃(T)` of a forest. -/
def invForestOp {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) :
    (F : List BinaryTree) → BlockMat n F.length (forestLeaves F)
  | [] => fun _ _ => 1
  | t :: ts =>
      fun a c =>
        invTreeOp lam F2t t (fun _ => a 0)
            (fun k : Fin t.leaves =>
              c (Fin.cast (by simp [forestLeaves, List.map_cons, List.sum_cons])
                (Fin.castAdd (forestLeaves ts) k))) *
          invForestOp lam F2t ts (Fin.tail a)
            (fun k : Fin (forestLeaves ts) =>
              c (Fin.cast (by simp [forestLeaves, List.map_cons, List.sum_cons])
                (Fin.natAdd t.leaves k)))

/-- Coerce an inverse-forest operator to the block type `(i,j)`. -/
def invForestOpAt {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) (i j : ℕ)
    (F : List BinaryTree) : BlockMat n i j :=
  if h1 : F.length = i then
    if h2 : forestLeaves F = j then
      fun a b => invForestOp lam F2t F
        (fun k : Fin F.length => a (Fin.cast h1 k))
        (fun k : Fin (forestLeaves F) => b (Fin.cast h2 k))
    else 0
  else 0

/-- The right-hand side of Proposition 5.4, Eq. (5.103):
`(−1)^{j−i} Σ_{T ∈ T_j^i} g̃(T)`. -/
def inverseForestSeries {n : ℕ} (lam : Fin n → ℂ) (F2t : BlockMat n 1 2) (i j : ℕ) :
    BlockMat n i j :=
  (-1 : ℂ) ^ (j - i) • ∑ F ∈ forestFinset i j, invForestOpAt lam F2t i j F

/-- `W` is a blockwise inverse of `V` up to truncation level `k`
(Proposition 5.4 supplies the blocks of `Ṽ⁻¹`). -/
def IsBlockwiseInverse {n : ℕ} (k : ℕ) (V W : (i j : ℕ) → BlockMat n i j) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ k → j ≤ k →
    (∑ l ∈ Finset.Icc 1 k, V i l * W l j) =
      if h : i = j then h ▸ identityBlock n i else 0

/-- The upper block `Ã_{i,i+1}` in block form: `F̃2` applied to two adjacent
tensor factors, with `i` possible positions (the block form of `carlemanUp`). -/
def shiftUp {n : ℕ} (F2t : BlockMat n 1 2) (i : ℕ) : BlockMat n i (i + 1) :=
  fun a b =>
    ∑ l : Fin i,
      F2t (fun _ => a l)
          (fun t : Fin 2 => if (t : ℕ) = 0 then b (Fin.castSucc l) else b (Fin.succ l)) *
        ∏ k : {k : Fin i // k ≠ l},
          (if a k.1 = b (Fin.succAbove (Fin.castSucc l) k.1) then (1 : ℂ) else 0)

end Qatlib.Papers.CarlemanSim26.MainResults
