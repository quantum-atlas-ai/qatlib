/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Formula and span-program definitions

This module defines finite AND/OR formulas, paths, maximal-false assignments, and the
span-program quantities used in game-tree evaluation [Reichardt2009]. Formula size counts leaf
occurrences, and `Formula.ReadOnce` requires all leaf labels to occur exactly once.

`SpanProgram` provides target and input vectors, associated matrices, positive and negative
witness conditions, and weighted witness-size expressions. The two-input programs `PAND` and
`POR` use fourth-root coefficients whose positivity and normalization identities are proved
here.

## Main statements

* `Formula`: Finite binary AND/OR trees with indexed leaves.
* `SpanProgram`: Target and input vectors over finite index types.
* `SpanProgram.wsize`: The supremum of input-dependent weighted witness sizes.
* `alpha_sum_sq`: The sum-of-squares identity for the two gate coefficients.

## References

* [Reichardt, 2009][Reichardt2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.GameTree09.MainResults

/-- A finite binary AND/OR formula whose leaves are labeled by `Fin n`. -/
inductive Formula (n : ℕ) where
  | leaf : Fin n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

namespace Formula

variable {n : ℕ}

/-- The Boolean evaluation of an AND/OR formula on an assignment to its leaf labels. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | leaf i, x => x i
  | and a b, x => a.eval x && b.eval x
  | or a b, x => a.eval x || b.eval x

/-- The number of leaf occurrences in a formula. -/
def size : Formula n → ℕ
  | leaf _ => 1
  | and a b => a.size + b.size
  | or a b => a.size + b.size

/-- The list of leaf labels in left-to-right recursive order. -/
def leaves : Formula n → List (Fin n)
  | leaf i => [i]
  | and a b => a.leaves ++ b.leaves
  | or a b => a.leaves ++ b.leaves

/-- The condition that the leaf-label list has no repetitions and has length `n`. -/
def ReadOnce (φ : Formula n) : Prop := φ.leaves.Nodup ∧ φ.leaves.length = n

/-- The optional subformula reached by following a Boolean path, with `false` selecting the left
child and `true` the right child. -/
def nodeAt (φ : Formula n) : List Bool → Option (Formula n)
  | [] => some φ
  | c :: rest =>
    match φ with
    | leaf _ => none
    | and a b => if c then b.nodeAt rest else a.nodeAt rest
    | or a b => if c then b.nodeAt rest else a.nodeAt rest

/-- The evaluation of the subformula at a path, defaulting to false when no node is present. -/
def evalAt (φ : Formula n) (p : List Bool) (x : Fin n → Bool) : Bool :=
  match φ.nodeAt p with
  | some ψ => ψ.eval x
  | none => false

/-- The leaf count of the subformula at a path, defaulting to zero when no node is present. -/
def sizeAt (φ : Formula n) (p : List Bool) : ℕ :=
  match φ.nodeAt p with
  | some ψ => ψ.size
  | none => 0

/-- The two binary gate kinds AND and OR. -/
inductive GateKind
  | and2
  | or2
  deriving DecidableEq

/-- The optional gate kind at a path, returning `none` for leaves and absent nodes. -/
def gateAt (φ : Formula n) (p : List Bool) : Option GateKind :=
  match φ.nodeAt p with
  | some (leaf _) => none
  | some (and _ _) => some .and2
  | some (or _ _) => some .or2
  | none => none

/-- The list of root-relative paths to internal gates, with the root listed before the
recursively listed children. -/
def internalPaths : Formula n → List (List Bool)
  | leaf _ => []
  | and a b =>
      [] :: (a.internalPaths.map (fun q => false :: q) ++
             b.internalPaths.map (fun q => true :: q))
  | or a b =>
      [] :: (a.internalPaths.map (fun q => false :: q) ++
             b.internalPaths.map (fun q => true :: q))

/-- The list of proper prefixes of a Boolean path, in increasing length order. -/
def pathVertices (γ : List Bool) : List (List Bool) :=
  (List.range γ.length).map (fun i => γ.take i)

/-- The product of `f` over the successive proper prefixes and corresponding branch bits of a
path. -/
def pathProd (γ : List Bool) (f : List Bool → Bool → ℝ) : ℝ :=
  ((List.range γ.length).map (fun i =>
    match γ[i]? with
    | some c => f (γ.take i) c
    | none => 1)).prod

/-- The condition that the formula evaluates to false but becomes true whenever any false input
bit is changed to true. -/
def IsMaximalFalse (φ : Formula n) (x : Fin n → Bool) : Prop :=
  φ.eval x = false ∧
    ∀ i : Fin n, x i = false → φ.eval (Function.update x i true) = true

/-- The subtype of maximal-false assignments of a formula. -/
def MaxFalse (φ : Formula n) : Type := {x : Fin n → Bool // φ.IsMaximalFalse x}

instance (φ : Formula n) : DecidablePred φ.IsMaximalFalse := fun x => by
  unfold IsMaximalFalse; infer_instance

instance (φ : Formula n) : Fintype φ.MaxFalse := by
  unfold MaxFalse; infer_instance

instance (φ : Formula n) : DecidableEq φ.MaxFalse := by
  unfold MaxFalse; infer_instance

/-- The condition that the node at `p` and every prefix of `p` evaluate to false on `x`. -/
def InTx (φ : Formula n) (x : Fin n → Bool) (p : List Bool) : Prop :=
  φ.evalAt p x = false ∧ ∀ q, q <+: p → φ.evalAt q x = false

end Formula

/-- A target vector and a family of complex input vectors, indexed by finite input and
coordinate types. -/
structure SpanProgram (β V : Type*) [Fintype β] [Fintype V] where
  target : V → ℂ
  vec : β → V → ℂ

namespace SpanProgram

variable {β V : Type*} [Fintype β] [Fintype V]

/-- The matrix whose `none` column is the target and whose `some b` column is input vector `b`. -/
def biadj (P : SpanProgram β V) : Matrix V (Option β) ℂ :=
  fun v o => Option.casesOn o (P.target v) (fun b => P.vec b v)

/-- The real matrix obtained by replacing each complex entry by its norm. -/
def absMatrix {R C : Type*} (M : Matrix R C ℂ) : Matrix R C ℝ :=
  fun i j => ‖M i j‖

/-- The Euclidean operator norm of the entrywise absolute-value biadjacency matrix. -/
def absBiadjNorm [DecidableEq β] (P : SpanProgram β V) : ℝ := ‖absMatrix P.biadj‖

/-- The block adjacency matrix with the biadjacency matrix and its conjugate transpose in the
off-diagonal blocks. -/
def adjacency (P : SpanProgram β V) : Matrix (V ⊕ Option β) (V ⊕ Option β) ℂ :=
  Matrix.fromBlocks (0 : Matrix V V ℂ) P.biadj
    (Matrix.conjTranspose P.biadj) (0 : Matrix (Option β) (Option β) ℂ)

/-- The number of nonzero entries in the row indexed by `w`. -/
def degreeAt {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℂ) (w : W) : ℕ :=
  (Finset.univ.filter (fun w' => A w w' ≠ 0)).card

/-- The finite supremum of the row degrees of a square matrix. -/
def maxDegree {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℂ) : ℕ :=
  Finset.univ.sup (fun w => degreeAt A w)

/-- The finite complex dot product that is conjugate-linear in the first argument. -/
def dot {W : Type*} [Fintype W] (w v : W → ℂ) : ℂ := ∑ i, star (w i) * v i

/-- The sum of squared coordinate norms of a complex vector. -/
def normSq {W : Type*} [Fintype W] (w : W → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2

/-- The condition that `u` is supported on true input labels and its linear combination of input
vectors equals the target. -/
def PosWitness (P : SpanProgram β V) (x : β → Bool) (u : β → ℂ) : Prop :=
  (∀ b, x b = false → u b = 0) ∧ (∑ b, u b • P.vec b) = P.target

/-- The condition that `dot P.target w = 1` and `dot (P.vec b) w = 0` for every true input label
`b`. -/
def NegWitness (P : SpanProgram β V) (x : β → Bool) (w : V → ℂ) : Prop :=
  dot P.target w = 1 ∧ ∀ b, x b = true → dot (P.vec b) w = 0

/-- The Boolean value that is true exactly when a positive witness exists. -/
def evals (P : SpanProgram β V) (x : β → Bool) : Bool := by
  classical
  exact if ∃ u, P.PosWitness x u then true else false

/-- The sum of the squared positive-witness coefficient norms weighted by `s`. -/
def posCost (P : SpanProgram β V) (s : β → ℝ) (u : β → ℂ) : ℝ :=
  ∑ b, ‖u b‖ ^ 2 * s b

/-- The sum of the squared input-vector dot products with the negative witness, weighted by `s`. -/
def negCost (P : SpanProgram β V) (s : β → ℝ) (w : V → ℂ) : ℝ :=
  ∑ b, s b * ‖dot (P.vec b) w‖ ^ 2

/-- The infimum of positive-witness costs on accepting inputs, or of negative-witness costs on
rejecting inputs. -/
def wsizeAt (P : SpanProgram β V) (s : β → ℝ) (x : β → Bool) : ℝ :=
  if P.evals x then
    sInf (posCost P s '' {u | P.PosWitness x u})
  else
    sInf (negCost P s '' {w | P.NegWitness x w})

/-- The supremum of the input-dependent weighted witness sizes over all Boolean inputs. -/
def wsize (P : SpanProgram β V) (s : β → ℝ) : ℝ :=
  sSup (Set.range (fun x : β → Bool => P.wsizeAt s x))

/-- The infimum of `1 + posCost` on accepting inputs, or of `normSq + negCost` on rejecting
inputs. -/
def fwsizeAt (P : SpanProgram β V) (s : β → ℝ) (x : β → Bool) : ℝ :=
  if P.evals x then
    sInf ((fun u => 1 + posCost P s u) '' {u | P.PosWitness x u})
  else
    sInf ((fun w => normSq w + negCost P s w) '' {w | P.NegWitness x w})

/-- The supremum of the input-dependent full witness sizes over all Boolean inputs. -/
def fwsize (P : SpanProgram β V) (s : β → ℝ) : ℝ :=
  sSup (Set.range (fun x : β → Bool => P.fwsizeAt s x))

end SpanProgram

/-- The nested-square-root gate coefficient `√√(s j / (s 0 + s 1))`. -/
def alpha (s : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  Real.sqrt (Real.sqrt (s j / (s 0 + s 1)))

/-- The Euclidean norm of the pair of gate coefficients `alpha s 0` and `alpha s 1`. -/
def alphaNorm (s : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (alpha s 0 ^ 2 + alpha s 1 ^ 2)

/-- The two-coordinate span program with target coordinates `alpha s i` and standard-basis input
vectors. -/
def PAND (s : Fin 2 → ℝ) : SpanProgram (Fin 2) (Fin 2) where
  target := fun i => ((alpha s i : ℝ) : ℂ)
  vec := fun b i => if b = i then 1 else 0

/-- The one-coordinate span program with target one and input-vector coordinates `alpha s b`. -/
def POR (s : Fin 2 → ℝ) : SpanProgram (Fin 2) (Fin 1) where
  target := fun _ => 1
  vec := fun b _ => ((alpha s b : ℝ) : ℂ)

/-- The constant `√2 * exp 1` used in the game-tree bounds. -/
def lam : ℝ := Real.sqrt 2 * Real.exp 1

/-- The constant `(1 + 1/√2) * lam / log 2` used in the game-tree bounds. -/
def kappa : ℝ := (1 + 1 / Real.sqrt 2) * lam / Real.log 2

/-- Every gate coefficient `alpha s j` is nonnegative. -/
theorem alpha_nonneg (s : Fin 2 → ℝ) (j : Fin 2) : 0 ≤ alpha s j :=
  Real.sqrt_nonneg _

/-- Both gate coefficients are strictly positive when both weights are strictly positive. -/
theorem alpha_pos {s : Fin 2 → ℝ} (h0 : 0 < s 0) (h1 : 0 < s 1) (j : Fin 2) :
    0 < alpha s j := by
  unfold alpha
  apply Real.sqrt_pos.mpr
  apply Real.sqrt_pos.mpr
  exact div_pos (by fin_cases j <;> assumption) (by positivity)

/-- For positive weights, `alpha s j` squared equals `√(s j) / √(s 0 + s 1)`. -/
theorem alpha_sq {s : Fin 2 → ℝ} (h0 : 0 < s 0) (h1 : 0 < s 1) (j : Fin 2) :
    alpha s j ^ 2 = Real.sqrt (s j) / Real.sqrt (s 0 + s 1) := by
  unfold alpha
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  exact Real.sqrt_div (by fin_cases j <;> [exact h0.le; exact h1.le]) _

/-- For positive weights, the sum of the squared gate coefficients is `(√(s 0) + √(s 1)) / √(s 0
+ s 1)`. -/
theorem alpha_sum_sq {s : Fin 2 → ℝ} (h0 : 0 < s 0) (h1 : 0 < s 1) :
    alpha s 0 ^ 2 + alpha s 1 ^ 2 =
      (Real.sqrt (s 0) + Real.sqrt (s 1)) / Real.sqrt (s 0 + s 1) := by
  rw [alpha_sq h0 h1, alpha_sq h0 h1]
  ring

/-- For two positive weights, the sum of the squared gate coefficients is strictly greater than
one. -/
theorem alpha_sum_sq_gt_one {s : Fin 2 → ℝ} (h0 : 0 < s 0) (h1 : 0 < s 1) :
    1 < alpha s 0 ^ 2 + alpha s 1 ^ 2 := by
  rw [alpha_sum_sq h0 h1]
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by positivity)), one_mul]
  have hp : (Real.sqrt (s 0 + s 1)) ^ 2 = s 0 + s 1 := Real.sq_sqrt (by positivity)
  have hq : (Real.sqrt (s 0) + Real.sqrt (s 1)) ^ 2 =
      s 0 + s 1 + 2 * Real.sqrt (s 0) * Real.sqrt (s 1) := by
    rw [add_sq, Real.sq_sqrt (le_of_lt h0), Real.sq_sqrt (le_of_lt h1)]
    ring
  have hpos : 0 < Real.sqrt (s 0) * Real.sqrt (s 1) :=
    mul_pos (Real.sqrt_pos.2 h0) (Real.sqrt_pos.2 h1)
  have hsq : (Real.sqrt (s 0 + s 1)) ^ 2 <
      (Real.sqrt (s 0) + Real.sqrt (s 1)) ^ 2 := by
    rw [hp, hq]; nlinarith
  rw [← Real.sqrt_sq (show 0 ≤ Real.sqrt (s 0) + Real.sqrt (s 1) by positivity)]
  rw [Real.lt_sqrt (Real.sqrt_nonneg _)]
  exact hsq

/-- The norm of the gate-coefficient pair is strictly greater than one for positive weights. -/
theorem alphaNorm_gt_one {s : Fin 2 → ℝ} (h0 : 0 < s 0) (h1 : 0 < s 1) :
    1 < alphaNorm s := by
  unfold alphaNorm
  rw [Real.lt_sqrt (by positivity)]
  simpa using alpha_sum_sq_gt_one h0 h1

/-- The game-tree constant `lam` is strictly positive. -/
theorem lam_pos : 0 < lam := by
  unfold lam
  positivity

/-- The game-tree constant `kappa` is strictly positive. -/
theorem kappa_pos : 0 < kappa := by
  unfold kappa
  have h1 : 0 < 1 + 1 / Real.sqrt 2 := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (mul_pos h1 lam_pos) hl

end Qatlib.Papers.GameTree09.MainResults
