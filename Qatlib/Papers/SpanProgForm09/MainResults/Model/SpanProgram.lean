/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgForm09.MainResults.Model.Formula

set_option backward.isDefEq.respectTransparency false

/-!
# Span programs for Reichardt, *Span-program-based quantum algorithm for evaluating
unbalanced formulas* (fixed arXiv:0907.1622v1)

This module formalises the paper's span programs (Definitions 2.2, 2.3, 2.5):
a target vector `|t⟩`, one input vector `|v_i⟩` per label `i`, and a labelling of each
label by either a variable/bit (`some (j,b)`, available when `x j = b`) or "free"
(`none`). It defines the witness sets, the complexity measures `wsize` and `fwsize`
of Eqs. (2.3)–(2.6), the biadjacency matrix of Eq. (3.5), the direct-sum composition
structure of Definition 2.5 (Lemma 2.6), and the abstract Theorem-1.9 construction
predicate consumed by Lemmas 3.3, 3.4 and 4.4.

Cost convention: the cost vector `s : I → ℝ` is carried on the *label* type `I`. The
paper's per-variable costs `s : [n] → (0,∞)` are the special case where `s` is constant
on the labels of each variable; free labels take `s_i = 0` in `wsize` and `s_i = 1` in
`fwsize` as in Eqs. (2.3)–(2.6). Nothing here is assumed about the construction; the
paper's later claims are stated over `IsDirectSumComposition` and
`IsTheorem19Construction`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgForm09.MainResults

open Matrix
open Formula
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

attribute [local instance] Classical.propDecidable

/-- A span program over `n` Boolean variables: a target vector `target : V → ℂ`, input
vectors `vec i : V → ℂ` indexed by labels `i : I`, and a labelling
`lab i = some (j,b)` (available when bit `j` equals `b`) or `lab i = none` (free). This
is Definition 2.2 of arXiv:0907.1622v1. -/
structure SpanProgram (n : ℕ) (V I : Type) [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] where
  /-- The target vector `|t⟩`. -/
  target : V → ℂ
  /-- The input vector `|v_i⟩`. -/
  vec : I → V → ℂ
  /-- The label of each input vector. -/
  lab : I → Option (Fin n × Bool)

namespace SpanProgram

variable {n : ℕ} {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The input vector `i` is available at `x` if its label is free or matches `x`. -/
def available (P : SpanProgram n V I) (x : Fin n → Bool) (i : I) : Prop :=
  match P.lab i with
  | none => True
  | some (j, b) => b = x j

/-- A positive witness for `f_P(x) = 1` (Definition 2.2): a combination of available
input vectors producing the target. -/
def PosWitness (P : SpanProgram n V I) (x : Fin n → Bool) (w : I → ℂ) : Prop :=
  (∀ i, ¬ P.available x i → w i = 0) ∧ ∀ v, ∑ i, P.vec i v * w i = P.target v

/-- A negative witness for `f_P(x) = 0` (Definition 2.2): a vector orthogonal to all
available input vectors and pairing to `1` with the target. -/
def NegWitness (P : SpanProgram n V I) (x : Fin n → Bool) (u : V → ℂ) : Prop :=
  (∑ v, P.target v * u v) = 1 ∧ ∀ i, P.available x i → ∑ v, star (P.vec i v) * u v = 0

/-- `f_P(x)`: `true` when a positive witness exists (Definition 2.2). -/
def fP (P : SpanProgram n V I) (x : Fin n → Bool) : Bool :=
  if ∃ w, P.PosWitness x w then true else false

/-- `wsize_s(P,x)` on the positive side, Eq. (2.3): the infimum of `∑_i s_i |w_i|²` over
positive witnesses `w`. -/
def wsizePos (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  sInf (Set.range (fun w : { w : I → ℂ // P.PosWitness x w } =>
    ∑ i, s i * ‖w.val i‖ ^ 2))

/-- `wsize_s(P,x)` on the negative side, Eq. (2.4): the infimum of the witness-size
functional of `P^†` over negative witnesses `u` of `P`. -/
def wsizeNeg (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  sInf (Set.range (fun u : { u : V → ℂ // P.NegWitness x u } =>
    (∑ v, ‖u.val v‖ ^ 2) + ∑ i, s i * ‖(∑ v, star (P.vec i v) * u.val v)‖ ^ 2))

/-- `wsize_s(P,x)` of Eq. (2.3)–(2.4): positive-witness size when `f_P(x) = 1`, and the
dual witness size when `f_P(x) = 0`. -/
def wsize (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  if P.fP x then P.wsizePos x s else P.wsizeNeg x s

/-- The positive `fwsize` of Eq. (2.5). -/
def fwsizePos (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  sInf (Set.range (fun w : { w : I → ℂ // P.PosWitness x w } =>
    1 + ∑ i, s i * ‖w.val i‖ ^ 2))

/-- The negative `fwsize` of Eq. (2.6). -/
def fwsizeNeg (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  sInf (Set.range (fun u : { u : V → ℂ // P.NegWitness x u } =>
    (∑ v, ‖u.val v‖ ^ 2) + ∑ i, s i * ‖(∑ v, star (P.vec i v) * u.val v)‖ ^ 2))

/-- `fwsize_s(P,x)` of Eqs. (2.5)–(2.6). -/
def fwsize (P : SpanProgram n V I) (x : Fin n → Bool) (s : I → ℝ) : ℝ :=
  if P.fP x then P.fwsizePos x s else P.fwsizeNeg x s

/-- The supremum of `wsize` over all inputs `x` (the paper's `wsize_s(P)`).  Written as a
fold of `max` over the finite cube, so it needs no order-topology on the cube. -/
def wsizeOf (P : SpanProgram n V I) (s : I → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).toList.foldr (fun x acc => max (P.wsize x s) acc) 0

/-- The supremum of `fwsize` over all inputs `x` (the paper's `fwsize_s(P)`). -/
def fwsizeOf (P : SpanProgram n V I) (s : I → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).toList.foldr (fun x acc => max (P.fwsize x s) acc) 0

/-- The minimum of the cost vector over the labels (the paper's `min_j s_j`, with the
paper's per-variable cost read as a label cost as discussed in the module header). -/
def sMin (s : I → ℝ) : ℝ :=
  (Finset.univ : Finset I).toList.foldr (fun i acc => min (s i) acc) 0

/-- The biadjacency matrix `A_Π = [[|t⟩, A],[0,1]]` of Eq. (3.5): rows `V ⊕ I`, columns
`Unit ⊕ I`, with `A_{i,v} = ⟨v_i|v⟩`. -/
def biadj (P : SpanProgram n V I) : Matrix (V ⊕ I) (Unit ⊕ I) ℂ :=
  fun r c =>
    match r, c with
    | Sum.inl v, Sum.inl _ => P.target v
    | Sum.inl v, Sum.inr i => P.vec i v
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr i, Sum.inr i' => if i = i' then 1 else 0

end SpanProgram

open SpanProgram

variable {n : ℕ} {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The bipartite adjacency matrix of the span program's graph, `[[0, A_Π],[A_Π^†, 0]]`.
Its operator norm is the `‖A_{G_P}‖` of the paper's Lemma 3.1. -/
def adjacency (P : SpanProgram n V I) :
    Matrix ((V ⊕ I) ⊕ (Unit ⊕ I)) ((V ⊕ I) ⊕ (Unit ⊕ I)) ℂ :=
  fun r c =>
    match r, c with
    | Sum.inl a, Sum.inr b => P.biadj a b
    | Sum.inr a, Sum.inl b => star (P.biadj b a)
    | _, _ => 0

/-- Entrywise absolute value of a complex matrix. -/
def entryAbs {m n' : Type} (M : Matrix m n' ℂ) : Matrix m n' ℂ := fun r c => (‖M r c‖ : ℂ)

/-- `‖abs(A_{G_P})‖`, the quantity bounded in Lemma 3.1. -/
def absGraphNorm (P : SpanProgram n V I) : ℝ := ‖entryAbs (adjacency P)‖

/-- The canonical span program of [Reichardt2009SpanPrograms, Definition 5.1], as used in the proof of
arXiv:0907.1622v1 Lemma 3.1: for `f : {0,1}^k → {0,1}` and a family of vectors
`v : {0,1}^k → Fin k → Fin m → ℂ`, the target is `|t⟩ = ∑_{x : f(x)=0} |x⟩` and the
input vector labelled `(j, b, k')` is `∑_{x : f(x)=0, b = ¬x_j} ⟨v_{x,j,k'}|x⟩`, i.e.
Eq. (3.2)'s `A = ∑_{x:f(x)=0} |x⟩⟨j,¬x_j| ⊗ ⟨v_{xj}|`. -/
def canonicalProgram (k m : ℕ) (f : (Fin k → Bool) → Bool) (v : (Fin k → Bool) → Fin k → Fin m → ℂ) :
    SpanProgram k { x : Fin k → Bool // f x = false } (Fin k × Bool × Fin m) where
  target := fun _ => 1
  vec := fun (j, b, k') x => if b = !(x.val j) then star (v x.val j k') else 0
  lab := fun (j, b, _) => some (j, b)

/-- `P` is canonical for `f` with cost vector `s` (the paper's Eq. (3.3) hypothesis, as
used in Lemma 3.1): `P` computes `f`, and on every zero input the basis vector `|x⟩` is an
optimal negative witness, so the witness size is the paper's `∑_j s_j ‖v_{xj}‖²`. -/
structure Canonical {k m : ℕ} (f : (Fin k → Bool) → Bool) (v : (Fin k → Bool) → Fin k → Fin m → ℂ)
    (s : Fin k → ℝ) : Prop where
  /-- The program computes `f`. -/
  computes : ∀ x : Fin k → Bool,
    (canonicalProgram k m f v).fP x = f x
  /-- On a zero input the basis vector is an optimal negative witness (Eq. (3.3)), with
  the per-variable cost `s` read on the label of each vector. -/
  optimal : ∀ x : Fin k → Bool, f x = false →
    (canonicalProgram k m f v).wsize x (fun p => s p.1) =
      ∑ j, s j * ∑ k', ‖v x j k'‖ ^ 2

/-- The direct-sum-composition data of Definition 2.5 (arXiv:0907.1622v1), as consumed by
Lemma 2.6: the outer program `P` over `n` bits, one inner program `Qin j c` for each
outer bit `j` and value `c`, and the composed program `Q` over `∑_j m_j` bits. The fields
record that the composed target is the outer target on the `V` summand, that the free
vectors are the outer free vectors, and that inner vector `i'` of `Qin j c` appears at
`(j,c,i')` in the inner summand. -/
structure IsDirectSumComposition (P : SpanProgram n V I) {m : Fin n → ℕ} {W J : Type}
    [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
    (Qin : (j : Fin n) → Bool → SpanProgram (m j) W J)
    (Q : SpanProgram (∑ j, m j) (V ⊕ ((j : Fin n) → Bool → W))
      (I ⊕ ((j : Fin n) × Bool × J))) : Prop where
  /-- The composed target restricts to the outer target on the `V` summand. -/
  target_inl : ∀ v, Q.target (Sum.inl v) = P.target v
  /-- The composed target vanishes on the inner summand. -/
  target_inr : ∀ g, Q.target (Sum.inr g) = 0
  /-- A free outer label contributes the outer vector on `V` and zero on the inner summand. -/
  vec_free : ∀ i, P.lab i = none → ∀ v, Q.vec (Sum.inl i) (Sum.inl v) = P.vec i v
  /-- A free outer label has no inner component. -/
  vec_free_off : ∀ i, P.lab i = none → ∀ g, Q.vec (Sum.inl i) (Sum.inr g) = 0
  /-- Inner vector `i'` of `Qin j c` sits at `(j,c,i')`, evaluated on the `(j,c)` copy. -/
  vec_inner : ∀ (j : Fin n) (c : Bool) (i' : J) (g : (j : Fin n) → Bool → W),
    Q.vec (Sum.inr ⟨j, c, i'⟩) (Sum.inr g) = (Qin j c).vec i' (g j c)
  /-- Inner vectors have no `V` component. -/
  vec_inner_off : ∀ (j : Fin n) (c : Bool) (i' : J) (v : V),
    Q.vec (Sum.inr ⟨j, c, i'⟩) (Sum.inl v) = 0

/-- The abstract Theorem-1.9 construction: a pair of span-program families along the
subformulas of `φ` (the program `P v` for `φ_v`, and `Pd v` for its negation) over the
leaf variable set. The construction of arXiv:0907.1622v1 Section 4 additionally makes each
`P v` canonical and a direct-sum composition of its children; those structural facts are
not yet mechanised and are documented in the PR description (the earlier pass's
statement-only scaffolding, removed for violating the no-`sorry` rule, is preserved in
`git log`). -/
structure IsTheorem19Construction {I : Type} [Fintype I] [DecidableEq I] {G : GateSet}
    (φ : Formula I G) (V : Type) [Fintype V] [DecidableEq V] (s : I → ℝ)
    (P Pd : (v : Formula I G) → SpanProgram (Fintype.card I) V I) : Prop where
  /-- `P v` computes the subformula `φ_v`. -/
  computes : ∀ (v : Formula I G), Subformula v φ → ∀ x : Fin (Fintype.card I) → Bool,
    (P v).fP x = v.eval (decodeBit I x)
  /-- `Pd v` computes the negation of the subformula `φ_v`. -/
  computesDual : ∀ (v : Formula I G), Subformula v φ → ∀ x : Fin (Fintype.card I) → Bool,
    (Pd v).fP x = !(v.eval (decodeBit I x))

end Qatlib.Papers.SpanProgForm09.MainResults
