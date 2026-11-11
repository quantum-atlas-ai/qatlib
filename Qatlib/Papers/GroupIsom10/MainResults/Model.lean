/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Range
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Modelling interfaces for the paper of arXiv:1001.0608v1

Source: François Le Gall, *An Efficient Quantum Algorithm for some Instances of the Group
Isomorphism Problem*, arXiv:1001.0608v1 (2010).

The paper's main results (Theorem 1.2, Theorem 3.1, Theorem 4.1, Proposition 4.1,
Theorem 5.1) assert the existence of *quantum algorithms* whose running time is bounded by a
polynomial in certain parameters and which succeed with high probability.  The repository has
no model of quantum circuits, of black-box group oracles, or of computational cost, so these
assertions cannot be formalised at the level of executable quantum computation.  This file
provides the minimal paper-level interfaces that the statements of those claims use:

* `QuantumAlgorithm I O` — an algorithm with an input type `I`, an output type `O`, a running
  time function and a success-probability function;
* `PolyBounded size alg` — the running time is bounded by a polynomial in `size`;
* `HighProbability alg` — the success probability is at least `2/3` on every input (the usual
  bounded-error convention behind "with high probability").

The paper's mathematical (non-algorithmic) claims — Lemma 3.1, Lemma 3.2, Lemma 5.1,
Lemma 5.2 — do not use this interface and are stated directly in their own files.

Also defined here are the elementary matrix notions used in Section 5 (Lemma 5.1 and
Lemma 5.2): a Jordan block `jordanBlock K c λ` and similarity of square matrices over a field.
Mathlib has neither Jordan blocks nor a similarity predicate at this version, so both are
defined locally; this is recorded as a modelling gap in the module docstring of the files that
use them.
-/

namespace Qatlib.Papers.GroupIsom10.MainResults.Model

/-- A paper-level quantum algorithm: an input type `I`, an output type `O`, a running-time
function `time`, a produced output `run`, and a success probability `succ`.  This is a
bookkeeping device for stating existence and cost bounds; it carries no circuit semantics. -/
structure QuantumAlgorithm (I O : Type*) where
  /-- Running time of the algorithm on each input. -/
  time : I → ℕ
  /-- Output produced by the algorithm on each input. -/
  run : I → O
  /-- Success probability of the algorithm on each input. -/
  succ : I → ℝ

/-- The running time of `alg` is bounded by a polynomial in the size function `size`. -/
def PolyBounded {I O : Type*} (size : I → ℕ) (alg : QuantumAlgorithm I O) : Prop :=
  ∃ c d : ℕ, ∀ x, alg.time x ≤ c * (size x + 1) ^ d

/-- The success probability of `alg` is at least `2/3` on every input ("with high
probability"). -/
def HighProbability {I O : Type*} (alg : QuantumAlgorithm I O) : Prop :=
  ∀ x, (2 : ℝ) / 3 ≤ alg.succ x

/-- Two square matrices over a field are **similar** when they are conjugate by an invertible
matrix (an element of `GL n K`).  Local definition: Mathlib at this version has no matrix
similarity predicate. -/
def IsSimilar {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup n K,
    B = ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * A * (P : Matrix n n K)

/-- The Jordan block of size `c` with eigenvalue `eig`: `eig` on the diagonal and `1` on the
superdiagonal.  Local definition: Mathlib at this version has no Jordan blocks. -/
noncomputable def jordanBlock (K : Type*) [Field K] (c : ℕ) (eig : K) :
    Matrix (Fin c) (Fin c) K :=
  fun i j => if i = j then eig else if j.val = i.val + 1 then 1 else 0

/-- The least common multiple of the orders of the elements `L h`, `h : Fin u` (the quantity
`m_S`, `m_T`, `m_1`, `m_2` of the paper for a tuple of lists or matrices). -/
noncomputable def familyLcm {u : ℕ} {α : Fin u → Type*} [∀ h, Monoid (α h)] (L : ∀ h, α h) : ℕ :=
  (List.finRange u).foldr (fun h acc => Nat.lcm (orderOf (L h)) acc) 1

/-- The least common multiple of the orders of all elements occurring in a list. -/
noncomputable def listOrderLcm {α : Type*} [Monoid α] (l : List α) : ℕ :=
  l.foldr (fun x acc => Nat.lcm (orderOf x) acc) 1

/-- The least common multiple of the element orders over a tuple of lists (the quantity `m_S`
or `m_T` of Section 4). -/
noncomputable def familyListLcm {u : ℕ} {F : Fin u → Type*} [∀ h, Monoid (F h)]
    (L : ∀ h, List (F h)) : ℕ :=
  (List.finRange u).foldr (fun h acc => Nat.lcm (listOrderLcm (L h)) acc) 1

end Qatlib.Papers.GroupIsom10.MainResults.Model
