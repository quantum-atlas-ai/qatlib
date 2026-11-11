/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — matrix products over semirings (definitions)

Le Gall and Nishimura, fixed arXiv:1310.3898v1.
PDF SHA-256 1d042e95c69668deb534b7bc64dacdbeab9ccd52d8c325d88efc1728fd339971.

This module records the algebraic objects the paper's algorithms compute, exactly as
stated in Section 1 (Boolean, `(max,min)` and distance products), Definition 2.1
(existence dominance product `A ∗ B` and the auxiliary product `A ⊳ B`) and
Definition 3.1 (generalized existence dominance product).

Carrier conventions.  The paper uses several carriers: `ℤ ∪ {-∞, ⊤}` for the
`(max,min)` semiring, `ℤ ∪ {∞}` for the distance product, `ℤ ∪ {∞}` for the left
factor and `ℤ ∪ {-∞}` for the right factor of a dominance product.  Here the
signed carrier `Val := WithBot (WithTop ℤ)` is used for the two dominance products
and for the `(max,min)` product (`⊥` is `-∞`, `⊤` is `+∞`), and `DVal := WithTop ℤ`
is used for the distance product (`⊤` is `∞`).  A matrix over `ℤ ∪ {∞}` or
`ℤ ∪ {-∞}` is represented as a matrix over the corresponding subcarrier, so every
statement below restricts verbatim to the paper's carriers; no value outside the
paper's sets is ever produced by a product.

Boundary: the running times of the paper's quantum algorithms are not modelled
here; only the products themselves and the exact algebraic identities that the
running-time analyses rely on are stated.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMatSemiring13.MainResults

open Matrix

/-- The signed carrier `ℤ ∪ {-∞, +∞}`: `⊥` is `-∞`, `⊤` is `+∞`, and `↑(↑z)` is `z`. -/
abbrev Val : Type := WithBot (WithTop ℤ)

/-- The carrier `ℤ ∪ {∞}` of the distance product; `⊤` is `∞`. -/
abbrev DVal : Type := WithTop ℤ

/-- The integer `z`, seen in `ℤ ∪ {-∞, +∞}`. -/
def Val.ofInt (z : ℤ) : Val := ↑(↑z)

/-- `-∞`, the bottom element of `ℤ ∪ {-∞, +∞}`. -/
def Val.negInf : Val := ⊥

/-- `+∞`, the top element of `ℤ ∪ {-∞, +∞}`. -/
def Val.posInf : Val := ⊤

/-- The embedding `ℤ ↪ ℤ ∪ {-∞, +∞}` is injective. -/
theorem Val.ofInt_injective : Function.Injective Val.ofInt := by
  intro a b h
  exact WithBot.coe_inj.mp (WithTop.coe_inj.mp h)

/-- `-∞` is below every integer of `ℤ ∪ {-∞, +∞}`. -/
theorem Val.negInf_lt_ofInt (z : ℤ) : Val.negInf < Val.ofInt z := WithBot.bot_lt_coe _

/-- `+∞` is above every integer of `ℤ ∪ {-∞, +∞}`. -/
theorem Val.ofInt_lt_posInf (z : ℤ) : Val.ofInt z < Val.posInf :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top z)

/-- Section 1: the Boolean matrix product, `C[i,j] = 1` iff some `k` has
`A[i,k] = 1` and `B[k,j] = 1`.  Boolean matrices are represented as `Prop`-valued
matrices, so `A i k` reads "the entry `A[i,k]` is `1`". -/
def booleanProd {n : ℕ} (A B : Matrix (Fin n) (Fin n) Prop) : Matrix (Fin n) (Fin n) Prop :=
  fun i j => ∃ k : Fin n, A i k ∧ B k j

/-- Section 1: the `(max, min)`-product over the semiring `(ℤ ∪ {-∞,∞}, max, min)`,
`C[i,j] = max_k min (A[i,k]) (B[k,j])`.  The maximum of an empty family is `-∞`. -/
def maxMinProd {n : ℕ} (A B : Matrix (Fin n) (Fin n) Val) : Matrix (Fin n) (Fin n) Val :=
  fun i j => (Finset.univ : Finset (Fin n)).sup (fun k => min (A i k) (B k j))

/-- Section 1: the distance product over the semiring `(ℤ ∪ {∞}, min, +)`,
`C[i,j] = min_k (A[i,k] + B[k,j])`.  The minimum of an empty family is `∞`. -/
def distProd {n : ℕ} (A B : Matrix (Fin n) (Fin n) DVal) : Matrix (Fin n) (Fin n) DVal :=
  fun i j => (Finset.univ : Finset (Fin n)).inf (fun k => A i k + B k j)

/-- Definition 2.1, first part: the existence dominance product `A ∗ B` is the
Boolean matrix with `(A ∗ B)[i,j] = 1` iff `A[i,k] ≤ B[k,j]` for some `k`.  The
carrier is kept general: Section 4.2 also applies the definition to shifted
rational matrices. -/
def existsDominance {R : Type*} [LE R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) Prop :=
  fun i j => ∃ k : Fin n, A i k ≤ B k j

/-- Definition 2.1, first part, strict variant (footnote 2 of the paper): replace
`≤` by `<` in the existence dominance product.  The paper notes that every result
on the existence dominance product transfers to this strict variant. -/
def strictExistsDominance {R : Type*} [LT R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) Prop :=
  fun i j => ∃ k : Fin n, A i k < B k j

/-- Definition 2.1, second part: the product `A ⊳ B` over `ℤ ∪ {-∞,∞}`.  Its
`(i,j)` entry is `-∞` when `A[i,k] > B[k,j]` for every `k`, and is
`max_k {A[i,k] | A[i,k] ≤ B[k,j]}` otherwise. -/
def dominance {n : ℕ} (A B : Matrix (Fin n) (Fin n) Val) : Matrix (Fin n) (Fin n) Val :=
  fun i j => (Finset.univ : Finset (Fin n)).sup (fun k => if A i k ≤ B k j then A i k else ⊥)

/-- The generalized existence dominance product of Definition 3.1.  Values live in
`S ∪ {(0,0)}` with `S = {1,...,u} × {1,...,v}`; `(0,0)` is the bottom element `⊥`
and `S` is ordered lexicographically, which is the order induced by `Lex` on
`Fin u × Fin v`.  The `(i,j)` entry is the lexicographic maximum of
`{(0,0)} ∪ {(x,y) | (A x ∗ B y)[i,j] = 1}`. -/
noncomputable def generalizedDominance {n u v : ℕ}
    (A : Fin u → Matrix (Fin n) (Fin n) Val)
    (B : Fin v → Matrix (Fin n) (Fin n) Val) :
    Matrix (Fin n) (Fin n) (WithBot (Lex (Fin u × Fin v))) := by
  classical
  exact fun i j => (Finset.univ : Finset (Fin u × Fin v)).sup
    (fun xy => if existsDominance (A xy.1) (B xy.2) i j
      then (↑(toLex xy) : WithBot (Lex (Fin u × Fin v))) else ⊥)

/-- `Lex` on `Fin u × Fin v` is the paper's lexicographic order: the first index
dominates. -/
theorem toLex_lt_of_fst_lt {u v : ℕ} {p q : Fin u × Fin v} (h : p.1 < q.1) :
    toLex p < toLex q := by
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- `Lex` on `Fin u × Fin v` is the paper's lexicographic order: the second index
breaks ties. -/
theorem toLex_lt_of_fst_eq {u v : ℕ} {p q : Fin u × Fin v} (h : p.1 = q.1) (h2 : p.2 < q.2) :
    toLex p < toLex q := by
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨h, h2⟩

end Qatlib.Papers.QMatSemiring13.MainResults
