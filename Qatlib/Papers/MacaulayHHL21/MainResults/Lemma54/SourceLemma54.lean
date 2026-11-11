/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.4 — sparsity of the Boolean Macaulay matrix

Fixed paper: arXiv:2111.00405, Lemma 5.4 on p.13.

Statement (verbatim): *The Boolean Macaulay matrix `B̂` of total degree `d` of `F₁` is an
`O(m · #F₁)`-sparse matrix.*  (Recall: a matrix is `s`-sparse if it has at most `s` entries in
any row or column; `m = #F₁`.)

The paper's proof has two steps: (i) each row `(m̂, f)` holds `ψ(m̂f)`, so its support has size
at most `#F₁`; (ii) for a column `m′` the only contributing rows have `m̂ = m′/t` with `t` a
divisor of `m′`, and a multilinear `t` of degree at most `2` has at most `4` divisors, giving
column sparsity at most `4·#F₁`.  Both bounds are recorded as fields of
`BooleanMacaulayMatrix`; deriving them from an explicit orbit/`ψ` construction of `B̂`
(Definition 5.1) is the remaining formalisation gap, so this claim is reported as partial in
the PR table.  The theorem below is the paper's conclusion from these two facts.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma54

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- A matrix is `s`-sparse when every row and every column has at most `s` nonzero entries
(p.13). -/
def Sparse {R C : ℕ} (A : Matrix (Fin R) (Fin C) ℂ) (s : ℕ) : Prop :=
  (∀ i, (univ.filter (fun j => A i j ≠ 0)).card ≤ s) ∧
  (∀ j, (univ.filter (fun i => A i j ≠ 0)).card ≤ s)

/-- The Boolean Macaulay matrix `B̂` of total degree `d` (Definition 5.1, p.12), together with
the two combinatorial bounds supplied by the proof of Lemma 5.4: row support at most `#F₁`,
column support at most `4·#F₁`. -/
structure BooleanMacaulayMatrix (m F1 R C : ℕ) where
  /-- The matrix itself (rows indexed by `(m̂, f)`, columns by multilinear monomials). -/
  matrix : Matrix (Fin R) (Fin C) ℂ
  /-- Row support: the support of `ψ(m̂·f)` has size at most `#F₁`. -/
  hrow : ∀ i, (univ.filter (fun j => matrix i j ≠ 0)).card ≤ F1
  /-- Column support: at most `4` divisors times `#F₁` polynomials. -/
  hcol : ∀ j, (univ.filter (fun i => matrix i j ≠ 0)).card ≤ 4 * F1

/-- **Lemma 5.4** (arXiv:2111.00405, p.13): the Boolean Macaulay matrix of `F₁` is
`O(m·#F₁)`-sparse; concretely, with `m ≥ 1` rows, it is `4·m·#F₁`-sparse. -/
theorem lemma54_sparsity {m F1 R C : ℕ} (hm : 1 ≤ m)
    (B : BooleanMacaulayMatrix m F1 R C) :
    Sparse B.matrix (4 * m * F1) := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have h4 : 1 ≤ 4 * m := Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 4) hmpos)
  have hle : F1 ≤ 4 * m * F1 := by
    have h := Nat.mul_le_mul_right F1 h4
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hle4 : 4 * F1 ≤ 4 * m * F1 :=
    Nat.mul_le_mul_right F1 (Nat.le_mul_of_pos_right 4 hmpos)
  exact ⟨fun i => (B.hrow i).trans hle, fun j => (B.hcol j).trans hle4⟩

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma54
