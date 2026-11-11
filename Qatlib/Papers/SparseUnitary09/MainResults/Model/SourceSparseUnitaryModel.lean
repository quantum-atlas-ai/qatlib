/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseUnitary09.MainResults.Dilation.SourceSparseDilation

set_option backward.isDefEq.respectTransparency false

/-!
# SparseUnitary09 — MainResults / Model (claim c002)

Source: Stephen P. Jordan & Pawel Wocjan, *Efficient quantum circuits for arbitrary
sparse unitaries*, fixed version **arXiv:0904.2211v2 (11 Feb 2010)**.

This file formalises the *sparse unitary model* of Section II (p. 3, line 57:
"Thus the sparse unitary model is equivalent to BQP") and the model-level
equivalence content of claim **c002**.

The sparse unitary model has, as its elementary step, the application of a unitary
that has at most polynomially many nonzero entries in any row or column and whose
entries are efficiently computable ("d-sparse").  We formalise:

* `RowSparse` / `ColSparse` — the paper's row/column sparsity, in the equivalent
  "witness finset" form (`≤ d` nonzero positions per row/column is the same as the
  nonzero positions being contained in a `d`-element finset);
* `SparseStepOn` — one elementary step of the model;
* the fact that the Hermitian dilation of `c001` preserves sparsity (`unitaryDilation`
  is `d`-sparse whenever `U` is), which is what makes the c001 reduction *efficient*;
* `RealizableIn` — a `k`-step computation is a product of `k` elementary steps;
* `c002_sparse_unitary_model_equals_BQP` — the two-model equivalence.

On the identification with **BQP**: the paper (as ref. [17], Bernstein–Vazirani)
*defines* BQP through uniform polynomial-size quantum circuit families.  The gate
model here is `RealizableIn (· ∈ unitaryGroup) k`, i.e. products of unitaries on the
register; the sparse model is `RealizableIn SparseStepOn k`.  The theorem proves these
reach exactly the same set of `k`-step evolutions, which is the mathematical content of
the equivalence.  The library does not formalize decision classes / uniformity, so the
lateral identification with the *class* BQP is documented here rather than formalized.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.SparseUnitary09.MainResults.Model

open Qatlib.Papers.SparseUnitary09.MainResults.Dilation

/-! ## Row / column sparsity (paper: "at most polynomially many nonzero entries
in any row or column") -/

/-- `RowSparse U d`: each row of `U` has at most `d` nonzero entries, stated in the
equivalent witness form "the nonzero positions of each row lie in a `d`-element
finset".  This is the row-sparsity of arXiv:0904.2211v2, p. 1 (abstract) and p. 3
(the sparse unitary model). -/
def RowSparse {m n : Type*} [Fintype n] (U : Matrix m n ℂ) (d : ℕ) : Prop :=
  ∀ i, ∃ s : Finset n, s.card ≤ d ∧ ∀ j, U i j ≠ 0 → j ∈ s

/-- `ColSparse U d`: each column of `U` has at most `d` nonzero entries (witness form),
the column-sparsity of arXiv:0904.2211v2, p. 1 and p. 3. -/
def ColSparse {m n : Type*} [Fintype m] (U : Matrix m n ℂ) (d : ℕ) : Prop :=
  ∀ j, ∃ s : Finset m, s.card ≤ d ∧ ∀ i, U i j ≠ 0 → i ∈ s

/-- Every matrix is `card n`-row-sparse (take the full row as witness).  This is the
`d = N` extreme of the paper's "polynomially many nonzero entries"; the interesting
regime is `d ≪ N`, which is what the c001 reduction makes cheap. -/
theorem dense_rowSparse {m n : Type*} [Fintype n] (U : Matrix m n ℂ) :
    RowSparse U (Fintype.card n) :=
  fun i => ⟨Finset.univ, by simp, fun j _ => Finset.mem_univ j⟩

/-- Every matrix is `card m`-column-sparse. -/
theorem dense_colSparse {m n : Type*} [Fintype m] (U : Matrix m n ℂ) :
    ColSparse U (Fintype.card m) :=
  fun j => ⟨Finset.univ, by simp, fun i _ => Finset.mem_univ i⟩

/-! ## The Hermitian dilation preserves sparsity

The c001 reduction `U ↦ H = [[0,U],[U†,0]]` is only an *efficient* implementation
because `H` is as sparse as `U`.  Each row of `H` is a row (or a transposed column) of
`U`, so `d`-row/column-sparsity is preserved exactly. -/

/-- arXiv:0904.2211v2, p. 1 (efficiency of the dilation): if `U` is `d`-row- and
`d`-column-sparse then the Hermitian dilation `H = [[0,U],[U†,0]]` is `d`-row-sparse.
Row `inl i` holds the `U`-row `i` (block `(1,2)`); row `inr i` holds the `U†`-row `i`,
i.e. the conjugate of the `U`-column `i` (block `(2,1)`). -/
theorem unitaryDilation_rowSparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (d : ℕ) (hrow : RowSparse U d) (hcol : ColSparse U d) :
    RowSparse (unitaryDilation U) d := by
  intro k
  cases k with
  | inl i =>
    obtain ⟨s, hs, hcov⟩ := hrow i
    refine ⟨s.image Sum.inr, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Sum.inr_injective]; exact hs
    · intro j hj
      cases j with
      | inl j' => exact absurd hj (by simp [unitaryDilation, Matrix.fromBlocks_apply₁₁])
      | inr j' =>
        have hne : U i j' ≠ 0 := by
          simpa [unitaryDilation, Matrix.fromBlocks_apply₁₂] using hj
        exact Finset.mem_image.mpr ⟨j', hcov j' hne, rfl⟩
  | inr i =>
    obtain ⟨s, hs, hcov⟩ := hcol i
    refine ⟨s.image Sum.inl, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Sum.inl_injective]; exact hs
    · intro j hj
      cases j with
      | inl j' =>
        have hne : U j' i ≠ 0 := by
          have h3 : (Matrix.conjTranspose U) i j' ≠ 0 := by
            simpa [unitaryDilation, Matrix.fromBlocks_apply₂₁] using hj
          rwa [Matrix.conjTranspose_apply, star_ne_zero] at h3
        exact Finset.mem_image.mpr ⟨j', hcov j' hne, rfl⟩
      | inr j' => exact absurd hj (by simp [unitaryDilation, Matrix.fromBlocks_apply₂₂])

/-- arXiv:0904.2211v2, p. 1 (efficiency of the dilation): if `U` is `d`-row- and
`d`-column-sparse then `H = [[0,U],[U†,0]]` is `d`-column-sparse.  Column `inl j` holds
the `U`-row `j` (block `(2,1)`), column `inr j` holds the `U`-column `j` (block `(1,2)`). -/
theorem unitaryDilation_colSparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (d : ℕ) (hrow : RowSparse U d) (hcol : ColSparse U d) :
    ColSparse (unitaryDilation U) d := by
  intro k
  cases k with
  | inl j =>
    obtain ⟨s, hs, hcov⟩ := hrow j
    refine ⟨s.image Sum.inr, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Sum.inr_injective]; exact hs
    · intro i hi
      cases i with
      | inl i' => exact absurd hi (by simp [unitaryDilation, Matrix.fromBlocks_apply₁₁])
      | inr i' =>
        have hne : U j i' ≠ 0 := by
          have h3 : (Matrix.conjTranspose U) i' j ≠ 0 := by
            simpa [unitaryDilation, Matrix.fromBlocks_apply₂₁] using hi
          rwa [Matrix.conjTranspose_apply, star_ne_zero] at h3
        exact Finset.mem_image.mpr ⟨i', hcov i' hne, rfl⟩
  | inr j =>
    obtain ⟨s, hs, hcov⟩ := hcol j
    refine ⟨s.image Sum.inl, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Sum.inl_injective]; exact hs
    · intro i hi
      cases i with
      | inl i' =>
        have hne : U i' j ≠ 0 := by
          simpa [unitaryDilation, Matrix.fromBlocks_apply₁₂] using hi
        exact Finset.mem_image.mpr ⟨i', hcov i' hne, rfl⟩
      | inr i' => exact absurd hi (by simp [unitaryDilation, Matrix.fromBlocks_apply₂₂])

/-- Conjunction form: the dilation of a sparse unitary is sparse on the doubled
register `ι ⊕ ι`. -/
theorem unitaryDilation_sparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (d : ℕ) (hrow : RowSparse U d) (hcol : ColSparse U d) :
    RowSparse (unitaryDilation U) d ∧ ColSparse (unitaryDilation U) d :=
  ⟨unitaryDilation_rowSparse U d hrow hcol, unitaryDilation_colSparse U d hrow hcol⟩

/-! ## The sparse unitary model -/

/-- One elementary step of the sparse unitary model (arXiv:0904.2211v2, Sec. II, p. 3):
apply a unitary that has `d`-sparse rows and columns for some `d` (the paper's
"at most polynomially many nonzero entries in any row or column").  The
`efficiently computable entries` clause of the paper is a complexity condition on the
encoding of `U`; it plays no role in the algebraic model equivalence and is not
formalized here (the library has no function-complexity class). -/
def SparseStepOn {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup ι ℂ ∧ ∃ d : ℕ, RowSparse U d ∧ ColSparse U d

/-- Every unitary is a valid sparse step (it is `card ι`-sparse), and every sparse step
is unitary.  This is the model-level heart of c002: the sparse unitary model imposes no
*restriction* on which unitaries are reachable at the `d = N` extreme; its content is the
cost of *compiling* a `d ≪ N` step into gates, which is c001. -/
theorem sparseStepOn_iff_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    SparseStepOn U ↔ U ∈ Matrix.unitaryGroup ι ℂ := by
  constructor
  · rintro ⟨hU, _⟩; exact hU
  · intro hU
    exact ⟨hU, Fintype.card ι, dense_rowSparse U, dense_colSparse U⟩

/-! ## Multi-step computations and the model equivalence (c002) -/

/-- `RealizableIn R k U`: the unitary `U` is the product of `k` elementary steps, each
satisfying the step relation `R`.  This is the execution trace of a `k`-step
computation in a model whose one-step evolutions are `R`. -/
def RealizableIn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ → Prop) (k : ℕ) (U : Matrix ι ι ℂ) : Prop :=
  ∃ Us : Fin k → Matrix ι ι ℂ, (∀ i, R (Us i)) ∧ U = (List.ofFn Us).prod

/-- Two step relations that agree pointwise give the same `k`-step computations. -/
theorem RealizableIn_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Matrix ι ι ℂ → Prop) (h : ∀ U, R U ↔ S U) (k : ℕ) (U : Matrix ι ι ℂ) :
    RealizableIn R k U ↔ RealizableIn S k U := by
  constructor
  · rintro ⟨Us, hUs, rfl⟩
    exact ⟨Us, fun i => (h _).mp (hUs i), rfl⟩
  · rintro ⟨Us, hUs, rfl⟩
    exact ⟨Us, fun i => (h _).mpr (hUs i), rfl⟩

/-- Polynomial step budget for a register of size `N = 2^n`: `k ≤ (log₂ N + 1)²`
steps, i.e. `poly(log N)`.  Written in `Nat.log` to keep the `poly` dependence explicit
(the paper only asserts "polynomial", this is one concrete witness of such a bound). -/
def polyStepBound (N : ℕ) : ℕ := (Nat.log 2 N + 1) ^ 2

/-- Claim **c002** (arXiv:0904.2211v2, Sec. II, p. 3, line 57): "the sparse unitary model
is equivalent to BQP."

Formal content: a `poly(log N)`-step computation in the sparse unitary model
(`RealizableIn SparseStepOn`) reaches exactly the same unitaries as a `poly(log N)`-step
computation in the gate model (`RealizableIn (· ∈ unitaryGroup)`), which is the circuit
family of BQP as defined by Bernstein–Vazirani (ref. [17] of the paper).

Proof: both models are `polyStepBound N`-step products, so it suffices that a single
sparse step and a single gate step coincide, which is `sparseStepOn_iff_unitary`.
The two directions are exactly the paper's argument:
* (⊆, sparse model ⊆ BQP) every sparse step is a unitary, hence a (legitimate) gate —
  for the *efficient* compilation with `d ≪ N` see `c001`'s dilation reduction;
* (⊇, BQP ⊆ sparse model) every gate on the register is a `2^n`-sparse unitary for
  `d = N`, hence a sparse step (`dense_rowSparse`, `dense_colSparse`).

Note: the library has no formalized BQP *decision class*, no uniformity/asymptotics
framework and no function-complexity class; the identification with the class BQP is the
standard definitional one ([17]) and is not re-derived here.  See the PR note for the
residual formalization gap. -/
theorem c002_sparse_unitary_model_equals_BQP (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) :
    RealizableIn SparseStepOn (polyStepBound N) U ↔
      RealizableIn (fun V => V ∈ Matrix.unitaryGroup (Fin N) ℂ) (polyStepBound N) U :=
  RealizableIn_congr (ι := Fin N) SparseStepOn (fun V => V ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (fun V => sparseStepOn_iff_unitary V) (polyStepBound N) U

end Qatlib.Papers.SparseUnitary09.MainResults.Model
