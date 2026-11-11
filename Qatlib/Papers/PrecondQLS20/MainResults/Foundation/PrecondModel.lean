/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# PrecondQLS20 — shared paper-layer vocabulary

Source: Chakraborty–Gilyén–Jeffery, *The power of block-encoded matrix powers:
improved fast inversion, preconditioned quantum linear system solvers and fast
evaluation of matrix functions*, arXiv:2008.13295v2 (2020), fixed for this
development by the `PrecondQLS20` metadata record (`arxiv_version_used` is null;
the extracted claim text matches the v2 arXiv posting, retrieved as
`assets/2008.13295.pdf` / `.txt`).

This file fixes **only vocabulary**; no paper result is proved here.

* `OracleLedger` — the per-oracle application counter used by the complexity
  results (Proposition 6/7/8, Theorem 13, Corollary 14, Theorem 17, Lemma 22,
  Theorem 23, Theorem 29, Corollary 30, Theorem 33, Lemma 34, Lemma 35).
* `QubitBlockEncoding n m T α ε` — the paper's `(α, m, ε)`-block-encoding of a
  square operator `T` on `n` data qubits with `m` ancilla qubits.  It is the
  library's spectral `BlockEncoding` with the workspace pinned to the paper's
  `2^(n+m)` dimensions, so the `m` in every claim has a definite meaning.
* `SpecQueryComplexity` — a small predicate packaging the paper's `O(·)` / `Õ(·)`
  query bounds as `Asymptotics.IsBigO` against a growth parameter.

The docstrings of every consumer file cite the printed theorem number and page
of the fixed source.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLS20.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.Execution.WorkspaceCP

/-- Per-oracle application ledger of a paper construction.

* `qA` — applications of `U_A'` (the fast-inversion block-encoding of `A⁻¹`),
* `qB` — applications of `U_B` (the block-encoding of `B`),
* `qC` — applications of the controlled versions of `U_A'`, `U_B`,
* `qV` — applications of `V`, `O_D` and their inverses (contour-integral route),
* `qb` — applications of `U_b` / `U_Ψ` (right-hand side / state preparation),
* `qPrim` — additional primitive one- and two-qubit gates. -/
structure OracleLedger where
  qA : ℕ
  qB : ℕ
  qC : ℕ
  qV : ℕ
  qb : ℕ
  qPrim : ℕ
  deriving Repr

namespace OracleLedger

/-- The empty ledger (no oracle applications). -/
def zero : OracleLedger := ⟨0, 0, 0, 0, 0, 0⟩

/-- Pointwise addition of ledgers — the cost of concatenating two sub-routines. -/
def add (x y : OracleLedger) : OracleLedger :=
  ⟨x.qA + y.qA, x.qB + y.qB, x.qC + y.qC, x.qV + y.qV, x.qb + y.qb, x.qPrim + y.qPrim⟩

/-- Scalar multiple of a ledger — the cost of `k` repetitions of a sub-routine. -/
def smul (k : ℕ) (x : OracleLedger) : OracleLedger :=
  ⟨k * x.qA, k * x.qB, k * x.qC, k * x.qV, k * x.qb, k * x.qPrim⟩

/-- Total number of oracle applications, ignoring primitive gates. -/
def total (x : OracleLedger) : ℕ := x.qA + x.qB + x.qC + x.qV + x.qb

/-- The empty ledger has zero `A`-oracle applications. -/
@[simp] theorem zero_qA : zero.qA = 0 := rfl
/-- The empty ledger has zero total oracle applications. -/
@[simp] theorem zero_total : zero.total = 0 := rfl
/-- The `A`-counter of a concatenation adds componentwise. -/
@[simp] theorem add_qA (x y : OracleLedger) : (add x y).qA = x.qA + y.qA := rfl
/-- The `A`-counter of `k` repetitions is multiplied by `k`. -/
@[simp] theorem smul_qA (k : ℕ) (x : OracleLedger) : (smul k x).qA = k * x.qA := rfl
/-- The empty ledger is a left identity for concatenation. -/
@[simp] theorem zero_add (x : OracleLedger) : add zero x = x := by
  cases x; simp [add, zero]
/-- The empty ledger is a right identity for concatenation. -/
@[simp] theorem add_zero (x : OracleLedger) : add x zero = x := by
  cases x; simp [add, zero]

/-- Concatenating `k` copies of a sub-routine multiplies every counter by `k`. -/
theorem smul_total (k : ℕ) (x : OracleLedger) :
    (smul k x).total = k * x.total := by
  cases x
  simp [smul, total]
  ring

end OracleLedger

/-- The paper's `(α, m, ε)`-block-encoding of a square operator `T` on `n` data
qubits with `m` ancilla qubits, in the library's scaled spectral convention.

The workspace is pinned to exactly `2^(n+m)` dimensions, so `m` is the ancilla
budget of the claim.  Encodings are always *scaled*: the compression of the
unitary `U` between the isometric frames `L` and `R` is `α`-proportional to `T`
within spectral error `ε` (see `BlockEncoding`). -/
structure QubitBlockEncoding (n m : ℕ) (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε : ℝ) where
  /-- The encoding unitary. -/
  U : Matrix (Fin (2 ^ (n + m))) (Fin (2 ^ (n + m))) ℂ
  /-- Left isometric frame selecting the output data register. -/
  L : Matrix (Fin (2 ^ (n + m))) (Fin (2 ^ n)) ℂ
  /-- Right isometric frame selecting the input data register. -/
  R : Matrix (Fin (2 ^ (n + m))) (Fin (2 ^ n)) ℂ
  /-- The scaled approximate block-encoding property. -/
  encoding : BlockEncoding T U L R α ε

namespace QubitBlockEncoding

variable {n m : ℕ} {T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {α ε : ℝ}

/-- Normalisation is positive. -/
theorem pos (E : QubitBlockEncoding n m T α ε) : 0 < α := E.encoding.normalization_pos

/-- The error is nonnegative. -/
theorem err_nonneg (E : QubitBlockEncoding n m T α ε) : 0 ≤ ε := E.encoding.error_nonneg

/-- The encoded operator is `α`-bounded in spectral norm up to the error. -/
theorem opNorm_le (E : QubitBlockEncoding n m T α ε) : ‖T‖ ≤ α + ε := by
  have h1 : ‖T - α • compress E.L E.U E.R‖ ≤ ε := E.encoding.error_le
  have hcomp : ‖compress E.L E.U E.R‖ ≤ 1 := by
    have hU : ‖E.U‖ ≤ 1 :=
      Qatlib.Concepts.BlockEncoding.Encoding.unitary_norm_le_one
        E.encoding.unitary
    exact (Qatlib.Concepts.BlockEncoding.Encoding.compress_norm_le
      E.encoding.left_isometry E.encoding.right_isometry E.U).trans hU
  have hsmul : ‖α • compress E.L E.U E.R‖ ≤ α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos E.pos]
    exact mul_le_of_le_one_right E.pos.le hcomp
  calc
    ‖T‖ = ‖(T - α • compress E.L E.U E.R) + α • compress E.L E.U E.R‖ := by
          congr 1; abel
    _ ≤ ‖T - α • compress E.L E.U E.R‖ + ‖α • compress E.L E.U E.R‖ := norm_add_le _ _
    _ ≤ ε + α := add_le_add h1 hsmul
    _ = α + ε := add_comm _ _

/-- A `(α, m, ε)`-encoding is also a `(α, m, ε')`-encoding for any `ε' ≥ ε`. -/
def relax (E : QubitBlockEncoding n m T α ε) {ε' : ℝ} (h : ε ≤ ε') :
    QubitBlockEncoding n m T α ε' :=
  ⟨E.U, E.L, E.R, E.encoding.mono h⟩

end QubitBlockEncoding

/-- `QueryCostBound f g` — the paper's `O(·)`/`Õ(·)` query statements rendered as
`f = O(g)` along the growth parameter, with `g` the explicit closed form printed
in the theorem.  `f` is the ledger counter of a construction and `g` the source
cost formula. -/
def QueryCostBound {α : Type*} (l : Filter α) (f g : α → ℝ) : Prop :=
  Asymptotics.IsBigO l f g

/-- `BigOConst f g` — the paper's `O(·)` read at fixed problem size: there is an
absolute constant `C > 0` with `f ≤ C * g`.  Used to render the query-count
upper bounds of the complexity statements without committing to a growth
parameter. -/
def BigOConst (f g : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ f ≤ C * g

end Qatlib.Papers.PrecondQLS20.MainResults
