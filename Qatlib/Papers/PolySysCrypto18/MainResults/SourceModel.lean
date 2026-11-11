/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# PolySysCrypto18 — shared model

Chen–Gao–Yuan, *Quantum Algorithm for Optimization and Polynomial System Solving
over Finite Field and Application to Cryptanalysis*, arXiv:1802.03856v2 (7 Oct
2018).  Fixed version used throughout this block.

This file fixes the small amount of shared vocabulary used by the section files
`Sec2Reductions` … `Sec9NTRU`:

* `System` / `Solves` — the decision-and-certificate specification of a
  polynomial-system solver (Theorem 1.1, 3.7, 3.13, …).  The paper's quantum
  algorithm returns a solution when one exists and reports "fail" otherwise; the
  abstract output type `Option (Fin n → ZMod p)` records exactly that.
* `theta` — the Boolean encoding `θ_b` of equation (2) on p.5.
* `SoftOh` — the paper's `O~` notation, made explicit as "at most a constant
  times the reported expression times a polylogarithmic slack in the stated
  size parameter".  The section theorems instantiate the reported expression
  with the explicit sparseness / variable bounds obtained from the preceding
  lemmas, so the remaining content is an ordinary real inequality.

Boundary: this block states the paper's results in the paper's own notation.
It does not claim a gate-level compilation of the algorithms; the quantum-algorithm
existence is encoded by the `∃ out, Solves F out` specification together with the
cost accounting of the paper's algorithm, as in the reference blocks
`ShorFactoring97` and `ClassShadows20`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults

/-! ## The decision / certificate specification -/

/-- A finite polynomial system over `ZMod p` in `n` variables, carried by its
solution set `V_{F_p}(F) ⊆ F_p^n` (`V_{F_q}(F)` in §3.3). -/
structure System (p n : ℕ) : Type where
  /-- the number of equations `r = #F` -/
  r : ℕ
  /-- the solution set `V_{F_p}(F)` (or `V_{F_q}(F)` for the `F_q` version) -/
  solutions : Set (Fin n → ZMod p)

/-- `Solves F out`: the output `out` decides whether `F = 0` has a solution and,
when it does, returns one.  This is the correctness specification of the paper's
`QBoolSol`-based solvers (Theorem 1.1, Theorem 3.7, Theorem 3.13, Proposition 4.7,
Theorem 5.4, …): the algorithm computes a solution "if F = 0 does have solutions"
and otherwise reports failure. -/
def Solves {p n : ℕ} (F : System p n) (out : Option (Fin n → ZMod p)) : Prop :=
  (∃ X, X ∈ F.solutions) ↔ ∃ X, out = some X ∧ X ∈ F.solutions

/-- A real-valued cost function of the paper's size parameters. -/
abbrev Cost (ι : Type) := ι → ℝ

/-! ## Soft-O notation (`O~`)

The paper writes every complexity as `O~(φ)`, meaning "`O(φ · polylog)`.  We keep
the reported expression `φ` explicit and allow a multiplicative
`(log (2 + size)) ^ k` slack with an existential exponent `k`; `size` is the
natural size parameter of the problem (`n + m + r + log p` etc.).  This is the
standard reading of `O~`, and the section theorems supply `φ` with the explicit
constants from the sparseness lemmas, so they are ordinary inequalities.
-/
def SoftOh (cost : ℝ) (bound : ℝ) (size : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 < C ∧ cost ≤ C * bound * (Real.log (2 + size)) ^ k

/-- The shape of an algorithmic claim: a correct output exists and the paper's
accounted cost is `O~ (bound)`. -/
def QAlgClaim (spec : Prop) (cost bound size : ℝ) : Prop :=
  spec ∧ SoftOh cost bound size

/-! ## The encoding θ_b of equation (2) -/

/-- The paper's `θ_b` (equation (2), p.5).  For `b > 0` and `s = ⌊log₂ b⌋`,
`θ_b (B) = Σ_{i<s} B_i 2^i + (b + 1 − 2^s) B_s`, where `B : Fin (s+1) → ℕ` is
fed Boolean values `0/1`. -/
def theta (b : ℕ) (B : Fin (Nat.log2 b + 1) → ℕ) : ℕ :=
  (∑ i : Fin (Nat.log2 b), B i.castSucc * 2 ^ (i : ℕ))
    + (b + 1 - 2 ^ Nat.log2 b) * B (Fin.last _)

/-- The number of monomials of `θ_b` (its sparseness `#θ_b`), as asserted in
Lemma 2.1: `⌊log₂ b⌋ + 1`. -/
def thetaSparseness (b : ℕ) : ℕ := Nat.log2 b + 1

/-- The number of Boolean variables in `B_bit` (Lemma 2.1: `#B_bit = ⌊log₂ b⌋+1`). -/
def thetaVarCount (b : ℕ) : ℕ := Nat.log2 b + 1

variable {b : ℕ}

-- (`theta_le`, the `θ_b` range lemma of Lemma 2.1, is proved in
-- `Sec2Reductions/SourceTheta.lean`, imported downstream.)

/-- Number of variables of `B_bit` equals the sparseness of `θ_b`
(Lemma 2.1, p.5). -/
theorem theta_varCount_eq_sparseness : thetaVarCount b = thetaSparseness b := rfl

/-! ## ℤ-matrix helpers used in §7–§8 -/

/-- The `∞`-norm (max absolute entry) of a matrix, as used in Lemma 8.1 – 8.4. -/
def infNorm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup (fun i => Finset.univ.sup (fun j => Int.natAbs (B i j)))

/-- The squared Euclidean norm `‖v‖₂² = Σ v_i²` of a real vector -/
def sqNorm {m : ℕ} (v : Fin m → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- The Euclidean norm `‖v‖₂ = √(Σ v_i²)` -/
noncomputable def l2Norm {m : ℕ} (v : Fin m → ℝ) : ℝ := Real.sqrt (sqNorm v)

end Qatlib.Papers.PolySysCrypto18.MainResults
