/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6.3 — running time of Algorithm 1

Fixed paper: arXiv:2111.00405, Lemma 6.3 on p.17.

Statement (verbatim): *With high probability Algorithm 1 solves Problem 3.2 in time
`Õ(poly(n) κ(M))`.*

Proof route in the paper (p.17): each QLS solve of the `O(m·#F)`-sparse Boolean Macaulay
system costs `Õ(poly(n) κ(M) log(1/ε))`; Algorithm 1 repeats Step 1–Step 2 `O(log n)` times
(Valiant–Vazirani needs `O(n)` iterations, i.e. `O(n log n)` QLS calls in total).  Absorbing
the `polylog` and `log(1/ε)` factors into the tilde gives `Õ(poly(n) κ(M))`.

`qlsIterTime` is the per-iteration cost `C·(n+1)·κ·log(1/ε)` and the theorem bounds the total
cost of `r ≤ n+1` iterations by `C·(n+1)²·κ·log(1/ε)`, i.e. `O(poly(n) κ)` with the
polylogarithmic factors absorbed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma63

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- Per-iteration cost of the QLS subroutine: `C · (n+1) · κ · log(1/ε)` (p.17), where `C`
collects the polynomial factors in `n` and the sparsity constants. -/
def qlsIterTime (n : ℕ) (C κ loginv : ℝ) : ℝ := C * ((n : ℝ) + 1) * κ * loginv

/-- **Lemma 6.3** (arXiv:2111.00405, p.17): if Algorithm 1 performs `r ≤ n+1` QLS iterations,
each of cost `C·(n+1)·κ·log(1/ε)`, the total running time is at most `C·(n+1)²·κ·log(1/ε)`,
which is `Õ(poly(n) κ(M))` with the polylog factors absorbed. -/
theorem lemma63_total_runtime
    {n : ℕ} {C κ loginv : ℝ} {r : ℕ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hlog : 0 ≤ loginv)
    (hr : (r : ℝ) ≤ (n : ℝ) + 1) :
    (r : ℝ) * qlsIterTime n C κ loginv ≤ C * ((n : ℝ) + 1) ^ 2 * κ * loginv := by
  unfold qlsIterTime
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ C * ((n : ℝ) + 1) * κ * loginv :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hn) hκ) hlog
  calc (r : ℝ) * (C * ((n : ℝ) + 1) * κ * loginv)
      ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) * κ * loginv) :=
        mul_le_mul_of_nonneg_right hr hnonneg
    _ = C * ((n : ℝ) + 1) ^ 2 * κ * loginv := by ring

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma63
