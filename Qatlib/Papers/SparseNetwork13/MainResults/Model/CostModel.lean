/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.ElectricalNetwork

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — query-cost model for the algorithmic claims

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

The paper's main results (Lemmas 3--5, Theorems 2--5, Corollaries 1--3) are *algorithmic
existence* statements: "there is a gate-efficient quantum algorithm making `O(·)` oracle
queries that outputs ...".  The quantum circuit model and its query-count analysis are not
formalised in this block; what *is* recorded and proved here is the quantitative backbone of
the claims — the paper's cost functions and the algebraic reductions its proofs perform
(e.g. Eq. (67), (81), (83)).

The leading-order cost functions are taken verbatim from the paper, with the unspecified
`poly log` factors dropped (as in the paper's displayed `O(·)` bounds).  `g` is the norm of
the rescaled right-hand side and `κ_f` the finite condition number, exactly as in the
proofs of Theorem 2 / Theorem 3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SparseNetwork13.MainResults.Model

/-! ## §3.1 state-estimation costs (Lemmas 3, 4, 5) -/

/-- Lemma 3's leading cost `d·κ²/ε` for an `ε`-multiplicative norm estimate (p.10). -/
def costLemma3 (d kappa eps : ℝ) : ℝ := d * kappa ^ 2 / eps

/-- Lemmas 4 and 5's leading cost `d·q²·κ³/ε²` for an `ε`-additive entry / entry-difference
estimate (p.10). -/
def costLemma45 (d q kappa eps : ℝ) : ℝ := d * q ^ 2 * kappa ^ 3 / eps ^ 2

/-! ## §3.2 Laplacian-system cost model (Theorem 2) -/

/-- The finite condition number `κ_f = 2cd/λ` of the rescaled Laplacian (proof of Theorem 2,
p.15, just below Eq. (66)). -/
def laplacianCond (c d lam : ℝ) : ℝ := 2 * c * d / lam

/-- The norm `g = ‖b̃‖ = 1/(2cd)` of the rescaled right-hand side (proof of Theorem 2,
p.16). -/
def laplacianBNorm (c d : ℝ) : ℝ := 1 / (2 * c * d)

/-- The cost `d·(d·g²·κ_f³/ε²)` that Lemma 5 supplies inside Theorem 2's proof, with `g` and
`κ_f` of the Laplacian system (proof of Theorem 2, Eq. (67), left side). -/
def costTheorem2Proof (c d lam eps : ℝ) : ℝ :=
  d ^ 2 * laplacianBNorm c d ^ 2 * laplacianCond c d lam ^ 3 / eps ^ 2

/-- The paper's stated ENA-V cost `c·d³/(λ³·ε²)` (Theorem 2, p.15; Eq. (67) right side). -/
def costTheorem2 (c d lam eps : ℝ) : ℝ := c * d ^ 3 / (lam ^ 3 * eps ^ 2)

/-- **Eq. (67) of Theorem 2.**  `d·(d·g²·κ_f³/ε²) = 2·c·d³/(λ³·ε²)`, i.e. the Lemma-5 cost
with `g = 1/(2cd)`, `κ_f = 2cd/λ` reduces to the paper's claimed ENA-V bound up to the
constant `2` (absorbed by `O(·)`). -/
theorem theorem2_cost_reduction (c d lam eps : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hlam : 0 < lam) (heps : 0 < eps) :
    costTheorem2Proof c d lam eps = 2 * costTheorem2 c d lam eps := by
  unfold costTheorem2Proof costTheorem2 laplacianBNorm laplacianCond
  field_simp

/-! ## §3.2 separated-system cost model (Theorem 3 / Corollary 1) -/

/-- The condition number `κ_f = √(2cd/λ)` of the separated system (proof of Theorem 3, p.17,
just below Eq. (79)). -/
def separatedCond (c d lam : ℝ) : ℝ := Real.sqrt (2 * c * d / lam)

/-- The norm `g = ‖|b⟩‖ = 1/√(2cd)` of the separated system's right-hand side (proof of
Theorem 3, p.17). -/
def separatedBNorm (c d : ℝ) : ℝ := 1 / Real.sqrt (2 * c * d)

/-- The cost that Lemma 4 supplies inside Theorem 3's proof, `d·g²·κ_f³/(ε')²` with
`ε' = ε/√c` (proof of Theorem 3, Eq. (81), left side). -/
def costTheorem3Proof (c d lam eps : ℝ) : ℝ :=
  d * separatedBNorm c d ^ 2 * separatedCond c d lam ^ 3 / (eps / Real.sqrt c) ^ 2

/-- The paper's stated ENA-C cost `c^{1.5}d^{1.5}/(λ^{1.5}ε²)` (Theorem 3, p.17), written as
`√2·(c√c)(d√d)/((λ√λ)ε²)` — the constant `√2` is what Eq. (81) produces and is absorbed by
`O(·)`. -/
def costTheorem3 (c d lam eps : ℝ) : ℝ :=
  Real.sqrt 2 * (c * Real.sqrt c) * (d * Real.sqrt d)
    / (lam * Real.sqrt lam * eps ^ 2)

/-- Corollary 1 (adjacent `s,t`) makes the same number of queries as Theorem 3 (p.18): the
Ohm's-law conversion `|v(s)−v(t)| = |i(e)|/w_e` costs nothing extra. -/
def costCorollary1 (c d lam eps : ℝ) : ℝ := costTheorem3 c d lam eps

/-! ## §3.2 power / effective-resistance model (Theorem 4 / Corollary 2) -/

/-- The cost `d·κ_f²/ε` that Lemma 3 supplies inside Theorem 4's proof, with the separated
system's `κ_f` (proof of Theorem 4, Eq. (83), left side). -/
def costTheorem4Proof (c d lam eps : ℝ) : ℝ := d * separatedCond c d lam ^ 2 / eps

/-- The paper's stated ENA-P cost `c·d²/(λ·ε)` (Theorem 4, p.18; Eq. (83) right side). -/
def costTheorem4 (c d lam eps : ℝ) : ℝ := 2 * c * d ^ 2 / (lam * eps)

/-- **Eq. (83) of Theorem 4.**  `d·κ_f²/ε = 2cd²/(λε)` with `κ_f = √(2cd/λ)`; exactly the
paper's claimed ENA-P bound (constant `2`). -/
theorem theorem4_cost_reduction (c d lam eps : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hlam : 0 < lam) (heps : 0 < eps) :
    costTheorem4Proof c d lam eps = costTheorem4 c d lam eps := by
  unfold costTheorem4Proof costTheorem4 separatedCond
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- Corollary 2 (effective resistance) makes the same number of queries as Theorem 4 (p.18):
the extra factor `2` is a downstream multiplicative constant on the *output*. -/
def costCorollary2 (c d lam eps : ℝ) : ℝ := costTheorem4 c d lam eps

/-! ## §4.3 quantum-walk cost model (Theorem 5 / Corollary 3) -/

/-- First branch of Theorem 5's cost, `c^{0.5}d^{1.5}/(ε·λ)` (p.28). -/
def costTheorem5BranchA (c d lam eps : ℝ) : ℝ :=
  Real.sqrt c * d * Real.sqrt d / (eps * lam)

/-- Second branch of Theorem 5's cost, `c·d^{0.5}/(ε·λ^{1.5})` (p.32). -/
def costTheorem5BranchB (c d lam eps : ℝ) : ℝ :=
  c * Real.sqrt d / (eps * lam * Real.sqrt lam)

/-- The paper's stated ENA-P walk cost `min{c^{0.5}d^{1.5}/(ε λ), c d^{0.5}/(ε λ^{1.5})}`
(Theorem 5, p.28). -/
def costTheorem5 (c d lam eps : ℝ) : ℝ :=
  min (costTheorem5BranchA c d lam eps) (costTheorem5BranchB c d lam eps)

/-- Corollary 3 (effective resistance by the walk) has the same cost as Theorem 5 (p.32). -/
def costCorollary3 (c d lam eps : ℝ) : ℝ := costTheorem5 c d lam eps

/-! ## §4.2 walk / phase-estimation implementation costs (Lemmas 12, 13, 14) -/

/-- Lemma 12: implementing `U(A,B)` perfectly costs `O(d)` oracle calls (p.25). -/
def costLemma12 (d : ℝ) : ℝ := d

/-- Lemma 13: implementing `U(A,B)` to precision `δ` costs `O(√(c/λ)·poly log(d/δ))`;
we record the leading factor and keep the polylog as an explicit input `pl` (p.26). -/
def costLemma13 (c lam pl : ℝ) : ℝ := Real.sqrt (c / lam) * pl

/-- Lemma 14: threshold phase estimation costs `O((1/Δ)·log(1/δ))` uses of `U` (p.28). -/
def costLemma14 (Delta delta : ℝ) : ℝ := Real.log (1 / delta) / Delta

end Qatlib.Papers.SparseNetwork13.MainResults.Model
