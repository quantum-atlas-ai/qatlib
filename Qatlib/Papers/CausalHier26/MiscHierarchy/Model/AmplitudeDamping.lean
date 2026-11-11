/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# AmplitudeDamping — reduced source model for the amplitude-damping hierarchy

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1.
PDF `prove/assets/2609.08639v1.pdf`,
plain text `.../2609.08639v1.txt`.

This file records the scalar quantities that appear after the paper's
symmetry reduction (Section 3) and the fixed-order/general-process charge-block
reductions (Appendices E and F).  It does **not** rebuild the raw 16x16 SDP;
the modelling boundary is stated per definition.

Objects:

* `s ε`      — coherence survival factor `sqrt (1 - ε)` (Eq. (51), p. 12).
* `Rε ε`     — `sqrt (ε^2 + 1 - ε)` (Eq. (51), p. 12).
* `Feps ε`   — the fixed-order variational objective `F_ε(x,y,z)` (Eq. (53), p. 12).
* `Hmat ε`   — the four-dimensional symmetric matrix `H_ε` (Eq. (63), p. 14).
* `pEps ε`   — the quartic `p_ε(μ)` (Eq. (66), p. 14).
* `genXc ε`  — the one-parameter general-process coherence family `x_c(t)` (Eq. (80), p. 16).
* `tStar ε`  — the optimal family parameter `t*` (Eq. (82), p. 16).

The reduced optimisation problems themselves (`muSeq`, `muPar`, `muGen`) are
defined in `ReducedBlocks.lean`, where the feasible block tuples are spelled out.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- Fixed arXiv:2609.08639v1, Eq. (51), p. 12: the no-jump coherence factor
`s = sqrt (1 - ε)`. -/
def s (ε : ℝ) : ℝ := Real.sqrt (1 - ε)

/-- Fixed arXiv:2609.08639v1, Eq. (51), p. 12: `R_ε = sqrt (ε^2 + 1 - ε)`. -/
def Rε (ε : ℝ) : ℝ := Real.sqrt (ε ^ 2 + 1 - ε)

/-- Fixed arXiv:2609.08639v1, Eq. (53), p. 12: the fixed-order objective
`F_ε (x,y,z) = 2 s x sqrt (y^2 + s^2 z^2) + 2 ε s y z + ε s z^2`. -/
def Feps (ε x y z : ℝ) : ℝ :=
  2 * s ε * x * Real.sqrt (y ^ 2 + (s ε) ^ 2 * z ^ 2)
    + 2 * ε * s ε * y * z + ε * s ε * z ^ 2

/-- Fixed arXiv:2609.08639v1, Eq. (63), p. 14: the real symmetric matrix `H_ε`
whose largest eigenvalue is the fixed-order optimum. -/
def Hmat (ε : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, s ε, 0;
     0, 0, 0, (s ε) ^ 2;
     s ε, 0, 0, ε * s ε;
     0, (s ε) ^ 2, ε * s ε, ε * s ε]

/-- Fixed arXiv:2609.08639v1, Eq. (66), p. 14: the quartic
`p_ε (μ) = (μ^2 - s^2)(μ^2 - ε s μ - s^4) - ε^2 s^2 μ^2`. -/
def pEps (ε μ : ℝ) : ℝ :=
  (μ ^ 2 - (s ε) ^ 2) * (μ ^ 2 - ε * s ε * μ - (s ε) ^ 4) - ε ^ 2 * (s ε) ^ 2 * μ ^ 2

/-- The closed unit-sphere constraint set in the nonnegative orthant used in
Eq. (52), p. 12. -/
def sphereNN : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The values of `F_ε` over `sphereNN`; Eq. (52), p. 12. -/
def sphereImage (ε : ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ × ℝ => Feps ε p.1 p.2.1 p.2.2) '' sphereNN

/-- Maximum of `F_ε` over the nonnegative unit sphere (Eq. (52), p. 12). -/
def maxF (ε : ℝ) : ℝ := sSup (sphereImage ε)

/-- Fixed arXiv:2609.08639v1, Eq. (80), p. 16: the coherence attained by the
one-parameter general-process family
`x_c(t) = 2 s (ε t + s sqrt (t (1 - t)))`. -/
def genXc (ε t : ℝ) : ℝ := 2 * s ε * (ε * t + s ε * Real.sqrt (t * (1 - t)))

/-- Fixed arXiv:2609.08639v1, Eq. (82), p. 16: the optimal family parameter
`t* = (1/2) (1 + ε / R_ε)`. -/
def tStar (ε : ℝ) : ℝ := (1 / 2) * (1 + ε / Rε ε)

/-- The closed-form general-process coherence `s (ε + R_ε)` (Eq. (79), p. 16). -/
def muGenClosed (ε : ℝ) : ℝ := s ε * (ε + Rε ε)

/-! ## Elementary facts about `s` and `R_ε` -/

/-- Strict positivity `0 < s` for `0 < ε < 1` (Eq. (51)). -/
theorem s_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < s ε := by
  unfold s
  exact Real.sqrt_pos.mpr (by linarith)

/-- Nonnegativity `0 ≤ s` for `ε ≤ 1`. -/
theorem s_nonneg {ε : ℝ} (h1 : ε ≤ 1) : 0 ≤ s ε :=
  Real.sqrt_nonneg _

/-- `s^2 = 1 - ε` for `ε ≤ 1`. -/
theorem s_sq {ε : ℝ} (h1 : ε ≤ 1) : s ε ^ 2 = 1 - ε := by
  unfold s
  exact Real.sq_sqrt (by linarith)

/-- `s < 1` for `0 < ε < 1`. -/
theorem s_lt_one {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : s ε < 1 := by
  have h := s_pos h0 h1
  have hsq := s_sq (ε := ε) (by linarith)
  nlinarith

/-- Nonnegativity `0 ≤ R_ε`. -/
theorem R_nonneg (ε : ℝ) : 0 ≤ Rε ε := Real.sqrt_nonneg _

/-- `R_ε^2 = ε^2 + 1 - ε` when the radicand is nonnegative. -/
theorem R_sq {ε : ℝ} (h0 : 0 ≤ ε ^ 2 + 1 - ε) : Rε ε ^ 2 = ε ^ 2 + 1 - ε := by
  unfold Rε
  exact Real.sq_sqrt h0

/-- For `0 ≤ ε ≤ 1` the relation `R_ε^2 = ε^2 + s^2`, used in the
Cauchy–Schwarz step of Lemma 4.5 and Proposition 4.4. -/
theorem R_sq_eq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Rε ε ^ 2 = ε ^ 2 + (s ε) ^ 2 := by
  rw [R_sq (ε := ε) (by nlinarith), s_sq (ε := ε) (by linarith)]
  ring

/-- Strict positivity `0 < R_ε` for `0 < ε < 1`. -/
theorem R_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < Rε ε := by
  unfold Rε
  apply Real.sqrt_pos.mpr
  nlinarith

/-- `R_ε ≥ ε` for `0 < ε < 1`; used to place `t*` in `[0,1]`. -/
theorem R_ge_s {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : s ε ≤ Rε ε := by
  unfold s Rε
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg ε]

end Qatlib.Papers.CausalHier26.MiscHierarchy.Model
