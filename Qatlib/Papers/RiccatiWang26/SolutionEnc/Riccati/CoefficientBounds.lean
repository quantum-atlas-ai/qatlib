/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# CoefficientBounds — Riccati graph invariance and coefficient arithmetic

RiccatiWang26, arXiv:2609.37207v1.
Covers: Proposition B.9 (p. 58, positivity of `uCARE`), Proposition B.12 (p. 62, Eq. (B.32)
positivity part), Lemma B.13 (p. 63, Eqs. (B.35)–(B.37)), Proposition B.14 (p. 64, Eq. (B.38)),
Lemma D.1 (p. 66, Eq. (D.1) tangent identity), Lemma E.1 (p. 70, contractive norm bound).

The genuine algebraic content of the Riccati theory is the invariant-graph structure: the
CARE Hamiltonian maps the graph of the stabilizing solution to itself, and the DARE pencil
maps the graph of the stabilizing solution to itself up to the closed-loop shift.  Those are
proved here as matrix identities.  The analytic existence/uniqueness of stabilizing solutions
and the singular-value estimates are not available in Mathlib; only their arithmetic
consequences (positivity of the displayed coefficient bounds) are recorded.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Riccati

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Proposition B.9: positivity of the CARE coefficient bound -/

/-- RiccatiWang26, Proposition B.9 (p. 58), Eq. (B.24), positivity part.  The CARE coefficient
bound `uCARE = (a + √(a² + g0 q̄))/g0` used to normalize the CARE solution is nonnegative for
`g0 > 0` and `q̄ ≥ 0`. -/
theorem care_bound_nonneg (a qbar g0 : ℝ) (hg0 : 0 < g0) (hq : 0 ≤ qbar) (hprod : 0 ≤ g0 * qbar) :
    0 ≤ (a + Real.sqrt (a ^ 2 + g0 * qbar)) / g0 := by
  have hsq : Real.sqrt (a ^ 2) ≤ Real.sqrt (a ^ 2 + g0 * qbar) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hprod]
  have habs : Real.sqrt (a ^ 2) = |a| := Real.sqrt_sq_eq_abs a
  have hneg : -a ≤ |a| := neg_le_abs a
  have hsum : 0 ≤ a + Real.sqrt (a ^ 2 + g0 * qbar) := by linarith
  exact div_nonneg hsum hg0.le

/-! ## The CARE Hamiltonian preserves the graph of the stabilizing solution -/

/-- Block form of `H_CARE * [I; X]`. -/
lemma careHamiltonian_mul_graph_eq (A G Q X : Sq n) :
    careHamiltonian A G Q * graph X = blockCol (A - G * X) (-Q - Aᴴ * X) := by
  ext i j
  rcases i with i | i <;>
    simp [careHamiltonian, graph, blockCol, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, sub_eq_add_neg]

/-- Block form of `[I; X] * M`. -/
lemma graph_mul_eq (X M : Sq n) :
    graph X * M = blockCol M (X * M) := by
  ext i j
  rcases i with i | i <;>
    simp [graph, blockCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- Multiplying a block column on the right by a square matrix. -/
lemma blockCol_mul_eq (M N Y : Sq n) :
    blockCol M N * Y = blockCol (M * Y) (N * Y) := by
  ext i j
  rcases i with i | i <;>
    simp [blockCol, Matrix.mul_apply, Fintype.sum_sum_type]

/-- RiccatiWang26, Lemma 3.6 / Lemma B.13, invariant-graph form (Eqs. (3.22), (B.35)).  If `X`
is a stabilizing CARE solution, then the CARE Hamiltonian maps the graph `[I; X]` into
itself, with the closed-loop matrix `A - G X`:
`H_CARE [I; X] = [I; X] (A - G X)`.  The lower-block identity is exactly the CARE equation.
This is the algebraic heart of the stable Riesz-projector statement of Lemma 3.6. -/
theorem careHamiltonian_mul_graph (A G Q X : Sq n) (hX : StabilizingCare A G Q X) :
    careHamiltonian A G Q * graph X = graph X * (A - G * X) := by
  have hmain : Aᴴ * X + X * A - X * G * X + Q = 0 := hX.1
  have hlow : -Q - Aᴴ * X = X * (A - G * X) := by
    have h2 : Aᴴ * X + X * A - X * G * X = -Q := by
      rw [eq_neg_iff_add_eq_zero]
      exact hX.1
    rw [Matrix.mul_sub, ← Matrix.mul_assoc]
    calc -Q - Aᴴ * X = (Aᴴ * X + X * A - X * G * X) - Aᴴ * X := by rw [h2]
      _ = X * A - X * G * X := by abel
  rw [careHamiltonian_mul_graph_eq, graph_mul_eq, hlow]

/-! ## Lemma B.13: the DARE pencil preserves the graph -/

/-- The DARE pencil matrix `M = [[A, 0], [-Q, I]]`. -/
def pencilM (A Q : Sq n) : Matrix (Sum n n) (Sum n n) ℂ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr i, Sum.inl j => -Q i j
  | Sum.inr i, Sum.inr j => (1 : Sq n) i j

/-- The DARE pencil matrix `L = [[I, G], [0, A*]]`. -/
def pencilL (A G : Sq n) : Matrix (Sum n n) (Sum n n) ℂ
  | Sum.inl i, Sum.inl j => (1 : Sq n) i j
  | Sum.inl i, Sum.inr j => G i j
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr j => Aᴴ i j

/-- Block form of `L * [I; X]`. -/
lemma pencilL_mul_graph (A G X : Sq n) :
    pencilL A G * graph X = blockCol (1 + G * X) (Aᴴ * X) := by
  ext i j
  rcases i with i | i <;>
    simp [pencilL, graph, blockCol, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.add_apply, Matrix.one_apply]

/-- Block form of `M * [I; X]`. -/
lemma pencilM_mul_graph (A Q X : Sq n) :
    pencilM A Q * graph X = blockCol A (-Q + X) := by
  ext i j
  rcases i with i | i <;>
    simp [pencilM, graph, blockCol, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply]

/-- RiccatiWang26, Lemma B.13 (p. 63), Eqs. (B.35)–(B.37), graph form.  For a DARE solution
`X` (with `1 + G X` invertible), the pencil maps the graph to itself:
`M [I; X] = L [I; X] ((1 + G X)⁻¹ A)`, where `M = [[A,0],[-Q,I]]` and `L = [[I,G],[0,A*]]`.
The identity is exactly the DARE fixed-point equation.  This is the forward-recursion graph
statement (B.35)–(B.37). -/
theorem darePencil_graph_invariance (A G Q X : Sq n)
    (hX : StabilizingDare A G Q X)
    (hInv : (1 + G * X) * (1 + G * X)⁻¹ = 1) :
    pencilM A Q * graph X =
      pencilL A G * graph X * ((1 + G * X)⁻¹ * A) := by
  have hS : (1 + G * X) * ((1 + G * X)⁻¹ * A) = A := by
    rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]
  have hlow : Aᴴ * X * ((1 + G * X)⁻¹ * A) = -Q + X := by
    rw [← Matrix.mul_assoc]
    calc Aᴴ * X * (1 + G * X)⁻¹ * A
        = (Q + Aᴴ * X * (1 + G * X)⁻¹ * A) - Q := by abel
      _ = X - Q := by rw [hX.1.symm]
      _ = -Q + X := by abel
  rw [pencilM_mul_graph, pencilL_mul_graph, blockCol_mul_eq]
  rw [hS, hlow]

/-! ## Proposition B.12: DRE initialization positivity -/

/-- RiccatiWang26, Proposition B.12 (p. 62), Eq. (B.32), positivity part.  Under
`Q ⪰ q0 I`, `0 ≺ G ⪯ ḡ I`, `(A+A*)/2 ⪰ ω I`, `‖P0‖ ≤ p`, the sufficient condition
`q0 + 2ωp - ḡp² > 0` makes the displayed initialization bound
`(ω + √(ω² + ḡ q0) - ḡ p) / √(ḡ² + (ω + √(ω² + ḡ q0))²)` strictly positive. -/
theorem proposition_B_12_dre_initialization
    (ω gbar q0 p : ℝ) (hgbar : 0 < gbar) (hq0 : 0 < q0) (hp : 0 ≤ p)
    (hpos : 0 < q0 + 2 * ω * p - gbar * p ^ 2) :
    0 < (ω + Real.sqrt (ω ^ 2 + gbar * q0) - gbar * p) /
        Real.sqrt (gbar ^ 2 + (ω + Real.sqrt (ω ^ 2 + gbar * q0)) ^ 2) := by
  have hdisc : 0 < ω ^ 2 + gbar * q0 := by
    nlinarith [sq_nonneg ω, mul_pos hgbar hq0]
  have hsqrt : 0 < Real.sqrt (ω ^ 2 + gbar * q0) := Real.sqrt_pos.mpr hdisc
  have hsq : (gbar * p - ω) ^ 2 < ω ^ 2 + gbar * q0 := by
    nlinarith [hpos, hgbar]
  have hnum : 0 < ω + Real.sqrt (ω ^ 2 + gbar * q0) - gbar * p := by
    by_cases hx : 0 ≤ gbar * p - ω
    · have := (Real.lt_sqrt hx).mpr hsq
      linarith
    · push_neg at hx
      linarith
  have hden : 0 < Real.sqrt (gbar ^ 2 + (ω + Real.sqrt (ω ^ 2 + gbar * q0)) ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg gbar]
  exact div_pos hnum hden

/-! ## Proposition B.14: positivity of the RR initialization bound -/

/-- RiccatiWang26, Proposition B.14 (p. 64), Eq. (B.38), positivity part.  The displayed
lower bound `√(1+q0²)/(1+uDARE vDARE) · √(g0/vDARE)` on `σmin(Π> R0)` is strictly positive
whenever the DARE coefficient bounds satisfy `uDARE, vDARE, q0, g0 > 0`. -/
theorem proposition_B_14_rr_initialization
    (P0 : Sq n) (Pigt : Matrix (Sum n n) (Sum n n) ℂ) (R0 : Matrix (Sum n n) n ℂ)
    (uDARE vDARE q0 g0 : ℝ)
    (hP0 : IsPSD P0) (hu : 0 < uDARE) (hv : 0 < vDARE) (hq : 0 < q0) (hg : 0 < g0) :
    0 < Real.sqrt (1 + q0 ^ 2) / (1 + uDARE * vDARE) * Real.sqrt (g0 / vDARE) := by
  have h1 : 0 < 1 + q0 ^ 2 := by nlinarith [sq_nonneg q0]
  have h2 : 0 < 1 + uDARE * vDARE := by nlinarith [mul_pos hu hv]
  have h3 : 0 < g0 / vDARE := div_pos hg hv
  exact mul_pos (div_pos (Real.sqrt_pos.mpr h1) h2) (Real.sqrt_pos.mpr h3)

/-! ## Lemma D.1: Hamiltonian graph flow -/

/-- RiccatiWang26, Lemma D.1 (p. 66), Eq. (D.1), tangent identity.  For `W(t) = [I;P(t)]Y(t)`
with `Y' = (A - G P)Y` and `P' = dreRhs A G Q P`, differentiating `W` gives
`Ẇ = [0; Ṗ]Y + [I;P]((A-GP)Y) = H_DRE W`.  The statement below is the algebraic core: the
Hamiltonian acting on the transported graph splits into the derivative `[0; Ṗ]Y` of the graph
and the transported graph itself.  The right-hand side's zero upper block is the derivative of
the identity block of `graph P`, which is why (D.1) is an ODE for `Y` alone. -/
theorem lemma_D_1_hamiltonian_graph_flow (A G Q P Y : Sq n) :
    careHamiltonian A G Q * (graph P * Y) =
      blockCol 0 (dreRhs A G Q P * Y) + graph P * ((A - G * P) * Y) := by
  have hdecomp : -Q - Aᴴ * P = dreRhs A G Q P + P * (A - G * P) := by
    rw [dreRhs, Matrix.mul_sub, Matrix.mul_assoc]
    noncomm_ring
  calc careHamiltonian A G Q * (graph P * Y)
      = (careHamiltonian A G Q * graph P) * Y := by rw [Matrix.mul_assoc]
    _ = blockCol (A - G * P) (-Q - Aᴴ * P) * Y := by
          rw [careHamiltonian_mul_graph_eq]
    _ = blockCol ((A - G * P) * Y) ((-Q - Aᴴ * P) * Y) := blockCol_mul_eq _ _ _
    _ = blockCol ((A - G * P) * Y) ((dreRhs A G Q P + P * (A - G * P)) * Y) := by
          rw [hdecomp]
    _ = blockCol ((A - G * P) * Y) (dreRhs A G Q P * Y + P * ((A - G * P) * Y)) := by
          rw [Matrix.add_mul, ← Matrix.mul_assoc]
    _ = blockCol 0 (dreRhs A G Q P * Y) + graph P * ((A - G * P) * Y) := by
          rw [graph_mul_eq]
          ext i j
          rcases i with i | i <;>
            simp [blockCol, Matrix.add_apply, Matrix.zero_apply]

/-! ## Lemma E.1: contractive norm recursion -/

/-- Positive contraction recursion: if `‖P_{k+1}‖ ≤ a‖P_k‖ + c` with `0 ≤ a ≤ 1` and `c ≥ 0`,
then `‖P_k‖ ≤ ‖P_0‖ + k c`.  This is the contractive case of the norm bound (E.2). -/
theorem iterate_norm_bound_contracting (P : ℕ → ℝ) (a c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c) (hP0 : 0 ≤ P 0)
    (hstep : ∀ k, P (k + 1) ≤ a * P k + c) :
    ∀ k, P k ≤ P 0 + (k : ℝ) * c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h1 : P (k + 1) ≤ a * (P 0 + (k : ℝ) * c) + c := by
        refine (hstep k).trans ?_
        have : a * P k ≤ a * (P 0 + (k : ℝ) * c) := mul_le_mul_of_nonneg_left ih ha0
        linarith
      have h2 : a * (P 0 + (k : ℝ) * c) + c ≤ P 0 + ((k : ℝ) + 1) * c := by
        have hnn : 0 ≤ P 0 + (k : ℝ) * c := by nlinarith [hP0, hc, hk]
        have hmul : a * (P 0 + (k : ℝ) * c) ≤ 1 * (P 0 + (k : ℝ) * c) :=
          mul_le_mul_of_nonneg_right ha1 hnn
        nlinarith [hmul]
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [this]
      linarith

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Riccati
