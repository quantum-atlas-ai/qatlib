/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Model

/-!
# HeatEquation20 — Theorem 3 (p. 10, App. B) and Lemma 4 (p. 10, App. C)

Fixed source: arXiv:2004.06516v2.

* **Theorem 3** (p. 10; proof in Appendix B, pp. 28–30) states that the
  coefficient matrix `A` of the linear system (38) satisfies
  `‖A‖ = Θ(1)`, `‖A⁻¹‖ = Θ(m)`, hence condition number `κ = Θ(m)`.
  The explicit bounds in the proof are (B11)–(B12) and (B13): the minimal
  nonzero singular value satisfies `2/(mπ) ≤ σmin ≤ π/(2m+1)`, and the
  maximal singular value satisfies `1 ≤ σmax ≤ 4`.

* **Lemma 4** (p. 10; proof in Appendix C, p. 33) states that with
  `Δt = Δx²/(2αd)` (Corollary 2), every nonnegative grid vector `u`
  satisfies `‖Lu‖₂²/‖u‖₂² ≥ 1/(2d)`.

The proof of Lemma 4 is formalised completely: the splitting
`L = Σ_i L_i` of (C1), the nonnegativity of the `L_i` (and hence the
off-diagonal nonnegativity of the quadratic form in (C3)), and the
diagonal bound (C4) are all proved.  Theorem 3 was not carried into this
port: its earlier formalisation rested on the unreproduced
characteristic-polynomial computation of Appendix B, contained an unproven
gap, and was dropped; it remains registered as a claim in
`metadata/papers/HeatEquation20.json`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators
open Matrix

/-! ## The coordinate shifts as permutations of the grid -/

/-- The cyclic shift `x ↦ x + e_i` of the grid as an equivalence. -/
def shiftEquiv {d n : ℕ} [NeZero n] (i : Fin d) : Grid d n ≃ Grid d n where
  toFun := shiftUp i
  invFun := shiftDown i
  left_inv x := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [shiftUp, shiftDown]
    · simp [shiftUp, shiftDown, Function.update_of_ne, hj]
  right_inv x := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [shiftUp, shiftDown]
    · simp [shiftUp, shiftDown, Function.update_of_ne, hj]

/-- Sums are invariant under the forward coordinate shift. -/
lemma sum_shiftUp {d n : ℕ} [NeZero n] (i : Fin d) (f : Grid d n → ℝ) :
    ∑ x : Grid d n, f (shiftUp i x) = ∑ x, f x :=
  Equiv.sum_comp (shiftEquiv i) f

/-- Sums are invariant under the backward coordinate shift. -/
lemma sum_shiftDown {d n : ℕ} [NeZero n] (i : Fin d) (f : Grid d n → ℝ) :
    ∑ x : Grid d n, f (shiftDown i x) = ∑ x, f x :=
  Equiv.sum_comp (shiftEquiv i).symm f

/-! ## The coordinate averaging operators `L_i` of (C1), p. 33 -/

/-- `L_i` of (C1), p. 33: the average of the two neighbours in coordinate `i`,
with the global `1/(2d)` normalisation. -/
def coordAvg {d n : ℕ} [NeZero n] (i : Fin d) (u : Grid d n → ℝ) : Grid d n → ℝ :=
  fun x => (2 * (d : ℝ))⁻¹ * (u (shiftUp i x) + u (shiftDown i x))

/-- The random-walk step is the sum of the coordinate averaging operators. -/
lemma heatStep_eq_sum_coordAvg {d n : ℕ} [NeZero n] (u : Grid d n → ℝ) :
    heatStep u = fun x => ∑ i : Fin d, coordAvg i u x := by
  funext x
  simp only [heatStep, coordAvg, Finset.mul_sum]

/-- The coordinate averaging operators preserve nonnegativity. -/
lemma coordAvg_nonneg {d n : ℕ} [NeZero n] (i : Fin d) (u : Grid d n → ℝ)
    (hu : ∀ x, 0 ≤ u x) (x : Grid d n) : 0 ≤ coordAvg i u x := by
  unfold coordAvg
  exact mul_nonneg (by positivity) (add_nonneg (hu _) (hu _))

/-- A sum of nonnegative coordinates is at least the sum of the squares. -/
lemma sq_sum_ge_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) ^ 2 ≥ ∑ i, (a i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (a i) ^ 2 = a i * a i := sq _
    _ ≤ ∑ j, a i * a j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (ha i) (ha j)) (Finset.mem_univ i)

/-- The diagonal lower bound (C4), p. 33: `u^T L_i² u ≥ ‖u‖₂²/(2d²)`. -/
lemma coordAvg_l2Sq_lower {d n : ℕ} [NeZero n] (hd : 0 < d) (i : Fin d)
    (u : Grid d n → ℝ) (hu : ∀ x, 0 ≤ u x) :
    l2Sq u / (2 * (d : ℝ) ^ 2) ≤ l2Sq (coordAvg i u) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hstep : ∀ x : Grid d n,
      (2 * (d : ℝ))⁻¹ ^ 2 * (u (shiftUp i x) ^ 2 + u (shiftDown i x) ^ 2)
        ≤ (coordAvg i u x) ^ 2 := by
    intro x
    unfold coordAvg
    have h1 : 0 ≤ u (shiftUp i x) := hu _
    have h2 : 0 ≤ u (shiftDown i x) := hu _
    have hcoef : (0 : ℝ) < (2 * (d : ℝ))⁻¹ ^ 2 := by positivity
    have hkey : u (shiftUp i x) ^ 2 + u (shiftDown i x) ^ 2
        ≤ (u (shiftUp i x) + u (shiftDown i x)) ^ 2 := by
      nlinarith [mul_nonneg h1 h2]
    calc (2 * (d : ℝ))⁻¹ ^ 2 * (u (shiftUp i x) ^ 2 + u (shiftDown i x) ^ 2)
        ≤ (2 * (d : ℝ))⁻¹ ^ 2 * (u (shiftUp i x) + u (shiftDown i x)) ^ 2 :=
          mul_le_mul_of_nonneg_left hkey hcoef.le
      _ = ((2 * (d : ℝ))⁻¹ * (u (shiftUp i x) + u (shiftDown i x))) ^ 2 := by ring
  have hcoef : (∑ x : Grid d n, u x ^ 2) / (2 * (d : ℝ) ^ 2)
      = (2 * (d : ℝ))⁻¹ ^ 2 * (2 * ∑ x : Grid d n, u x ^ 2) := by
    have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
    field_simp <;> ring
  simp only [l2Sq]
  rw [hcoef]
  calc (2 * (d : ℝ))⁻¹ ^ 2 * (2 * ∑ x : Grid d n, u x ^ 2)
      = (2 * (d : ℝ))⁻¹ ^ 2
          * (∑ x : Grid d n, u (shiftUp i x) ^ 2 + ∑ x : Grid d n, u (shiftDown i x) ^ 2) := by
        rw [sum_shiftUp i (fun y => u y ^ 2), sum_shiftDown i (fun y => u y ^ 2)]
        ring
    _ = (2 * (d : ℝ))⁻¹ ^ 2
          * ∑ x : Grid d n, (u (shiftUp i x) ^ 2 + u (shiftDown i x) ^ 2) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ x : Grid d n,
          (2 * (d : ℝ))⁻¹ ^ 2 * (u (shiftUp i x) ^ 2 + u (shiftDown i x) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ x : Grid d n, (coordAvg i u x) ^ 2 := Finset.sum_le_sum fun x _ => hstep x

/-- Equation (C3), p. 33: `‖Lu‖₂² ≥ Σ_i ‖L_i u‖₂²`. -/
lemma l2Sq_heatStep_lower {d n : ℕ} [NeZero n] (hd : 0 < d)
    (u : Grid d n → ℝ) (hu : ∀ x, 0 ≤ u x) :
    l2Sq u / (2 * (d : ℝ)) ≤ l2Sq (heatStep u) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  calc l2Sq u / (2 * (d : ℝ))
      = ∑ _i : Fin d, l2Sq u / (2 * (d : ℝ) ^ 2) := by
        have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp <;> ring
    _ ≤ ∑ i : Fin d, l2Sq (coordAvg i u) :=
        Finset.sum_le_sum fun i _ => coordAvg_l2Sq_lower hd i u hu
    _ = ∑ i : Fin d, ∑ x : Grid d n, (coordAvg i u x) ^ 2 := by
        simp only [l2Sq]
    _ = ∑ x : Grid d n, ∑ i : Fin d, (coordAvg i u x) ^ 2 := Finset.sum_comm
    _ ≤ ∑ x : Grid d n, (∑ i : Fin d, coordAvg i u x) ^ 2 :=
        Finset.sum_le_sum fun x _ =>
          sq_sum_ge_sum_sq (fun i => coordAvg i u x) (fun i => coordAvg_nonneg i u hu x)
    _ = ∑ x : Grid d n, (heatStep u x) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [congrFun (heatStep_eq_sum_coordAvg u) x]
    _ = l2Sq (heatStep u) := by
        simp only [l2Sq]

/-- **Lemma 4** (arXiv:2004.06516v2, p. 10; restated and proved in Appendix C,
p. 33).  With `Δt = Δx²/(2αd)` as in Corollary 2, every nonnegative grid
vector `u ≠ 0` satisfies `‖Lu‖₂²/‖u‖₂² ≥ 1/(2d)`. -/
theorem lemma4_heatStep_l2_ratio {d n : ℕ} [NeZero n] (hd : 0 < d)
    (u : Grid d n → ℝ) (hu : ∀ x, 0 ≤ u x) (hu0 : l2Sq u ≠ 0) :
    l2Sq (heatStep u) / l2Sq u ≥ 1 / (2 * (d : ℝ)) := by
  have hpos : 0 < l2Sq u := lt_of_le_of_ne (l2Sq_nonneg u) (Ne.symm hu0)
  rw [ge_iff_le, le_div_iff₀ hpos]
  have h1 : l2Sq u / (2 * (d : ℝ)) ≤ l2Sq (heatStep u) := l2Sq_heatStep_lower hd u hu
  have h2 : 1 / (2 * (d : ℝ)) * l2Sq u = l2Sq u / (2 * (d : ℝ)) := by ring
  linarith

end Qatlib.Papers.HeatEquation20.MainResults
