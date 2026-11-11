/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QsampleCoup25.MainResults.EdgeLaplacian

set_option backward.isDefEq.respectTransparency false

/-!
# `C*` preserves elementary graph Laplacians (source Lemma 14)

Temme--Wocjan, *Quantized Markov Chain Couplings that Prepare Qsamples*,
arXiv:2504.02651v2, Quantum 9, 1951 (2025). Fixed source PDF SHA-256
`616a3932dd7120d6c178df5869e910d5891e93396e55f7ccd07c11d3110cabf6`.

Source Lemma 14 (86): for `x ≠ y`,

`C*(|−xy⟩⟨−xy|) = ∑_{x',y'} c_{(x',y'),(x,y)} |−x'y'⟩⟨−x'y'|`.

The proof uses the coupling conditions of source eq. (9)--(13): conditions (11)
and (12) turn `C*(|x⟩⟨x|)` and `C*(|y⟩⟨y|)` into the diagonal action of `P`; the
two marginal conditions (9)--(10) collapse the right-hand side to the same
expression; and condition (13) identifies the two off-diagonal terms. We prove the
identity without the hypothesis `x ≠ y`, which is a stronger statement: at `x = y`
both sides vanish.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QsampleCoup25.MainResults

open Finset BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {P : Matrix Ω Ω ℝ} {C : Matrix (Ω × Ω) (Ω × Ω) ℝ}

omit [Fintype Ω] in
/-- `eVec` is symmetric in its two arguments: `e_x(y) = δ_{xy} = e_y(x)`. -/
lemma eVec_comm (x p : Ω) : eVec x p = eVec p x := by
  simp only [eVec]
  by_cases h : p = x
  · rw [if_pos h, if_pos h.symm]
  · have h2 : ¬ (x = p) := fun hh => h hh.symm
    rw [if_neg h, if_neg h2]

/-- The same collapse as `sum_eVec_mul_vec`, for the argument order produced by
`edgeProj`, where the delta target comes first. -/
lemma sum_eVec_target_mul_vec (a b : Ω) (g : Ω → Ω → ℝ) :
    (∑ x, ∑ y, eVec a x * eVec b y * g x y) = g a b := by
  rw [show (∑ x, ∑ y, eVec a x * eVec b y * g x y)
      = ∑ x, ∑ y, eVec x a * eVec y b * g x y from by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [eVec_comm a x, eVec_comm b y]]
  exact sum_eVec_mul_vec a b g

/-- Cross collapse with the two delta indices exchanged, which is the shape of the
`|y⟩⟨x|` term of source eq. (94). -/
lemma sum_eVec_cross_swapped (a b u v : Ω) :
    (∑ x', ∑ y', eVec y' a * eVec x' b * C (x', y') (u, v)) = C (b, a) (u, v) := by
  rw [Finset.sum_comm]
  exact sum_eVec_mul_vec a b (fun y' x' => C (x', y') (u, v))

/-- Conditions (11)--(12): on a coalesced input pair `(s,s)` the coupling behaves
like `P` on the diagonal, which is the indicator form `eVec a b * P a s`. -/
lemma C_diag_eq (hc : Coupling P C) (a b s : Ω) :
    C (a, b) (s, s) = eVec a b * P a s := by
  by_cases h : a = b
  · subst h
    rw [hc.meet_diag]
    simp only [eVec, if_true, one_mul]
  · have hba : ¬ (b = a) := fun hh => h hh.symm
    rw [hc.meet_offdiag a b s h]
    simp only [eVec, hba, if_false, zero_mul]

/-- Collapsing a sum whose two deltas both sit on the first coordinate of the
coupling matrix. The second marginal (condition (10)) leaves `P` on the diagonal,
and the remaining sum is a single delta. -/
lemma sum_coupling_double_first (hc : Coupling P C) (a b u v : Ω) :
    (∑ x', ∑ y', eVec x' a * eVec x' b * C (x', y') (u, v)) = eVec a b * P a u := by
  have hstep : ∀ x' : Ω, (∑ y' : Ω, eVec x' a * eVec x' b * C (x', y') (u, v))
      = eVec x' a * (eVec x' b * P x' u) := by
    intro x'
    rw [show (∑ y' : Ω, eVec x' a * eVec x' b * C (x', y') (u, v))
        = (eVec x' a * eVec x' b) * (∑ y' : Ω, C (x', y') (u, v)) from by
          rw [Finset.mul_sum],
      hc.marginal_left x' u v]
    ring
  rw [Finset.sum_congr rfl (fun x' _ => hstep x')]
  exact sum_eVec_mul_left a (fun x' => eVec x' b * P x' u)

/-- The mirror case of `sum_coupling_double_first`: both deltas sit on the second
coordinate, and the first marginal (condition (9)) leaves `P`. -/
lemma sum_coupling_double_second (hc : Coupling P C) (a b u v : Ω) :
    (∑ x', ∑ y', eVec y' a * eVec y' b * C (x', y') (u, v)) = eVec a b * P a v := by
  have hstep : ∀ y' : Ω, (∑ x' : Ω, eVec y' a * eVec y' b * C (x', y') (u, v))
      = eVec y' a * (eVec y' b * P y' v) := by
    intro y'
    rw [show (∑ x' : Ω, eVec y' a * eVec y' b * C (x', y') (u, v))
        = (eVec y' a * eVec y' b) * (∑ x' : Ω, C (x', y') (u, v)) from by
          rw [Finset.mul_sum],
      hc.marginal_right y' u v]
    ring
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun y' _ => hstep y')]
  exact sum_eVec_mul_left a (fun y' => eVec y' b * P y' v)

/-- Source Lemma 14 (86): the matricization `C*` maps the elementary Laplacian of
the edge `{x,y}` to the `C`-weighted sum of elementary Laplacians. -/
theorem cStar_edgeProj (hc : Coupling P C) (x y : Ω) :
    cStar C (edgeProj x y) = ∑ x', ∑ y', C (x', y') (x, y) • edgeProj x' y' := by
  funext a b
  have hL : cStar C (edgeProj x y) a b
      = (1 / 2 : ℝ) * (C (a, b) (x, x) - C (a, b) (x, y) - C (a, b) (y, x) +
          C (a, b) (y, y)) := by
    have hpt : ∀ p q : Ω, C (a, b) (p, q) * edgeProj x y p q
        = (1 / 2 : ℝ) * (eVec x p * eVec x q * C (a, b) (p, q))
          - (1 / 2 : ℝ) * (eVec x p * eVec y q * C (a, b) (p, q))
          - (1 / 2 : ℝ) * (eVec y p * eVec x q * C (a, b) (p, q))
          + (1 / 2 : ℝ) * (eVec y p * eVec y q * C (a, b) (p, q)) := by
      intro p q
      simp only [edgeProj]
      ring
    have hsum : cStar C (edgeProj x y) a b
        = (1 / 2 : ℝ) * (∑ p, ∑ q, eVec x p * eVec x q * C (a, b) (p, q))
          - (1 / 2 : ℝ) * (∑ p, ∑ q, eVec x p * eVec y q * C (a, b) (p, q))
          - (1 / 2 : ℝ) * (∑ p, ∑ q, eVec y p * eVec x q * C (a, b) (p, q))
          + (1 / 2 : ℝ) * (∑ p, ∑ q, eVec y p * eVec y q * C (a, b) (p, q)) := by
      simp only [cStar, hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    rw [hsum,
      sum_eVec_target_mul_vec x x (fun p q => C (a, b) (p, q)),
      sum_eVec_target_mul_vec x y (fun p q => C (a, b) (p, q)),
      sum_eVec_target_mul_vec y x (fun p q => C (a, b) (p, q)),
      sum_eVec_target_mul_vec y y (fun p q => C (a, b) (p, q))]
    ring
  have hR : (∑ x', ∑ y', C (x', y') (x, y) • edgeProj x' y') a b
      = (1 / 2 : ℝ) * (eVec a b * P a x - C (a, b) (x, y) - C (b, a) (x, y) +
          eVec a b * P a y) := by
    have hpt : ∀ x' y' : Ω, C (x', y') (x, y) * edgeProj x' y' a b
        = (1 / 2 : ℝ) * (eVec x' a * eVec x' b * C (x', y') (x, y))
          - (1 / 2 : ℝ) * (eVec x' a * eVec y' b * C (x', y') (x, y))
          - (1 / 2 : ℝ) * (eVec y' a * eVec x' b * C (x', y') (x, y))
          + (1 / 2 : ℝ) * (eVec y' a * eVec y' b * C (x', y') (x, y)) := by
      intro x' y'
      simp only [edgeProj]
      ring
    have hsum : (∑ x', ∑ y', C (x', y') (x, y) • edgeProj x' y') a b
        = (1 / 2 : ℝ) * (∑ x', ∑ y', eVec x' a * eVec x' b * C (x', y') (x, y))
          - (1 / 2 : ℝ) * (∑ x', ∑ y', eVec x' a * eVec y' b * C (x', y') (x, y))
          - (1 / 2 : ℝ) * (∑ x', ∑ y', eVec y' a * eVec x' b * C (x', y') (x, y))
          + (1 / 2 : ℝ) * (∑ x', ∑ y', eVec y' a * eVec y' b * C (x', y') (x, y)) := by
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hpt,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum,
      sum_coupling_double_first hc a b x y,
      sum_eVec_mul_vec a b (fun x' y' => C (x', y') (x, y)),
      sum_eVec_cross_swapped a b x y,
      sum_coupling_double_second hc a b x y]
    ring
  rw [hL, hR]
  rw [C_diag_eq hc a b x, C_diag_eq hc a b y, hc.swap a b y x]

end Qatlib.Papers.QsampleCoup25.MainResults
