/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Source Proposition 22: the block form and its diagonal relation

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Section 3.4,
Proposition 22 and its proof.

The paper's statement has two halves:

1. *"Without loss of generality, the matrices `M^(t)` in the above SDP
   (Equations (86)–(89)) may be assumed to have the form
   `M^(t) = [[U^(t), V^(t)], [V^(t), U^(t)]]`, where `U^(t) ∈ S^n_+` and `V^(t)`
   is a symmetric `n × n` matrix."*
2. *"Moreover, for any such solution the main diagonals of `U^(t)` and
   `(-1)^t V^(t)` are identical."*

This module formalises the second half (the "Moreover" sentence, Equations
(113)–(114) of the proof). Given a positive semidefinite `2n × 2n` matrix `M`
whose four `n × n` blocks are `U`, `V`, `V`, `U`, applying the quadratic form to
`e_i ± e_{n+i}` yields `-U_jj ≤ V_jj ≤ U_jj` entrywise; since by Equations
(86)–(87) the traces satisfy `tr U = (-1)^t tr V`, summing the appropriate
nonnegative slack gives zero, hence the diagonal identity.

Not covered here: the first half (the symmetrisation `M ↦ (M + M̌)/2` that makes
the block form without loss of generality). That step needs the cyclic-trace
functional `Tr_j` of Proposition 21, which this repository does not yet
formalise, so the coverage of this source result stays partial.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open scoped BigOperators ComplexOrder
open Matrix

/-- The `i`-th index of the first half of `Fin (2n)`, the paper's `i ∈ {0,…,n-1}`. -/
def halfL (n : ℕ) (i : Fin n) : Fin (2 * n) := ⟨i.val, by omega⟩

/-- The `i`-th index of the second half of `Fin (2n)`, the paper's `n + i`. -/
def halfR (n : ℕ) (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by omega⟩

/-- The block form `M = [[U, V], [V, U]]` of Equation (113): the four `n × n`
corner blocks of a `2n × 2n` matrix are `U`, `V`, `V`, `U`. -/
def HasBlockForm (n : ℕ) (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (U V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n,
    M (halfL n i) (halfL n j) = U i j ∧
    M (halfL n i) (halfR n j) = V i j ∧
    M (halfR n i) (halfL n j) = V i j ∧
    M (halfR n i) (halfR n j) = U i j

/-- Square roots of the trace identity of Equations (86)–(87) in diagonal
form: positive semidefiniteness of the `2 × 2` block `[[U_jj, V_jj], [V_jj, U_jj]]`
bounds `|V_jj|` by `U_jj`. -/
theorem block_diag_abs_le {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (U V : Matrix (Fin n) (Fin n) ℂ) (hpsd : M.PosSemidef) (hblk : HasBlockForm n M U V)
    (j : Fin n) :
    -((U j j).re) ≤ (V j j).re ∧ (V j j).re ≤ (U j j).re := by
  have hcorner := hblk j j
  obtain ⟨h00, h01, h10, h11⟩ := hcorner
  have hquad : ∀ x : Fin 2 → ℂ, (0 : ℝ) ≤ (star x ⬝ᵥ
      ((M.submatrix ![halfL n j, halfR n j] ![halfL n j, halfR n j]) *ᵥ x)).re := by
    intro x
    exact (hpsd.submatrix ![halfL n j, halfR n j]).re_dotProduct_nonneg x
  constructor
  · have h := hquad ![1, 1]
    simp [dotProduct, mulVec, Fin.sum_univ_two, submatrix_apply, h00, h01, h10, h11,
      Complex.add_re] at h
    linarith
  · have h := hquad ![1, -1]
    simp [dotProduct, mulVec, Fin.sum_univ_two, submatrix_apply, h00, h01, h10, h11,
      Complex.add_re] at h
    linarith

/-- Fixed arXiv:2503.21090v2, Proposition 22, "Moreover" clause. For a positive
semidefinite `2n × 2n` matrix `M` in the block form `[[U, V], [V, U]]` of
Equation (113) whose blocks satisfy the trace identity `tr U = (-1)^t tr V` of
Equations (86)–(87), the main diagonals of `U` and `(-1)^t V` agree:
`U_jj = (-1)^t V_jj` for every `j` (Equation (114)). -/
theorem source_prop22_block_diagonal {n : ℕ} (t : ℕ)
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (hpsd : M.PosSemidef) (hblk : HasBlockForm n M U V)
    (htr : (U.trace).re = (-1 : ℝ) ^ t * (V.trace).re) :
    ∀ j : Fin n, (U j j).re = (-1 : ℝ) ^ t * (V j j).re := by
  classical
  have hbound : ∀ j : Fin n, -((U j j).re) ≤ (V j j).re ∧ (V j j).re ≤ (U j j).re :=
    fun j => block_diag_abs_le M U V hpsd hblk j
  have htrU : (∑ j : Fin n, (U j j).re) = (U.trace).re := by
    simp [Matrix.trace, Complex.re_sum]
  have htrV : (∑ j : Fin n, (V j j).re) = (V.trace).re := by
    simp [Matrix.trace, Complex.re_sum]
  rcases Nat.even_or_odd t with ht | ht
  · have hp : (-1 : ℝ) ^ t = 1 := ht.neg_one_pow
    have hsum : (∑ j : Fin n, ((U j j).re - (V j j).re)) = 0 := by
      rw [Finset.sum_sub_distrib, htrU, htrV, htr, hp]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (U j j).re - (V j j).re :=
      fun j _ => by linarith [(hbound j).2]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    intro j
    have := hzero j (Finset.mem_univ j)
    rw [hp]
    linarith
  · have hp : (-1 : ℝ) ^ t = -1 := ht.neg_one_pow
    have hsum : (∑ j : Fin n, ((U j j).re + (V j j).re)) = 0 := by
      rw [Finset.sum_add_distrib, htrU, htrV, htr, hp]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (U j j).re + (V j j).re :=
      fun j _ => by linarith [(hbound j).1]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    intro j
    have := hzero j (Finset.mem_univ j)
    rw [hp]
    linarith

end Qatlib.Papers.OrderedSearch25.MainResults
