/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PEPSObs16.MainResults.SourceMainResults
import Mathlib.Tactic

/-!
# PEPSObs16 — transfer operator and its gap, eqs. (19)–(24)

Fixed source: arXiv:1606.06301v2, Appendix "Implications for the gap of the
transfer operator", eqs. (19)–(24), pp. 6–7.

The paper contracts the `d`-dimensional PEPS along a one-dimensional line `L`
into a transfer operator `e`, computes two-point functions as

`⟨O_A ⊗ O_B⟩ = tr(e_A e^x e_B e^{|L|-x-2}) / tr(e^{|L|})`   (eq. (21))

and, using the spectral expansion `e^x = |r⟩⟨l| + Σ_{j>1} lam_j^x |r_j⟩⟨l_j|`
(eq. (23)) together with the exponential clustering of eq. (22), concludes

`lam_2 / lam_1 ≤ e^{-c_2 δ}`   (eq. (24)).

This file formalises the two rigorous directions of that appendix on the
diagonal spectral model of eq. (23):

* `trace_transfer_insert` and `transferCorr_eq_trace` are the exact trace
  identity of eq. (21) for a transfer operator in diagonal form;
* `decay_of_gap` proves **gap ⇒ exponential decay** of the spectral
  correlations (eq. (24) ⇒ eq. (22)), the converse of
  `SourceMainResults.transfer_operator_gap`, which proves
  **exponential decay ⇒ gap** for the observable pair projecting on the second
  eigenvector.

Together they are the paper's statement that the transfer operator along `L`
inherits the gap of the parent Hamiltonian iff its correlations decay
exponentially.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Eq. (21): exact trace formula -/

/-- Trace of a power of a diagonal transfer operator:
`tr(e^n) = Σ_j lam_j^n`. -/
theorem trace_diag_pow (lam : ι → ℝ) (n : ℕ) :
    Matrix.trace (Matrix.diagonal lam ^ n) = ∑ j, lam j ^ n := by
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- **Eq. (21) (p. 6), exact form.** With the transfer operator `e` in
diagonal form `diag lam` (eq. (23)) and the observable insertions `e_A = diag a`,
`e_B = diag b`, the expectation of eq. (21) is
`tr(e_A e^x e_B e^y) = Σ_j a_j b_j lam_j^{x+y}` with `|L| = x + y + 2`. -/
theorem trace_transfer_insert (lam a b : ι → ℝ) (x y : ℕ) :
    Matrix.trace (Matrix.diagonal a * Matrix.diagonal lam ^ x *
        Matrix.diagonal b * Matrix.diagonal lam ^ y) =
      ∑ j, a j * b j * lam j ^ (x + y) := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow]
  simp only [Matrix.diagonal_mul_diagonal]
  rw [Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  show a j * lam j ^ x * b j * lam j ^ y = a j * b j * lam j ^ (x + y)
  rw [pow_add]
  ring

/-- The normalised two-point function of eq. (21) on the diagonal model:
`tr(e_A e^x e_B e^y)/tr(e^{x+y+2})`, with the line length `|L| = x + y + 2`. -/
def transferCorr (lam a b : ι → ℝ) (x y : ℕ) : ℝ :=
  (∑ j, a j * b j * lam j ^ (x + y)) / (∑ j, lam j ^ (x + y + 2))

/-- **Eq. (21) as a ratio of traces.** The normalised correlation is exactly the
ratio of the two trace expressions of eq. (21), so `transferCorr` is not a
re-definition but a consequence of `trace_transfer_insert`. -/
theorem transferCorr_eq_trace (lam a b : ι → ℝ) (x y : ℕ) :
    transferCorr lam a b x y =
      Matrix.trace (Matrix.diagonal a * Matrix.diagonal lam ^ x *
          Matrix.diagonal b * Matrix.diagonal lam ^ y) /
        Matrix.trace (Matrix.diagonal lam ^ (x + y + 2)) := by
  unfold transferCorr
  rw [trace_transfer_insert, trace_diag_pow]

/-! ## Eq. (22): exponential decay from a spectral gap -/

/-- **Gap ⇒ exponential decay (eq. (24) ⇒ eq. (22)).** If every subleading
eigenvalue has modulus at most `ρ`, then every spectral correlation
`C(x) = Σ_{j≠1} lam_j^x w_j` decays with rate `ρ`. Taking `ρ = e^{-c_2 δ}` gives
the paper's `|⟨O_A ⊗ O_B⟩ − ⟨O_A⟩⟨O_B⟩| ≤ c_1 e^{-c_2 x δ}` with
`c_1 = Σ_{j≠1} |w_j|`. -/
theorem decay_of_gap (lam w : ι → ℝ) (j1 : ι) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (hbound : ∀ j, j ≠ j1 → |lam j| ≤ ρ) (x : ℕ) :
    |∑ j ∈ Finset.univ.erase j1, lam j ^ x * w j| ≤
      (∑ j ∈ Finset.univ.erase j1, |w j|) * ρ ^ x := by
  calc
    |∑ j ∈ Finset.univ.erase j1, lam j ^ x * w j|
        ≤ ∑ j ∈ Finset.univ.erase j1, |lam j ^ x * w j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.univ.erase j1, ρ ^ x * |w j| := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) (hbound j (Finset.mem_erase.mp hj).1) x)
            (abs_nonneg _)
    _ = (∑ j ∈ Finset.univ.erase j1, |w j|) * ρ ^ x := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- **Eq. (24) ⇒ eq. (22), explicit exponential rate.** With
`ρ = e^{-c_2 δ}` the correlation bound reads
`|C(x)| ≤ (Σ_{j≠1}|w_j|) e^{-c_2 x δ}`, the paper's eq. (22) with
`c_1 = Σ_{j≠1}|w_j|` and the same rate `c_2 δ` appearing in the gap (24). -/
theorem correlation_decay_of_gap (lam w : ι → ℝ) (j1 : ι) (c2 δ : ℝ)
    (_hd : 0 < c2 * δ)
    (hbound : ∀ j, j ≠ j1 → |lam j| ≤ Real.exp (-(c2 * δ))) (x : ℕ) :
    |∑ j ∈ Finset.univ.erase j1, lam j ^ x * w j| ≤
      (∑ j ∈ Finset.univ.erase j1, |w j|) * Real.exp (-(c2 * (x : ℝ) * δ)) := by
  have hρ : 0 ≤ Real.exp (-(c2 * δ)) := (Real.exp_pos _).le
  have hmain := decay_of_gap lam w j1 (Real.exp (-(c2 * δ))) hρ hbound x
  have hpow : Real.exp (-(c2 * δ)) ^ x = Real.exp (-(c2 * (x : ℝ) * δ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hpow] at hmain

/-! ## Eq. (24): the spectral gap of the transfer operator -/

/-- **Eqs. (22)–(24), both directions.** For a nonnegative second eigenvalue
`lam_2 ≥ 0` selected by the observable pair (the pair `(a, b)` projects onto the
second eigenvector), exponential decay of the spectral correlation at rate
`c_2 δ` is *equivalent* to the gap bound `lam_2 ≤ e^{-c_2 δ}` of eq. (24). The
forward direction is `SourceMainResults.transfer_operator_gap`, the reverse is
`correlation_decay_of_gap`. -/
theorem transfer_gap_iff_decay (lam : ι → ℝ) (a b : ι → ℝ) (j1 j2 : ι) (hj : j2 ≠ j1)
    (hlam2 : 0 ≤ lam j2) (c2 δ : ℝ) (hc2 : 0 < c2) (hδ : 0 < δ)
    (hproj : a j2 = 1 ∧ b j2 = 1 ∧ ∀ j, j ≠ j1 → j ≠ j2 → a j * b j = 0)
    (hlam1 : lam j1 = 1) :
    (∀ x : ℕ, 1 ≤ x →
        |spectralCorrelation lam a b j1 x| ≤ 1 * Real.exp (-(c2 * (x : ℝ) * δ))) ↔
      lam j2 / lam j1 ≤ Real.exp (-(c2 * δ)) := by
  constructor
  · intro hdecay
    exact transfer_operator_gap lam a b j1 j2 hj hlam2 1 c2 δ one_pos hc2 hδ hdecay hproj hlam1
  · intro hgap x _
    -- the gap gives the correlation bound with `c_1 = 1`
    have hspec : spectralCorrelation lam a b j1 x = (lam j2) ^ x := by
      unfold spectralCorrelation
      have hmem : j2 ∈ Finset.univ.erase j1 :=
        Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j2⟩
      have h := Finset.sum_eq_single (s := Finset.univ.erase j1)
        (f := fun j => (lam j) ^ x * a j * b j) j2 ?_ ?_
      · rw [h, hproj.1, hproj.2.1]
        ring
      · intro j hmemj hjj2
        have hjj1 : j ≠ j1 := (Finset.mem_erase.mp hmemj).1
        show lam j ^ x * a j * b j = 0
        rw [show lam j ^ x * a j * b j = lam j ^ x * (a j * b j) by ring,
          hproj.2.2 j hjj1 hjj2, mul_zero]
      · intro hnot
        exact absurd hmem hnot
    have hnonneg : 0 ≤ (lam j2) ^ x := pow_nonneg hlam2 x
    rw [hspec, abs_of_nonneg hnonneg]
    have hgap' : lam j2 ≤ Real.exp (-(c2 * δ)) := by
      rwa [hlam1, div_one] at hgap
    have hexp : Real.exp (-(c2 * δ)) ^ x = Real.exp (-(c2 * (x : ℝ) * δ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc (lam j2) ^ x
        ≤ Real.exp (-(c2 * δ)) ^ x :=
          pow_le_pow_left₀ hlam2 hgap' x
      _ = Real.exp (-(c2 * (x : ℝ) * δ)) := hexp
      _ = 1 * Real.exp (-(c2 * (x : ℝ) * δ)) := by ring

end Qatlib.Papers.PEPSObs16.MainResults
