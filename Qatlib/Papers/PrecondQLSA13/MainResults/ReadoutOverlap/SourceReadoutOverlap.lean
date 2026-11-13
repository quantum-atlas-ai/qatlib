/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation

set_option backward.isDefEq.respectTransparency false

/-!
# ReadoutOverlap — source interface for the ancilla readout of PrecondQLSA13

Clader--Jacobs--Sprouse, *Preconditioned quantum linear system algorithm*,
fixed arXiv:1301.2340v4 (2013-05-07). Source location: p. 2, Eq. (9) and the
preceding Hadamard/controlled-swap/Hadamard (swap-test) construction.

The paper adjoins `|R_T> = cos φ_r |R~>|0> + sin φ_r |R>|1>` to the QLSA output
(which carries success amplitude `sin φ_b sin φ_x`), applies a Hadamard gate to a
fourth ancilla, a controlled swap between the `|x>` and `|R>` registers, and a
second Hadamard, obtaining

  `|⟨R|x⟩|^2 = (P_1110 - P_1111) / (sin^2 φ_b sin^2 φ_x sin^2 φ_r)`   (Eq. 9),

with `P_1110`/`P_1111` the probabilities of reading `1` in the first three
ancillas and `0`/`1` in the fourth.

This module records:
* `overlap`, the paper's `⟨R|x⟩`, identified with the shared complex inner
  product `Qatlib.Concepts.SqEstimation.InnerProduct.sqInnerTarget`;
* the swap-test law `P_0 = (1 + |⟨R|x⟩|^2)/2`, `P_1 = (1 - |⟨R|x⟩|^2)/2`,
  proved for real amplitudes by explicit finite-sum expansion of the
  H·CSWAP·H circuit (the complex case is the same computation with `|c|^2`);
* the Eq. (9) extraction identity for the four-ancilla probabilities.

Scope note: the three success ancillas contribute the common factor
`sin^2 φ_b sin^2 φ_x sin^2 φ_r`, treated as a parameter `s`; the paper's claim is
the conditional readout formula, which is exactly what is proved.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PrecondQLSA13.MainResults.ReadoutOverlap

/-- The paper's overlap `⟨R|x⟩ = Σ_j conj(R_j) x_j`, bridged to the shared
same-record inner-product target `sqInnerTarget` (arXiv:1301.2340v4, Eq. (9),
p. 2). -/
def overlap {N : ℕ} (R x : Fin N → ℂ) : ℂ :=
  Qatlib.Concepts.SqEstimation.InnerProduct.sqInnerTarget R x

/-- Eq. (9): the squared modulus of the overlap is the shared inner-product
target's squared modulus. -/
theorem overlap_normSq {N : ℕ} (R x : Fin N → ℂ) :
    Complex.normSq (overlap R x)
      = Complex.normSq (Qatlib.Concepts.SqEstimation.InnerProduct.sqInnerTarget R x) := by
  rfl

/-- Swap-test ancilla-`0` probability for squared overlap `o = |⟨R|x⟩|^2`. -/
def swapZeroProb (o : ℝ) : ℝ := (1 + o) / 2

/-- Swap-test ancilla-`1` probability for squared overlap `o = |⟨R|x⟩|^2`. -/
def swapOneProb (o : ℝ) : ℝ := (1 - o) / 2

/-- Eq. (9), `P_1110`: the first three ancillas read `1` (probability `s`) and
the fourth reads `0`. -/
def p1110 (s o : ℝ) : ℝ := s * swapZeroProb o

/-- Eq. (9), `P_1111`: the first three ancillas read `1` and the fourth reads
`1`. -/
def p1111 (s o : ℝ) : ℝ := s * swapOneProb o

/-- The two swap-test outcomes are complementary. -/
theorem swap_probabilities_sum (o : ℝ) :
    swapZeroProb o + swapOneProb o = 1 := by
  unfold swapZeroProb swapOneProb
  ring

/-- Fixed arXiv:1301.2340v4, Eq. (9), p. 2: with the fourth-ancilla swap-test
law and the common three-ancilla success probability
`s = sin^2 φ_b sin^2 φ_x sin^2 φ_r`, the measured probability difference
extracts the squared overlap:

`(P_1110 - P_1111) / (sin^2 φ_b sin^2 φ_x sin^2 φ_r) = |⟨R|x⟩|^2`. -/
theorem eq9_overlap_extraction (sb sx sr o : ℝ)
    (hsb : 0 < sb) (hsx : 0 < sx) (hsr : 0 < sr) :
    (p1110 (sb ^ 2 * sx ^ 2 * sr ^ 2) o - p1111 (sb ^ 2 * sx ^ 2 * sr ^ 2) o)
        / (sb ^ 2 * sx ^ 2 * sr ^ 2) = o := by
  have hs : sb ^ 2 * sx ^ 2 * sr ^ 2 ≠ 0 := by positivity
  unfold p1110 p1111 swapZeroProb swapOneProb
  field_simp [hs]
  ring

/-- Fixed arXiv:1301.2340v4, p. 2 (Hadamard / controlled-swap / Hadamard
construction): for unit-norm real amplitudes `R`, `x`, the probability that the
swap ancilla reads `0` is `(1 + c^2)/2`, where `c = Σ_j R_j x_j` is the real
overlap. Proof: expanding the post-circuit amplitude
`(R_j x_k + x_j R_k)/2` over the two register indices. -/
theorem swap_test_zero_weight {N : ℕ} (R x : Fin N → ℝ)
    (hR : ∑ j, (R j) ^ 2 = 1) (hx : ∑ j, (x j) ^ 2 = 1) :
    (∑ j : Fin N, ∑ k : Fin N, ((R j * x k + x j * R k) / 2) ^ 2)
      = (1 + (∑ j : Fin N, R j * x j) ^ 2) / 2 := by
  have hA : (∑ j : Fin N, ∑ k : Fin N, (R j) ^ 2 * (x k) ^ 2) = 1 := by
    rw [← Fintype.sum_mul_sum, hR, hx, mul_one]
  have hB : (∑ j : Fin N, ∑ k : Fin N, (x j) ^ 2 * (R k) ^ 2) = 1 := by
    rw [← Fintype.sum_mul_sum, hx, hR, mul_one]
  have hC : (∑ j : Fin N, ∑ k : Fin N, R j * x k * (x j * R k))
      = (∑ j : Fin N, R j * x j) ^ 2 := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hE : (∑ j : Fin N, ∑ k : Fin N, ((R j * x k + x j * R k) / 2) ^ 2)
      = (1 / 4) * (∑ j : Fin N, ∑ k : Fin N, (R j) ^ 2 * (x k) ^ 2)
        + (1 / 4) * (∑ j : Fin N, ∑ k : Fin N, (x j) ^ 2 * (R k) ^ 2)
        + (1 / 2) * (∑ j : Fin N, ∑ k : Fin N, R j * x k * (x j * R k)) := by
    simp_rw [show ∀ j k : Fin N,
      ((R j * x k + x j * R k) / 2) ^ 2
        = (1 / 4) * ((R j) ^ 2 * (x k) ^ 2)
          + (1 / 4) * ((x j) ^ 2 * (R k) ^ 2)
          + (1 / 2) * (R j * x k * (x j * R k)) by
      intro j k
      ring]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hE, hA, hB, hC]
  ring

/-- Fixed arXiv:1301.2340v4, p. 2: companion of `swap_test_zero_weight`; the
swap ancilla reads `1` with probability `(1 - c^2)/2` for real overlap
`c = Σ_j R_j x_j`. -/
theorem swap_test_one_weight {N : ℕ} (R x : Fin N → ℝ)
    (hR : ∑ j, (R j) ^ 2 = 1) (hx : ∑ j, (x j) ^ 2 = 1) :
    (∑ j : Fin N, ∑ k : Fin N, ((R j * x k - x j * R k) / 2) ^ 2)
      = (1 - (∑ j : Fin N, R j * x j) ^ 2) / 2 := by
  have hA : (∑ j : Fin N, ∑ k : Fin N, (R j) ^ 2 * (x k) ^ 2) = 1 := by
    rw [← Fintype.sum_mul_sum, hR, hx, mul_one]
  have hB : (∑ j : Fin N, ∑ k : Fin N, (x j) ^ 2 * (R k) ^ 2) = 1 := by
    rw [← Fintype.sum_mul_sum, hx, hR, mul_one]
  have hC : (∑ j : Fin N, ∑ k : Fin N, R j * x k * (x j * R k))
      = (∑ j : Fin N, R j * x j) ^ 2 := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hE : (∑ j : Fin N, ∑ k : Fin N, ((R j * x k - x j * R k) / 2) ^ 2)
      = (1 / 4) * (∑ j : Fin N, ∑ k : Fin N, (R j) ^ 2 * (x k) ^ 2)
        + (1 / 4) * (∑ j : Fin N, ∑ k : Fin N, (x j) ^ 2 * (R k) ^ 2)
        - (1 / 2) * (∑ j : Fin N, ∑ k : Fin N, R j * x k * (x j * R k)) := by
    simp_rw [show ∀ j k : Fin N,
      ((R j * x k - x j * R k) / 2) ^ 2
        = (1 / 4) * ((R j) ^ 2 * (x k) ^ 2)
          + (1 / 4) * ((x j) ^ 2 * (R k) ^ 2)
          - (1 / 2) * (R j * x k * (x j * R k)) by
      intro j k
      ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hE, hA, hB, hC]
  ring

end Qatlib.Papers.PrecondQLSA13.MainResults.ReadoutOverlap
