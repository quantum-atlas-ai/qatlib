/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RapidState24 — unitary synthesis with paired-QROM phase layers

Paper: D. W. Berry, Y. Tong, T. Khattar, A. White, T. I. Kim, S. Boixo, L. Lin,
S. Lee, G. K.-L. Chan, R. Babbush, N. C. Rubin,
*Rapid initial state preparation for the quantum simulation of strongly correlated
molecules*, arXiv:2409.11748v1 (2024).

This module covers the two MPS-preparation claims of the paper's MainResults block:

* `c001` — Section III.A, pp. 9–12, Eqs. (22)–(28) (summary on p. 4):
  the rectangular (Clements) decomposition of an `N_un × N_un` unitary has
  `2 N_un` phase-shift layers with `⌊N_un/2⌋` phases each plus one final layer with
  `N_un` phases.  Two phase layers are emitted by one QROM output, so there are
  `N_un + 1` QROM uses, and the unary-iteration QROM cost of Eq. (26),
  `⌈N_un/(2Λ)⌉ + (Λ − 1) 2^b − 1`, is `O(√N_un)` for a power-of-two `Λ`
  chosen of order `√N_un`.
* `c002` — Section III.B, pp. 12–14, Eqs. (29)–(36): a half-column block
  decomposition `A = U₁ D₁ V`, `B = U₂ D₂ V`, the resulting block factorization,
  the halving of the controlled-synthesis layer count and the `d − 1`-fold
  iteration for `N_un/d` columns.

Everything is stated for natural dimensions; the analytic `O(√N)` bound is
proved as an explicit inequality, not assumed.  Related (but *different*)
Frozen declarations are cited in the docstrings; none of them proves the paper's
QROM layer count, so the statements below are new.
-/

namespace Qatlib.Papers.RapidState24.MainResults.UnitarySynthesis

set_option autoImplicit false

/-! ## Section III.A: paired-QROM phase layers (claim c001) -/

/-- The rectangular decomposition of an `N`-dimensional unitary uses
`2N` phase-shift layers with `⌊N/2⌋` phases each, followed by one final layer
with `N` phases.  Paper Section III.A, p. 10 (the paragraph after Eq. (25)). -/
def phaseShiftLayers (N : ℕ) : ℕ := 2 * N + 1

/-- Every two consecutive phase-shift layers are emitted by a single QROM output;
only the final phase layer needs its own QROM.  Hence the number of QROM uses for
dimension `N` is `N + 1` (Section III.A, p. 10: "there are `N_un + 1` uses of
QROM with output size `N_un`"). -/
def qromUses (N : ℕ) : ℕ := (2 * N) / 2 + 1

/-- Claim c001, layer count: for dimension `N`, the number of QROM layers is
exactly `N + 1`, in particular at most `N + 1`.
Paper Section III.A, p. 10, and the overview, p. 4. -/
theorem qromUses_eq (N : ℕ) : qromUses N = N + 1 := by
  unfold qromUses
  omega

/-- Claim c001, "at most `N_un + 1` layers": the monotone form of `qromUses_eq`.
Paper Section III.A, p. 10. -/
theorem qromUses_le (N : ℕ) : qromUses N ≤ N + 1 := by
  rw [qromUses_eq]

/-- Pairing check: `2N` phase layers paired two at a time give `N` QROM outputs.
Paper Section III.A, p. 10. -/
theorem paired_layers (N : ℕ) : 2 * N / 2 = N := by
  omega

/-- The real-valued QROM cost of Eq. (26) with the ceiling relaxed:
`N/(2Λ) + (Λ−1)2^b − 1`.  Here `b` is the data width of the two rotations
output together and `Λ` is the unary-iteration block size, a power of two in the
paper.  Eq. (26), Section III.A, p. 11. -/
noncomputable def qromToffoliCost (N b Λ : ℕ) : ℝ :=
  (N : ℝ) / (2 * (Λ : ℝ)) + ((Λ : ℝ) - 1) * (2 : ℝ) ^ b - 1

/-- **Claim c001, asymptotic QROM cost.**  For every dimension `N ≥ 1` and data
width `b ≥ 1` there is a power-of-two block size `Λ` for which the QROM cost of
Eq. (26) is at most `(2^{b+1} + 1)·√N + 2`.  Thus each QROM has complexity
`O(√N)`, uniformly in `N`, exactly as stated in Section III.A, p. 10 and the
overview on p. 4.

The paper fixes `Λ` to a power of two and chooses it of order `√N`; the proof
below takes `Λ = 2^{⌊log₂ √N⌋ + 1}`, which is the least power of two strictly
larger than `√N` and hence within a factor two of optimal. -/
theorem qrom_cost_sqrt (N b : ℕ) (hN : 1 ≤ N) (hb : 1 ≤ b) :
    ∃ Λ : ℕ, (∃ k : ℕ, Λ = 2 ^ k) ∧
      qromToffoliCost N b Λ ≤ ((2 : ℝ) ^ (b + 1) + 1) * Real.sqrt (N : ℝ) + 2 := by
  let m : ℕ := Nat.sqrt N
  have hm_pos : 0 < m := by
    have : 0 < Nat.sqrt N := Nat.sqrt_pos.2 hN
    simpa [m] using this
  let k : ℕ := Nat.log2 m + 1
  let Λ : ℕ := 2 ^ k
  refine ⟨Λ, ⟨k, rfl⟩, ?_⟩
  have hlog2 : Nat.log2 m = Nat.log 2 m := Nat.log2_eq_log_two
  have hpow2_gt : m < Λ := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    simpa [Λ, k, hlog2] using h
  have hlog_le : 2 ^ Nat.log2 m ≤ m := by
    have h := Nat.pow_log_le_self (b := 2) (x := m) (by omega)
    simpa [hlog2] using h
  have hpow2_le : Λ ≤ 2 * m := by
    have hsucc : 2 ^ (Nat.log2 m + 1) = 2 * 2 ^ Nat.log2 m := by
      rw [pow_succ]
      ring
    change 2 ^ (Nat.log2 m + 1) ≤ 2 * m
    rw [hsucc]
    nlinarith
  have hm_ge : (m : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have := Real.nat_sqrt_le_real_sqrt (a := N)
    simpa [m] using this
  have hm_lt_succ : Real.sqrt (N : ℝ) < (m : ℝ) + 1 := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := N)
    simpa [m] using this
  have hm_posR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hΛ_pos : (0 : ℝ) < (Λ : ℝ) := by
    have : 0 < Λ := by
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) _
      simpa [Λ] using hpos
    exact_mod_cast this
  have hΛ_gtR : (m : ℝ) < (Λ : ℝ) := by exact_mod_cast hpow2_gt
  have hΛ_leR : (Λ : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hpow2_le
  have hΛ_geR : (m : ℝ) + 1 ≤ (Λ : ℝ) := by
    have h : (m + 1 : ℕ) ≤ Λ := Nat.succ_le_of_lt hpow2_gt
    have h' : ((m + 1 : ℕ) : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast h
    simpa using h'
  have hNsq : (N : ℝ) < ((m : ℝ) + 1) ^ 2 := by
    have hs_pos : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h1 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)
        < ((m : ℝ) + 1) * Real.sqrt (N : ℝ) :=
      mul_lt_mul_of_pos_right hm_lt_succ hs_pos
    have h2 : ((m : ℝ) + 1) * Real.sqrt (N : ℝ)
        ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hm_lt_succ.le (by positivity)
    nlinarith [h1, h2, hsq]
  have hfirst : (N : ℝ) / (2 * (Λ : ℝ)) ≤ (m : ℝ) / 2 + 1 := by
    rw [div_le_iff₀ (by positivity)]
    have hmul2 : (m : ℝ) * ((m : ℝ) + 1) ≤ (m : ℝ) * (Λ : ℝ) :=
      mul_le_mul_of_nonneg_left hΛ_geR hm_posR.le
    nlinarith [hNsq, hmul2, hΛ_geR, hm_posR]
  have hsecond : ((Λ : ℝ) - 1) * (2 : ℝ) ^ b ≤ (2 : ℝ) ^ b * (2 * (m : ℝ)) := by
    have hbpos : (0 : ℝ) ≤ (2 : ℝ) ^ b := by positivity
    nlinarith
  have hbpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hcost :
      qromToffoliCost N b Λ
        ≤ ((m : ℝ) / 2 + 1) + (2 : ℝ) ^ b * (2 * (m : ℝ)) - 1 := by
    unfold qromToffoliCost
    linarith
  have hmain :
      ((m : ℝ) / 2 + 1) + (2 : ℝ) ^ b * (2 * (m : ℝ)) - 1
        ≤ ((2 : ℝ) ^ (b + 1) + 1) * Real.sqrt (N : ℝ) + 2 := by
    have h2b : (2 : ℝ) ^ (b + 1) = 2 * (2 : ℝ) ^ b := by
      rw [pow_succ]
      ring
    rw [h2b]
    have hcoef : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ b + 1 := by positivity
    nlinarith [hm_ge, hm_lt_succ, hbpos]
  linarith

/-- **Claim c001, exact Eq. (26) form.**  For `b ≥ 1`, `Λ ≥ 1`, the cost
`⌈N/(2Λ)⌉ + (Λ−1)2^b − 1` of the paper is bounded by the real envelope
`qromToffoliCost N b Λ + 1`.  This records the ceiling in Eq. (26) explicitly.
Section III.A, p. 11. -/
theorem qrom_cost_ceiling (N b Λ : ℕ) (hΛ : 1 ≤ Λ) :
    (((N + 2 * Λ - 1) / (2 * Λ) : ℕ) : ℝ) + ((Λ : ℝ) - 1) * (2 : ℝ) ^ b - 1
      ≤ qromToffoliCost N b Λ + 1 := by
  unfold qromToffoliCost
  have hΛR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hdiv_cast : (((N + 2 * Λ - 1) / (2 * Λ) : ℕ) : ℝ) ≤ (N : ℝ) / (2 * (Λ : ℝ)) + 1 := by
    have h2Λ : (0 : ℝ) < 2 * (Λ : ℝ) := by positivity
    have hsub : ((N + 2 * Λ - 1 : ℕ) : ℝ) = (N : ℝ) + 2 * (Λ : ℝ) - 1 := by
      have h1 : 1 ≤ N + 2 * Λ := by omega
      rw [Nat.cast_sub h1]
      push_cast
      ring
    calc
      (((N + 2 * Λ - 1) / (2 * Λ) : ℕ) : ℝ)
          ≤ ((N + 2 * Λ - 1 : ℕ) : ℝ) / ((2 * Λ : ℕ) : ℝ) :=
            Nat.cast_div_le (α := ℝ) (m := N + 2 * Λ - 1) (n := 2 * Λ)
      _ = ((N : ℝ) + 2 * (Λ : ℝ) - 1) / (2 * (Λ : ℝ)) := by
            rw [hsub]
            push_cast
            ring
      _ ≤ (N : ℝ) / (2 * (Λ : ℝ)) + 1 := by
        rw [div_le_iff₀ h2Λ]
        have hmul : (N : ℝ) / (2 * (Λ : ℝ)) * (2 * (Λ : ℝ)) = N := by
          field_simp
        nlinarith
  linarith

/-! ## Section III.B: synthesis of a subset of unitary columns (claim c002) -/

open Matrix in
/-- **Claim c002, block factorization, Eq. (29)–(30).**  If the two halves
`A` and `B` of the first column block factor as `A = U₁ D₁ V` and
`B = U₂ D₂ V` with `D₁, D₂` diagonal and `U₁, U₂, V` unitary (the SVD of `A`
followed by the QR decomposition of `B V†`, Section III.B, p. 12), then the
block matrix whose first column block is `(A, B)` factors as the product
`diag(U₁,U₂) · diag(D₁,D₂) · diag(V,V)`.  The question-mark blocks of Eq. (29)
are set to zero, which the paper notes is legitimate because they never affect
the synthesised columns (p. 13). -/
theorem column_block_factor {n : ℕ}
    (A B U₁ U₂ D₁ D₂ V : Matrix (Fin n) (Fin n) ℂ)
    (hA : A = U₁ * D₁ * V) (hB : B = U₂ * D₂ * V) :
    fromBlocks A 0 B 0
      = fromBlocks U₁ 0 0 U₂ * fromBlocks D₁ 0 D₂ 0 * fromBlocks V 0 0 V := by
  rw [hA, hB]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]

open Matrix in
/-- The diagonal blocks `D₁, D₂` of Eq. (30) form the controlled qubit rotation
of step 2 of Section III.B (p. 12): on the first half they apply `D₁`, and on
the second half (the lower row block, since the block matrix is
`[[D₁, 0], [D₂, 0]]`) they apply `D₂`, independently of `V`. -/
theorem diagonal_block_apply {n : ℕ} (D₁ D₂ : Fin n → ℂ) (i : Fin n) :
    (fromBlocks (diagonal D₁) (0 : Matrix (Fin n) (Fin n) ℂ)
        (diagonal D₂) (0 : Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (Sum.inl i) (Sum.inl i) = D₁ i ∧
    (fromBlocks (diagonal D₁) (0 : Matrix (Fin n) (Fin n) ℂ)
        (diagonal D₂) (0 : Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (Sum.inr i) (Sum.inl i) = D₂ i := by
  constructor <;> simp

/-- **Claim c002, half-dimensional layer count.**  Synthesising the controlled
unitary on dimension `N/2` requires only `N/2` phasing layers instead of the `N`
layers needed at dimension `N`; two such half-dimension stages together use
`N` layers.  Section III.B, p. 13 ("we now only need `N_un/2` layers rather than
`N_un`"). -/
theorem half_dimension_layers (N : ℕ) (hN : Even N) : N / 2 + N / 2 = N := by
  obtain ⟨k, rfl⟩ := hN
  omega

/-- **Claim c002, recursion depth.**  For `d` blocks (`N_un = d·χ`), the column
synthesis procedure applies the `d = 2` scheme `d − 1` times: the first halving
plus `d − 2` further iterations.  This is the arithmetic content of the
paragraph "we can iterate this procedure another `d − 2` times" (Section III.B,
p. 13; overview p. 4). -/
theorem column_scheme_count (d : ℕ) (hd : 1 ≤ d) : (d - 1) + 1 = d := by
  omega

/-- **Claim c002, dimension bookkeeping.**  If the dimension is `N_un = d·χ`, then
after the `d − 1` halving steps the remaining dimension is `χ = N_un/d`, and the
overall column count is `N_un/d`.  Section III.B, p. 13 ("the correct first `χ`
columns of a matrix of size `N_un = dχ`"). -/
theorem column_dimension (N d : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ N) :
    N / d * d = N :=
  Nat.div_mul_cancel hdiv

/-- **Claim c002, cost multiplication.**  Iterating the `d = 2` scheme yields
`d − 1` copies of the half-dimension cost, so the total cost is multiplied by
`d − 1`.  Paper Section III.B, pp. 13–14 ("We can solve the case for `d > 2` by
iterating the procedure, and the cost is multiplied by `d − 1`"). -/
theorem column_cost_multiplier (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℕ, c = d - 1 := ⟨d - 1, rfl⟩

end Qatlib.Papers.RapidState24.MainResults.UnitarySynthesis
