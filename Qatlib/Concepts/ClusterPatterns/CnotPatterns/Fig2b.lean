/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Kraus
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Tools

/-!
# The two-output cluster-chain isometry

This module calculates the branch semantics of `mpTwoOutputPattern`, the four-vertex chain with
one input, two measured vertices, and two outputs. Following the cluster measurement setting of
[RaussendorfBriegel2000], it constructs an explicit matrix from one qubit to two qubits and
proves that its columns are orthonormal.

The calculation expands the entangler, evaluates the two measured coordinates, and tracks the
Pauli corrections. Every measurement outcome gives one quarter of the same isometric conjugation
map; the outcome-dependent sign in the core disappears under conjugation.

## Main statements

* `cnotAux_W` is the explicit one-input, two-output matrix, and `cnotAux_W_isometry` proves its
  isometry identity.
* `cnotAux_two_ent_diag` gives the chain entangler entrywise.
* `cnotAux_two_core` expresses each corrected core as a signed half multiple of `cnotAux_W`.
* `cnotAux_clause3_channel` proves the common branch formula.
* `cnotAux_clause3` packages the isometry and all branch identities into an existence statement.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000], *Quantum computing via measurements
  only*.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a

/-- The one-input, two-output matrix whose first output bit is the complement of the input bit.
Its nonzero entries have magnitude `1 / sqrt 2` and phase `bitPhase (input &&
!secondOutput)`. -/
noncomputable def cnotAux_W : Matrix (Fin 4) (Fin 2) ℂ := Matrix.of fun xp y =>
  if ((bitVecEquiv 2).symm xp) 0 = !((bitVecEquiv 1).symm y) 0 then
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (((bitVecEquiv 1).symm y) 0
        && !((bitVecEquiv 2).symm xp) 1)
      * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  else 0

/-- An entry of `cnotAux_W` vanishes unless the first decoded output bit complements the decoded
input bit; otherwise it is `bitPhase (input && !secondOutput) / sqrt 2`. -/
theorem cnotAux_W_apply (xp : Fin 4) (y : Fin 2) :
    cnotAux_W xp y
      = if ((bitVecEquiv 2).symm xp) 0 = !((bitVecEquiv 1).symm y) 0 then
          Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (((bitVecEquiv 1).symm y) 0
              && !((bitVecEquiv 2).symm xp) 1)
            * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else 0 :=
  rfl

/-- The matrix `cnotAux_W` is an isometry: its conjugate transpose multiplied by itself is the
one-qubit identity. It supplies the common output map for the two-output cluster pattern in
the setting of [RaussendorfBriegel2000]. -/
theorem cnotAux_W_isometry : cnotAux_W.conjTranspose * cnotAux_W = 1 := by
  have hreal : ∀ k i, star (cnotAux_W k i) = cnotAux_W k i := by
    intro k i
    rw [cnotAux_W_apply]
    by_cases h : ((bitVecEquiv 2).symm k) 0 = !((bitVecEquiv 1).symm i) 0
    · rw [if_pos h, star_mul', cnotAux_star_bitPhase, cnotAux_star_inv_sqrt2]
    · rw [if_neg h, star_zero]
  ext i j
  show (∑ k : Fin 4, (cnotAux_W.conjTranspose i k : ℂ) * cnotAux_W k j)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  simp only [Matrix.conjTranspose_apply]
  simp_rw [hreal]
  fin_cases i <;> fin_cases j <;> rw [Fin.sum_univ_four] <;>
    simp only [cnotAux_W_apply, cnotAux_bv2_bits, cnotAux_bv1, mul_ite, ite_mul, mul_zero, zero_mul,
      Matrix.one_apply] <;>
    norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, cnotAux_inv_sqrt2_mul_self, cnotAux_sqrt2_sq]

/-- The three successive directed edges of the four-vertex path from zero to three. -/
def cnotAux_twoE : Finset (Fin 4 × Fin 4) :=
  {(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨2, by omega⟩, ⟨3, by omega⟩)}

/-- The two-output pattern's entangler is the product of the frame matrix and the controlled-Z
matrix for `cnotAux_twoE`. -/
theorem cnotAux_two_entangler :
    mpTwoOutputPattern.entangler
      = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix cnotAux_twoE * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix cnotAux_twoE := by
  simp only [mpTwoOutputPattern]
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz _

/-- A product over `Fin 4` equals the product of its values at zero, one, two, and three. -/
theorem cnotAux_prod_fin4 (g : Fin 4 → ℂ) :
    (∏ v : Fin 4, g v) = g 0 * g 1 * g 2 * g 3 := by
  rw [Fin.prod_univ_four]

/-- The diagonal frame entry on the four-vertex path is the product of the bit phases at
vertices one, two, and three. -/
theorem cnotAux_two_frame (x : Reg 4) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix cnotAux_twoE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
      if_pos (rfl : x = x)]
  rw [cnotAux_prod_fin4]
  have h0 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_twoE 0 = false := by decide
  have h1 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_twoE 1 = true := by decide
  have h2 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_twoE 2 = true := by decide
  have h3 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd cnotAux_twoE 3 = true := by decide
  rw [h0, h1, h2, h3]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The diagonal controlled-Z entry on the four-vertex path is the product of the bit phases for
the adjacent pairs `(0,1)`, `(1,2)`, and `(2,3)`. -/
theorem cnotAux_two_cz (x : Reg 4) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix cnotAux_twoE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 3) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x)]
  show (∏ e ∈ cnotAux_twoE, if x e.1 && x e.2 then (-1 : ℂ) else 1) = _
  rw [cnotAux_twoE]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The four-vertex path phase obtained by multiplying its three local frame signs and its three
adjacent-pair controlled-Z signs. -/
def cnotAux_twoPhase (x : Reg 4) : ℂ :=
  (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3))
    * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 3))

/-- The two-output pattern's entangler has diagonal entries `cnotAux_twoPhase x` and zero
off-diagonal entries. -/
theorem cnotAux_two_ent_diag (x y : Reg 4) :
    mpTwoOutputPattern.entangler x y = if x = y then cnotAux_twoPhase x else 0 := by
  rw [cnotAux_two_entangler]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [cnotAux_two_frame, cnotAux_two_cz]
      rfl
    · intro k _ hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_neg (Ne.symm hk),
        zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = x
    · subst hk
      rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_neg h, mul_zero]
    · rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_neg (Ne.symm hk),
        zero_mul]

/-- Every amplitude of the uniform three-qubit vector is `1 / sqrt 8`. -/
theorem cnotAux_uniform3 (x : Reg 3) : Uniform (Reg 3) x = ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ := by
  show ((Real.sqrt (Fintype.card (Reg 3)) : ℝ) : ℂ)⁻¹ = _
  rw [card_reg]
  norm_num

/-- The two-output pattern's loading entry is `1 / sqrt 8` when the zeroth register bit matches
the input bit, and zero otherwise. -/
theorem cnotAux_two_load (d : Reg 4) (y : Reg 1) :
    mpLoadMatrix mpTwoOutputPattern (Uniform (Reg 3)) d y
      = if d 0 = y 0 then ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ else 0 := by
  simp only [mpLoadMatrix, mpTwoOutputPattern, Matrix.of_apply]
  by_cases h : ∀ i : Fin 1, d (Fin.castLE (by omega : (1:ℕ) ≤ 2 + 2) i) = y i
  · rw [if_pos h]
    have h0 : d 0 = y 0 := h ⟨0, by omega⟩
    rw [if_pos h0]
    have hres : Uniform (Reg 3)
        (fun k : Fin 3 => d (Fin.cast (by omega) (Fin.natAdd 1 k))) = ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ :=
      cnotAux_uniform3 _
    rw [hres]
  · rw [if_neg h]
    have h0 : ¬ d 0 = y 0 := by
      intro hh
      apply h
      intro i
      fin_cases i
      exact hh
    rw [if_neg h0]

/-- Entangling the loaded three-qubit uniform resource gives `cnotAux_twoPhase d / sqrt 8` when
the input bit matches register coordinate zero, and zero otherwise. -/
theorem cnotAux_two_EL (d : Reg 4) (y : Reg 1) :
    (mpTwoOutputPattern.entangler
        * mpLoadMatrix mpTwoOutputPattern (Uniform (Reg 3))) d y
      = if d 0 = y 0 then
          ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * cnotAux_twoPhase d
        else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single d]
  · rw [cnotAux_two_ent_diag, if_pos rfl, cnotAux_two_load]
    by_cases h : d 0 = y 0
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  · intro d' _ hdne
    rw [cnotAux_two_ent_diag, if_neg (Ne.symm hdne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Every adaptive measurement angle of the two-output pattern is zero, for every outcome
string. -/
theorem cnotAux_two_sv (s : Fin 2 → Bool) (j : Fin 2) :
    mpAdaptiveAngle mpTwoOutputPattern s j = 0 := by
  simp only [mpAdaptiveAngle, mpTwoOutputPattern, mpParity_empty]
  norm_num

/-- The two-output register constraint is equivalent to the two coordinate equalities at
vertices two and three. -/
theorem cnotAux_two_delta_iff (s : Fin 2 → Bool) (xp : Fin 4) (c : Reg 4) :
    (∀ v : Fin 2, c (Fin.natAdd 2 v) = mpOutBit mpTwoOutputPattern s xp v)
      ↔ (c 2 = mpOutBit mpTwoOutputPattern s xp 0
        ∧ c 3 = mpOutBit mpTwoOutputPattern s xp 1) := by
  constructor
  · intro h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    refine ⟨?_, ?_⟩
    · simpa using h0
    · simpa using h1
  · intro h v
    fin_cases v
    · simpa using h.1
    · simpa using h.2

/-- The register summand for the two-output core before the final correction phase, combining
conjugate measurement amplitudes, corrected output constraints, and the entangled loading
entry. -/
noncomputable def cnotAux_twoSummand (s : Fin 2 → Bool) (xp : Fin 4) (y : Reg 1) : Reg 4 → ℂ :=
  fun c =>
    (∏ j : Fin 2, star (mpSVector (mpAdaptiveAngle mpTwoOutputPattern s j) (s j)
        (c (Fin.castLE (by omega : 2 ≤ 2 + 2) j))))
      * (if ∀ v : Fin 2, c (Fin.natAdd 2 v) = mpOutBit mpTwoOutputPattern s xp v then (1 : ℂ)
        else 0)
      * (mpTwoOutputPattern.entangler
          * mpLoadMatrix mpTwoOutputPattern (Uniform (Reg 3))) c y

/-- The `corePre` entry of the two-output pattern is its output `Z`-correction sign multiplied
by the sum of `cnotAux_twoSummand` over four-bit registers. -/
theorem cnotAux_two_corePre_eq (s : Fin 2 → Bool) (xp : Fin 4) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s xp y
      = (∏ k : Fin 2,
            if mpTwoOutputPattern.zCorr k s && mpOutBit mpTwoOutputPattern s xp k
            then (-1 : ℂ) else 1)
          * ∑ c : Reg 4, cnotAux_twoSummand s xp y c := by
  simp only [corePre, Matrix.of_apply, cnotAux_twoSummand]

/-- The two-output core summand factors into zero-angle conjugate measurement amplitudes,
constraints on coordinates two and three, and the input-matching entangler phase divided by
`sqrt 8`. -/
theorem cnotAux_two_summand_eq (s : Fin 2 → Bool) (xp : Fin 4) (y : Reg 1) (c : Reg 4) :
    cnotAux_twoSummand s xp y c
      = (∏ j : Fin 2, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 2 ≤ 2 + 2) j))))
          * (if c 2 = mpOutBit mpTwoOutputPattern s xp 0
              ∧ c 3 = mpOutBit mpTwoOutputPattern s xp 1 then (1 : ℂ) else 0)
          * (if c 0 = y 0 then ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * cnotAux_twoPhase c else 0) := by
  simp only [cnotAux_twoSummand]
  rw [cnotAux_two_EL]
  simp only [cnotAux_two_sv]
  simp only [cnotAux_two_delta_iff]

/-- The two-factor product of conjugate measurement amplitudes is the product of the terms at
register coordinates zero and one. -/
theorem cnotAux_two_prod_star (s : Fin 2 → Bool) (c : Reg 4) :
    (∏ j : Fin 2, star (mpSVector 0 (s j) (c (Fin.castLE (by omega : 2 ≤ 2 + 2) j))))
      = star (mpSVector 0 (s 0) (c 0)) * star (mpSVector 0 (s 1) (c 1)) := by
  rw [Fin.prod_univ_two]
  rfl

/-- The full four-bit summand sum reduces to the two choices for coordinate one after fixing
coordinate zero to the input and coordinates two and three to the corrected output bits. -/
theorem cnotAux_two_sum_eq (s : Fin 2 → Bool) (xp : Fin 4) (y : Reg 1) :
    ∑ c : Reg 4, cnotAux_twoSummand s xp y c
      = cnotAux_twoSummand s xp y
          (cnotAux_pin4 (y 0) true (mpOutBit mpTwoOutputPattern s xp 0)
            (mpOutBit mpTwoOutputPattern s xp 1))
        + cnotAux_twoSummand s xp y
          (cnotAux_pin4 (y 0) false (mpOutBit mpTwoOutputPattern s xp 0)
            (mpOutBit mpTwoOutputPattern s xp 1)) := by
  rw [cnotAux_sum_reclause4_fix (cnotAux_twoSummand s xp y) (y 0)
    (mpOutBit mpTwoOutputPattern s xp 0) (mpOutBit mpTwoOutputPattern s xp 1) ?_]
  · exact sum_bool_eq _
  · intro c hc
    rw [cnotAux_two_summand_eq]
    by_cases h0 : c 0 = y 0
    · by_cases h2 : c 2 = mpOutBit mpTwoOutputPattern s xp 0
      · by_cases h3 : c 3 = mpOutBit mpTwoOutputPattern s xp 1
        · rcases hc with hc | hc | hc
          · exact absurd h0 hc
          · exact absurd h2 hc
          · exact absurd h3 hc
        · rw [if_neg (fun hh => h3 hh.2), mul_zero, zero_mul]
      · rw [if_neg (fun hh => h2 hh.1), mul_zero, zero_mul]
    · rw [if_neg h0, mul_zero]

/-- The first output's `X` correction is controlled by the second measurement outcome `s 1`. -/
theorem cnotAux_two_xCorr0 (s : Fin 2 → Bool) : mpTwoOutputPattern.xCorr 0 s = s 1 := by
  simp only [mpTwoOutputPattern]
  rfl

/-- The second output has no `X` correction. -/
theorem cnotAux_two_xCorr1 (s : Fin 2 → Bool) : mpTwoOutputPattern.xCorr 1 s = false := by
  simp only [mpTwoOutputPattern]
  rfl

/-- The first output's `Z` correction is controlled by the first measurement outcome `s 0`. -/
theorem cnotAux_two_zCorr0 (s : Fin 2 → Bool) : mpTwoOutputPattern.zCorr 0 s = s 0 := by
  simp only [mpTwoOutputPattern]
  rfl

/-- The second output's `Z` correction is controlled by the second measurement outcome `s 1`. -/
theorem cnotAux_two_zCorr1 (s : Fin 2 → Bool) : mpTwoOutputPattern.zCorr 1 s = s 1 := by
  simp only [mpTwoOutputPattern]
  rfl

/-- The first corrected output bit is the XOR of `s 1` with the first bit decoded from `xp`. -/
theorem cnotAux_two_outBit0 (s : Fin 2 → Bool) (xp : Fin 4) :
    mpOutBit mpTwoOutputPattern s xp 0 = xor (s 1) ((bitVecEquiv 2).symm xp 0) := by
  rw [mpOutBit, cnotAux_two_xCorr0]

/-- The second corrected output bit is the second bit decoded from `xp`. -/
theorem cnotAux_two_outBit1 (s : Fin 2 → Bool) (xp : Fin 4) :
    mpOutBit mpTwoOutputPattern s xp 1 = ((bitVecEquiv 2).symm xp 1) := by
  rw [mpOutBit, cnotAux_two_xCorr1]
  simp [Bool.xor]

/-- The `corePre` entry at output index zero is the corresponding `cnotAux_W` entry times
`bitPhase (!(s 0 || s 1)) / 2`. -/
theorem cnotAux_two_corePre_0 (s : Fin 2 → Bool) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s 0 y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ)
          * cnotAux_W 0 ((bitVecEquiv 1) y) := by
  rw [cnotAux_two_corePre_eq, cnotAux_two_sum_eq, Fin.prod_univ_two]
  simp only [cnotAux_two_summand_eq, cnotAux_two_prod_star]
  have hs0 : s 0 = true ∨ s 0 = false := Bool.eq_false_or_eq_true _
  have hs1 : s 1 = true ∨ s 1 = false := Bool.eq_false_or_eq_true _
  have hy0 : y 0 = true ∨ y 0 = false := Bool.eq_false_or_eq_true _
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;> rcases hy0 with hy0 | hy0
  all_goals simp only [cnotAux_two_zCorr0, cnotAux_two_zCorr1, cnotAux_two_outBit0, cnotAux_two_outBit1,
    cnotAux_bv2_00, cnotAux_bv2_01, cnotAux_bv2_10, cnotAux_bv2_11,
    cnotAux_bv2_20, cnotAux_bv2_21, cnotAux_bv2_30, cnotAux_bv2_31, cnotAux_W_apply,
    Equiv.symm_apply_apply, hs0, hs1, hy0]
  all_goals simp [cnotAux_star_sv0, cnotAux_sv0, cnotAux_twoPhase, cnotAux_inv_sqrt8, div_eq_mul_inv,
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube']
  all_goals (try rw [cnotAux_inv_sqrt2_mul_self]) <;>
    field_simp [cnotAux_inv_sqrt2_mul_self, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube'] <;> ring

/-- The `corePre` entry at output index one is the corresponding `cnotAux_W` entry times
`bitPhase (!(s 0 || s 1)) / 2`. -/
theorem cnotAux_two_corePre_1 (s : Fin 2 → Bool) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s 1 y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ)
          * cnotAux_W 1 ((bitVecEquiv 1) y) := by
  rw [cnotAux_two_corePre_eq, cnotAux_two_sum_eq, Fin.prod_univ_two]
  simp only [cnotAux_two_summand_eq, cnotAux_two_prod_star]
  have hs0 : s 0 = true ∨ s 0 = false := Bool.eq_false_or_eq_true _
  have hs1 : s 1 = true ∨ s 1 = false := Bool.eq_false_or_eq_true _
  have hy0 : y 0 = true ∨ y 0 = false := Bool.eq_false_or_eq_true _
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;> rcases hy0 with hy0 | hy0
  all_goals simp only [cnotAux_two_zCorr0, cnotAux_two_zCorr1, cnotAux_two_outBit0, cnotAux_two_outBit1,
    cnotAux_bv2_00, cnotAux_bv2_01, cnotAux_bv2_10, cnotAux_bv2_11,
    cnotAux_bv2_20, cnotAux_bv2_21, cnotAux_bv2_30, cnotAux_bv2_31, cnotAux_W_apply,
    Equiv.symm_apply_apply, hs0, hs1, hy0]
  all_goals simp [cnotAux_star_sv0, cnotAux_sv0, cnotAux_twoPhase, cnotAux_inv_sqrt8, div_eq_mul_inv,
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube']
  all_goals (try rw [cnotAux_inv_sqrt2_mul_self]) <;>
    field_simp [cnotAux_inv_sqrt2_mul_self, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube'] <;> ring

/-- The `corePre` entry at output index two is the corresponding `cnotAux_W` entry times
`bitPhase (!(s 0 || s 1)) / 2`. -/
theorem cnotAux_two_corePre_2 (s : Fin 2 → Bool) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s 2 y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ)
          * cnotAux_W 2 ((bitVecEquiv 1) y) := by
  rw [cnotAux_two_corePre_eq, cnotAux_two_sum_eq, Fin.prod_univ_two]
  simp only [cnotAux_two_summand_eq, cnotAux_two_prod_star]
  have hs0 : s 0 = true ∨ s 0 = false := Bool.eq_false_or_eq_true _
  have hs1 : s 1 = true ∨ s 1 = false := Bool.eq_false_or_eq_true _
  have hy0 : y 0 = true ∨ y 0 = false := Bool.eq_false_or_eq_true _
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;> rcases hy0 with hy0 | hy0
  all_goals simp only [cnotAux_two_zCorr0, cnotAux_two_zCorr1, cnotAux_two_outBit0, cnotAux_two_outBit1,
    cnotAux_bv2_00, cnotAux_bv2_01, cnotAux_bv2_10, cnotAux_bv2_11,
    cnotAux_bv2_20, cnotAux_bv2_21, cnotAux_bv2_30, cnotAux_bv2_31, cnotAux_W_apply,
    Equiv.symm_apply_apply, hs0, hs1, hy0]
  all_goals simp [cnotAux_star_sv0, cnotAux_sv0, cnotAux_twoPhase, cnotAux_inv_sqrt8, div_eq_mul_inv,
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube']
  all_goals (try rw [cnotAux_inv_sqrt2_mul_self]) <;>
    field_simp [cnotAux_inv_sqrt2_mul_self, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube'] <;> ring

/-- The `corePre` entry at output index three is the corresponding `cnotAux_W` entry times
`bitPhase (!(s 0 || s 1)) / 2`. -/
theorem cnotAux_two_corePre_3 (s : Fin 2 → Bool) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s 3 y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ)
          * cnotAux_W 3 ((bitVecEquiv 1) y) := by
  rw [cnotAux_two_corePre_eq, cnotAux_two_sum_eq, Fin.prod_univ_two]
  simp only [cnotAux_two_summand_eq, cnotAux_two_prod_star]
  have hs0 : s 0 = true ∨ s 0 = false := Bool.eq_false_or_eq_true _
  have hs1 : s 1 = true ∨ s 1 = false := Bool.eq_false_or_eq_true _
  have hy0 : y 0 = true ∨ y 0 = false := Bool.eq_false_or_eq_true _
  rcases hs0 with hs0 | hs0 <;> rcases hs1 with hs1 | hs1 <;> rcases hy0 with hy0 | hy0
  all_goals simp only [cnotAux_two_zCorr0, cnotAux_two_zCorr1, cnotAux_two_outBit0, cnotAux_two_outBit1,
    cnotAux_bv2_00, cnotAux_bv2_01, cnotAux_bv2_10, cnotAux_bv2_11,
    cnotAux_bv2_20, cnotAux_bv2_21, cnotAux_bv2_30, cnotAux_bv2_31, cnotAux_W_apply,
    Equiv.symm_apply_apply, hs0, hs1, hy0]
  all_goals simp [cnotAux_star_sv0, cnotAux_sv0, cnotAux_twoPhase, cnotAux_inv_sqrt8, div_eq_mul_inv,
    Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube']
  all_goals (try rw [cnotAux_inv_sqrt2_mul_self]) <;>
    field_simp [cnotAux_inv_sqrt2_mul_self, cnotAux_inv_sqrt2_cube, cnotAux_inv_sqrt2_cube'] <;> ring

/-- Every two-output `corePre` entry is `bitPhase (!(s 0 || s 1)) / 2` times the corresponding
entry of `cnotAux_W`, with the input register encoded by `bitVecEquiv 1`. -/
theorem cnotAux_two_corePre (s : Fin 2 → Bool) (xp : Fin 4) (y : Reg 1) :
    corePre mpTwoOutputPattern (Uniform (Reg 3)) s xp y
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ)
          * cnotAux_W xp ((bitVecEquiv 1) y) := by
  fin_cases xp
  · exact cnotAux_two_corePre_0 s y
  · exact cnotAux_two_corePre_1 s y
  · exact cnotAux_two_corePre_2 s y
  · exact cnotAux_two_corePre_3 s y

/-- The corrected core of every two-output outcome branch is the matrix `cnotAux_W` scaled by
`bitPhase (!(s 0 || s 1)) / 2`. -/
theorem cnotAux_two_core (s : Fin 2 → Bool) :
    core mpTwoOutputPattern (Uniform (Reg 3)) s
      = (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 : ℂ) • cnotAux_W := by
  ext xp yp
  simp only [core, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul, Equiv.refl_symm, Equiv.refl_apply]
  rw [cnotAux_two_corePre, Equiv.apply_symm_apply]

/-- Conjugation by the two-output core is one quarter of conjugation by `cnotAux_W`, since the
outcome-dependent phase cancels. -/
theorem cnotAux_two_core_conj (s : Fin 2 → Bool) (ρ : Operator 2) :
    core mpTwoOutputPattern (Uniform (Reg 3)) s * ρ
        * (core mpTwoOutputPattern (Uniform (Reg 3)) s).conjTranspose
      = (1 / 4 : ℂ) • (cnotAux_W * ρ * cnotAux_W.conjTranspose) := by
  rw [cnotAux_two_core]
  set c : ℂ := Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) / 2 with hc
  have h1 : (c • cnotAux_W) * ρ = c • (cnotAux_W * ρ) := cnotAux_smul_mul c cnotAux_W ρ
  rw [h1, Matrix.conjTranspose_smul, cnotAux_smul_mul_smul]
  have h3 : c * star c = (1 / 4 : ℂ) := by
    rw [hc]
    have hst : star (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)))
        = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) :=
      cnotAux_star_bitPhase _
    rw [star_div₀, hst, star_ofNat]
    have hsqb : Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1))
        * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!(s 0 || s 1)) = 1 :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase_sq _
    rw [div_mul_div_comm, hsqb]
    norm_num
  rw [h3]

/-- The squared magnitudes of the two-output measurement-amplitude products sum to one over all
discarded-register strings. -/
theorem cnotAux_two_sv_sum (s : Fin 2 → Bool) :
    ∑ z : Fin 2 → Bool,
      (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpTwoOutputPattern s j) (s j) (z j))
        * star (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpTwoOutputPattern s j) (s j) (z j)) = 1 := by
  simp only [cnotAux_two_sv]
  have hz : ∀ z : Fin 2 → Bool,
      (∏ j : Fin 2, mpSVector 0 (s j) (z j))
          * star (∏ j : Fin 2, mpSVector 0 (s j) (z j)) = (1 / 4 : ℂ) := by
    intro z
    have hstar : star (∏ j : Fin 2, mpSVector 0 (s j) (z j))
        = ∏ j : Fin 2, star (mpSVector 0 (s j) (z j)) :=
      map_prod (starRingEnd ℂ) (fun j => mpSVector 0 (s j) (z j)) Finset.univ
    rw [hstar, Fin.prod_univ_two, Fin.prod_univ_two, mul_mul_mul_comm, sv_zero_sq, sv_zero_sq]
    norm_num
  simp_rw [hz]
  rw [Finset.sum_const, Finset.card_univ]
  rw [card_reg]
  norm_num

/-- For every measurement outcome, the two-output branch equals `1 / 4` times conjugation by
`cnotAux_W`. This is the explicit branch formula for the cluster-chain construction in the
setting of [RaussendorfBriegel2000]. -/
theorem cnotAux_clause3_channel : ∀ (s : Fin 2 → Bool) (ρ : Operator 2),
    ∑ z : Fin 2 → Bool,
        (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z) * ρ
          * (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z).conjTranspose
      = (1 / 4 : ℂ) • (cnotAux_W * ρ * cnotAux_W.conjTranspose) := by
  intro s ρ
  have hkey : ∀ z : Fin 2 → Bool,
      (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z) * ρ
          * (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z).conjTranspose
        = ((∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpTwoOutputPattern s j) (s j) (z j))
            * star (∏ j : Fin 2, mpSVector (mpAdaptiveAngle mpTwoOutputPattern s j) (s j) (z j)))
            • (core mpTwoOutputPattern (Uniform (Reg 3)) s * ρ
                * (core mpTwoOutputPattern (Uniform (Reg 3)) s).conjTranspose) := by
    intro z
    rw [kraus_eq_smul_core, Matrix.conjTranspose_smul, cnotAux_smul_mul, cnotAux_smul_mul_smul]
  simp_rw [hkey]
  rw [← Finset.sum_smul, cnotAux_two_sv_sum, one_smul]
  exact cnotAux_two_core_conj s ρ

/-- There exists an isometry from one qubit to two qubits such that every outcome branch of
`mpTwoOutputPattern` is `1 / 4` times conjugation by that isometry. The witness `cnotAux_W`
realizes this cluster measurement construction motivated by [RaussendorfBriegel2000]. -/
theorem cnotAux_clause3 :
    ∃ W : Matrix (Fin 4) (Fin 2) ℂ,
      W.conjTranspose * W = 1 ∧
      ∀ (s : Fin 2 → Bool) (ρ : Operator 2),
        ∑ z : Fin 2 → Bool,
            (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z) * ρ
              * (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z).conjTranspose
          = (1 / 4 : ℂ) • (W * ρ * W.conjTranspose) :=
  ⟨cnotAux_W, cnotAux_W_isometry, cnotAux_clause3_channel⟩
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
