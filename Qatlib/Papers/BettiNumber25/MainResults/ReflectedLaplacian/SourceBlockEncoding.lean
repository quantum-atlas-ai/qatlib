/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Block Encoding of the Complementary Projection

This module formalizes Theorem 6.1 of Akhalwaya et al.: given a unitary `U`
that block-encodes an idempotent projection `P_Γ` at scale `1` on ancilla state
`j₀`, there exists a unitary `V` on one additional ancilla qubit (`Fin 2 × J`)
that block-encodes the complementary projection `1 - P_Γ` at scale `1` on the
`(0, j₀)` ancilla corner.

## Main statements

* `theorem_6_1_block_encoding`: existence of a scale-`1` unitary block encoding
  of `1 - P_Γ` on `(Fin 2 × J) × I` from a scale-`1` unitary block encoding of
  an idempotent `P_Γ`.

## References

* [Akhalwaya et al., 2025][AkhalwayaEtAl2025], Section 6, Theorem 6.1 and
  Figure 1.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Papers.BettiNumber25.MainResults.ReflectedLaplacian

/-- **Theorem 6.1**: if `U` block-encodes an idempotent matrix `PΓ` at scale `1`
on ancilla index `j₀`, then there exists a unitary `V` on `(Fin 2 × J) × I`
that block-encodes `1 - PΓ` at scale `1` on ancilla index `(0, j₀)`. -/
theorem theorem_6_1_block_encoding
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (PΓ : Matrix I I ℂ)
    (hU : IsBlockEncoding U j₀ PΓ 1) (hP : PΓ * PΓ = PΓ) :
    ∃ V : Matrix ((Fin 2 × J) × I) ((Fin 2 × J) × I) ℂ,
      IsBlockEncoding V (0, j₀) ((1 : Matrix I I ℂ) - PΓ) 1 := by
  have hcorner : BlockCorner U j₀ = PΓ := by simpa using hU.2.2
  have hunit : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU.1
  -- The rows outside the designated fiber give the positive defect of the corner.
  let B : Matrix (J × I) I ℂ := fun p i => if p.1 = j₀ then 0 else U p (j₀, i)
  have hdefect : Bᴴ * B = 1 - PΓᴴ * PΓ := by
    apply eq_sub_iff_add_eq.mpr
    ext a b
    rw [← hcorner]
    change (Bᴴ * B) a b + ((BlockCorner U j₀)ᴴ * BlockCorner U j₀) a b = _
    calc
      _ = (∑ j, ∑ i, if j = j₀ then 0 else
            star (U (j, i) (j₀, a)) * U (j, i) (j₀, b)) +
          ∑ i, star (U (j₀, i) (j₀, a)) * U (j₀, i) (j₀, b) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
          B, BlockCorner, Matrix.of_apply]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = (∑ j, ∑ i, if j = j₀ then 0 else
            star (U (j, i) (j₀, a)) * U (j, i) (j₀, b)) +
          ∑ j, if j = j₀ then
            (∑ i, star (U (j, i) (j₀, a)) * U (j, i) (j₀, b)) else 0 := by simp
      _ = ∑ j, ∑ i, star (U (j, i) (j₀, a)) * U (j, i) (j₀, b) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = j₀ <;> simp [h]
      _ = (Uᴴ * U) (j₀, a) (j₀, b) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      _ = (1 : Matrix I I ℂ) a b := by simp [hunit, Matrix.one_apply]
  have hpositive : (1 - PΓᴴ * PΓ).PosSemidef := by
    rw [← hdefect]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have hstaridem : PΓᴴ * PΓᴴ = PΓᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hP
  have hzero : PΓᴴ * (1 - PΓᴴ * PΓ) * PΓ = 0 := by
    calc
      _ = PΓᴴ * PΓ - (PΓᴴ * PΓᴴ) * (PΓ * PΓ) := by noncomm_ring
      _ = 0 := by rw [hstaridem, hP, sub_self]
  have hannihilate : (1 - PΓᴴ * PΓ) * PΓ = 0 := by
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    apply hpositive.dotProduct_mulVec_zero_iff.mp
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← mul_assoc, hzero, Matrix.vecMul_zero,
      zero_dotProduct]
  have hgram : PΓ = PΓᴴ * PΓ := by
    simpa only [sub_mul, one_mul, mul_assoc, hP, sub_eq_zero] using hannihilate
  have hhermitian : PΓᴴ = PΓ := by
    calc
      PΓᴴ = PΓᴴ * PΓ := by
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
          congrArg Matrix.conjTranspose hgram
      _ = PΓ := hgram.symm
  have hleft : PΓ * (1 - PΓ) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hright : (1 - PΓ) * PΓ = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hcomplement : (1 - PΓ) * (1 - PΓ) = 1 - PΓ := by
    rw [sub_mul, one_mul, hleft, sub_zero]
  let V : Matrix ((Fin 2 × J) × I) ((Fin 2 × J) × I) ℂ :=
    fun p q => if p.1.2 = q.1.2 then
      (if p.1.1 = q.1.1 then (1 - PΓ) p.2 q.2 else PΓ p.2 q.2) else 0
  have hVstar : Vᴴ = V := by
    ext ⟨⟨b, j⟩, i⟩ ⟨⟨b', j'⟩, i'⟩
    have hp := congrFun (congrFun hhermitian i) i'
    have hq := congrFun (congrFun
      (show (1 - PΓ)ᴴ = 1 - PΓ by simp [hhermitian]) i) i'
    simp only [Matrix.conjTranspose_apply] at hp hq ⊢
    dsimp only [V]
    by_cases hj : j = j'
    · subst j'
      by_cases hb : b = b'
      · subst b'
        simpa only [eq_self_iff_true, ite_true] using hq
      · simpa only [eq_self_iff_true, ite_true, hb, Ne.symm hb, ite_false] using hp
    · simp only [hj, Ne.symm hj, ite_false, star_zero]
  have hVsquare : V * V = 1 := by
    ext ⟨⟨b, j⟩, i⟩ ⟨⟨b', j'⟩, i'⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    by_cases hj : j = j'
    · subst j'
      simp only [V]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero]
      fin_cases b <;> fin_cases b' <;>
        simp [-Matrix.sub_apply, -Pi.sub_apply, ← Matrix.mul_apply, hP, hleft, hright,
          hcomplement, Matrix.one_apply]
      all_goals simp [Matrix.one_apply]
    · have hterm (c : Fin 2) (k : J) (l : I) :
          V ((b, j), i) ((c, k), l) * V ((c, k), l) ((b', j'), i') = 0 := by
        dsimp only [V]
        by_cases hk : j = k
        · have hk' : k ≠ j' := fun h => hj (hk.trans h)
          simp [hk']
        · simp [hk]
      simp only [hterm, Finset.sum_const_zero, zero_add]
      simp [hj]
  refine ⟨V, ?_, one_pos, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hVstar, hVsquare]
  · simp only [inv_one, Complex.ofReal_one, one_smul]
    ext i i'
    simp [BlockCorner, V]

end Qatlib.Papers.BettiNumber25.MainResults.ReflectedLaplacian
