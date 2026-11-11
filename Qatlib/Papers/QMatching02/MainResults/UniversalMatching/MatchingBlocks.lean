/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Spectral blocks for universal quantum matching

This module computes the three-dimensional blocks used in universal quantum matching in
[SasakiCarlini2002]. The matrix `blockMat b c` has explicit vector relations at scalars `√(b² +
c²)`, its negative, and zero; normalized outer products give positive effects summing to the
identity when `b² + c² > 0`.

Specializing to the binomial coefficients `binomB` and `binomC` evaluates the weighted
positive-block trace sum. The final score formula separates the two endpoint contributions from
the interior binomial terms.

## Main statements

* `block_povm_complete`: the three normalized effects sum to the identity for a nonzero block.
* `universal_matching_blocks`: positivity, block completeness, and the total weighted trace
  formula.
* `universal_machine_score`: the resulting score including the baseline one half.

## References

* [Sasaki and Carlini, 2002][SasakiCarlini2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.UniversalMatching

/-- The symmetric three-by-three matrix with adjacent off-diagonal entries `-b` and `c` and zero
elsewhere. -/
def blockMat (b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(0 : ℂ), -(b : ℂ), 0; -(b : ℂ), 0, (c : ℂ); 0, (c : ℂ), 0]

/-- The nonnegative real number `√(b ^ 2 + c ^ 2)` associated with the block. -/
def blockEig (b c : ℝ) : ℝ := Real.sqrt (b ^ 2 + c ^ 2)

/-- The vector `(-b, blockEig b c, c)` for the positive scalar relation. -/
def ePlus (b c : ℝ) : Fin 3 → ℂ := ![-(b : ℂ), (blockEig b c : ℂ), (c : ℂ)]

/-- The vector `(b, blockEig b c, -c)` for the negative scalar relation. -/
def eMinus (b c : ℝ) : Fin 3 → ℂ := ![(b : ℂ), (blockEig b c : ℂ), -(c : ℂ)]

/-- The kernel vector `(c, 0, b)` of the block matrix. -/
def eZero (b c : ℝ) : Fin 3 → ℂ := ![(c : ℂ), (0 : ℂ), (b : ℂ)]

/-- The square of `blockEig b c` is `b ^ 2 + c ^ 2`. -/
theorem blockEig_sq (b c : ℝ) : blockEig b c ^ 2 = b ^ 2 + c ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The block value `blockEig b c` is positive when `b ^ 2 + c ^ 2 > 0`. -/
theorem blockEig_pos {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) : 0 < blockEig b c :=
  Real.sqrt_pos.mpr h

/-- The product of the complex image of `blockEig b c` with itself is the complex image of `b ^
2 + c ^ 2`. -/
theorem blockEig_mul_self (b c : ℝ) :
    (blockEig b c : ℂ) * (blockEig b c : ℂ) = ((b ^ 2 + c ^ 2 : ℝ) : ℂ) := by
  have h := blockEig_sq b c
  rw [pow_two] at h
  rw [← Complex.ofReal_mul, h]

/-- The square of the complex image of `blockEig b c` is the complex image of `b ^ 2 + c ^ 2`. -/
theorem blockEig_sq_complex (b c : ℝ) :
    ((blockEig b c : ℂ)) ^ 2 = ((b ^ 2 + c ^ 2 : ℝ) : ℂ) := by
  rw [pow_two, blockEig_mul_self]

/-- The block matrix sends `ePlus b c` to `blockEig b c` times that vector. -/
theorem blockMat_mulVec_ePlus (b c : ℝ) :
    blockMat b c *ᵥ ePlus b c = (blockEig b c : ℂ) • ePlus b c := by
  funext i
  fin_cases i <;>
    simp [blockMat, ePlus, Matrix.mulVec]
  · ring
  · rw [blockEig_mul_self]; push_cast; ring
  · ring

/-- The block matrix sends `eMinus b c` to `-blockEig b c` times that vector. -/
theorem blockMat_mulVec_eMinus (b c : ℝ) :
    blockMat b c *ᵥ eMinus b c = -((blockEig b c : ℂ)) • eMinus b c := by
  funext i
  fin_cases i <;>
    simp [blockMat, eMinus, Matrix.mulVec]
  · ring
  · rw [blockEig_mul_self]; push_cast; ring
  · ring

/-- The block matrix annihilates `eZero b c`. -/
theorem blockMat_mulVec_eZero (b c : ℝ) :
    blockMat b c *ᵥ eZero b c = 0 := by
  funext i
  fin_cases i <;>
    simp [blockMat, eZero, Matrix.mulVec]
  all_goals ring

/-- The vector `ePlus b c` is fixed by complex conjugation. -/
theorem star_ePlus (b c : ℝ) : star (ePlus b c) = ePlus b c := by
  funext i; fin_cases i <;> simp [ePlus]

/-- The vector `eMinus b c` is fixed by complex conjugation. -/
theorem star_eMinus (b c : ℝ) : star (eMinus b c) = eMinus b c := by
  funext i; fin_cases i <;> simp [eMinus]

/-- The vector `eZero b c` is fixed by complex conjugation. -/
theorem star_eZero (b c : ℝ) : star (eZero b c) = eZero b c := by
  funext i; fin_cases i <;> simp [eZero]

/-- The dot product of `ePlus b c` with itself is the complex image of `2 * blockEig b c ^ 2`. -/
theorem dot_ePlus (b c : ℝ) :
    (ePlus b c) ⬝ᵥ (ePlus b c) = ((2 * blockEig b c ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, ePlus, Fin.sum_univ_three, pow_two, blockEig_mul_self]
  ring

/-- The outer product of `ePlus b c` with its conjugate, scaled by `1 / (2 * blockEig b c ^ 2)`. -/
def projPlus (b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 / (2 * blockEig b c ^ 2) : ℝ)) • vecMulVec (ePlus b c) (star (ePlus b c))

/-- The outer product of `eMinus b c` with its conjugate, scaled by `1 / (2 * blockEig b c ^
2)`. -/
def projMinus (b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 / (2 * blockEig b c ^ 2) : ℝ)) • vecMulVec (eMinus b c) (star (eMinus b c))

/-- The outer product of `eZero b c` with its conjugate, scaled by `1 / blockEig b c ^ 2`. -/
def projZero (b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 / (blockEig b c ^ 2) : ℝ)) • vecMulVec (eZero b c) (star (eZero b c))

/-- For a nonzero block, `projPlus b c` has trace one. -/
theorem trace_projPlus {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) : (projPlus b c).trace = 1 := by
  have hp : (0:ℝ) < 2 * blockEig b c ^ 2 := by
    have := blockEig_pos h; positivity
  unfold projPlus
  rw [Matrix.trace_smul, Matrix.trace_vecMulVec, star_ePlus, dot_ePlus, Complex.real_smul,
    ← Complex.ofReal_mul,
    show (1 / (2 * blockEig b c ^ 2)) * (2 * blockEig b c ^ 2) = 1 by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hp)]]
  simp

/-- Left multiplication by `blockMat b c` scales `projPlus b c` by `blockEig b c`. -/
theorem blockMat_mul_projPlus (b c : ℝ) :
    blockMat b c * projPlus b c = (blockEig b c : ℂ) • projPlus b c := by
  unfold projPlus
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, blockMat_mulVec_ePlus, Matrix.smul_vecMulVec]
  exact smul_comm _ _ _

/-- For a nonzero block, the trace of `blockMat b c * projPlus b c` is `blockEig b c`. -/
theorem trace_blockMat_projPlus {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) :
    (blockMat b c * projPlus b c).trace = (blockEig b c : ℂ) := by
  rw [blockMat_mul_projPlus, Matrix.trace_smul, trace_projPlus h, smul_eq_mul, mul_one]

/-- For a nonzero block, the matrix `projPlus b c` is positive semidefinite. -/
theorem projPlus_posSemidef {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) :
    (projPlus b c).PosSemidef := by
  have hp : (0:ℝ) < blockEig b c ^ 2 := pow_pos (blockEig_pos h) 2
  unfold projPlus
  exact (Matrix.posSemidef_vecMulVec_self_star (ePlus b c)).smul (by positivity)

/-- For a nonzero block, the matrix `projMinus b c` is positive semidefinite. -/
theorem projMinus_posSemidef {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) :
    (projMinus b c).PosSemidef := by
  have hp : (0:ℝ) < blockEig b c ^ 2 := pow_pos (blockEig_pos h) 2
  unfold projMinus
  exact (Matrix.posSemidef_vecMulVec_self_star (eMinus b c)).smul (by positivity)

/-- For a nonzero block, the matrix `projZero b c` is positive semidefinite. -/
theorem projZero_posSemidef {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) :
    (projZero b c).PosSemidef := by
  have hp : (0:ℝ) < blockEig b c ^ 2 := pow_pos (blockEig_pos h) 2
  unfold projZero
  exact (Matrix.posSemidef_vecMulVec_self_star (eZero b c)).smul (by positivity)

/-- When `b ^ 2 + c ^ 2 > 0`, the three block effects sum to the identity. See
[SasakiCarlini2002]. -/
theorem block_povm_complete {b c : ℝ} (h : 0 < b ^ 2 + c ^ 2) :
    projPlus b c + projMinus b c + projZero b c = 1 := by
  have hp : (0:ℝ) < 2 * blockEig b c ^ 2 := by
    have := blockEig_pos h; positivity
  have hp' : (0:ℝ) < blockEig b c ^ 2 := pow_pos (blockEig_pos h) 2
  have ha1 : (2 * blockEig b c ^ 2) * (1 / (2 * blockEig b c ^ 2)) = 1 := by
    rw [one_div, mul_inv_cancel₀ (ne_of_gt hp)]
  have ha2 : (2 * blockEig b c ^ 2) * (1 / (blockEig b c ^ 2)) = 2 := by
    rw [mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hp'), mul_one]
  have hmul : (2 * blockEig b c ^ 2 : ℝ) •
      (projPlus b c + projMinus b c + projZero b c)
      = (2 * blockEig b c ^ 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    simp only [projPlus, projMinus, projZero, smul_add]
    rw [smul_smul, smul_smul, smul_smul, ha1, ha2]
    simp only [one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ePlus, eMinus, eZero, Matrix.add_apply, Matrix.smul_apply,
        blockEig_mul_self, pow_two, Complex.real_smul] <;>
      ring
  have hne : (2 * blockEig b c ^ 2 : ℝ) ≠ 0 := ne_of_gt hp
  have hzero : (2 * blockEig b c ^ 2 : ℝ) •
      (projPlus b c + projMinus b c + projZero b c - 1) = 0 := by
    rw [smul_sub, hmul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hne)

/-- The scalar block weight `√2 / 2 ^ (N + 4)`. -/
def blockWeight (N : ℕ) : ℝ := Real.sqrt 2 / (2 : ℝ) ^ (N + 4)

/-- The product of the square roots of `choose N k` and `choose N (k + 1)`. -/
def binomB (N k : ℕ) : ℝ :=
  Real.sqrt (Nat.choose N k) * Real.sqrt (Nat.choose N (k + 1))

/-- The product of the square roots of `choose N k` and `choose N (k - 1)`, with the value at `k
= 0` set to zero. -/
def binomC (N k : ℕ) : ℝ :=
  if k = 0 then 0 else Real.sqrt (Nat.choose N k) * Real.sqrt (Nat.choose N (k - 1))

/-- The binomial block magnitude, using a zero lower-neighbor term at `k = 0`. -/
def binomS (N k : ℕ) : ℝ :=
  Real.sqrt (Nat.choose N k) *
    Real.sqrt ((Nat.choose N (k + 1) : ℝ) +
      (if k = 0 then 0 else (Nat.choose N (k - 1) : ℝ)))

/-- The block value at `binomB N k` and `binomC N k` equals `binomS N k`. -/
theorem blockEig_binom (N k : ℕ) :
    blockEig (binomB N k) (binomC N k) = binomS N k := by
  unfold blockEig binomB binomC binomS
  by_cases hk : k = 0
  · subst hk
    simp [Nat.choose_one_right]
  · simp only [hk, if_false]
    rw [show (Real.sqrt (↑(Nat.choose N k)) * Real.sqrt (↑(Nat.choose N (k + 1)))) ^ 2
          = (Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ) by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]]
    rw [show (Real.sqrt (↑(Nat.choose N k)) * Real.sqrt (↑(Nat.choose N (k - 1)))) ^ 2
          = (Nat.choose N k : ℝ) * (Nat.choose N (k - 1) : ℝ) by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]]
    rw [← mul_add, ← Real.sqrt_mul (by positivity)]

/-- For `N ≥ 1` and `k ≤ N`, the sum of the squares of `binomB N k` and `binomC N k` is
positive. -/
theorem binom_block_pos {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    0 < binomB N k ^ 2 + binomC N k ^ 2 := by
  have hchoose : (1 : ℝ) ≤ (Nat.choose N k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hb : binomB N k ^ 2 = (Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ) := by
    unfold binomB
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  rcases lt_or_eq_of_le hk with hlt | heq
  · have hch : (1 : ℝ) ≤ (Nat.choose N (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [hb]
    nlinarith [sq_nonneg (binomC N k)]
  · rw [heq]
    have hc : binomC N N ^ 2 = (Nat.choose N N : ℝ) * (Nat.choose N (N - 1) : ℝ) := by
      unfold binomC
      rw [if_neg (by omega), mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
    have hchN : Nat.choose N (N - 1) = N := by
      rw [Nat.choose_symm hN]; exact Nat.choose_one_right N
    have hch : (1 : ℝ) ≤ (Nat.choose N (N - 1) : ℝ) := by
      rw [hchN]; exact_mod_cast hN
    have hcN : (Nat.choose N N : ℝ) = 1 := by simp
    rw [hc, hcN]
    nlinarith [sq_nonneg (binomB N N)]

/-- The binomial block magnitude at `k = 0` is `√N`. -/
theorem binomS_zero (N : ℕ) : binomS N 0 = Real.sqrt N := by
  unfold binomS
  simp [Nat.choose_one_right]

/-- For `N ≥ 1`, the binomial block magnitude at `k = N` is `√N`. -/
theorem binomS_top {N : ℕ} (hN : 1 ≤ N) : binomS N N = Real.sqrt N := by
  unfold binomS
  have hN0 : N ≠ 0 := by omega
  rw [if_neg hN0, Nat.choose_self, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N),
    show Nat.choose N (N - 1) = N by
      rw [Nat.choose_symm hN]; exact Nat.choose_one_right N]
  simp

/-- For `k ≥ 1`, `binomS N k` is the square root of `choose N k` times the square root of the
sum of its two neighboring binomial coefficients. -/
theorem binomS_interior {N k : ℕ} (hk : 1 ≤ k) :
    binomS N k = Real.sqrt (Nat.choose N k) *
      Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)) := by
  unfold binomS
  rw [if_neg (by omega)]

/-- For `N ≥ 1`, the sum of the block values splits into two `√N` endpoint terms and the
interior sum of `binomS`. -/
theorem sum_blockEig_split (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range (N + 1), blockEig (binomB N k) (binomC N k))
      = Real.sqrt N + (∑ k ∈ Finset.Icc 1 (N - 1), binomS N k) + Real.sqrt N := by
  simp only [blockEig_binom]
  have hIcc : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext k; simp [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_range_succ' _ N]
  have hsucc : (∑ k ∈ Finset.range N, binomS N (k + 1))
      = (∑ k ∈ Finset.range (N - 1), binomS N (k + 1)) + binomS N N := by
    have := Finset.sum_range_succ (fun k => binomS N (k + 1)) (N - 1)
    rwa [Nat.sub_add_cancel hN] at this
  rw [hsucc, binomS_top hN, Finset.sum_Ico_eq_sum_range, binomS_zero]
  have hshift : (∑ k ∈ Finset.range (N - 1), binomS N (k + 1))
      = ∑ k ∈ Finset.range (N - 1), binomS N (1 + k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm]
  rw [hshift]
  ring

/-- For `N ≥ 1`, the weighted block-value sum equals the expression with two endpoint terms and
the interior binomial square-root sum. See [SasakiCarlini2002]. -/
theorem qmScore_blocks (N : ℕ) (hN : 1 ≤ N) :
    blockWeight N * (∑ k ∈ Finset.range (N + 1), blockEig (binomB N k) (binomC N k))
      = blockWeight N * (2 * Real.sqrt N +
          ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) := by
  have hS : (∑ k ∈ Finset.Icc 1 (N - 1), binomS N k)
      = ∑ k ∈ Finset.Icc 1 (N - 1),
          Real.sqrt (Nat.choose N k) *
            Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact binomS_interior (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [sum_blockEig_split N hN, hS]
  ring

/-- The binomial block matrix multiplied by the scalar `blockWeight N`. -/
def deltaW (N k : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  blockWeight N • blockMat (binomB N k) (binomC N k)

/-- For a nonzero binomial block, the real trace of `deltaW N k * projPlus` is the block weight
times the block value. See [SasakiCarlini2002]. -/
theorem trace_deltaW_projPlus {N k : ℕ} (h : 0 < binomB N k ^ 2 + binomC N k ^ 2) :
    Complex.re ((deltaW N k * projPlus (binomB N k) (binomC N k)).trace)
      = blockWeight N * blockEig (binomB N k) (binomC N k) := by
  unfold deltaW
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_blockMat_projPlus h, Complex.real_smul,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- For `N ≥ 1`, the positive effects are positive semidefinite, each block triple sums to the
identity, and the weighted trace sum has the stated binomial expression. See
[SasakiCarlini2002]. -/
theorem universal_matching_blocks (N : ℕ) (hN : 1 ≤ N) :
    (∀ k ∈ Finset.range (N + 1), (projPlus (binomB N k) (binomC N k)).PosSemidef)
    ∧ (∀ k ∈ Finset.range (N + 1),
        projPlus (binomB N k) (binomC N k) + projMinus (binomB N k) (binomC N k)
          + projZero (binomB N k) (binomC N k) = 1)
    ∧ (∑ k ∈ Finset.range (N + 1),
          Complex.re ((deltaW N k * projPlus (binomB N k) (binomC N k)).trace))
        = blockWeight N * (2 * Real.sqrt N +
            ∑ k ∈ Finset.Icc 1 (N - 1),
              Real.sqrt (Nat.choose N k) *
                Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) := by
  have hpos : ∀ k ∈ Finset.range (N + 1), 0 < binomB N k ^ 2 + binomC N k ^ 2 := by
    intro k hk
    exact binom_block_pos hN (by have := Finset.mem_range.mp hk; omega)
  refine ⟨fun k hk => projPlus_posSemidef (hpos k hk),
    fun k hk => block_povm_complete (hpos k hk), ?_⟩
  calc (∑ k ∈ Finset.range (N + 1),
        Complex.re ((deltaW N k * projPlus (binomB N k) (binomC N k)).trace))
      = ∑ k ∈ Finset.range (N + 1),
          blockWeight N * blockEig (binomB N k) (binomC N k) :=
        Finset.sum_congr rfl fun k hk => trace_deltaW_projPlus (hpos k hk)
    _ = blockWeight N * (∑ k ∈ Finset.range (N + 1),
          blockEig (binomB N k) (binomC N k)) := by rw [Finset.mul_sum]
    _ = blockWeight N * (2 * Real.sqrt N +
          ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) :=
        qmScore_blocks N hN

/-- For `N ≥ 1`, adding one half to the weighted positive-block trace sum gives the displayed
universal matching score formula. See [SasakiCarlini2002]. -/
theorem universal_machine_score (N : ℕ) (hN : 1 ≤ N) :
    1 / 2 + (∑ k ∈ Finset.range (N + 1),
        Complex.re ((deltaW N k * projPlus (binomB N k) (binomC N k)).trace))
      = 1 / 2 + blockWeight N * (2 * Real.sqrt N +
          ∑ k ∈ Finset.Icc 1 (N - 1),
            Real.sqrt (Nat.choose N k) *
              Real.sqrt ((Nat.choose N (k + 1) : ℝ) + (Nat.choose N (k - 1) : ℝ))) := by
  rw [(universal_matching_blocks N hN).2.2]

end Qatlib.Papers.QMatching02.MainResults.UniversalMatching
