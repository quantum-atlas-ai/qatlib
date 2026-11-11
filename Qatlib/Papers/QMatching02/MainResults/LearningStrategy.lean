/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

/-!
# Learning measurements for quantum template matching

This module verifies explicit learning measurements and score formulas for the template-matching
setting of [SasakiCarlini2002]. The matrices `muTilde`, `gTilde`, and `gammaTilde` satisfy
positivity, dominance, and annihilation identities, with the score expression `1 / 2 + R / √2`
for nonnegative `R`.

Three equally spaced phases give a finite completeness identity after scaling. A second
construction uses four product vectors from the `Aplus`, `Aminus`, `Bplus`, and `Bminus` bases,
proves positivity and completeness of their effects, and evaluates their total score.

## Main statements

* `squareRoot_measurement_optimal`: positivity, dominance, annihilation, and score certificates
  for the square-root construction.
* `discrete_three_output_learning_pom`: three-phase positivity and completeness certificates.
* `four_output_product_vonNeumann_pom`: positivity and completeness of the four product effects.
* `four_output_product_pom_score`: the four contributions sum to `1 / 2 + R / √2`.

## References

* [Sasaki and Carlini, 2002][SasakiCarlini2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.LearningStrategy

open Complex

/-- The diagonal matrix with entries `1 / 4`, `1 / 2`, and `1 / 4` used in the learning
construction. -/
def aOp : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1/4 : ℂ), 0, 0; 0, (1/2 : ℂ), 0; 0, 0, (1/4 : ℂ)]

/-- The inverse square root of `aOp`, explicitly diagonal with entries `2`, `√2`, and `2`. -/
def aInvSqrt : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(2 : ℂ), 0, 0; 0, (Real.sqrt 2 : ℂ), 0; 0, 0, (2 : ℂ)]

/-- The phase-dependent three-component vector used for the positive-weight term of `gTilde`. -/
def aPlus (θ : ℝ) : Fin 3 → ℂ :=
  ![-((1/2 : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2))),
    (1/2 : ℂ) * (Real.sqrt 2),
    (1/2 : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2))]

/-- The phase-dependent three-component vector used for the `1 - 2 * R` term of `gTilde`. -/
def aZero (θ : ℝ) : Fin 3 → ℂ :=
  ![((1/2 : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2))),
    (1/2 : ℂ) * (Real.sqrt 2),
    -((1/2 : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2)))]

/-- The phase-dependent three-component vector used for the unit-weight term of `gTilde`. -/
def aMinus (θ : ℝ) : Fin 3 → ℂ :=
  ![((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2)),
    0,
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2))]

/-- The explicit complex conjugate of `aPlus θ`. -/
def starAPlus (θ : ℝ) : Fin 3 → ℂ :=
  ![-((1/2 : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2))),
    (1/2 : ℂ) * (Real.sqrt 2),
    (1/2 : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2))]

/-- The explicit complex conjugate of `aZero θ`. -/
def starAZero (θ : ℝ) : Fin 3 → ℂ :=
  ![((1/2 : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2))),
    (1/2 : ℂ) * (Real.sqrt 2),
    -((1/2 : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2)))]

/-- The explicit complex conjugate of `aMinus θ`. -/
def starAMinus (θ : ℝ) : Fin 3 → ℂ :=
  ![((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ + Real.pi / 2)),
    0,
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I) * (θ + Real.pi / 2))]

/-- The vector obtained by applying `aInvSqrt` to `aPlus θ`. -/
def phiTilde (θ : ℝ) : Fin 3 → ℂ :=
  ![-Complex.exp (-(Complex.I) * (θ + Real.pi / 2)),
    1,
    Complex.exp (Complex.I * (θ + Real.pi / 2))]

/-- The outer product of `phiTilde θ` with its complex conjugate. -/
def muTilde (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (phiTilde θ) (star (phiTilde θ))

/-- The weighted sum of the outer products associated with `aPlus`, `aMinus`, and `aZero`. -/
def gTilde (R : ℝ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 + 2*R) • vecMulVec (aPlus θ) (starAPlus θ)
    + (1 : ℂ) • vecMulVec (aMinus θ) (starAMinus θ)
    + (1 - 2*R) • vecMulVec (aZero θ) (starAZero θ)

/-- The diagonal comparison matrix with entries `1 + √2 * R`, `1 + 2 * √2 * R`, and `1 + √2 *
R`. -/
def gammaTilde (R : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 + Real.sqrt 2 * R : ℂ), 0, 0;
     0, (1 + 2 * Real.sqrt 2 * R : ℂ), 0;
     0, 0, (1 + Real.sqrt 2 * R : ℂ)]

/-- The vector `(exp(-iθ), 0, -exp(iθ))` used in the dominance decomposition. -/
def vOne (θ : ℝ) : Fin 3 → ℂ :=
  ![Complex.exp (-(Complex.I) * θ), 0, -(Complex.exp (Complex.I * θ))]

/-- The vector `(exp(-iθ), 2i, exp(iθ))` used in the dominance decomposition. -/
def vTwo (θ : ℝ) : Fin 3 → ℂ :=
  ![Complex.exp (-(Complex.I) * θ), (2 * Complex.I), Complex.exp (Complex.I * θ)]

/-- The coefficient `√2 / 2` multiplying the first outer-product term in the dominance
decomposition. -/
def coefOne : ℝ := Real.sqrt 2 / 2

/-- The coefficient `√2 / 2` multiplying the second outer-product term in the dominance
decomposition. -/
def coefTwo : ℝ := Real.sqrt 2 / 2

/-- Adding `π / 2` to the phase multiplies `exp(iθ)` by `i`. -/
theorem exp_pos (θ : ℝ) :
    Complex.exp (Complex.I * (θ + Real.pi/2)) = Complex.I * Complex.exp (Complex.I*θ) := by
  have h : Complex.I*(θ+Real.pi/2) = Complex.I*θ + Real.pi/2*Complex.I := by ring
  rw [h, Complex.exp_add, Complex.exp_pi_div_two_mul_I]; ring

/-- Adding `π / 2` to the phase multiplies `exp(-iθ)` by `-i` in the negative exponential. -/
theorem exp_neg (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ + Real.pi/2))) = -Complex.I * Complex.exp (-(Complex.I*θ)) := by
  have h : -(Complex.I*(θ+Real.pi/2)) = -(Complex.I*θ) + (-(Real.pi/2)*Complex.I) := by ring
  rw [h, Complex.exp_add]
  have h2 : Complex.exp (-(Real.pi/2)*Complex.I) = -Complex.I := by
    rw [show -(Real.pi/2)*Complex.I = (-Real.pi/2)*Complex.I by ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  rw [h2]; ring

/-- Complex conjugation sends `exp(iθ)` to `exp(-iθ)` for real `θ`. -/
theorem star_exp_pos (θ : ℝ) :
    star (Complex.exp (Complex.I * θ)) = Complex.exp (-(Complex.I * θ)) := by
  rw [Complex.star_def, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

/-- Complex conjugation sends `exp(-iθ)` to `exp(iθ)` for real `θ`. -/
theorem star_exp_neg (θ : ℝ) :
    star (Complex.exp (-(Complex.I * θ))) = Complex.exp (Complex.I * θ) := by
  rw [Complex.star_def, ← Complex.exp_conj]; congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

/-- The square of the complex image of `√2` is two. -/
theorem sq2c : ((Real.sqrt 2 : ℂ))^2 = 2 := by
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The square of the complex image of `√6` is six. -/
theorem sq6c : ((Real.sqrt 6 : ℂ))^2 = 6 := by
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- Complex conjugation commutes with the complex exponential. -/
theorem star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  rw [Complex.star_def]; rw [← Complex.exp_conj]

/-- Multiplication of `aPlus θ` by `aInvSqrt` gives `phiTilde θ`. -/
theorem aInvSqrt_mulVec_aPlus (θ : ℝ) :
    aInvSqrt *ᵥ aPlus θ = phiTilde θ := by
  funext i
  fin_cases i <;>
    simp [aInvSqrt, aPlus, phiTilde, Matrix.mulVec, Fin.sum_univ_three] <;>
    ring_nf
  · have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hc : ((Real.sqrt 2 : ℂ))^2 = (2 : ℂ) := by
      rw [pow_two,
        show ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))
            = ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring,
        h2]
      norm_num
    rw [hc]; norm_num

/-- The matrix `muTilde θ` is positive semidefinite for every real phase. -/
theorem muTilde_posSemidef (θ : ℝ) : (muTilde θ).PosSemidef := by
  rw [muTilde]
  exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr
    ⟨1, fun _ => phiTilde θ, by simp⟩

/-- The conjugate of `aPlus θ` is the explicit vector `starAPlus θ`. -/
theorem star_aPlus (θ : ℝ) : star (aPlus θ) = starAPlus θ := by
  funext i; fin_cases i <;>
    simp [aPlus, starAPlus, star_exp, Complex.star_def, map_mul, map_add, map_neg,
      Complex.conj_I, Complex.conj_ofReal]

/-- The conjugate of `aZero θ` is the explicit vector `starAZero θ`. -/
theorem star_aZero (θ : ℝ) : star (aZero θ) = starAZero θ := by
  funext i; fin_cases i <;>
    simp [aZero, starAZero, star_exp, Complex.star_def, map_mul, map_add, map_neg,
      Complex.conj_I, Complex.conj_ofReal]

/-- The conjugate of `aMinus θ` is the explicit vector `starAMinus θ`. -/
theorem star_aMinus (θ : ℝ) : star (aMinus θ) = starAMinus θ := by
  funext i; fin_cases i <;>
    simp [aMinus, starAMinus, star_exp, Complex.star_def, map_mul, map_add, map_neg,
      Complex.conj_I, Complex.conj_ofReal]

/-- The explicit complex conjugate of `vOne θ`. -/
def starVOne (θ : ℝ) : Fin 3 → ℂ :=
  ![Complex.exp (Complex.I*θ), 0, -(Complex.exp (-(Complex.I*θ)))]

/-- The explicit complex conjugate of `vTwo θ`. -/
def starVTwo (θ : ℝ) : Fin 3 → ℂ :=
  ![Complex.exp (Complex.I*θ), -(2*Complex.I), Complex.exp (-(Complex.I*θ))]

/-- The conjugate of `vOne θ` is `starVOne θ`. -/
theorem star_vOne (θ : ℝ) : star (vOne θ) = starVOne θ := by
  funext i; fin_cases i <;> simp [vOne, starVOne, star_exp_pos, star_exp_neg]

/-- The conjugate of `vTwo θ` is `starVTwo θ`. -/
theorem star_vTwo (θ : ℝ) : star (vTwo θ) = starVTwo θ := by
  funext i; fin_cases i <;> simp [vTwo, starVTwo, star_exp_pos, star_exp_neg]

/-- The difference `gammaTilde R - gTilde R θ` is the sum of two outer products weighted by `R *
coefOne` and `R * coefTwo`. -/
theorem main_identity (R θ : ℝ) :
    gammaTilde R - gTilde R θ
      = (R * coefOne) • vecMulVec (vOne θ) (star (vOne θ))
        + (R * coefTwo) • vecMulVec (vTwo θ) (star (vTwo θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gammaTilde, gTilde, aPlus, aZero, aMinus, starAPlus, starAZero, starAMinus,
    vOne, vTwo, coefOne, coefTwo, exp_pos, exp_neg, star_exp_pos, star_exp_neg, Fin.sum_univ_three]
  all_goals
    (ring_nf <;>
     (try simp only [sq2c, sq6c, Complex.I_sq]) <;>
     (try simp only [Complex.exp_neg]) <;>
     (try field_simp) <;>
     (try ring))

/-- The product of `exp a` and `exp (-a)` is one for any complex `a`. -/
theorem exp_mul_exp_neg (a : ℂ) : Complex.exp a * Complex.exp (-a) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- For nonnegative `R`, the difference `gammaTilde R - gTilde R θ` is positive semidefinite. -/
theorem dominance (R : ℝ) (hR : 0 ≤ R) (θ : ℝ) :
    (gammaTilde R - gTilde R θ).PosSemidef := by
  rw [main_identity]
  have h1 : (0:ℝ) ≤ R * coefOne := mul_nonneg hR (by unfold coefOne; positivity)
  have h2 : (0:ℝ) ≤ R * coefTwo := mul_nonneg hR (by unfold coefTwo; positivity)
  have hA : (vecMulVec (vOne θ) (star (vOne θ))).PosSemidef :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨1, fun _ => vOne θ, by simp⟩
  have hB : (vecMulVec (vTwo θ) (star (vTwo θ))).PosSemidef :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr ⟨1, fun _ => vTwo θ, by simp⟩
  exact (hA.smul h1).add (hB.smul h2)

/-- The outer product of any vector with the zero vector is the zero matrix. -/
theorem vecMulVec_zero (u : Fin 3 → ℂ) : vecMulVec u (0 : Fin 3 → ℂ) = 0 := by
  ext i j; simp [vecMulVec_apply]

/-- The vector `vOne θ` is orthogonal to `phiTilde θ` under the conjugated dot product. -/
theorem dot_vOne_phi (θ : ℝ) : (star (vOne θ) ⬝ᵥ phiTilde θ) = 0 := by
  rw [star_vOne]
  simp [dotProduct, starVOne, phiTilde, Fin.sum_univ_three]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [show Complex.I*↑θ + -(Complex.I*(↑θ+Real.pi/2)) = -(Real.pi/2)*Complex.I by ring]
  rw [show -(Complex.I*↑θ) + Complex.I*(↑θ+Real.pi/2) = (Real.pi/2)*Complex.I by ring]
  rw [show -(Real.pi/2)*Complex.I = (-Real.pi/2)*Complex.I by ring]
  rw [Complex.exp_neg_pi_div_two_mul_I, Complex.exp_pi_div_two_mul_I]
  ring

/-- The vector `vTwo θ` is orthogonal to `phiTilde θ` under the conjugated dot product. -/
theorem dot_vTwo_phi (θ : ℝ) : (star (vTwo θ) ⬝ᵥ phiTilde θ) = 0 := by
  rw [star_vTwo]
  simp [dotProduct, starVTwo, phiTilde, Fin.sum_univ_three]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [show Complex.I*↑θ + -(Complex.I*(↑θ+Real.pi/2)) = -(Real.pi/2)*Complex.I by ring]
  rw [show -(Complex.I*↑θ) + Complex.I*(↑θ+Real.pi/2) = (Real.pi/2)*Complex.I by ring]
  rw [show -(Real.pi/2)*Complex.I = (-Real.pi/2)*Complex.I by ring]
  rw [Complex.exp_neg_pi_div_two_mul_I, Complex.exp_pi_div_two_mul_I]
  ring

/-- The product `(gammaTilde R - gTilde R θ) * muTilde θ` is zero. -/
theorem annihilation (R : ℝ) (θ : ℝ) :
    (gammaTilde R - gTilde R θ) * muTilde θ = 0 := by
  rw [main_identity]
  have h1 : vecMulVec (vOne θ) (star (vOne θ)) * muTilde θ = 0 := by
    rw [muTilde, Matrix.vecMulVec_mul_vecMulVec, dot_vOne_phi, zero_smul, vecMulVec_zero]
  have h2 : vecMulVec (vTwo θ) (star (vTwo θ)) * muTilde θ = 0 := by
    rw [muTilde, Matrix.vecMulVec_mul_vecMulVec, dot_vTwo_phi, zero_smul, vecMulVec_zero]
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, h1, h2]
  simp

/-- The real part of the trace of `gammaTilde R` is `3 + 4 * √2 * R`. See [SasakiCarlini2002]. -/
theorem gammaTilde_trace (R : ℝ) :
    Complex.re (gammaTilde R).trace = 3 + 4 * Real.sqrt 2 * R := by
  simp [gammaTilde, Matrix.trace, Fin.sum_univ_three]
  ring

/-- The trace-based learning score expression equals `1 / 2 + R / √2`. See [SasakiCarlini2002]. -/
theorem learning_score_arith (R : ℝ) :
    (1/8 : ℝ) + (1/8) * (Complex.re (gammaTilde R).trace)
      = 1/2 + R / Real.sqrt 2 := by
  rw [gammaTilde_trace]
  have h : Real.sqrt 2 * (1 / 2) = (Real.sqrt 2)⁻¹ := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith
  linear_combination R * h

/-- For nonnegative `R`, the square-root construction satisfies positivity, dominance, and
annihilation, together with the stated learning score formula. See [SasakiCarlini2002]. -/
theorem squareRoot_measurement_optimal (R : ℝ) (hR : 0 ≤ R) :
    (∀ θ : ℝ, (muTilde θ).PosSemidef)
    ∧ (∀ θ : ℝ, (gammaTilde R - gTilde R θ).PosSemidef)
    ∧ (∀ θ : ℝ, (gammaTilde R - gTilde R θ) * muTilde θ = 0)
    ∧ ((1/8 : ℝ) + (1/8) * (Complex.re (gammaTilde R).trace)
        = 1/2 + R / Real.sqrt 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ; exact muTilde_posSemidef θ
  · intro θ; exact dominance R hR θ
  · intro θ; exact annihilation R θ
  · exact learning_score_arith R

/-- The three phases `0`, `2 * π / 3`, and `4 * π / 3`. -/
def discretePhase : Fin 3 → ℝ :=
  ![0, 2 * Real.pi / 3, 4 * Real.pi / 3]

/-- The complex number `exp(2πi / 3)`. -/
def zeta : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- The number `zeta` is a primitive cube root of unity. -/
theorem zeta_prim : IsPrimitiveRoot zeta 3 := by
  rw [zeta]; exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The cube of `zeta` is one. -/
theorem zeta3 : zeta ^ 3 = 1 := zeta_prim.pow_eq_one

/-- The sum `1 + zeta + zeta ^ 2` is zero. -/
theorem hroot : 1 + zeta + zeta ^ 2 = 0 := by
  have h := zeta_prim.geom_sum_eq_zero (by norm_num : 1 < 3)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

/-- The inverse of `zeta` is its square. -/
theorem zeta_inv : zeta⁻¹ = zeta ^ 2 := by
  have h : zeta * zeta ^ 2 = 1 := by rw [← pow_succ']; exact zeta3
  exact inv_eq_of_mul_eq_one_right h

/-- The square of the inverse of `zeta` is `zeta`. -/
theorem zeta_inv_sq : (zeta⁻¹) ^ 2 = zeta := by
  rw [zeta_inv, ← pow_mul]
  have : (2 * 2 : ℕ) = 3 + 1 := by norm_num
  rw [this, pow_add, zeta3, one_mul, pow_one]

/-- The inverse of the square of `zeta` is `zeta`. -/
theorem zeta_sq_inv : (zeta ^ 2)⁻¹ = zeta := by
  rw [← inv_pow, zeta_inv_sq]

/-- The square of `zeta ^ 2` is `zeta`. -/
theorem zeta_sq_sq : (zeta ^ 2) ^ 2 = zeta := by
  rw [← pow_mul]
  have : (2 * 2 : ℕ) = 3 + 1 := by norm_num
  rw [this, pow_add, zeta3, one_mul, pow_one]

/-- The inverse of `(zeta ^ 2) ^ 2` is `zeta ^ 2`. -/
theorem zeta_four_inv : ((zeta ^ 2) ^ 2)⁻¹ = zeta ^ 2 := by
  rw [← inv_pow, zeta_sq_inv]

/-- The complex exponential at `-πi / 2` equals `-i`. -/
theorem exp_neg_pi_div_two : Complex.exp (-(Real.pi / 2) * Complex.I) = -Complex.I := by
  rw [show -(Real.pi / 2) * Complex.I = -((Real.pi / 2) * Complex.I) by ring]
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]

/-- The negative exponential at phase `θ + π / 2` factors as `-i * exp(-iθ)`. -/
theorem exp_neg_split (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ + Real.pi / 2)))
      = -(Complex.I) * Complex.exp (-(Complex.I * θ)) := by
  have hsplit : -(Complex.I * ((θ : ℂ) + (Real.pi : ℂ) / 2))
      = (-(Complex.I * (θ : ℂ))) + (-((Real.pi : ℂ) / 2) * Complex.I) := by ring
  rw [hsplit, Complex.exp_add]
  rw [show -((Real.pi : ℂ) / 2) * Complex.I = -(Real.pi / 2) * Complex.I by push_cast; ring]
  rw [exp_neg_pi_div_two]
  ring

/-- The positive exponential at phase `θ + π / 2` factors as `i * exp(iθ)`. -/
theorem exp_pos_split (θ : ℝ) :
    Complex.exp (Complex.I * (θ + Real.pi / 2)) = Complex.I * Complex.exp (Complex.I * θ) := by
  have hsplit : Complex.I * ((θ : ℂ) + (Real.pi : ℂ) / 2)
      = Complex.I * (θ : ℂ) + ((Real.pi : ℂ) / 2) * Complex.I := by ring
  rw [hsplit, Complex.exp_add]
  rw [show (Real.pi : ℂ) / 2 * Complex.I = Real.pi / 2 * Complex.I by push_cast; ring]
  rw [Complex.exp_pi_div_two_mul_I]
  ring

/-- The phase at index `i` is `2 * π / 3` times the real value of `i`. -/
theorem discretePhase_eq (i : Fin 3) :
    discretePhase i = 2 * Real.pi / 3 * (i : ℝ) := by
  fin_cases i <;> simp [discretePhase] <;> ring

/-- The exponential of `i` times the discrete phase is the corresponding natural power of
`zeta`. -/
theorem E_eq (i : Fin 3) :
    Complex.exp (Complex.I * (discretePhase i : ℂ)) = zeta ^ (i : ℕ) := by
  rw [discretePhase_eq]
  have harg : Complex.I * (((2 * Real.pi / 3 * (i : ℝ)) : ℝ) : ℂ)
      = (i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 3) := by push_cast; ring
  rw [zeta, ← Complex.exp_nat_mul, harg]

/-- The negative phase exponential is the corresponding natural power of the inverse of `zeta`. -/
theorem F_eq (i : Fin 3) :
    Complex.exp (-(Complex.I * (discretePhase i : ℂ))) = (zeta⁻¹) ^ (i : ℕ) := by
  rw [discretePhase_eq]
  have harg : -(Complex.I * (((2 * Real.pi / 3 * (i : ℝ)) : ℝ) : ℂ))
      = (i : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I / 3)) := by push_cast; ring
  rw [zeta, ← Complex.exp_neg, ← Complex.exp_nat_mul, harg]

/-- The matrix `muTilde θ` has the displayed three-by-three expression in positive and negative
phase exponentials. -/
theorem muTilde_eq (θ : ℝ) :
    muTilde θ = !![1, Complex.I * Complex.exp (-(Complex.I * θ)),
                    (Complex.exp (-(Complex.I * θ))) ^ 2;
                    -(Complex.I) * Complex.exp (Complex.I * θ), 1,
                      -(Complex.I) * Complex.exp (-(Complex.I * θ));
                    (Complex.exp (Complex.I * θ)) ^ 2,
                      Complex.I * Complex.exp (Complex.I * θ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [muTilde, phiTilde, vecMulVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, exp_neg_split, exp_pos_split,
    star_exp, Complex.conj_I]
  all_goals
    (have hfe : Complex.exp (-(Complex.I * (θ:ℂ))) * Complex.exp (Complex.I * (θ:ℂ)) = 1 := by
        rw [← Complex.exp_add, show -(Complex.I * (θ:ℂ)) + Complex.I * (θ:ℂ) = 0 by ring,
          Complex.exp_zero]
     have hef : Complex.exp (Complex.I * (θ:ℂ)) * Complex.exp (-(Complex.I * (θ:ℂ))) = 1 := by
        rw [← Complex.exp_add, show Complex.I * (θ:ℂ) + -(Complex.I * (θ:ℂ)) = 0 by ring,
          Complex.exp_zero]
     ring_nf
     try simp only [Complex.I_sq]
     try ring_nf
     try simp only [hfe, hef]
     try ring)

/-- The sum of `muTilde` over the three discrete phases is three times the identity matrix. See
[SasakiCarlini2002]. -/
theorem discrete_complete :
    (∑ i : Fin 3, muTilde (discretePhase i)) = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
  simp [Matrix.sum_apply, muTilde_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, E_eq, F_eq, Fin.sum_univ_three]
  all_goals
    (try simp only [zeta_inv, zeta_sq_inv, zeta_four_inv, zeta_sq_sq]
     try ring_nf
     first
      | linear_combination hroot
      | linear_combination Complex.I * hroot
      | linear_combination (-Complex.I) * hroot
      | linear_combination (-1 : ℂ) * hroot)

/-- For nonnegative `R`, the three discrete effects satisfy positivity, sum to three times the
identity, and satisfy dominance and annihilation with `gammaTilde R`. See
[SasakiCarlini2002]. -/
theorem discrete_three_output_learning_pom (R : ℝ) (hR : 0 ≤ R) :
    (∀ i : Fin 3, (muTilde (discretePhase i)).PosSemidef)
    ∧ ((∑ i : Fin 3, muTilde (discretePhase i)) = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    ∧ (∀ i : Fin 3, (gammaTilde R - gTilde R (discretePhase i)).PosSemidef)
    ∧ (∀ i : Fin 3,
        (gammaTilde R - gTilde R (discretePhase i)) * muTilde (discretePhase i) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; exact muTilde_posSemidef _
  · exact discrete_complete
  · intro i; exact dominance R hR _
  · intro i; exact annihilation R _

/-- The normalized vector `(1, 1) / √2` for the first local measurement. -/
def Aplus : Fin 2 → ℂ := ![1 / Real.sqrt 2, 1 / Real.sqrt 2]

/-- The normalized vector `(1, -1) / √2` for the first local measurement. -/
def Aminus : Fin 2 → ℂ := ![1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-- The normalized vector `(1, i) / √2` for the second local measurement. -/
def Bplus : Fin 2 → ℂ := ![1 / Real.sqrt 2, Complex.I / Real.sqrt 2]

/-- The normalized vector `(1, -i) / √2` for the second local measurement. -/
def Bminus : Fin 2 → ℂ := ![1 / Real.sqrt 2, -(Complex.I / Real.sqrt 2)]

/-- The product vector selecting an `A` vector and a `B` vector according to the two binary
labels. -/
def muProd (s : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  fun p => (if s.1 = 0 then Aplus else Aminus) p.1
            * (if s.2 = 0 then Bplus else Bminus) p.2

/-- The outer product of the selected vector `muProd s` with its complex conjugate. -/
def muProj (s : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  vecMulVec (muProd s) (star (muProd s))

/-- The four matrices `muProj s` are positive semidefinite and sum to the identity. See
[SasakiCarlini2002]. -/
theorem four_output_product_vonNeumann_pom :
    (∀ s : Fin 2 × Fin 2, (muProj s).PosSemidef)
    ∧ ((∑ s : Fin 2 × Fin 2, muProj s) = 1) := by
  refine ⟨?_, ?_⟩
  · intro s
    rw [muProj]
    exact Matrix.posSemidef_iff_eq_sum_vecMulVec.mpr
      ⟨1, fun _ => muProd s, by simp⟩
  · ext p q
    fin_cases p <;> fin_cases q <;>
    simp [muProj, muProd, Aplus, Aminus, Bplus, Bminus, vecMulVec_apply, Matrix.sum_apply,
      Matrix.one_apply, Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_four]
    all_goals
      (have h2 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
         rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
         norm_num
       have h4 : ((Real.sqrt 2 : ℂ))^4 = 4 := by
         rw [show ((Real.sqrt 2:ℂ))^4
              = (((Real.sqrt 2:ℂ))*((Real.sqrt 2:ℂ)))*(((Real.sqrt 2:ℂ))*((Real.sqrt 2:ℂ))) by ring, h2]
         norm_num
       field_simp
       simp only [Complex.I_sq, h2, h4, mul_neg, one_mul, mul_one, neg_mul]
       ring_nf
       try simp
       try norm_num)

end Qatlib.Papers.QMatching02.MainResults.LearningStrategy

namespace Qatlib.Papers.QMatching02.MainResults.LearningStrategy

/-- The two-by-two matrix equal to one half of the identity. -/
def Cmat : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • 1

/-- The Kronecker product of two two-by-two complex matrices, indexed by pairs. -/
def kronApply (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of (fun p q => A p.1 q.1 * B p.2 q.2)

/-- The two-by-two matrix with zero diagonal and off-diagonal entries `-(s + i * c) / 2` and `(i
* c - s) / 2`. -/
def Dmat (s c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -(((s : ℂ) + Complex.I * (c : ℂ)) / 2);
     ((Complex.I * (c : ℂ) - (s : ℂ)) / 2), (0 : ℂ)]

/-- The two-template score matrix formed from `Cmat`, `Dmat s c`, and the real parameter `R`. -/
def Ghat (R s c : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • kronApply Cmat Cmat +
    ((R / 2 : ℝ) : ℂ) • (kronApply (Dmat s c) Cmat - kronApply Cmat (Dmat s c))

/-- The product vector whose component at `(i, j)` is `u i * v j`. -/
def prodVec2 (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => u p.1 * v p.2

/-- The component of `prodVec2 u v` at `p` is `u p.1 * v p.2`. -/
theorem prodVec2_apply (u v : Fin 2 → ℂ) (p : Fin 2 × Fin 2) :
    prodVec2 u v p = u p.1 * v p.2 := rfl

/-- The real number `√2 / 2` equals `1 / √2`. -/
theorem sqrt2_div_two : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith [h2]

/-- The product of the complex image of `√2` with itself is two. -/
theorem sqrt2c_sq : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The square of the inverse of the complex image of `√2` is one half. -/
theorem inv_sqrt2c_sq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = (1 / 2 : ℂ) := by
  rw [pow_two, ← mul_inv, sqrt2c_sq]
  norm_num

/-- The conjugate product vector has component `star (v p.2) * star (u p.1)`. -/
theorem star_prodVec2 (u v : Fin 2 → ℂ) :
    star (prodVec2 u v) = fun p => star (v p.2) * star (u p.1) := by
  funext p
  simp [prodVec2, star_mul]

/-- The complex image of `√2` divided by two equals its inverse. -/
theorem sqrt2c_div_two : ((Real.sqrt 2 : ℂ) / 2) = ((Real.sqrt 2 : ℂ))⁻¹ := by
  have h2 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := sqrt2c_sq
  have hne : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro h; rw [h] at h2; norm_num at h2
  field_simp
  rw [pow_two]
  exact h2

/-- The expectation of a Kronecker product on a product vector factors as the product of the two
local expectations. -/
theorem kronVec_expect (u v : Fin 2 → ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    star (prodVec2 u v) ⬝ᵥ (kronApply A B *ᵥ prodVec2 u v)
      = (star u ⬝ᵥ (A *ᵥ u)) * (star v ⬝ᵥ (B *ᵥ v)) := by
  have hu' : star u = fun i => star (u i) := rfl
  have hv' : star v = fun i => star (v i) := rfl
  simp only [star_prodVec2, hu', hv', prodVec2_apply, kronApply, Matrix.of_apply, dotProduct,
    mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The dot product distributes over addition in its second argument. -/
theorem dot_add {ι : Type*} [Fintype ι] (x y z : ι → ℂ) :
    x ⬝ᵥ (y + z) = x ⬝ᵥ y + x ⬝ᵥ z := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

/-- The dot product distributes over subtraction in its second argument. -/
theorem dot_sub {ι : Type*} [Fintype ι] (x y z : ι → ℂ) :
    x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := by
  simp [dotProduct, mul_sub, Finset.sum_sub_distrib]

/-- Scaling the second argument of the complex dot product scales its value by the same scalar. -/
theorem dot_smul {ι : Type*} [Fintype ι] (x y : ι → ℂ) (a : ℂ) :
    x ⬝ᵥ (a • y) = a * (x ⬝ᵥ y) := by
  simp [dotProduct, Finset.mul_sum, mul_left_comm]

/-- Multiplication by `Cmat` scales every two-component vector by one half. -/
theorem Cmat_mulVec (u : Fin 2 → ℂ) : Cmat *ᵥ u = (1 / 2 : ℂ) • u := by
  rw [Cmat, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- On normalized product vectors, the expectation of `Ghat` is one eighth plus `R / 4` times
the difference of the two `Dmat` expectations. See [SasakiCarlini2002]. -/
theorem Ghat_expect (R s c : ℝ) (u v : Fin 2 → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1) :
    star (prodVec2 u v) ⬝ᵥ (Ghat R s c *ᵥ prodVec2 u v)
      = (1 / 8 : ℂ) + ((R / 4 : ℝ) : ℂ) *
          ((star u ⬝ᵥ (Dmat s c *ᵥ u)) - (star v ⬝ᵥ (Dmat s c *ᵥ v))) := by
  have huC : star u ⬝ᵥ (Cmat *ᵥ u) = (1 / 2 : ℂ) := by
    rw [Cmat_mulVec, dot_smul, hu, mul_one]
  have hvC : star v ⬝ᵥ (Cmat *ᵥ v) = (1 / 2 : ℂ) := by
    rw [Cmat_mulVec, dot_smul, hv, mul_one]
  have hC : star (prodVec2 u v) ⬝ᵥ (kronApply Cmat Cmat *ᵥ prodVec2 u v) = (1 / 4 : ℂ) := by
    rw [kronVec_expect, huC, hvC]; norm_num
  have hD : star (prodVec2 u v) ⬝ᵥ (kronApply (Dmat s c) Cmat *ᵥ prodVec2 u v)
      = (star u ⬝ᵥ (Dmat s c *ᵥ u)) * (1 / 2 : ℂ) := by
    rw [kronVec_expect, hvC]
  have hD' : star (prodVec2 u v) ⬝ᵥ (kronApply Cmat (Dmat s c) *ᵥ prodVec2 u v)
      = (1 / 2 : ℂ) * (star v ⬝ᵥ (Dmat s c *ᵥ v)) := by
    rw [kronVec_expect, huC]
  rw [Ghat]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [dot_add, dot_smul, dot_smul, dot_sub, hC, hD, hD']
  push_cast
  ring

/-- The vector `Aplus` is fixed by complex conjugation. -/
theorem star_Aplus : star Aplus = Aplus := by
  funext i; fin_cases i <;> simp [Aplus]

/-- The vector `Aminus` is fixed by complex conjugation. -/
theorem star_Aminus : star Aminus = Aminus := by
  funext i; fin_cases i <;> simp [Aminus]

/-- The complex conjugate of `Bplus` is `Bminus`. -/
theorem star_Bplus : star Bplus = Bminus := by
  funext i; fin_cases i
  · simp [Bplus, Bminus]
  · simp [Bplus, Bminus]; ring

/-- The complex conjugate of `Bminus` is `Bplus`. -/
theorem star_Bminus : star Bminus = Bplus := by
  funext i; fin_cases i
  · simp [Bplus, Bminus]
  · simp [Bplus, Bminus]; ring

/-- The expectation of `Dmat s c` in `Aplus` is `-s / 2`. -/
theorem D_Aplus (s c : ℝ) : Aplus ⬝ᵥ (Dmat s c *ᵥ Aplus) = -((s : ℂ) / 2) := by
  simp [Aplus, Dmat, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq]
  ring

/-- The expectation of `Dmat s c` in `Aminus` is `s / 2`. -/
theorem D_Aminus (s c : ℝ) : Aminus ⬝ᵥ (Dmat s c *ᵥ Aminus) = (s : ℂ) / 2 := by
  simp [Aminus, Dmat, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq]
  ring

/-- The expectation of `Dmat s c` in `Bplus` is `c / 2`. -/
theorem D_Bplus (s c : ℝ) : Bminus ⬝ᵥ (Dmat s c *ᵥ Bplus) = (c : ℂ) / 2 := by
  simp [Bminus, Bplus, Dmat, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq, Complex.I_sq]
  ring

/-- The expectation of `Dmat s c` in `Bminus` is `-c / 2`. -/
theorem D_Bminus (s c : ℝ) : Bplus ⬝ᵥ (Dmat s c *ᵥ Bminus) = -((c : ℂ) / 2) := by
  simp [Bplus, Bminus, Dmat, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq, Complex.I_sq]
  ring

/-- The dot product of `Aplus` with itself is one. -/
theorem dot_Aplus : Aplus ⬝ᵥ Aplus = 1 := by
  simp [Aplus, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq]
  norm_num

/-- The dot product of `Aminus` with itself is one. -/
theorem dot_Aminus : Aminus ⬝ᵥ Aminus = 1 := by
  simp [Aminus, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq]
  norm_num

/-- The conjugated dot product of `Bplus` with itself is one. -/
theorem dot_Bplus : Bminus ⬝ᵥ Bplus = 1 := by
  simp [Bminus, Bplus, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq, Complex.I_sq]
  norm_num

/-- The conjugated dot product of `Bminus` with itself is one. -/
theorem dot_Bminus : Bplus ⬝ᵥ Bminus = 1 := by
  simp [Bplus, Bminus, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [inv_sqrt2c_sq, Complex.I_sq]
  norm_num

/-- The phase `-3 * π / 4` assigned to the first product outcome. -/
def Theta0 : ℝ := -(3 * Real.pi / 4)

/-- The phase `-π / 4` assigned to the second product outcome. -/
def Theta1 : ℝ := -(Real.pi / 4)

/-- The phase `3 * π / 4` assigned to the third product outcome. -/
def Theta2 : ℝ := 3 * Real.pi / 4

/-- The phase `π / 4` assigned to the fourth product outcome. -/
def Theta3 : ℝ := Real.pi / 4

/-- At `Theta0`, both sine and cosine are `-√2 / 2`. -/
theorem sin_cos_theta0 :
    Real.sin Theta0 = -(Real.sqrt 2 / 2) ∧ Real.cos Theta0 = -(Real.sqrt 2 / 2) := by
  have h : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  constructor
  · unfold Theta0
    rw [Real.sin_neg, h, Real.sin_pi_sub, Real.sin_pi_div_four]
  · unfold Theta0
    rw [Real.cos_neg, h, Real.cos_pi_sub, Real.cos_pi_div_four]

/-- At `Theta1`, sine is `-√2 / 2` and cosine is `√2 / 2`. -/
theorem sin_cos_theta1 :
    Real.sin Theta1 = -(Real.sqrt 2 / 2) ∧ Real.cos Theta1 = Real.sqrt 2 / 2 := by
  constructor
  · unfold Theta1
    rw [Real.sin_neg, Real.sin_pi_div_four]
  · unfold Theta1
    rw [Real.cos_neg, Real.cos_pi_div_four]

/-- At `Theta2`, sine is `√2 / 2` and cosine is `-√2 / 2`. -/
theorem sin_cos_theta2 :
    Real.sin Theta2 = Real.sqrt 2 / 2 ∧ Real.cos Theta2 = -(Real.sqrt 2 / 2) := by
  have h : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  constructor
  · unfold Theta2
    rw [h, Real.sin_pi_sub, Real.sin_pi_div_four]
  · unfold Theta2
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_four]

/-- At `Theta3`, both sine and cosine are `√2 / 2`. -/
theorem sin_cos_theta3 :
    Real.sin Theta3 = Real.sqrt 2 / 2 ∧ Real.cos Theta3 = Real.sqrt 2 / 2 := by
  constructor
  · unfold Theta3; rw [Real.sin_pi_div_four]
  · unfold Theta3; rw [Real.cos_pi_div_four]

/-- The score contribution of `Aplus ⊗ Bplus` at `Theta0` is `1 / 8 + (R / 4) * (√2 / 2)`. -/
theorem score_mu0 (R : ℝ) :
    star (prodVec2 Aplus Bplus) ⬝ᵥ (Ghat R (Real.sin Theta0) (Real.cos Theta0) *ᵥ
      prodVec2 Aplus Bplus) = (1 / 8 : ℂ) + ((R / 4 : ℝ) : ℂ) * (Real.sqrt 2 / 2 : ℂ) := by
  rw [Ghat_expect R _ _ _ _ (by rw [star_Aplus]; exact dot_Aplus)
      (by rw [star_Bplus]; exact dot_Bplus),
    star_Aplus, star_Bplus, D_Aplus, D_Bplus,
    sin_cos_theta0.1, sin_cos_theta0.2]
  push_cast
  ring

/-- The score contribution of `Aplus ⊗ Bminus` at `Theta1` is `1 / 8 + (R / 4) * (√2 / 2)`. -/
theorem score_mu1 (R : ℝ) :
    star (prodVec2 Aplus Bminus) ⬝ᵥ (Ghat R (Real.sin Theta1) (Real.cos Theta1) *ᵥ
      prodVec2 Aplus Bminus) = (1 / 8 : ℂ) + ((R / 4 : ℝ) : ℂ) * (Real.sqrt 2 / 2 : ℂ) := by
  rw [Ghat_expect R _ _ _ _ (by rw [star_Aplus]; exact dot_Aplus)
      (by rw [star_Bminus]; exact dot_Bminus),
    star_Aplus, star_Bminus, D_Aplus, D_Bminus,
    sin_cos_theta1.1, sin_cos_theta1.2]
  push_cast
  ring

/-- The score contribution of `Aminus ⊗ Bplus` at `Theta2` is `1 / 8 + (R / 4) * (√2 / 2)`. -/
theorem score_mu2 (R : ℝ) :
    star (prodVec2 Aminus Bplus) ⬝ᵥ (Ghat R (Real.sin Theta2) (Real.cos Theta2) *ᵥ
      prodVec2 Aminus Bplus) = (1 / 8 : ℂ) + ((R / 4 : ℝ) : ℂ) * (Real.sqrt 2 / 2 : ℂ) := by
  rw [Ghat_expect R _ _ _ _ (by rw [star_Aminus]; exact dot_Aminus)
      (by rw [star_Bplus]; exact dot_Bplus),
    star_Aminus, star_Bplus, D_Aminus, D_Bplus,
    sin_cos_theta2.1, sin_cos_theta2.2]
  push_cast
  ring

/-- The score contribution of `Aminus ⊗ Bminus` at `Theta3` is `1 / 8 + (R / 4) * (√2 / 2)`. -/
theorem score_mu3 (R : ℝ) :
    star (prodVec2 Aminus Bminus) ⬝ᵥ (Ghat R (Real.sin Theta3) (Real.cos Theta3) *ᵥ
      prodVec2 Aminus Bminus) = (1 / 8 : ℂ) + ((R / 4 : ℝ) : ℂ) * (Real.sqrt 2 / 2 : ℂ) := by
  rw [Ghat_expect R _ _ _ _ (by rw [star_Aminus]; exact dot_Aminus)
      (by rw [star_Bminus]; exact dot_Bminus),
    star_Aminus, star_Bminus, D_Aminus, D_Bminus,
    sin_cos_theta3.1, sin_cos_theta3.2]
  push_cast
  ring

/-- The sum of the four specified product-measurement score contributions is `1 / 2 + R / √2`.
See [SasakiCarlini2002]. -/
theorem four_output_product_pom_score (R : ℝ) :
    star (prodVec2 Aplus Bplus) ⬝ᵥ (Ghat R (Real.sin Theta0) (Real.cos Theta0) *ᵥ
        prodVec2 Aplus Bplus)
      + star (prodVec2 Aplus Bminus) ⬝ᵥ (Ghat R (Real.sin Theta1) (Real.cos Theta1) *ᵥ
          prodVec2 Aplus Bminus)
      + star (prodVec2 Aminus Bplus) ⬝ᵥ (Ghat R (Real.sin Theta2) (Real.cos Theta2) *ᵥ
          prodVec2 Aminus Bplus)
      + star (prodVec2 Aminus Bminus) ⬝ᵥ (Ghat R (Real.sin Theta3) (Real.cos Theta3) *ᵥ
          prodVec2 Aminus Bminus)
      = (1 / 2 : ℂ) + ((R : ℝ) : ℂ) / (Real.sqrt 2 : ℂ) := by
  rw [score_mu0, score_mu1, score_mu2, score_mu3, sqrt2c_div_two]
  push_cast
  field_simp
  ring

end Qatlib.Papers.QMatching02.MainResults.LearningStrategy
