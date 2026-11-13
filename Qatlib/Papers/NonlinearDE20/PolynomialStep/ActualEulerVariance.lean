/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.ReducedVariance

/-!
# Exact variance of a reduced Euler step

This module compares `actualEulerReduced`, obtained from a joint Euler update, with the pure
target `idealEulerVector`. For a normalized environment, their difference is exactly a quadratic
multiple of `reducedVariance`; this yields positivity and an exact residual trace-norm formula
for the single-step analysis of [LloydEtAl2020].

## Main statements

* `actualEuler_variance`: For normalized `q`, the actual reduced Euler output minus its ideal
  outer product is `c * star c` times the interaction reduced variance.
* `actualEuler_difference_psd`: For normalized `q`, the actual reduced Euler output minus the
  ideal outer product is positive semidefinite.
* `actualEuler_traceNorm`: For normalized `q`, the reduced Euler discrepancy has trace norm
  equal to `Complex.normSq c` times the squared norm of the entangling residual.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

/-- Expand the outer product of `v - c • w` into its two diagonal and two cross terms. -/
theorem outer_euler {J : Type} (v w : J→ℂ) (c : ℂ) :
    outer (v-c •w)=outer v-c •cross w v-star c •cross v w+(c*star c) •outer w := by
  ext i j
  simp only [outer,cross,Matrix.vecMulVec,Matrix.of_apply,Pi.star_apply,Pi.sub_apply,Pi.smul_apply,
    star_sub,star_mul,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- For normalized `q`, the reduced joint update differs from its captured pure update by `c *
star c` times the reduced variance. -/
theorem productEuler_variance {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (z : I→ℂ) (v : I×E→ℂ) (c : ℂ) :
    (outer (inflate q z-c •v)).traceRight-outer (z-c •capture q v)=
      (c*star c) •reducedVariance q v := by
  rw [outer_euler,Matrix.traceRight_add,Matrix.traceRight_sub,Matrix.traceRight_sub,
    Matrix.traceRight_smul,Matrix.traceRight_smul,Matrix.traceRight_smul,
    reducedOuter_product q hq,reducedCross_left,reducedCross_right,outer_euler,
    reducedVariance,smul_sub]
  abel

/-- The partial trace of the joint outer product after applying the Euler operator `1 - c • F`
to the inflated input. -/
def actualEulerReduced {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) (c : ℂ) : Matrix I I ℂ :=
  (outer ((1-c •F)*ᵥ inflate q x)).traceRight

/-- The system Euler vector obtained using the compression of `F` against the environment vector
`q`. -/
def idealEulerVector {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) (c : ℂ) : I→ℂ :=
  x-c •(compression F q*ᵥ x)

/-- For normalized `q`, the actual reduced Euler output minus its ideal outer product is `c *
star c` times the interaction reduced variance [LloydEtAl2020]. -/
theorem actualEuler_variance {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1)
    (x : I→ℂ) (c : ℂ) :
    actualEulerReduced F q x c-outer (idealEulerVector F q x c)=
      (c*star c) •reducedVariance q (F*ᵥ inflate q x) := by
  rw [actualEulerReduced,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,outer_euler,
    Matrix.traceRight_add,Matrix.traceRight_sub,Matrix.traceRight_sub,
    Matrix.traceRight_smul,Matrix.traceRight_smul,Matrix.traceRight_smul,
    reducedOuter_product q hq,reducedCross_left,reducedCross_right]
  rw [idealEulerVector,compression_action,outer_euler,reducedVariance,smul_sub]
  abel

/-- The actual reduced Euler output is positive semidefinite. -/
theorem actualEulerReduced_psd {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) (c : ℂ) :
    (actualEulerReduced F q x c).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star ((1-c •F)*ᵥ inflate q x)).traceRight

/-- For normalized `q`, the actual reduced Euler output minus the ideal outer product is
positive semidefinite. -/
theorem actualEuler_difference_psd {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1)
    (x : I→ℂ) (c : ℂ) :
    (actualEulerReduced F q x c-outer (idealEulerVector F q x c)).PosSemidef := by
  have hc : c*star c=(Complex.normSq c:ℂ) := Complex.mul_conj c
  rw [actualEuler_variance F q hq x c,hc]
  exact (reducedVariance_psd q hq _).smul (RCLike.ofReal_nonneg.mpr (Complex.normSq_nonneg c))

/-- For normalized `q`, the reduced Euler discrepancy has trace norm equal to `Complex.normSq c`
times the squared norm of the entangling residual. -/
theorem actualEuler_traceNorm {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1)
    (x : I→ℂ) (c : ℂ) :
    (actualEulerReduced F q x c-outer (idealEulerVector F q x c)).traceNorm=
      Complex.normSq c*∑ p : I×E,Complex.normSq (entanglingResidual q (F*ᵥ inflate q x) p) := by
  rw [actualEuler_variance F q hq x c,Matrix.traceNorm_smul,reducedVariance_traceNorm q hq,
    norm_mul,norm_star,← pow_two,Complex.sq_norm]

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
