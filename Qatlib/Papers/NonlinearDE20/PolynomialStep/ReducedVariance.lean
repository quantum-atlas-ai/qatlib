/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame
import Qatlib.Papers.NonlinearDE20.AffineLift.AffinePostselect
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

def cross {J : Type} (v w : J→ℂ) : Matrix J J ℂ := Matrix.vecMulVec v (star w)

def outer {J : Type} (v : J→ℂ) : Matrix J J ℂ := cross v v

theorem capture_inflate {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (x : I→ℂ) :
    capture q (inflate q x)=x := by
  rw [← environmentFrame_action,← environmentFrame_adjoint_action,Matrix.mulVec_mulVec,
    environmentFrame_isometry q hq,Matrix.one_mulVec]

theorem capture_sub {I E : Type} [Fintype E] (q : E→ℂ) (v w : I×E→ℂ) :
    capture q (v-w)=capture q v-capture q w := by
  funext i
  simp [capture,mul_sub,Finset.sum_sub_distrib]

theorem reducedCross_left {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) (x : I→ℂ) :
    (cross v (inflate q x)).traceRight=cross (capture q v) x := by
  ext i j
  change (∑ a : E,v (i,a)*star (x j*q a))=(∑ a : E,star (q a)*v (i,a))*star (x j)
  simp only [star_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem reducedCross_right {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) (x : I→ℂ) :
    (cross (inflate q x) v).traceRight=cross x (capture q v) := by
  ext i j
  change (∑ a : E,(x i*q a)*star (v (j,a)))=x i*star (∑ a : E,star (q a)*v (j,a))
  simp only [star_sum,star_mul,star_star]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem reducedOuter_product {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (x : I→ℂ) :
    (outer (inflate q x)).traceRight=outer x := by
  exact (reducedCross_left q (inflate q x) x).trans
      (congrArg (fun z=>cross z x) (capture_inflate q hq x))

theorem outer_sub {J : Type} (v w : J→ℂ) :
    outer (v-w)=outer v-cross v w-cross w v+outer w := by
  ext i j
  simp only [outer,cross,Matrix.vecMulVec,Pi.star_apply,Pi.sub_apply,star_sub,
    Matrix.add_apply,Matrix.sub_apply,Matrix.of_apply]
  ring

def entanglingResidual {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) : I×E→ℂ :=
  v-inflate q (capture q v)

def reducedVariance {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) : Matrix I I ℂ :=
  (outer v).traceRight-outer (capture q v)

theorem reducedVariance_residual {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (v : I×E→ℂ) :
    reducedVariance q v=(outer (entanglingResidual q v)).traceRight := by
  rw [entanglingResidual,outer_sub,Matrix.traceRight_add,Matrix.traceRight_sub,Matrix.traceRight_sub,
    reducedCross_left,reducedCross_right,reducedOuter_product q hq]
  change (outer v).traceRight-outer (capture q v)=
    (outer v).traceRight-outer (capture q v)-outer (capture q v)+outer (capture q v)
  abel

theorem reducedVariance_psd {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (v : I×E→ℂ) :
    (reducedVariance q v).PosSemidef := by
  rw [reducedVariance_residual q hq]
  exact (Matrix.posSemidef_vecMulVec_self_star (entanglingResidual q v)).traceRight

theorem reducedVariance_traceNorm {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) (v : I×E→ℂ) :
    (reducedVariance q v).traceNorm=∑ p : I×E,Complex.normSq (entanglingResidual q v p) := by
  have hh := (reducedVariance_psd q hq v).traceNorm_eq_trace
  have hr := congrArg Complex.re hh
  rw [reducedVariance_residual q hq,Matrix.traceRight_trace] at hr
  rw [reducedVariance_residual q hq]
  simpa [outer,cross,Matrix.trace,Matrix.vecMulVec,Complex.mul_conj] using hr

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
