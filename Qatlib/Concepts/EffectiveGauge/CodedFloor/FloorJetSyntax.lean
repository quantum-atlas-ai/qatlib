/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorBumpFamily
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Jet Syntax

Coded Floor constructions for Effective Gauge.
Defines `FloorJetExpr`, `floorJetEval`, `floorBumpDerivativeExpr`.
Proves `contDiff_iterated_flat`, `contDiff_floorBumpArgument`, `contDiff_floorJetEval`.
-/

set_option autoImplicit false
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Finite syntax closed under every spatial derivative needed by the floor family.
The flat atom denotes an actual derivative of the fixed smooth radial bump. -/
inductive FloorJetExpr where
  | integer (z : ℤ)
  | coordinate (i : Fin 3)
  | parameter
  | flat (n : ℕ)
  | add (f g : FloorJetExpr)
  | neg (f : FloorJetExpr)
  | mul (f g : FloorJetExpr)
  | sin (f : FloorJetExpr)
  | cos (f : FloorJetExpr)
  deriving DecidableEq

/-- Definition of floor Jet Eval in the Coded Floor construction. -/
noncomputable def floorJetEval (a : ℝ) (X : SpatialPoint) : FloorJetExpr → ℝ
  | .integer z => z
  | .coordinate i => X i
  | .parameter => a
  | .flat n => iteratedDeriv n expNegInvGlue (floorBumpArgument X)
  | .add f g => floorJetEval a X f+floorJetEval a X g
  | .neg f => -floorJetEval a X f
  | .mul f g => floorJetEval a X f*floorJetEval a X g
  | .sin f => Real.sin (floorJetEval a X f)
  | .cos f => Real.cos (floorJetEval a X f)

/-- Definition of floor Bump Derivative Expr in the Coded Floor construction. -/
def floorBumpDerivativeExpr (i : Fin 3) : FloorJetExpr :=
  .mul (.integer (-2)) (.add (.coordinate i) (.integer (-3)))

/-- Definition of floor Jet Diff in the Coded Floor construction. -/
def floorJetDiff (i : Fin 3) : FloorJetExpr → FloorJetExpr
  | .integer _ => .integer 0
  | .coordinate j => .integer (if i=j then 1 else 0)
  | .parameter => .integer 0
  | .flat n => .mul (.flat (n+1)) (floorBumpDerivativeExpr i)
  | .add f g => .add (floorJetDiff i f) (floorJetDiff i g)
  | .neg f => .neg (floorJetDiff i f)
  | .mul f g => .add (.mul (floorJetDiff i f) g) (.mul f (floorJetDiff i g))
  | .sin f => .mul (.cos f) (floorJetDiff i f)
  | .cos f => .neg (.mul (.sin f) (floorJetDiff i f))

/-- Definition of floor Jet Word in the Coded Floor construction. -/
def floorJetWord (e : FloorJetExpr) : List (Fin 3) → FloorJetExpr
  | [] => e
  | i::w => floorJetDiff i (floorJetWord e w)

/-- An integer bound computed solely from finite syntax and the proved cutoff budgets. -/
def floorJetBound : FloorJetExpr → ℕ
  | .integer z => z.natAbs
  | .coordinate _ => 7
  | .parameter => 1
  | .flat n => cutoffBumpMajorant n
  | .add f g => floorJetBound f+floorJetBound g
  | .neg f => floorJetBound f
  | .mul f g => floorJetBound f*floorJetBound g
  | .sin _ => 1
  | .cos _ => 1

noncomputable section

/-- Original `contDiff_iterated_flat` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem contDiff_iterated_flat (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n expNegInvGlue) := by
  induction n with
  | zero => exact expNegInvGlue.contDiff
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

/-- Original `contDiff_floorBumpArgument` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem contDiff_floorBumpArgument : ContDiff ℝ ∞ floorBumpArgument :=
  contDiff_const.sub (ContDiff.sum (s := Finset.univ) (fun i _ =>
    ((EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).contDiff.sub contDiff_const).pow 2))

/-- Original `contDiff_floorJetEval` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem contDiff_floorJetEval (e : FloorJetExpr) (a : ℝ) :
    ContDiff ℝ ∞ (fun X => floorJetEval a X e) := by
  induction e with
  | integer z => exact contDiff_const
  | coordinate i => exact (EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).contDiff
  | parameter => exact contDiff_const
  | flat n => exact (contDiff_iterated_flat n).comp contDiff_floorBumpArgument
  | add f g hf hg => exact hf.add hg
  | neg f hf => exact hf.neg
  | mul f g hf hg => exact hf.mul hg
  | sin f hf => exact hf.sin
  | cos f hf => exact hf.cos

/-- Original `floorBumpArgument_fderiv` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem floorBumpArgument_fderiv (X : SpatialPoint) (i : Fin 3) :
    fderiv ℝ floorBumpArgument X (EuclideanSpace.single i 1)= -2*(X i-3) := by
  let p := fun j : Fin 3 => (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ)
  have hd := (hasFDerivAt_const (1 : ℝ) X).sub
    ((((p 0).hasFDerivAt.sub_const 3).pow 2).add
      (((p 1).hasFDerivAt.sub_const 3).pow 2) |>.add
      (((p 2).hasFDerivAt.sub_const 3).pow 2))
  have he : floorBumpArgument=(fun Y : SpatialPoint =>
      1-(((Y 0-3)^2+(Y 1-3)^2)+(Y 2-3)^2)) := by
    funext Y
    simp [floorBumpArgument,Fin.sum_univ_succ]
    ring
  change HasFDerivAt (fun Y : SpatialPoint => 1-(((Y 0-3)^2+(Y 1-3)^2)+(Y 2-3)^2)) _ X at hd
  rw [he,hd.fderiv]
  fin_cases i <;> simp [p]

/-- Original `floorJetDiff_correct` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem floorJetDiff_correct (e : FloorJetExpr) (a : ℝ) (X : SpatialPoint) (i : Fin 3) :
    floorJetEval a X (floorJetDiff i e)=
      fderiv ℝ (fun Y => floorJetEval a Y e) X (EuclideanSpace.single i 1) := by
  induction e with
  | integer z => simp [floorJetDiff,floorJetEval]
  | coordinate j =>
    simp only [floorJetDiff,floorJetEval]
    have hd : HasFDerivAt (fun Y : SpatialPoint => Y j)
        (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ) X :=
      (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).hasFDerivAt
    rw [hd.fderiv]
    fin_cases i <;> fin_cases j <;> norm_num
  | parameter => simp [floorJetDiff,floorJetEval]
  | flat n =>
    have hd := ((contDiff_iterated_flat n).differentiable (by simp)
      (floorBumpArgument X)).hasDerivAt.hasFDerivAt.comp X
      ((contDiff_floorBumpArgument.differentiable (by simp) X).hasFDerivAt)
    change HasFDerivAt (fun Y => floorJetEval a Y (.flat n)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,floorBumpDerivativeExpr,
      ← iteratedDeriv_succ,floorBumpArgument_fderiv]
    ring
  | add f g hf hg =>
    have hd := ((contDiff_floorJetEval f a).differentiable (by simp) X).hasFDerivAt.add
      (((contDiff_floorJetEval g a).differentiable (by simp) X).hasFDerivAt)
    change HasFDerivAt (fun Y => floorJetEval a Y (.add f g)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,hf,hg]
  | neg f hf =>
    have hd := ((contDiff_floorJetEval f a).differentiable (by simp) X).hasFDerivAt.neg
    change HasFDerivAt (fun Y => floorJetEval a Y (.neg f)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,hf]
  | mul f g hf hg =>
    have hd := ((contDiff_floorJetEval f a).differentiable (by simp) X).hasFDerivAt.mul
      (((contDiff_floorJetEval g a).differentiable (by simp) X).hasFDerivAt)
    change HasFDerivAt (fun Y => floorJetEval a Y (.mul f g)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,hf,hg,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  | sin f hf =>
    have hd := ((contDiff_floorJetEval f a).differentiable (by simp) X).hasFDerivAt.sin
    change HasFDerivAt (fun Y => floorJetEval a Y (.sin f)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,hf,ContinuousLinearMap.smul_apply,smul_eq_mul]
  | cos f hf =>
    have hd := ((contDiff_floorJetEval f a).differentiable (by simp) X).hasFDerivAt.cos
    change HasFDerivAt (fun Y => floorJetEval a Y (.cos f)) _ X at hd
    rw [hd.fderiv]
    simp [floorJetDiff,floorJetEval,hf,ContinuousLinearMap.smul_apply,smul_eq_mul]

/-- Original `floorJetWord_correct` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem floorJetWord_correct (e : FloorJetExpr) (a : ℝ) (w : List (Fin 3)) :
    (fun X => floorJetEval a X (floorJetWord e w))=
      spatialWordPartial (fun X => floorJetEval a X e) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext X
    simp only [floorJetWord,spatialWordPartial,floorJetDiff_correct,ih]

/-- Original `floorJetBound_correct` guarantee for the `FloorJetSyntax` construction; the complete source hypotheses are retained. -/
theorem floorJetBound_correct (e : FloorJetExpr) (a : ℝ) (ha : |a| ≤ 1)
    (X : SpatialPoint) (hX : InFundamentalCube X) :
    |floorJetEval a X e| ≤ (floorJetBound e : ℝ) := by
  induction e with
  | integer z => simp [floorJetEval,floorJetBound]
  | coordinate i =>
    simp only [floorJetEval,floorJetBound,Nat.cast_ofNat,abs_of_nonneg (hX i).1]
    have hp : physicalPeriod ≤ 7 := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
    exact ((hX i).2.trans hp)
  | parameter => simpa [floorJetEval,floorJetBound] using ha
  | flat n => exact iteratedDeriv_expNegInvGlue_abs_le n _
  | add f g hf hg => exact (abs_add_le _ _).trans (by simpa [floorJetBound] using add_le_add hf hg)
  | neg f hf => simpa [floorJetEval,floorJetBound] using hf
  | mul f g hf hg =>
    simpa [floorJetEval,floorJetBound,abs_mul] using mul_le_mul hf hg (abs_nonneg _) (by positivity)
  | sin f _ => simpa [floorJetEval,floorJetBound] using Real.abs_sin_le_one (floorJetEval a X f)
  | cos f _ => simpa [floorJetEval,floorJetBound] using Real.abs_cos_le_one (floorJetEval a X f)

end
end Qatlib.Concepts.EffectiveGauge.CodedFloor
