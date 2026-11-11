/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorJetSyntax
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSpinFamily

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Source Syntax

Coded Floor constructions for Effective Gauge.
Defines `floorThetaExpr`, `floorRealExpr`, `floorJExpr`.
Proves `floorJetWord_append`, `floorJetOrderBound_word`, `floorSpinExpr_correct`.
-/

set_option autoImplicit false
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Theta Expr in the Coded Floor construction. -/
def floorThetaExpr : FloorJetExpr := .mul .parameter (.flat 0)
/-- Definition of floor Real Expr in the Coded Floor construction. -/
def floorRealExpr : FloorJetExpr := .cos floorThetaExpr
/-- Definition of floor JExpr in the Coded Floor construction. -/
def floorJExpr : FloorJetExpr := .mul (.sin floorThetaExpr) (.cos (.neg (.coordinate 1)))
/-- Definition of floor KExpr in the Coded Floor construction. -/
def floorKExpr : FloorJetExpr := .mul (.sin floorThetaExpr) (.sin (.neg (.coordinate 1)))

/-- Exact coordinates of star(q) I q, including the sign of the second coordinate. -/
def floorSpinExpr (j : Fin 3) : FloorJetExpr :=
  if j=0 then .add (.mul floorRealExpr floorRealExpr)
    (.neg (.add (.mul floorJExpr floorJExpr) (.mul floorKExpr floorKExpr)))
  else if j=1 then .mul (.integer (-2)) (.mul floorRealExpr floorKExpr)
  else .mul (.integer 2) (.mul floorRealExpr floorJExpr)

/-- Definition of floor Jet Order Bound in the Coded Floor construction. -/
def floorJetOrderBound : ℕ → FloorJetExpr → ℕ
  | 0,e => floorJetBound e
  | n+1,e => ∑ i : Fin 3, floorJetOrderBound n (floorJetDiff i e)

/-- Definition of floor Source Jet Bound in the Coded Floor construction. -/
def floorSourceJetBound (n : ℕ) : ℚ :=
  (∑ j : Fin 3, floorJetOrderBound n (floorSpinExpr j) : ℕ)

/-- Original `floorJetWord_append` guarantee for the `FloorSourceSyntax` construction; the complete source hypotheses are retained. -/
theorem floorJetWord_append (e : FloorJetExpr) (w w' : List (Fin 3)) :
    floorJetWord e (w++w')=floorJetWord (floorJetWord e w') w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append,floorJetWord,ih]

/-- Original `floorJetOrderBound_word` guarantee for the `FloorSourceSyntax` construction; the complete source hypotheses are retained. -/
theorem floorJetOrderBound_word (e : FloorJetExpr) (w : List (Fin 3)) :
    floorJetBound (floorJetWord e w) ≤ floorJetOrderBound w.length e := by
  induction w using List.reverseRecOn generalizing e with
  | nil => exact le_rfl
  | append_singleton w i ih =>
    simp only [floorJetWord_append,floorJetWord,List.length_append,List.length_singleton,floorJetOrderBound]
    exact (ih (floorJetDiff i e)).trans
      (Finset.single_le_sum (f := fun j : Fin 3 => floorJetOrderBound w.length (floorJetDiff j e))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

noncomputable section

/-- Original `floorSpinExpr_correct` guarantee for the `FloorSourceSyntax` construction; the complete source hypotheses are retained. -/
theorem floorSpinExpr_correct (a : ℝ) (X : SpatialPoint) (j : Fin 3) :
    floorJetEval a X (floorSpinExpr j)=floorRawSpin a X j := by
  fin_cases j <;>
    simp [floorSpinExpr,floorRealExpr,floorJExpr,floorKExpr,floorThetaExpr,
      floorJetEval,iteratedDeriv_zero,floorInteriorBump,floorRawSpin,quaternionSpinProjection,
      hopf,floorRawLift_mk,quaternionCoordinateCLM,iAxis] <;> ring

/-- Original `floorSourceJetExpr_correct` guarantee for the `FloorSourceSyntax` construction; the complete source hypotheses are retained. -/
theorem floorSourceJetExpr_correct (a : ℝ) (alpha : Fin 3 → ℕ) (X : SpatialPoint)
    (hX : InFundamentalCube X) (j : Fin 3) :
    floorJetEval a X (floorJetWord (floorSpinExpr j) (sourceCanonicalWord alpha))=
      sourceCanonicalJet (floorPeriodicSpin a) alpha X j := by
  have he : (fun Y => floorJetEval a Y (floorSpinExpr j))=
      (fun Y => (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ) (floorRawSpin a Y)) := by
    funext Y
    exact floorSpinExpr_correct a Y j
  rw [congrFun (floorJetWord_correct (floorSpinExpr j) a (sourceCanonicalWord alpha)) X,he,
    spatialWordPartial_clm _ _ (floorRawSpin_contDiff a)]
  change spatialWordPartial (floorRawSpin a) (sourceCanonicalWord alpha) X j=
    spatialWordPartial (floorPeriodicSpin a) (sourceCanonicalWord alpha) X j
  rw [floorPeriodicSpin_word_eq_raw a _ X hX]

/-- Original `floorSourceJetBound_correct` guarantee for the `FloorSourceSyntax` construction; the complete source hypotheses are retained. -/
theorem floorSourceJetBound_correct (a : ℝ) (ha : |a| ≤ 1) :
    OriginalPositiveJetBounds (floorPeriodicSpin a) floorSourceJetBound := by
  intro alpha _ X hX
  let z := sourceCanonicalJet (floorPeriodicSpin a) alpha X
  have hc (j : Fin 3) : |z j| ≤
      (floorJetOrderBound (∑ i : Fin 3, alpha i) (floorSpinExpr j) : ℝ) := by
    rw [← floorSourceJetExpr_correct a alpha X hX j]
    exact (floorJetBound_correct _ a ha X hX).trans
      (by exact_mod_cast (sourceCanonicalWord_length alpha ▸
        floorJetOrderBound_word (floorSpinExpr j) (sourceCanonicalWord alpha)))
  have hz : z=∑ j : Fin 3, EuclideanSpace.single j (z j) := by
    ext j
    simp
  calc
    ‖z‖ = ‖∑ j : Fin 3, EuclideanSpace.single j (z j)‖ := congrArg norm hz
    _ ≤ ∑ j : Fin 3, ‖EuclideanSpace.single j (z j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, |z j| := by simp [PiLp.norm_single,Real.norm_eq_abs]
    _ ≤ ∑ j : Fin 3, (floorJetOrderBound (∑ i : Fin 3, alpha i) (floorSpinExpr j) : ℝ) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = (floorSourceJetBound (∑ i : Fin 3, alpha i) : ℝ) := by
      simp [floorSourceJetBound]

end
end Qatlib.Concepts.EffectiveGauge.CodedFloor
