/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.HarmonicError.WeightedError

/-!
# Graph Pair Certificate

Harmonic Error constructions for Decision Risk.
Defines `pairedAxesCost`.
Proves `pairAverage_pos`, `pairWeight_axes`, `pairWeight_affine_identity`.
-/


set_option autoImplicit false
noncomputable section

namespace Qatlib.Foundations.DecisionRisk.HarmonicError

/-- A normalized qubit effect's two coordinates in a pair's orthogonal axes
give a positive average likelihood. -/
lemma pairAverage_pos {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) : 0 < 1+c*y := by
  have hy : -1 ≤ y ∧ y ≤ 1 := by
    constructor
    · nlinarith [sq_nonneg x, sq_nonneg (y+1)]
    · nlinarith [sq_nonneg x, sq_nonneg (y-1)]
  have hcy : -c ≤ c*y := by
    have h := mul_le_mul_of_nonneg_left hy.1 hc
    nlinarith only [h]
  linarith

/-- Exact harmonic mass, retaining both actual pair likelihoods. -/
lemma pairWeight_axes {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) :
    pairWeight (1+c*y+Real.sqrt (1-c^2)*x) (1+c*y-Real.sqrt (1-c^2)*x) =
      (1+c*y)/2-(1-c^2)*x^2/(2*(1+c*y)) := by
  have hA := pairAverage_pos hc hc1 hball
  have hs : (Real.sqrt (1-c^2))^2=1-c^2 :=
    Real.sq_sqrt (by nlinarith)
  unfold pairWeight
  have hsum : (1+c*y+Real.sqrt (1-c^2)*x)+(1+c*y-Real.sqrt (1-c^2)*x)=
      2*(1+c*y) := by ring
  rw [hsum]
  field_simp
  nlinarith only [hs]

/-- Exact affine-plus-positive remainder for an arbitrary pair of distinct
pure qubit inputs. The coordinates are effect Bloch coordinates; no error or
optimality inequality is assumed. -/
theorem pairWeight_affine_identity {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) :
    pairWeight (1+c*y+Real.sqrt (1-c^2)*x) (1+c*y-Real.sqrt (1-c^2)*x)
      -c^2/2-c*(2-c^2)*y/2 =
        (1-c^2)/(2*(1+c*y))*(1-x^2-c^2*y^2) := by
  rw [pairWeight_axes hc hc1 hball]
  have hA : 1+c*y ≠ 0 := ne_of_gt (pairAverage_pos hc hc1 hball)
  field_simp
  ring

/-- A uniform dual certificate. It can be summed over dominant-overlap edges
and integrated over arbitrary effect distributions; completeness cancels its
affine term. The graph/frame and physical-measurement consumers are separate
obligations, not hypotheses disguised as a final risk theorem. -/
theorem pairWeight_affine_lower {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) :
    c^2/2+c*(2-c^2)*y/2+(1-c)/2*(1-x^2-c^2*y^2) ≤
      pairWeight (1+c*y+Real.sqrt (1-c^2)*x) (1+c*y-Real.sqrt (1-c^2)*x) := by
  have hA := pairAverage_pos hc hc1 hball
  have hy : y ≤ 1 := by nlinarith [sq_nonneg x]
  have hAu : 1+c*y ≤ 1+c := by nlinarith
  have hc2 : c^2 ≤ 1 := by nlinarith
  have hrem : 0 ≤ 1-x^2-c^2*y^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg y)
    nlinarith
  have hcoeff : (1-c)/2 ≤ (1-c^2)/(2*(1+c*y)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(1+c*y))).2
    have h := mul_le_mul_of_nonneg_left hAu (by linarith : 0 ≤ 1-c)
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right hcoeff hrem
  have he := pairWeight_affine_identity hc hc1 hball
  linarith

/-- The same two opposite effect directions must serve two orthogonal binary
axes. Signs and axis swaps are shared data, not separately optimized oracles. -/
def pairedAxesCost (c x y : ℝ) : ℝ :=
  (pairWeight (1+c*y+Real.sqrt (1-c^2)*x) (1+c*y-Real.sqrt (1-c^2)*x) +
   pairWeight (1+c*(-y)+Real.sqrt (1-c^2)*(-x))
     (1+c*(-y)-Real.sqrt (1-c^2)*(-x)) +
   pairWeight (1+c*x+Real.sqrt (1-c^2)*y) (1+c*x-Real.sqrt (1-c^2)*y) +
   pairWeight (1+c*(-x)+Real.sqrt (1-c^2)*(-y))
     (1+c*(-x)-Real.sqrt (1-c^2)*(-y)))/2

/-- A scalar shared-measurement consumer of the dual certificate. Physical
Bloch-to-POVM and arbitrary graph consumers are not claimed by this lemma. -/
theorem pairedAxesCost_lower {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) :
    c^2+(1-c)/2*(1-c^2) ≤ pairedAxesCost c x y := by
  have h1 := pairWeight_affine_lower hc hc1 hball
  have h2 := pairWeight_affine_lower (x := -x) (y := -y) hc hc1 (by nlinarith)
  have h3 := pairWeight_affine_lower (x := y) (y := x) hc hc1 (by linarith)
  have h4 := pairWeight_affine_lower (x := -y) (y := -x) hc hc1 (by nlinarith)
  have hk : 0 ≤ (1-c)/2 := by linarith
  have hprod := mul_nonneg (mul_nonneg hk (by positivity : 0 ≤ 1+c^2))
    (by linarith : 0 ≤ 1-x^2-y^2)
  dsimp only [pairedAxesCost]
  nlinarith only [h1, h2, h3, h4, hprod]

/-- The stated finite risk construction satisfies `pairedAxesCost_strict` with all displayed hypotheses retained. -/
theorem pairedAxesCost_strict {c x y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hball : x^2+y^2 ≤ 1) : c^2 < pairedAxesCost c x y := by
  have h := pairedAxesCost_lower hc hc1 hball
  have hp : 0 < (1-c)/2*(1-c^2) := mul_pos (by linarith) (by nlinarith)
  linarith

end Qatlib.Foundations.DecisionRisk.HarmonicError
