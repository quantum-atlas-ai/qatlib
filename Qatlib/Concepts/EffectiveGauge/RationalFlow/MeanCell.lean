/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite overlapping-cell selection for a certified reference mean

The program compares rational interval endpoints only. It never evaluates
the floor of an unknown real mean. Its two candidates are exactly the
shifts used by the source-sector producer, in their prescribed order.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- A rational cell shift, an applied integer phase, and its certified margin. -/
structure MeanCellSelection where
  shift : ℚ
  winding : ℤ
  margin : ℚ
  deriving DecidableEq, Repr

/-- One finite candidate computed from the midpoint and radius of a mean interval. -/
def meanCellCandidate (a e d : ℚ) : MeanCellSelection :=
  let k := Int.floor (a-d)
  ⟨d, -k, min (a-e-d-k) (d+k+1-a-e)⟩

/-- Prefer shift zero; otherwise use the overlapping half-shift. -/
def selectMeanCell (a e : ℚ) : MeanCellSelection :=
  let first := meanCellCandidate a e 0
  if 1/8 < first.margin then first else meanCellCandidate a e (-1/2)

/-- If the first rational test fails, the half-shift has a strict margin.
This proves totality without equality tests on a computable real name. -/
theorem halfShift_margin (a e : ℚ) (he : e ≤ 1/32)
    (hfirst : ¬ 1/8 < (meanCellCandidate a e 0).margin) :
    1/8 < (meanCellCandidate a e (-1/2)).margin := by
  have hlo := Int.floor_le a
  have hhi := Int.lt_floor_add_one a
  have hbad : min (a-e-(Int.floor a : ℚ)) ((Int.floor a : ℚ)+1-a-e) ≤ 1/8 := by
    simpa [meanCellCandidate] using le_of_not_gt hfirst
  rcases min_le_iff.mp hbad with hleft | hright
  · have hfloor : Int.floor (a-(-1/2 : ℚ))=Int.floor a := by
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith
    simp only [meanCellCandidate, hfloor]
    apply lt_min <;> linarith
  · have hfloor : Int.floor (a-(-1/2 : ℚ))=Int.floor a+1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    simp only [meanCellCandidate, hfloor, Int.cast_add, Int.cast_one]
    apply lt_min <;> linarith

/-- Both the chosen shift and its positive margin are properties of the actual output. -/
theorem selectMeanCell_margin (a e : ℚ) (he : e ≤ 1/32) :
    ((selectMeanCell a e).shift=0 ∨ (selectMeanCell a e).shift=-1/2) ∧
      1/8 < (selectMeanCell a e).margin := by
  dsimp only [selectMeanCell]
  split_ifs with h
  · exact ⟨Or.inl rfl,h⟩
  · exact ⟨Or.inr rfl,halfShift_margin a e he h⟩

/-- A candidate encloses every real mean represented by the same rational interval. -/
theorem meanCellCandidate_encloses (a e d : ℚ) (m : ℝ) (hm : |m-(a : ℝ)| ≤ (e : ℝ)) :
    ((meanCellCandidate a e d).shift : ℝ)+(meanCellCandidate a e d).margin ≤
        m+((meanCellCandidate a e d).winding : ℝ) ∧
      m+((meanCellCandidate a e d).winding : ℝ) ≤
        ((meanCellCandidate a e d).shift : ℝ)+1-(meanCellCandidate a e d).margin := by
  have hlow : (min (a-e-d-(Int.floor (a-d) : ℚ)) (d+(Int.floor (a-d) : ℚ)+1-a-e) : ℚ) ≤
      a-e-d-(Int.floor (a-d) : ℚ) := min_le_left _ _
  have hhigh : (min (a-e-d-(Int.floor (a-d) : ℚ)) (d+(Int.floor (a-d) : ℚ)+1-a-e) : ℚ) ≤
      d+(Int.floor (a-d) : ℚ)+1-a-e := min_le_right _ _
  have hl := (Rat.cast_le (K := ℝ)).mpr hlow
  have hh := (Rat.cast_le (K := ℝ)).mpr hhigh
  push_cast at hl hh
  have habs := abs_le.mp hm
  dsimp only [meanCellCandidate]
  push_cast
  constructor <;> linarith

/-- The selected applied winding places the true mean in a width-three-quarter
open cell. The program takes no unknown real mean or target precision as input. -/
theorem selectMeanCell_correct (a e : ℚ) (he : e ≤ 1/32)
    (m : ℝ) (hm : |m-(a : ℝ)| ≤ (e : ℝ)) :
    ((selectMeanCell a e).shift : ℝ)+1/8 < m+((selectMeanCell a e).winding : ℝ) ∧
      m+((selectMeanCell a e).winding : ℝ) < ((selectMeanCell a e).shift : ℝ)+7/8 := by
  have hmargin : (1/8 : ℝ) < ((selectMeanCell a e).margin : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (selectMeanCell_margin a e he).2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h
  have hc :
      ((selectMeanCell a e).shift : ℝ)+(selectMeanCell a e).margin ≤
          m+((selectMeanCell a e).winding : ℝ) ∧
        m+((selectMeanCell a e).winding : ℝ) ≤
          ((selectMeanCell a e).shift : ℝ)+1-(selectMeanCell a e).margin := by
    dsimp only [selectMeanCell]
    split_ifs <;> exact meanCellCandidate_encloses a e _ m hm
  constructor <;> linarith [hc.1,hc.2]

/-- At most one applied integer winding can place a real mean in the fixed output cell. -/
theorem meanCell_winding_unique (d m : ℝ) (n k : ℤ)
    (hn : d+1/8 < m+(n : ℝ) ∧ m+(n : ℝ) < d+7/8)
    (hk : d+1/8 < m+(k : ℝ) ∧ m+(k : ℝ) < d+7/8) : n=k := by
  have hl : (-1 : ℝ) < ((n-k : ℤ) : ℝ) := by push_cast; linarith [hn.1,hk.2]
  have hh : ((n-k : ℤ) : ℝ) < (1 : ℝ) := by push_cast; linarith [hn.2,hk.1]
  have hi : (-1 : ℤ) < n-k := by exact_mod_cast hl
  have hj : n-k < (1 : ℤ) := by exact_mod_cast hh
  omega

/-- The actual three-coordinate sector program; one preprocessing interval
per coordinate is fixed before any approximation precision is supplied. -/
def selectMeanSector (a e : Fin 3 → ℚ) : Fin 3 → MeanCellSelection :=
  fun j => selectMeanCell (a j) (e j)

/-- Literal three-coordinate soundness and uniqueness for the finite selector. -/
theorem selectMeanSector_correct (a e : Fin 3 → ℚ) (he : ∀ j, e j ≤ 1/32)
    (m : Fin 3 → ℝ) (hm : ∀ j, |m j-(a j : ℝ)| ≤ (e j : ℝ)) :
    (∀ j, ((selectMeanSector a e j).shift : ℝ)+1/8 < m j+((selectMeanSector a e j).winding : ℝ) ∧
      m j+((selectMeanSector a e j).winding : ℝ) < ((selectMeanSector a e j).shift : ℝ)+7/8) ∧
    ∀ n : Fin 3 → ℤ,
      (∀ j, ((selectMeanSector a e j).shift : ℝ)+1/8 < m j+(n j : ℝ) ∧
        m j+(n j : ℝ) < ((selectMeanSector a e j).shift : ℝ)+7/8) →
      n=fun j => (selectMeanSector a e j).winding := by
  have hc (j : Fin 3) := selectMeanCell_correct (a j) (e j) (he j) (m j) (hm j)
  refine ⟨hc,?_⟩
  intro n hn
  funext j
  exact meanCell_winding_unique _ _ _ _ (hn j) (hc j)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
