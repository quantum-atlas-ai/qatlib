/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.CurveGroups.AffineAdd.CheckedBits
import Qatlib.Concepts.FiniteCounts.OffsetWord.MapChecked
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

open WeierstrassCurve.Affine
open Qatlib.Concepts.FiniteCounts.OffsetWord

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K] {w : ℕ} {a b : K}

def cyclicWord (P : (shortCurve a b).Point) (m : ℕ) (k l : List Bool) :
    List (Instruction (shortCurve a b).Point) :=
  (doubleWord (cyclicGenerator P) (m • cyclicGenerator P) k l).map
    (fun s => (s.1, (s.2 : (shortCurve a b).Point)))

def bitError (E : FieldEncoding K w) (P : (shortCurve a b).Point) (m : ℕ)
    (k l : List Bool) (a0 : AddSubgroup.zmultiples P) : Prop :=
  bitRun E (pointBits E (a0 : (shortCurve a b).Point)) (cyclicWord P m k l) ≠
    pointBits E ((a0 + binaryValue k • cyclicGenerator P +
      binaryValue l • (m • cyclicGenerator P) : AddSubgroup.zmultiples P) :
        (shortCurve a b).Point)

omit [Fintype K] in

theorem bitError_subset (E : FieldEncoding K w) (P : (shortCurve a b).Point) (m : ℕ)
    (k l : List Bool) :
    {a0 | bitError E P m k l a0} ⊆
      {a0 | checkedRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P) k l) = none} := by
  intro a0 herr
  cases hh : checkedRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P) k l) with
  | none => exact hh
  | some z =>
    have hmap := checkedRun_map_success (AddSubgroup.subtype (AddSubgroup.zmultiples P))
      Subtype.val_injective _ a0 z hh
    have hbit := bitRun_checked E _ (a0 : (shortCurve a b).Point)
      (z : (shortCurve a b).Point) hmap
    have hz := checked_doubleWord_correct (cyclicGenerator P) (m • cyclicGenerator P)
      a0 z k l hh
    apply False.elim
    apply herr
    change _ = _ at hbit
    simpa only [cyclicWord, hz] using! hbit

theorem cyclic_bit_error_le (E : FieldEncoding K w) (P : (shortCurve a b).Point)
    (m n : ℕ) (k l : Fin (n+1) → Bool)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    letI := cyclicFintype P
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h).toOuterMeasure
      {a0 | bitError E P m (List.ofFn k) (List.ofFn l) a0}).toReal ≤
      (8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ) := by
  letI := cyclicFintype P
  let p0 := PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h
  have hmono := p0.toOuterMeasure.mono (bitError_subset E P m (List.ofFn k) (List.ofFn l))
  have hfin : p0.toOuterMeasure
      {a0 | checkedRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P)
        (List.ofFn k) (List.ofFn l)) = none} ≠ ⊤ := by
    rw [p0.toOuterMeasure_apply]
    exact p0.tsum_coe_indicator_ne_top _
  exact (ENNReal.toReal_mono hfin hmono).trans (native_cyclic_failure P m n k l h)

end Qatlib.Concepts.CurveGroups.AffineAdd
