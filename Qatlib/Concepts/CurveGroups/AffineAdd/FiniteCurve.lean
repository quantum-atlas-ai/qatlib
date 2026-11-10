/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.CurveGroups.AffineAdd.NativeXor
import Qatlib.Concepts.FiniteCounts.OffsetWord.BinaryWord
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

open WeierstrassCurve.Affine
open Qatlib.Concepts.FiniteCounts.OffsetWord

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable abbrev curveFintype (a b : K) : Fintype (shortCurve a b).Point := by
  classical
  exact Fintype.ofEquiv (Option {xy : K × K // (shortCurve a b).Nonsingular xy.1 xy.2})
    (nonsingularPointEquiv _).symm

noncomputable abbrev cyclicFintype {a b : K} (P : (shortCurve a b).Point) :
    Fintype (AddSubgroup.zmultiples P) := by
  letI := curveFintype a b
  exact Fintype.ofFinite _

def cyclicGenerator {a b : K} (P : (shortCurve a b).Point) : AddSubgroup.zmultiples P :=
  ⟨P, AddSubgroup.mem_zmultiples P⟩

omit [Fintype K] in

theorem native_double_scalar {a b : K} (P : (shortCurve a b).Point) (m : ℕ)
    (a0 : AddSubgroup.zmultiples P) (k l : List Bool) :
    ((idealRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P) k l) :
      AddSubgroup.zmultiples P) : (shortCurve a b).Point) =
      (a0 : (shortCurve a b).Point) + binaryValue k • P + binaryValue l • (m • P) := by
  rw [doubleWord_correct]
  rfl

theorem native_cyclic_failure {a b : K} (P : (shortCurve a b).Point) (m n : ℕ)
    (k l : Fin (n+1) → Bool)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    letI := cyclicFintype P
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h).toOuterMeasure
      {a0 | checkedRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P)
        (List.ofFn k) (List.ofFn l)) = none}).toReal ≤
      (8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ) := by
  letI := cyclicFintype P
  exact source_width_failure_le (cyclicGenerator P) (m • cyclicGenerator P) n k l h

end Qatlib.Concepts.CurveGroups.AffineAdd
