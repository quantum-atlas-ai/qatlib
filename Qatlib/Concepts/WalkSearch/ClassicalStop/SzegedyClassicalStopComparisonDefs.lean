/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayStat
set_option warningAsError false

open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

noncomputable def absorbingKernel {I : Type} [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (i j : I) : ℝ :=
  if i ∈ S then (if j = i then 1 else 0) else P i j

noncomputable def stepAbsorbingLaw {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (law : I → ℝ) : I → ℝ :=
  fun j => ∑ i, law i * absorbingKernel P S i j

noncomputable def absorbingLaw {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I) (K : ℕ) :
    I → ℝ :=
  (stepAbsorbingLaw P S)^[K] (fun _ => 1/(Fintype.card I : ℝ))

noncomputable def classicalDetectSuccess {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (K : ℕ) : ℝ :=
  1 - ∑ i : {x : I // x ∉ S}, absorbingLaw P S K i
end Qatlib.Concepts.WalkSearch.ClassicalStop
