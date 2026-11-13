/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayStat

/-!
# Classical absorbing detection definitions

`absorbingKernel` makes each marked state absorbing and otherwise follows the original kernel.
`absorbingLaw` iterates this kernel from the uniform law, and `classicalDetectSuccess` measures
one minus the remaining unmarked mass. See [Szegedy2004] for the mathematical background.

## Main statements

* `absorbingLaw`: the uniformly initialized absorbing evolution.
* `classicalDetectSuccess`: the detection success expression.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

/-- The kernel that stays at a marked state and otherwise uses the transition entries of `P`. -/
noncomputable def absorbingKernel {I : Type} [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (i j : I) : ℝ :=
  if i ∈ S then (if j = i then 1 else 0) else P i j

/-- One step of law evolution under `absorbingKernel P S`, with incoming mass summed over the
starting state. -/
noncomputable def stepAbsorbingLaw {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (law : I → ℝ) : I → ℝ :=
  fun j => ∑ i, law i * absorbingKernel P S i j

/-- The real-valued law obtained after `K` absorbing-kernel steps from the uniform initial law. -/
noncomputable def absorbingLaw {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I) (K : ℕ) :
    I → ℝ :=
  (stepAbsorbingLaw P S)^[K] (fun _ => 1/(Fintype.card I : ℝ))

/-- One minus the total mass of `absorbingLaw P S K` on unmarked states. -/
noncomputable def classicalDetectSuccess {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I)
    (K : ℕ) : ℝ :=
  1 - ∑ i : {x : I // x ∉ S}, absorbingLaw P S K i
end Qatlib.Concepts.WalkSearch.ClassicalStop
