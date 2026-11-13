/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Flagged variable-time states and costs

`VtSpace` combines a three-valued outcome flag with a payload register. This module defines the
stopped, good, bad, and running sets, prefix evolution, stopping increments, success mass, and
dyadic timing quantities. `IsVtStage` requires a unitary matrix that fixes every stopped basis
ket.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `IsVtStage`: unitary stages fixing the full stopped subspace.
* `vtTav` and `vtTmax`: second-moment average and maximum dyadic stopping times.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Matrix

set_option autoImplicit false

section Model

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The product of a three-valued outcome flag and the payload type `C`. -/
abbrev VtSpace (C : Type) [Fintype C] : Type := Fin 3 × C

/-- The outcome flag `0`, representing a bad stopped outcome. -/
def vtBadFlag : Fin 3 := 0

/-- The outcome flag `1`, representing a good stopped outcome. -/
def vtGoodFlag : Fin 3 := 1

/-- The outcome flag `2`, representing a running computation. -/
def vtRunningFlag : Fin 3 := 2

/-- The basis labels whose outcome flag is different from the running flag. -/
def stoppedSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 ≠ vtRunningFlag)

/-- The basis labels carrying the good outcome flag. -/
def goodSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtGoodFlag)

/-- The basis labels carrying the bad outcome flag. -/
def badSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtBadFlag)

/-- The basis labels carrying the running outcome flag. -/
def runningSet (C : Type) [Fintype C] : Finset (VtSpace C) :=
  Finset.univ.filter (fun p => p.1 = vtRunningFlag)

/-- A unitary matrix that fixes each basis ket whose outcome flag is stopped. -/
def IsVtStage (U : Matrix (VtSpace C) (VtSpace C) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (VtSpace C) ℂ ∧
    ∀ p : VtSpace C, p.1 ≠ vtRunningFlag → ∀ q : VtSpace C,
      U q p = if q = p then (1 : ℂ) else 0

/-- The product of the first `k` stage matrices in execution order, with later stages
multiplying on the left. -/
noncomputable def vtRunMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (k : ℕ) : Matrix (VtSpace C) (VtSpace C) ℂ :=
  (stages.take k).foldl (fun A U => U * A) 1

/-- The state obtained by applying the first `k` stages to `ψ`. -/
noncomputable def vtState (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (k : ℕ) (ψ : QState (VtSpace C)) : QState (VtSpace C) :=
  vtRunMatrix stages k *ᵥ ψ

/-- The measurement mass on stopped labels after the first `k` stages, starting from `Ket j₀`. -/
noncomputable def stoppedMass (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (k : ℕ) : ℝ :=
  MeasureProb (vtState stages k (Ket j₀)) (stoppedSet C)

/-- The increase in stopped mass from prefix `j` to prefix `j + 1`. -/
noncomputable def pstop (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (j : ℕ) : ℝ :=
  stoppedMass stages j₀ (j + 1) - stoppedMass stages j₀ j

/-- The measurement mass on good labels after all stages, starting from `Ket j₀`. -/
noncomputable def psucc (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) : ℝ :=
  MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)

/-- The real-valued dyadic stopping time `2^(j + 1)` associated with stage index `j`. -/
noncomputable def stopTime (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

/-- The square root of the sum of stopping increments weighted by squared dyadic stopping times. -/
noncomputable def vtTav (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range stages.length,
    pstop stages j₀ j * (stopTime j) ^ 2)

/-- The maximum dyadic stopping-time parameter `2^stages.length`. -/
noncomputable def vtTmax (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) : ℝ :=
  (2 : ℝ) ^ stages.length

/-- The natural-valued access duration `2^j` of stage index `j`. -/
def stageDuration (j : ℕ) : ℕ := 2 ^ j

end Model

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
