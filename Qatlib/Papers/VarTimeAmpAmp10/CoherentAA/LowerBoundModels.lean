/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows

/-!
# Grover hard-family query models

This module defines the Grover-based hard family used alongside the variable-time amplification
analysis of [Ambainis2012]. The predicate `hardFamilyAccepts` requires a legal query word to
meet the state guarantee for every marked index, and `hardFamilyMinimum` takes the infimum of
its oracle-call counts.

## Main statements

* `groverRatio`: The dimension-dependent ratio for the hard family.
* `hardFamilyAccepts`: Correctness and legality requirements for hard-family query words.
* `hardFamilyMinimum`: The infimum of achievable oracle-call counts.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound

open Qatlib.Concepts.QueryWordCore.QueryMachinery
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The real dimension-dependent ratio `(5d² - 8d + 4) / d³`. -/
def groverRatio (d : ℕ) : ℝ := (5*(d : ℝ)^2-8*d+4)/(d : ℝ)^3

/-- The predicate that `C` is legal for one oracle and, for every marked index, its run from the
uniform state satisfies `stateGuarantee` with tolerance `1 / 100` for the corresponding
Grover-inverse target. -/
def hardFamilyAccepts (d r : ℕ) (hr : 0 < r) (C : Word (Fin d) r)
    (T : Finset (Fin r)) : Prop :=
  legal 1 C ∧ ∀ x : Fin d,
    stateGuarantee (1 : Matrix (Fin d) (Fin d) ℂ) T
      (run hr (fun _ =>  PhaseOracle (fun i : Fin d =>  decide (i=x))) C
        (uniformQState (I := Fin d)))
      (groverInverse (I := Fin d) *ᵥ bState x) (1/100)

/-- The infimum in the extended nonnegative reals of counts of calls to oracle 0 among query
words satisfying `hardFamilyAccepts`. -/
def hardFamilyMinimum (d : ℕ) : ℝ≥0∞ :=
  sInf {q : ℝ≥0∞ | ∃ (r : ℕ) (hr : 0 < r) (C : Word (Fin d) r) (T : Finset (Fin r)),
    hardFamilyAccepts d r hr C T ∧ q=(calls C 0 : ℝ≥0∞)}

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
