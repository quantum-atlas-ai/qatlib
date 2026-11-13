/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit

/-!
# Cubic singular value amplification

This module gives a three-phase sequence whose response polynomial is `3 * X - 4 * X ^ 3`. It
realizes the cubic amplitude amplification response from [BrassardEtAl2002] within the projected
unitary encoding framework.

The theorem `cubic_singularPair` computes the action on a supplied singular pair, and
`cubic_queryCount` records the exact three-query cost of its compiled word.

## Main statements

* `responseP_cubic`: the phase sequence has the cubic response polynomial.
* `cubic_singularPair`: the compressed circuit transforms a singular value to `3 * σ - 4 * σ ^
  3`.
* `cubic_queryCount`: compilation uses three oracle queries.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib

/-- The three-element phase sequence consisting of `Complex.I` at every position. -/
def cubicPhases : List ℂ := [Complex.I, Complex.I, Complex.I]

/-- With base phase `-Complex.I`, the cubic phase sequence has response polynomial `3 * X - 4 *
X ^ 3`. -/
theorem responseP_cubic :
    responseP (-Complex.I) cubicPhases = 3 * X - 4 * X ^ 3 := by
  have hI4 : Complex.I ^ 4 = (1 : ℂ) := by
    calc
      _ = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  apply Polynomial.funext
  intro x
  simp [cubicPhases, responseP_cons, responseQ_cons]
  ring_nf
  rw [Complex.I_sq, hI4]
  ring

/-- For a supplied pair satisfying the two singular-pair equations, the compressed cubic
sequence sends `v` to `(3 * σ - 4 * σ ^ 3) • w`. This is the cubic amplification response of
[BrassardEtAl2002]. -/
theorem cubic_singularPair {H I O K : Type*}
    [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L)
      (-Complex.I) cubicPhases) R * v = (3 * σ - 4 * σ ^ 3) • w := by
  have he := qsvt_odd h hav haw (-Complex.I) cubicPhases (by decide)
  simpa [responseP_cubic] using he

/-- The compiled cubic amplification word contains exactly three oracle queries. -/
theorem cubic_queryCount {H : Type*} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) :
    adjointQueryCount (compileQSVT P Q (-Complex.I) cubicPhases) = 3 := by
  rw [queryCount_compileQSVT]
  rfl

end Qatlib.Concepts.CoherentSim.CoherentOAA
