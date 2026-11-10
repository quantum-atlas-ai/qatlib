/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib

def cubicPhases : List ℂ := [Complex.I, Complex.I, Complex.I]

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

theorem cubic_queryCount {H : Type*} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) :
    adjointQueryCount (compileQSVT P Q (-Complex.I) cubicPhases) = 3 := by
  rw [queryCount_compileQSVT]
  rfl

end Qatlib.Concepts.CoherentSim.CoherentOAA
