/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial gate count for time-dependent local Hamiltonian simulation

Source: Poulin–Qarry–Somma–Verstraete, "Quantum simulation of time-dependent
Hamiltonians and the convenient illusion of Hilbert space", fixed arXiv:1102.1360v1
(7 Feb 2011). Displayed equations on p. 3:

`G(ε, L) = L (T/ΔT) = (c_max²/ε) T² L³`
and
`G_tot(ε, T) = d_SK G(ε, T) log^{c_SK}(G(ε, T)/ε)`.

The paper's total-gate-count formula is an algebraic identity once the step size
`ΔT = ε/(T c_max² L²)` and the number of segments `T/ΔT` are substituted. This module
records that identity exactly. The accompanying prose that `G_tot` is polynomial in the
number of qubits (and that rapidly time-dependent local Hamiltonian models are no more
powerful than the circuit model) is the asymptotic reading of this identity and is not
separately formalised here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeDepSim11.MainResults.GateCountScaling

/-- The paper's step-size substitution: with `ΔT = ε/(T c_max² L²)`, a product of `L`
local terms per segment costs `L·(T/ΔT) = (c_max²/ε) T² L³` gates. -/
theorem gate_count_eq (ε T L cmax : ℝ)
    (hε : ε ≠ 0) (hT : T ≠ 0) (hcmax : cmax ≠ 0) (hL : L ≠ 0) :
    L * (T / (ε / (T * cmax ^ 2 * L ^ 2))) = (cmax ^ 2 / ε) * T ^ 2 * L ^ 3 := by
  have hc : cmax ^ 2 ≠ 0 := pow_ne_zero _ hcmax
  have hl : L ^ 2 ≠ 0 := pow_ne_zero _ hL
  field_simp

/-- The source's total gate count `G_tot(ε,T) = d_SK · G · log^{c_SK}(G/ε)` as a function
of `G`, `ε`, `d_SK`, `c_SK`. -/
noncomputable def totalGateCount (dSK cSK ε G : ℝ) : ℝ :=
  dSK * G * (Real.log (G / ε)) ^ cSK

/-- Main-result gate-count formula (p. 3). Substituting the step size into the total count
gives `G_tot = d_SK · ((c_max²/ε) T² L³) · log^{c_SK}(((c_max²/ε) T² L³)/ε)`.
This is the exact displayed identity of the paper. -/
theorem gate_total_form (dSK cSK ε T L cmax : ℝ)
    (hε : ε ≠ 0) (hT : T ≠ 0) (hcmax : cmax ≠ 0) (hL : L ≠ 0) :
    totalGateCount dSK cSK ε (L * (T / (ε / (T * cmax ^ 2 * L ^ 2))))
      = dSK * ((cmax ^ 2 / ε) * T ^ 2 * L ^ 3)
          * (Real.log (((cmax ^ 2 / ε) * T ^ 2 * L ^ 3) / ε)) ^ cSK := by
  unfold totalGateCount
  rw [gate_count_eq ε T L cmax hε hT hcmax hL]

end Qatlib.Papers.TimeDepSim11.MainResults.GateCountScaling
