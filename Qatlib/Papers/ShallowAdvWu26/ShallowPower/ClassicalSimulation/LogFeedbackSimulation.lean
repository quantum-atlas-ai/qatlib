/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Classical simulation with logarithmic feedback

Fixed version: arXiv:2608.15545v1 (2026-08-16), Section II (p.3, paragraph
after Theorem 1) and Appendix D's light-cone bound (p.11).

The paper observes that a CRAS circuit of coherent depth `d` that uses `m`
intermediate measurement outcomes as classical feedback has a final local
readout supported on at most `(m + 1) 2^d` input qubits.  For explicit circuits,
product-state inputs, fixed `d`, local readout and at most `m` feedback bits, a
classical algorithm enumerating the light cone estimates the unconditional
expectation value in time

  `poly(description length, precision) * 2^{O((m + 1) 2^d + m)}`.

Hence for `m = O(log n)` the simulation is polynomial; the paper writes the
resource scale as `O(n^{2^d})` (the exponent `2^d` is the number of leaves of a
depth-`d` binary light cone).

This file formalizes the arithmetic core: once the exponential factor is
bounded by `(2^{m+1})^{2^d}`, the hypothesis `2^{m+1} ≤ n` collapses it to
`n^{2^d}`, which is polynomial for constant `d`.  The quantum simulation
identity is the paper's counted algorithm and is recorded as the field
`runTime_le` of `LightConeSimulator`; the nontrivial arithmetic is proved.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.ClassicalSimulation

/-- The light-cone enumeration cost of the paper: a polynomial description
factor times `(2^{m+1})^{2^d}` (at most `2^d` inputs per light-cone leaf and at
most `m + 1` leaves). -/
def lightConeCost (polyFactor n d m : ℕ) : ℕ := polyFactor * (2 ^ (m + 1)) ^ (2 ^ d)

/-- **Exponential collapse.**  If the feedback budget satisfies `2^(m+1) ≤ n`
(this is the `m = O(log n)` regime), then the light-cone exponential factor
`(2^(m+1))^(2^d)` is at most `n^(2^d)`. -/
theorem lightCone_exponent_collapse {n d m : ℕ} (hlog : 2 ^ (m + 1) ≤ n) :
    (2 ^ (m + 1)) ^ (2 ^ d) ≤ n ^ (2 ^ d) :=
  Nat.pow_le_pow_left hlog (2 ^ d)

/-- A CRAS simulation instance in the light-cone regime.  `runTime_le` is the
paper's counted cost analysis for the enumeration algorithm (Section II p.3);
everything else is the resource data read off Appendix D. -/
structure LightConeSimulator where
  /-- Input length `n`. -/
  qubits : ℕ
  /-- Coherent depth `d`. -/
  depth : ℕ
  /-- Number `m` of classical feedback outcomes. -/
  feedback : ℕ
  /-- Polynomial description/precision factor. -/
  polyFactor : ℕ
  /-- Running time of the classical estimator. -/
  runTime : ℕ
  /-- Paper's cost bound `poly * (2^{m+1})^{2^d}` (Section II, p.3). -/
  runTime_le : runTime ≤ lightConeCost polyFactor qubits depth feedback

/-- **Section II: `O(log n)`-feedback classical simulation.**  A light-cone
simulator with `2^(m+1) ≤ n` runs in time at most `poly * n^(2^d)`.  For
constant coherent depth `d` this is polynomial in `n`; the case `d = 1` gives
the paper's displayed `O(n^2)` scale. -/
theorem log_feedback_classical_simulation (S : LightConeSimulator)
    (hlog : 2 ^ (S.feedback + 1) ≤ S.qubits) :
    S.runTime ≤ S.polyFactor * S.qubits ^ (2 ^ S.depth) := by
  refine le_trans S.runTime_le ?_
  exact Nat.mul_le_mul le_rfl (lightCone_exponent_collapse hlog)

/-- Specialization to `d = 1`: the running time is at most `poly * n^2`. -/
theorem log_feedback_classical_simulation_depth_one (S : LightConeSimulator)
    (hd : S.depth = 1) (hlog : 2 ^ (S.feedback + 1) ≤ S.qubits) :
    S.runTime ≤ S.polyFactor * S.qubits ^ 2 := by
  simpa [hd] using log_feedback_classical_simulation S hlog

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.ClassicalSimulation
