/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c012 — Linear PDEs: quantum `d^{O(1)} ε^{-1} ε^{-O(1)}` versus classical `ε^{-Ω(d)}`

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 7 (arXiv source lines 6518–6524).

Source conclusion: for a `d`-dimensional linear PDE solved with grid spacing `h`
(inverse accuracy `e = 1/ε` per dimension, `N = e^d` grid points), classical
algorithms cost `ε^{-Ω(d)} = N^{Ω(1)}` — exponential in the dimension; the
quantum linear-solver approach costs `d^{O(1)} ε^{-1} ε^{-O(1)}`, i.e. at most
polynomial in `N` for fixed `d`.  So at best a polynomial speedup for constant
dimension.

Formalization notes:
* `pdeClassicalCost e d = e^d = N` (the number of grid points),
* `pdeQuantumCost e d c = (d+1)^{c+1} · e^{c+1}` (the survey's
  `d^{O(1)} ε^{-1} ε^{-O(1)}` with constants `c+1`).

The main theorem computes the speedup factor exactly:
`quantumCost · e^{d-c-1} = classicalCost · (d+1)^{c+1}`.  Thus the speedup over
the `e^d`-point classical algorithm is `e^{d-c-1} ≤ e^d = N`, i.e. polynomial
(degree at most 1) in the number of grid points — the survey's "at best
polynomial for fixed `d`".

`Qatlib.Concepts.QlsReadoutSpec.PseudoInverse` models the quantum
linear-system readout that underlies the `ε^{-1}` scaling; this module records
the cost arithmetic only.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Pde

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Classical cost of a `d`-dimensional PDE on a grid with `e = 1/h` points per
dimension: `e^d` grid points. -/
def pdeClassicalCost (e d : ℕ) : ℕ := e ^ d

/-- Quantum cost `d^{O(1)} ε^{-1} ε^{-O(1)}`, with polynomial exponents
`c+1`. -/
def pdeQuantumCost (e d c : ℕ) : ℕ := (d + 1) ^ (c + 1) * e ^ (c + 1)

/-- **c012a (Section 7).** The quantum cost and the classical grid cost are
related by the exact speedup factor `e^{d-c-1}`:
`quantumCost · e^{d-c-1} = classicalCost · (d+1)^{c+1}`. -/
theorem pde_speedup_identity (e d c : ℕ) (hc : c + 1 ≤ d) :
    pdeQuantumCost e d c * e ^ (d - c - 1) =
      pdeClassicalCost e d * (d + 1) ^ (c + 1) := by
  unfold pdeQuantumCost pdeClassicalCost
  have hd : c + 1 + (d - c - 1) = d := by omega
  calc (d + 1) ^ (c + 1) * e ^ (c + 1) * e ^ (d - c - 1)
      = (d + 1) ^ (c + 1) * (e ^ (c + 1) * e ^ (d - c - 1)) := by
          rw [Nat.mul_assoc]
    _ = (d + 1) ^ (c + 1) * e ^ d := by rw [← pow_add, hd]
    _ = e ^ d * (d + 1) ^ (c + 1) := by rw [Nat.mul_comm]

/-- **c012b (Section 7).** The speedup factor `e^{d-c-1}` is at most the
number of grid points `N = e^d`: at best polynomial (degree 1) in `N` for fixed
dimension `d`. -/
theorem pde_speedup_at_most_linear (e d c : ℕ) (he : 1 ≤ e) (hc : c + 1 ≤ d) :
    e ^ (d - c - 1) ≤ pdeClassicalCost e d := by
  unfold pdeClassicalCost
  exact Nat.pow_le_pow_right (by omega : 0 < e) (by omega)

/-- **c012 (Section 7), combined assessment.** The quantum cost is
`d^{O(1)} ε^{-O(1)}`, its advantage over the `e^d`-point classical algorithm is
exactly `e^{d-c-1}`, and that advantage is at most linear in the grid size. -/
theorem linear_pde_polynomial_speedup (e d c : ℕ) (he : 1 ≤ e) (hc : c + 1 ≤ d) :
    pdeQuantumCost e d c * e ^ (d - c - 1) =
        pdeClassicalCost e d * (d + 1) ^ (c + 1) ∧
    e ^ (d - c - 1) ≤ pdeClassicalCost e d :=
  ⟨pde_speedup_identity e d c hc, pde_speedup_at_most_linear e d c he hc⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Pde
