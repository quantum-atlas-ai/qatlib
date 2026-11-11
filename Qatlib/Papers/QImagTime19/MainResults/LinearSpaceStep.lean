/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagTime19.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Cost of one QITE time step: linear space, polynomial time

Paper: M. Motta et al., "Determining eigenstates and thermal states on a quantum
computer using quantum imaginary time evolution", arXiv:1901.07653 (2019).
Fixed source: `assets/1901.07653.pdf` (main text p. 2, "Cost of QITE";
Supplemental Information Eq. (36)).

The paper states:

> Compared to a direct classical implementation of imaginary time evolution,
> the cost of a QITE time-step (for bounded correlation length `C`) is linear
> in `N` in space and polynomial in `N` in time.

Here `N` is the number of lattice sites (qubits), `m` the number of local
Hamiltonian terms (typically `m = O(N)`), and `N_q` the number of qubits the
local unitary acts on (Eq. (25) for the global approximation, Eq. (37) for the
local approximation).

We formalise the two arithmetic statements behind that sentence:

* the space used by a step acting on `N_q` extra qubits of an `N`-qubit register
  is `N + N_q ≤ 2N`, hence linear in `N`;
* the time of a step is `m e^{O(N_q)}` (tomography, classical solve and circuit
  synthesis each cost `e^{O(N_q)}` per term); with `m ≤ N` and `N_q` bounded by
  a constant (local approximation) this is `O(N)` — polynomial, in fact linear,
  in `N`; in the global approximation `N_q` is a polylogarithm of `N`, giving the
  quasi-polynomial bound `T = m e^{O(k(2C)^d ln^d(2√2 n m ε^{-1}))}` of Eq. (36).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QImagTime19.MainResults

open scoped BigOperators

/-- Space of a QITE step: the register has `N` qubits and the local unitary acts
on `N_q ≤ N` of them, so the total footprint `N + N_q` is at most `2N`, linear
in `N`. -/
theorem qite_step_space_linear (N Nq : ℕ) (h : Nq ≤ N) :
    ((N : ℝ) + (Nq : ℝ)) ≤ 2 * (N : ℝ) := by
  have h' : (Nq : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
  linarith

/-- Time of a QITE step with a bounded domain: if the per-term cost is
`e^{c N_q}` and the unitary acts on at most `D` qubits, then a step over `m ≤ N`
terms costs at most `N e^{c D}`, linear in `N`. -/
theorem qite_step_time_polynomial_local (N m Nq D : ℕ) (c : ℝ)
    (hm : m ≤ N) (hNq : Nq ≤ D) (hc : 0 ≤ c) :
    (m : ℝ) * Real.exp (c * (Nq : ℝ)) ≤ (N : ℝ) * Real.exp (c * (D : ℝ)) := by
  have hm' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
  have hNq' : (Nq : ℝ) ≤ (D : ℝ) := by exact_mod_cast hNq
  have hexp : Real.exp (c * (Nq : ℝ)) ≤ Real.exp (c * (D : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hNq' hc
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc (m : ℝ) * Real.exp (c * (Nq : ℝ))
      ≤ (N : ℝ) * Real.exp (c * (Nq : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hm' (Real.exp_pos _).le
    _ ≤ (N : ℝ) * Real.exp (c * (D : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hexp hNnonneg

/-- Time of a QITE step in the global approximation: with the qubit budget
bounded by the polylogarithm `k(2C)^d ln^d(2√2 N²/ε)` coming from Eq. (25) with
`n, m ≤ N`, the step over `m ≤ N` terms costs at most
`N exp(k(2C)^d ln^d(2√2 N²/ε))` — the quasi-polynomial bound of Eq. (36). -/
theorem qite_step_time_quasipolynomial_global (N m Nq : ℕ) (c C ε : ℝ) {k d : ℕ}
    (hm : m ≤ N)
    (hNq : (Nq : ℝ) ≤
      (k : ℝ) * (2 * C) ^ d * (Real.log (2 * Real.sqrt 2 * (N : ℝ) ^ 2 / ε)) ^ d)
    (hc : 0 ≤ c) :
    (m : ℝ) * Real.exp (c * (Nq : ℝ)) ≤
      (N : ℝ) * Real.exp (c * ((k : ℝ) * (2 * C) ^ d *
        (Real.log (2 * Real.sqrt 2 * (N : ℝ) ^ 2 / ε)) ^ d)) := by
  have hm' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (c * (Nq : ℝ)) ≤
      Real.exp (c * ((k : ℝ) * (2 * C) ^ d *
        (Real.log (2 * Real.sqrt 2 * (N : ℝ) ^ 2 / ε)) ^ d)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hNq hc
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc (m : ℝ) * Real.exp (c * (Nq : ℝ))
      ≤ (N : ℝ) * Real.exp (c * (Nq : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hm' (Real.exp_pos _).le
    _ ≤ (N : ℝ) * Real.exp (c * ((k : ℝ) * (2 * C) ^ d *
        (Real.log (2 * Real.sqrt 2 * (N : ℝ) ^ 2 / ε)) ^ d)) := by
        exact mul_le_mul_of_nonneg_left hexp hNnonneg

/-- **Cost of a QITE time step (main text p. 2, "Cost of QITE").**  Space is
linear in `N` and, for a bounded local domain, time is linear (hence
polynomial) in `N`. -/
theorem qite_step_cost_linear_space_polynomial_time (N m Nq D : ℕ) (c : ℝ)
    (hm : m ≤ N) (hNq : Nq ≤ D) (hNqN : Nq ≤ N) (hc : 0 ≤ c) :
    ((N : ℝ) + (Nq : ℝ)) ≤ 2 * (N : ℝ) ∧
      (m : ℝ) * Real.exp (c * (Nq : ℝ)) ≤ (N : ℝ) * Real.exp (c * (D : ℝ)) :=
  ⟨qite_step_space_linear N Nq hNqN, qite_step_time_polynomial_local N m Nq D c hm hNq hc⟩

end Qatlib.Papers.QImagTime19.MainResults
