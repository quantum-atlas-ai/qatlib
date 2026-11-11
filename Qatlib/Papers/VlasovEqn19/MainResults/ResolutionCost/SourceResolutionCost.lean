/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# ResolutionCost — grid-resolution independence of the Vlasov simulation cost

Paper: Engel--Smith--Parker, "Quantum Algorithm for the Vlasov Equation",
fixed arXiv:1907.09418.  Claim `c002` (MainResults, p. 5).

The paper's block-encoding normalisation is governed by (Eq. (30)--(31))

  `Λ := |k| v_max + sqrt(Δv · N_v · v_max · g_max)`,
  `4Λ/5 ≤ 1/β ≤ Λ`,

and the velocity grid satisfies `v_max = (N_v - 1) Δv / 2`, i.e.
`Δv · N_v = 2 v_max + Δv`.  Because the product `Δv · N_v` is bounded by
`2 v_max + 1` when `0 < Δv ≤ 1`, the quantity `Λ` does not grow when the
velocity resolution `Δv` is decreased (with `N_v` adapting so that the
identity holds).  Hence increasing the velocity-grid resolution does not
increase the Hamiltonian-simulation query count.  The space/gate complexity
enters the resolution only through the qubit count `n_v = log₂ N_v`, which
grows logarithmically in `1/Δv`.

This file formalises exactly those two mathematical statements:
`lambda_resolution_free_bound` and `nv_bits_logarithmic`.  The normalisation
sandwich `4Λ/5 ≤ 1/β ≤ Λ` of Eq. (30) is quoted from the paper but is *not*
re-derived here: it depends on the paper's `β = c²/(k v_max)` and the
auxiliary algebraic bound of footnote 3, and is outside the two explicit
sentences of the claim.

Boundary: all quantities are real numbers of the paper's *dimensionless*
model; no discretisation error and no Hamiltonian query implementation are
assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VlasovEqn19.MainResults.ResolutionCost

/-- `Λ` of Eq. (31): the block-encoding normalisation bound
`|k| v_max + sqrt(Δv · N_v · v_max · g_max)`. -/
def Lambda (k vmax dv Nv gmax : ℝ) : ℝ :=
  |k| * vmax + Real.sqrt (dv * Nv * vmax * gmax)

/-- The velocity-grid identity `v_max = (N_v - 1) Δv / 2` rearranged, used in
the paper immediately before Eq. (30): `Δv · N_v = 2 v_max + Δv`. -/
theorem grid_identity (vmax dv Nv : ℝ) (hdv : dv ≠ 0)
    (h : dv * Nv = 2 * vmax + dv) :
    Nv = (2 * vmax + dv) / dv := by
  rw [eq_div_iff hdv]
  linarith [h]

/-- Under the grid identity, `Λ` is exactly the resolution-only expression
`|k| v_max + sqrt((2 v_max + Δv) · v_max · g_max)`; the raw `N_v` disappears. -/
theorem lambda_eq (k vmax dv Nv gmax : ℝ)
    (h : dv * Nv = 2 * vmax + dv) :
    Lambda k vmax dv Nv gmax =
      |k| * vmax + Real.sqrt ((2 * vmax + dv) * vmax * gmax) := by
  unfold Lambda
  rw [h]

/-- Claim `c002`, core inequality: for `0 < Δv ≤ 1` the normalisation `Λ` is
bounded by a quantity that depends only on the fixed problem range
`v_max` and the coupling size `g_max`, and *not* on the number of velocity
cells `N_v`.  Decreasing `Δv` (while `N_v` grows so that
`Δv · N_v = 2 v_max + Δv`) therefore cannot increase `Λ`, hence cannot
increase the simulation query complexity.  (Paper Eq. (30)--(31), p. 5.) -/
theorem lambda_resolution_free_bound (k vmax dv Nv gmax : ℝ)
    (hvmax : 0 ≤ vmax) (hgmax : 0 ≤ gmax) (_hdv : 0 < dv) (hdv1 : dv ≤ 1)
    (h : dv * Nv = 2 * vmax + dv) :
    Lambda k vmax dv Nv gmax ≤
      |k| * vmax + Real.sqrt ((2 * vmax + 1) * vmax * gmax) := by
  unfold Lambda
  rw [h]
  have hnum : 2 * vmax + dv ≤ 2 * vmax + 1 := by linarith
  have hprod : (2 * vmax + dv) * vmax * gmax ≤ (2 * vmax + 1) * vmax * gmax := by
    have hvg : 0 ≤ vmax * gmax := mul_nonneg hvmax hgmax
    nlinarith [hnum, hvg]
  have hsqrt :
      Real.sqrt ((2 * vmax + dv) * vmax * gmax) ≤
        Real.sqrt ((2 * vmax + 1) * vmax * gmax) :=
    Real.sqrt_le_sqrt hprod
  linarith

/-- Claim `c002`, logarithmic resolution dependence: with `N_v` velocity cells,
the register size is `n_v = log₂ N_v` qubits.  Under the grid identity and
`0 < Δv ≤ 1`, this qubit count is at most `log₂ (2 v_max + 1) + log₂ (1/Δv)`;
the second term is the only residue of an "extremely high-resolution" grid,
so space and gate complexity scale logarithmically in the velocity
resolution.  (Paper p. 5, discussion around Eq. (30)--(31).) -/
theorem nv_bits_logarithmic (vmax dv Nv : ℝ)
    (hvmax : 0 ≤ vmax) (hdv : 0 < dv) (hdv1 : dv ≤ 1)
    (h : dv * Nv = 2 * vmax + dv) :
    Real.log Nv / Real.log 2 ≤
      Real.log (2 * vmax + 1) / Real.log 2 + Real.log (1 / dv) / Real.log 2 := by
  have hdv_ne : dv ≠ 0 := ne_of_gt hdv
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNv_eq : Nv = (2 * vmax + dv) / dv := grid_identity vmax dv Nv hdv_ne h
  have hnum_pos : 0 < 2 * vmax + dv := by linarith
  have hNv_pos : 0 < Nv := by
    rw [hNv_eq]
    positivity
  have hle : Nv ≤ (2 * vmax + 1) / dv := by
    rw [hNv_eq]
    exact div_le_div_of_nonneg_right (by linarith) hdv.le
  have hlogN : Real.log Nv ≤ Real.log ((2 * vmax + 1) / dv) :=
    Real.log_le_log hNv_pos hle
  have hnum1_pos : 0 < 2 * vmax + 1 := by linarith
  have hsplit : Real.log ((2 * vmax + 1) / dv) =
      Real.log (2 * vmax + 1) + Real.log (1 / dv) := by
    rw [Real.log_div (ne_of_gt hnum1_pos) hdv_ne]
    rw [div_eq_mul_inv, one_mul, Real.log_inv]
    ring
  rw [hsplit] at hlogN
  have hdiv := div_le_div_of_nonneg_right hlogN hlog2.le
  rwa [add_div] at hdiv

end Qatlib.Papers.VlasovEqn19.MainResults.ResolutionCost
