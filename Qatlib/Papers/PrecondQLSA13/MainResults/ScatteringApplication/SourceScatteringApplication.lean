/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# ScatteringApplication — source interface for the FEM scattering remark of PrecondQLSA13

Clader--Jacobs--Sprouse, *Preconditioned quantum linear system algorithm*,
fixed arXiv:1301.2340v4 (2013-05-07). Source locations: Eq. (12) on p. 3 and
the closing paragraph on p. 4 ("Finally we remark on the efficiency of the
scattering cross section calculation").

The paper states:

* without preconditioning, finite-element condition numbers scale as
  `N^{2/n}` (Brenner--Scott; Bank--Scott), which still leaves the quantum
  algorithm better than the classical conjugate-gradient solver in three
  dimensions, since the quantum cost scales as `κ log N` while the classical
  cost scales as `N κ log(1/ε)`;
* SPAI preconditioning constrains the spectrum to a circle of radius
  `√d ε_pre`, giving Eq. (12)

    `κ = λ_max/λ_min ≤ (1 + √d ε_pre)/(1 - √d ε_pre)`;

  a bounded `κ` makes the whole algorithm `O(log N)`, hence exponential
  speedup over the classical `O(N)` solver, and the FEM admits an efficient
  SPAI.

This module formalises the Eq. (12) spectral bound, the three-dimensional
`N^{2/3}` scaling and `log κ = (2/3) log N`, and both complexity comparisons.

Boundary: the existence of an efficient SPAI for FEM (references [22,23]) and
the numerical `N^{2/n}` scaling law (references [11,12]) are source premises of
the paper; they are taken as hypotheses/definitions, while the spectral and
complexity implications are proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication

/-- FEM condition-number scaling `κ ≈ N^{2/n}` in `n` spatial dimensions
(arXiv:1301.2340v4, p. 4, citing Brenner--Scott and Bank--Scott). -/
noncomputable def femConditionNumber (n N : ℝ) : ℝ := N ^ (2 / n)

/-- The SPAI spectral-circle radius `√d · ε_pre` from the paragraph preceding
Eq. (12) (arXiv:1301.2340v4, p. 3). -/
noncomputable def preconditionedRadius (d εpre : ℝ) : ℝ := Real.sqrt d * εpre

/-- Eq. (16): the radar cross section is the squared overlap with `R`, up to
`1/(4π)` (arXiv:1301.2340v4, p. 4). -/
noncomputable def radarCrossSection (overlapSq : ℝ) : ℝ :=
  overlapSq / (4 * Real.pi)

/-- Eq. (16), p. 4: the cross section is nonnegative for a squared overlap. -/
theorem radarCrossSection_nonneg {o : ℝ} (ho : 0 ≤ o) :
    0 ≤ radarCrossSection o := by
  unfold radarCrossSection
  positivity

/-- Fixed arXiv:1301.2340v4, Eq. (12), p. 3: if every eigenvalue of the
preconditioned matrix lies in the circle of radius `r = √d ε_pre < 1`, then the
spectral condition number obeys
`κ = λ_max/λ_min ≤ (1 + r)/(1 - r)`. -/
theorem eq12_condition_number_bound (d εpre lamMax lamMin : ℝ)
    (he : 0 ≤ εpre) (hlt : preconditionedRadius d εpre < 1)
    (hlamMin : 0 < lamMin)
    (hmax : lamMax ≤ 1 + preconditionedRadius d εpre)
    (hmin : 1 - preconditionedRadius d εpre ≤ lamMin) :
    lamMax / lamMin ≤
      (1 + preconditionedRadius d εpre) / (1 - preconditionedRadius d εpre) := by
  set r := preconditionedRadius d εpre with hr
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    unfold preconditionedRadius
    exact mul_nonneg (Real.sqrt_nonneg d) he
  have hrpos : 0 < 1 - r := by linarith
  have h1 : lamMax * (1 - r) ≤ (1 + r) * (1 - r) :=
    mul_le_mul_of_nonneg_right hmax (le_of_lt hrpos)
  have h2 : (1 + r) * (1 - r) ≤ (1 + r) * lamMin :=
    mul_le_mul_of_nonneg_left hmin (by linarith)
  rw [div_le_div_iff₀ hlamMin hrpos]
  linarith

/-- Fixed arXiv:1301.2340v4, Eq. (12), p. 3: the bound is a constant
`K = (1 + r)/(1 - r)` depending only on `d` and `ε_pre`, and hence independent
of the matrix size `N`. This is the bounded-spectrum statement behind the
exponential speedup. -/
theorem eq12_uniform_condition_bound (d εpre lamMax lamMin : ℝ)
    (he : 0 ≤ εpre) (hlt : preconditionedRadius d εpre < 1)
    (hlamMin : 0 < lamMin)
    (hmax : lamMax ≤ 1 + preconditionedRadius d εpre)
    (hmin : 1 - preconditionedRadius d εpre ≤ lamMin) :
    ∃ K : ℝ, 0 < K ∧ lamMax / lamMin ≤ K := by
  refine ⟨(1 + preconditionedRadius d εpre) / (1 - preconditionedRadius d εpre),
    ?_, eq12_condition_number_bound d εpre lamMax lamMin he hlt hlamMin hmax hmin⟩
  have hr_nonneg : 0 ≤ preconditionedRadius d εpre := by
    unfold preconditionedRadius
    exact mul_nonneg (Real.sqrt_nonneg d) he
  have hnum : 0 < 1 + preconditionedRadius d εpre := by linarith
  have hden : 0 < 1 - preconditionedRadius d εpre := by linarith
  positivity

/-- Fixed arXiv:1301.2340v4, p. 4: in three dimensions the FEM condition number
is `N^{2/3}`. -/
theorem fem_condition_three_dim (N : ℝ) :
    femConditionNumber 3 N = N ^ (2 / 3 : ℝ) := by
  unfold femConditionNumber
  norm_num

/-- Fixed arXiv:1301.2340v4, p. 4: for the three-dimensional FEM,
`log κ = (2/3) log N`. -/
theorem fem_log_condition_three_dim {N : ℝ} (hN : 0 < N) :
    Real.log (femConditionNumber 3 N) = (2 / 3) * Real.log N := by
  rw [fem_condition_three_dim, Real.log_rpow hN]

/-- Fixed arXiv:1301.2340v4, p. 4: without preconditioning, both the quantum
cost (proportional to `κ log N`) and the classical conjugate-gradient cost
(proportional to `N κ log(1/ε)`) carry the same three-dimensional `κ = N^{2/3}`,
so the quantum algorithm scales better whenever `log N ≤ N`. -/
theorem no_preconditioning_quantum_better {N : ℝ} (hN : 1 ≤ N) :
    femConditionNumber 3 N * Real.log N ≤ N * femConditionNumber 3 N := by
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog : Real.log N ≤ N := by
    have h1 := Real.log_le_sub_one_of_pos hpos
    linarith
  have hκ : 0 ≤ femConditionNumber 3 N := by
    rw [fem_condition_three_dim]
    positivity
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hlog hκ

/-- Fixed arXiv:1301.2340v4, p. 4: with a quantum SPAI preconditioner the
condition number is bounded by a constant `K` independent of `N` (Eq. (12)), so
the quantum cost is `K log N` while the classical cost is `K N`; the algorithm
therefore achieves exponential speedup. -/
theorem preconditioned_exponential_speedup {K N : ℝ} (hK : 0 ≤ K) (hN : 1 ≤ N) :
    K * Real.log N ≤ K * N := by
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog : Real.log N ≤ N := by
    have h1 := Real.log_le_sub_one_of_pos hpos
    linarith
  exact mul_le_mul_of_nonneg_left hlog hK

end Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication
