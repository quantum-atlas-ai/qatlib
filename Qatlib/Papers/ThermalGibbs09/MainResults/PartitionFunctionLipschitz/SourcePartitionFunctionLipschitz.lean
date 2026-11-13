/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — Appendix B: Lipschitz continuity of partition functions

Poulin--Wocjan, fixed arXiv:0905.2199, Appendix B (eq. (B1)).

Claim `c004`: if `H̃ = H + E` and `‖E‖ ≤ ε/t`, then the partition functions at
inverse temperature `β` satisfy

`(1/δ) Z(β) ≤ Z̃(β) ≤ δ Z(β)`, with `δ = exp(β ε / t)`.

The proof follows the paper: Weyl's eigenvalue perturbation bound gives
`e^{-‖A-B‖} Tr e^A ≤ Tr e^B ≤ e^{‖A-B‖} Tr e^A` (eq. (B3)); applying it to
`A = -βH`, `B = -βH̃` and `‖-βH + βH̃‖ = β‖H - H̃‖ = β‖E‖ ≤ βε/t` yields the
two-sided bound. In Lean the same content is the theorem
`Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.exp_trace_le`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionLipschitz

open Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
open Qatlib.Papers.ThermalGibbs09.MainResults

variable {I : Type} [Fintype I] [DecidableEq I]

/-- **arXiv:0905.2199, Appendix B, eq. (B1).** Let `H` and `H̃` be two
self-adjoint Hamiltonians with `H̃ = H + E` and `‖E‖ ≤ ε/t`. Then the
partition functions at inverse temperature `β ≥ 0` obey
`(1/δ) Z(β) ≤ Z̃(β) ≤ δ Z(β)` for `δ = exp(β ε / t)`.

The hypothesis `hHt` records `H̃ = H + E` and `hE` the norm bound on `E`;
`t` is the simulation time appearing in the paper. -/
theorem partition_function_lipschitz
    (H E Ht : Matrix I I ℂ) (hH : H.IsHermitian) (hHt : Ht.IsHermitian)
    (hHt_def : Ht = H + E) (_hE_Hermitian : E.IsHermitian)
    (β ε t : ℝ) (hβ : 0 ≤ β) (_ht : 0 < t) (hE : ‖E‖ ≤ ε / t) :
    let δ := Real.exp (β * ε / t)
    (1 / δ) * partitionFunction β H ≤ partitionFunction β Ht ∧
      partitionFunction β Ht ≤ δ * partitionFunction β H := by
  intro δ
  have hE' : ‖Ht - H‖ ≤ ε / t := by
    rw [hHt_def]
    simpa using hE
  have hβH : ((-β : ℝ) • H).IsHermitian := hH.smul (R := ℝ) (IsSelfAdjoint.all _)
  have hβHt : ((-β : ℝ) • Ht).IsHermitian := hHt.smul (R := ℝ) (IsSelfAdjoint.all _)
  -- The operator norm of `-βH - (-β)H̃` is `β ‖H̃ - H‖`.
  have hnorm : ‖((-β : ℝ) • H) - ((-β : ℝ) • Ht)‖ = β * ‖Ht - H‖ := by
    have hscalar : ((-β : ℝ) • H) - ((-β : ℝ) • Ht) = β • (Ht - H) := by
      module
    rw [hscalar, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
  have hnorm' : ‖((-β : ℝ) • Ht) - ((-β : ℝ) • H)‖ = β * ‖Ht - H‖ := by
    rw [← norm_neg, neg_sub]
    exact hnorm
  have hbound : β * ‖Ht - H‖ ≤ β * ε / t := by
    have h1 : β * ‖Ht - H‖ ≤ β * (ε / t) := mul_le_mul_of_nonneg_left hE' hβ
    have h2 : β * (ε / t) = β * ε / t := by ring
    linarith
  -- Upper bound: `Z(β̃) ≤ exp(β‖H̃-H‖) Z(β) ≤ δ Z(β)`.
  have hupper := exp_trace_le ((-β : ℝ) • H) ((-β : ℝ) • Ht) hβH hβHt
  have hexp_le : Real.exp ‖((-β : ℝ) • H) - ((-β : ℝ) • Ht)‖
      ≤ Real.exp (β * ε / t) := by
    rw [hnorm]
    exact Real.exp_le_exp.mpr hbound
  have hZ_nonneg : 0 ≤ partitionFunction β H := partitionFunction_nonneg β H hH
  have hupperZ : partitionFunction β Ht ≤ δ * partitionFunction β H := by
    have h := hupper.trans (mul_le_mul_of_nonneg_right hexp_le hZ_nonneg)
    simpa [partitionFunction, δ] using h
  -- Lower bound: `Z(β) ≤ exp(β‖H̃-H‖) Z(β̃)`, hence `Z(β)/δ ≤ Z(β̃)`.
  have hlower := exp_trace_le ((-β : ℝ) • Ht) ((-β : ℝ) • H) hβHt hβH
  have hexp_le' : Real.exp ‖((-β : ℝ) • Ht) - ((-β : ℝ) • H)‖
      ≤ Real.exp (β * ε / t) := by
    rw [hnorm']
    exact Real.exp_le_exp.mpr hbound
  have hZt_nonneg : 0 ≤ partitionFunction β Ht := partitionFunction_nonneg β Ht hHt
  have hlowerZ : partitionFunction β H ≤ δ * partitionFunction β Ht := by
    have h := hlower.trans (mul_le_mul_of_nonneg_right hexp_le' hZt_nonneg)
    simpa [partitionFunction, δ] using h
  have hδpos : 0 < δ := by
    simp only [δ]
    exact Real.exp_pos _
  constructor
  · rw [one_div, inv_mul_le_iff₀ hδpos]
    linarith [hlowerZ]
  · exact hupperZ

end Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionLipschitz
