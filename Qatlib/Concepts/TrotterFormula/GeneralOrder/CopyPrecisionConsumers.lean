/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision

/-!
# Concrete copy-based simulation and coherence

The Bell density matrix `copyComparisonBell` provides an entangled input for an explicit
fresh-copy simulation bound with resource counts. The module also computes the off-diagonal
coherence after repeated partial swaps with a pure basis-state resource, separating its cosine
attenuation from the ideal evolution phase. For background, see [LloydMohseniRebentrost2014].

## Main statements

* `copy_entangled_actual_precision_consumer`: a concrete entangled-input error bound and copy
  counts.
* `copy_pure_projector_exact_coherence_consumer`: exact coherence after equal partial-swap
  steps.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped ComplexOrder Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The square of the inverse square root of two, viewed in `ℂ`, is `1 / 2`. -/
private theorem invsqrt2_mul_self_ℂ :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [inv_sqrt2_mul_self]
  norm_num

/-- The outer product of `copyEvolutionBellInput`, used as a bipartite comparison density
matrix. -/
noncomputable def copyComparisonBell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  outerProduct copyEvolutionBellInput

/-- The squared complex norm of the inverse square root of two is `1 / 2`. -/
private theorem bell_norm_sq : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = 1 / 2 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The Bell input vector used for copy-evolution comparison is normalized. -/
private theorem normalized_copyEvolutionBellInput : Normalized copyEvolutionBellInput := by
  show ∑ p : Fin 2 × Fin 2, ‖copyEvolutionBellInput p‖ ^ 2 = 1
  rw [Fintype.sum_prod_type]
  simp only [copyEvolutionBellInput, Fin.isValue, Fin.sum_univ_two, bell_norm_sq]
  norm_num

/-- The Bell comparison matrix is positive semidefinite. -/
theorem copyComparisonBell_posSemidef : copyComparisonBell.PosSemidef := by
  rw [copyComparisonBell]
  exact outerProduct_posSemidef _

/-- The Bell comparison matrix has trace one. -/
theorem copyComparisonBell_trace : Matrix.trace copyComparisonBell = 1 := by
  have hstar : starRingEnd ℂ ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ = Complex.ofReal ((Real.sqrt 2 : ℝ)⁻¹) from
      (Complex.ofReal_inv (Real.sqrt 2 : ℝ)).symm,
      Complex.conj_ofReal]
  have happ : ∀ p q : Fin 2 × Fin 2,
      copyComparisonBell p q
        = (if p.1 = p.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0)
          * (if q.1 = q.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0) := by
    intro p q
    rw [copyComparisonBell, outerProduct_apply, copyEvolutionBellInput, copyEvolutionBellInput]
    by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq, hstar]
  simp only [Matrix.trace, Matrix.diag_apply, happ]
  simp [Fintype.sum_prod_type, invsqrt2_mul_self_ℂ]

/-- The Bell comparison matrix has trace norm one. -/
theorem copyComparisonBell_traceNorm : Matrix.traceNorm copyComparisonBell = 1 := by
  have h := psd_traceNorm_eq_trace copyComparisonBell copyComparisonBell_posSemidef
  rw [copyComparisonBell_trace] at h
  norm_num at h
  exact h

/-- The copy precision budget at parameters one and two is 32. -/
private theorem budget_one_two : copyPrecisionBudget 1 2 = 32 := by
  rw [copyPrecisionBudget_eq_of_pos (by norm_num)]
  norm_num

/-- The scalar step size `(1 / 2) / 32` equals `1 / 64`. -/
private theorem half_div_thirty_two : ((1/2 : ℝ) / (32 : ℝ)) = 1 / 64 := by norm_num

/-- Identifies the Bell comparison input and bounds the trace-norm error of 32 fresh-copy steps
of size `1 / 64` at time `1 / 2` by `1 / 4`. The resource-count tuple is `(32, 32, 32, 0)`
[LloydMohseniRebentrost2014]. -/
theorem copy_entangled_actual_precision_consumer :
    copyComparisonBell = outerProduct (fun p : Fin 2 × Fin 2 =>
        if p.1 = p.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0) ∧
      let ρ := outerProduct (Qatlib.Foundations.PureStateMath.Ket (0:Fin 2))
      let U := TensorGate (HamiltonianEvolution ρ (1/2)) (1:Operator 2)
      Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate 32 (1/64)) 2 copyComparisonBell
        - U*copyComparisonBell*Uᴴ) ≤ 1/4 ∧
      freshCopyResourceCounts 2 (List.replicate 32 (1/64)) = (32,32,32,0) := by
  refine ⟨?_, ?_⟩
  · rw [copyComparisonBell]
    rfl
  · have hρ : IsDensityOperator (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) :=
      isDensityOperator_outerProduct (normalized_ket 0)
    have hG6 := copy_precision_same_protocol_and_four_resource_counts
      2 2 1 2 (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (1/2) copyComparisonBell hρ
      copyComparisonBell_posSemidef (by norm_num)
    dsimp only at hG6
    have hsteps : List.replicate (copyPrecisionBudget 1 2)
          ((1/2 : ℝ) / (copyPrecisionBudget 1 2 : ℝ))
        = List.replicate 32 (1/64) := by
      rw [budget_one_two]
      norm_num
    rw [hsteps] at hG6
    have h1 := hG6.1
    have hbudget : ((2 : ℝ)⁻¹)^2 * Matrix.traceNorm copyComparisonBell ≤ (1/4 : ℝ) := by
      rw [copyComparisonBell_traceNorm]
      norm_num
    (try dsimp only)
    refine ⟨?_, ?_⟩
    · exact h1.trans hbudget
    · rw [freshCopyResourceCounts_eq, List.length_replicate]

/-- The complex exponential `exp (-I * θ)` equals `cos θ - I * sin θ`. -/
private theorem exp_neg_I (θ : ℝ) :
    Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
  have hre : (-Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re]
  have him : (-Complex.I * (θ : ℂ)).im = -(θ : ℝ) := by
    simp [Complex.mul_im, Complex.I_im]
  have hM : (Real.cos θ : ℂ).im = 0 := Complex.ofReal_im (Real.cos θ)
  have hS : (Real.sin θ : ℂ).re = Real.sin θ := Complex.ofReal_re (Real.sin θ)
  have hS' : (Real.sin θ : ℂ).im = 0 := Complex.ofReal_im (Real.sin θ)
  have hI : (Complex.I * (Real.sin θ : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, hS']
    ring
  have hI' : (Complex.I * (Real.sin θ : ℂ)).im = Real.sin θ := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, hS', hS]
    ring
  refine Complex.ext ?_ ?_
  · rw [Complex.exp_re, hre, him, Real.exp_zero, Real.cos_neg]
    rw [Complex.sub_re, Complex.ofReal_re (Real.cos θ), hI]
    ring
  · rw [Complex.exp_im, hre, him, Real.exp_zero, Real.sin_neg]
    rw [Complex.sub_im, hM, hI']
    ring

/-- The expression `cos² θ - I * sin θ * cos θ` factors as `cos θ * exp (-I * θ)`. -/
private theorem cos_sq_sub_I (θ : ℝ) :
    (Real.cos θ)^2 - Complex.I*(Real.sin θ:ℂ)*(Real.cos θ:ℂ)
      = (Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)) := by
  rw [exp_neg_I θ]
  push_cast
  ring

/-- A partial swap with the basis-zero pure projector multiplies the `(0, 1)` coherence by `cos
θ * exp (-I * θ)`. -/
theorem copy_zero_projector_coherence_step (θ : ℝ) (σ : Operator 2) :
    partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ 0 1
      = σ 0 1 * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ))) := by
  rw [copy_zero_projector_one_step θ σ]
  show (((Real.cos θ)^2 : ℂ)-Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))*σ 0 1
      = σ 0 1 * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))
  rw [mul_comm (((Real.cos θ)^2 : ℂ) - Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))
      (σ 0 1),
    cos_sq_sub_I]

/-- After `m` equal fresh-copy steps with the basis-zero projector, the `(0, 1)` coherence is
multiplied by `(cos θ * exp (-I * θ)) ^ m`. -/
theorem copy_zero_projector_coherence_foldl (θ : ℝ) (m : ℕ) (σ : Operator 2) :
    (freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate m θ) σ) 0 1
      = σ 0 1 * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))^m := by
  induction m generalizing σ with
  | zero =>
      have hrun : freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate 0 θ) σ
          = σ := by
        simp only [freshCopyRun, List.replicate_zero, List.foldl_nil]
      rw [hrun, pow_zero, mul_one]
  | succ m ih =>
      have ih' :=
          ih (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ)
      rw [freshCopyRun] at ih'
      rw [List.replicate_succ, freshCopyRun, List.foldl_cons, ih',
        copy_zero_projector_coherence_step θ σ]
      calc
        σ 0 1 * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))
            * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))^m
            = σ 0 1 * (((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))
                * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))^m) := by ring
        _ = σ 0 1 * ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))^(m + 1) := by
              rw [pow_succ']

/-- Every component of the equally weighted two-basis-state superposition equals the inverse
square root of two. -/
private theorem plusPure_apply (i : Fin 2) :
    ((Real.sqrt 2 : ℂ)⁻¹ • (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1 : Fin 2))) i
      = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases i <;> simp [Matrix.smul_apply, Matrix.add_apply, Qatlib.Foundations.PureStateMath.Ket]

/-- Every entry of the outer product of the equally weighted two-basis-state superposition is
the square of the inverse square root of two. -/
private theorem plusPure_outer_apply (i j : Fin 2) :
    outerProduct ((Real.sqrt 2 : ℂ)⁻¹ • (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1 : Fin 2))) i j
      = ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) := by
  rw [outerProduct_apply, plusPure_apply, plusPure_apply]
  have hstar : starRingEnd ℂ ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [show ((Real.sqrt 2 : ℂ))⁻¹ = Complex.ofReal ((Real.sqrt 2 : ℝ)⁻¹) from
      (Complex.ofReal_inv (Real.sqrt 2 : ℝ)).symm,
      Complex.conj_ofReal]
  rw [hstar]

/-- The `(0, 1)` entry of the equally weighted qubit superposition's pure-state matrix is `1 /
2`. -/
theorem copy_plusProjector_01 :
    outerProduct ((Real.sqrt 2 : ℂ)⁻¹ • (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) + Qatlib.Foundations.PureStateMath.Ket (1 : Fin 2))) 0 1 = (1/2 : ℂ) := by
  rw [plusPure_outer_apply, inv_sqrt2_mul_self]
  norm_num

/-- The `m`th power of the coherence factor separates as `cos θ ^ m * exp (-I * (m * θ))`. -/
theorem copy_coherence_power (θ : ℝ) (m : ℕ) :
    ((Real.cos θ : ℂ) * Complex.exp (-Complex.I*(θ:ℂ)))^m
      = (Real.cos θ : ℂ)^m * Complex.exp (-Complex.I * ((m:ℝ)*(θ:ℝ) : ℂ)) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  have hexp : (m : ℂ) * (-Complex.I * (θ : ℂ)) = -Complex.I * ((m:ℝ)*(θ:ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp]

/-- For positive `n`, simulating the basis-zero projector on the equally weighted qubit state
with `n` steps of size `t / n` gives coherence `(1/2) * cos (t/n) ^ n * exp (-I * t)`
[LloydMohseniRebentrost2014]. -/
theorem copy_pure_projector_exact_coherence_consumer (t : ℝ) (n : ℕ) (hn : 0 < n) :
    let ρ := outerProduct (Qatlib.Foundations.PureStateMath.Ket (0:Fin 2))
    let σ :=
        outerProduct
        ((Real.sqrt 2:ℂ)⁻¹ • (Qatlib.Foundations.PureStateMath.Ket (0:Fin 2)+Qatlib.Foundations.PureStateMath.Ket (1:Fin 2)))
    (freshCopyRun ρ (List.replicate n (t/(n:ℝ))) σ) 0 1 =
      (1/2:ℂ) * (Real.cos (t/(n:ℝ)):ℂ)^n * Complex.exp (-Complex.I*(t:ℂ)) := by
  (try dsimp only)
  rw [copy_zero_projector_coherence_foldl (t / (n : ℝ)) n,
    copy_plusProjector_01, copy_coherence_power (t / (n : ℝ)) n]
  have hmul : (n : ℝ) * (t / (n : ℝ)) = t := nat_mul_div_self hn t
  have hcc : ((n : ℝ) * (t / (n : ℝ) : ℝ) : ℂ) = (t : ℂ) := by
    exact_mod_cast hmul
  rw [hcc]
  ring

end Qatlib.Concepts.TrotterFormula.GeneralOrder
