/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Qatlib.Papers.EllipticPDELi26.MainResults.MultilevelAllocation.SourceMultilevelAllocation

set_option backward.isDefEq.respectTransparency false

/-!
# SourceMultilevelEstimation — Theorem 5.10 of arXiv:2606.01270v2

Xiantao Li, arXiv:2606.01270v2 (2026-09-22).  Section 5.4, Theorem 5.10, page 21.

For a nested Galerkin hierarchy with compatible loads/readouts, uniformly bounded load norms, and
admissible readout order `0 ≤ χ ≤ 2`, and a `D_ℓ` block encoding with normalization `O(h_ℓ²)` and
error `O(η h_ℓ²)` at cost `τ_ℓ(η) = polylog(N_ℓ, η^{-1})`, the finest discrete output `Q_L` is
estimable to additive error `ε` with probability `≥ 2/3` at amplitude-estimation cost

  `C^{AE}_Schur = Õ(ε^{-1} [∑_{ℓ=0}^L (τ_ℓ h_ℓ^{2-χ})^{1/2}]²) = Õ(ε^{-1})`,   (5.27)

and independent direct sampling achieves RMS error `≤ ε` at cost

  `C^{samp}_Schur = Õ(ε^{-2} [∑_{ℓ=0}^L τ_ℓ^{1/2} h_ℓ^{2-χ}]²) = Õ(ε^{-2})`.   (5.28)

The allocation step is Lemma 4.1 (formalized in `MultilevelAllocation.SourceMultilevelAllocation`,
reused below as private helpers so that this file is self-contained for the single-file compile
gate).  The `Õ` asymptotic assembly is the paper's final cost statement.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.EllipticPDELi26.MainResults.QuantumEstimator

/-- Allocation lower bound (Titu / Cauchy–Schwarz), the engine of (5.27).  Same statement as
`...MultilevelAllocation.source_mlmc_amplitude_cost_lower`. -/
private theorem mlmc_amplitude_cost_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (c budget : ι → ℝ) (ε : ℝ) (hc : ∀ l, 0 ≤ c l) (hε : 0 < ε)
    (hbudget_pos : ∀ l, 0 < budget l) (hbudget : ∑ l, budget l ≤ ε) :
    (∑ l, Real.sqrt (c l)) ^ 2 / ε ≤ ∑ l, c l / budget l := by
  have hsum_pos : 0 < ∑ l, budget l :=
    Finset.sum_pos (fun l _ => hbudget_pos l) Finset.univ_nonempty
  have htitu : (∑ l, Real.sqrt (c l)) ^ 2 / (∑ l, budget l) ≤ ∑ l, c l / budget l := by
    have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ)
      (fun l => Real.sqrt (c l)) (g := budget) (fun l _ => hbudget_pos l)
    have hterm : (∑ l, (Real.sqrt (c l)) ^ 2 / budget l) = ∑ l, c l / budget l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Real.sq_sqrt (hc l)]
    rwa [hterm] at h
  have hmono : (∑ l, Real.sqrt (c l)) ^ 2 / ε ≤
      (∑ l, Real.sqrt (c l)) ^ 2 / (∑ l, budget l) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hsum_pos hbudget
  exact hmono.trans htitu

/-- Allocation attainment (the optimal `ε_ℓ ∝ √c_ℓ`), the equality behind (5.27).  Same statement
as `...MultilevelAllocation.source_mlmc_amplitude_cost_attains`. -/
private theorem mlmc_amplitude_cost_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (hcpos : ∀ l, 0 < c l) (ε : ℝ) (hε : 0 < ε) :
    ∃ budget : ι → ℝ,
      (∀ l, 0 < budget l) ∧ (∑ l, budget l = ε) ∧
        (∑ l, c l / budget l = (∑ l, Real.sqrt (c l)) ^ 2 / ε) :=
  Qatlib.Papers.EllipticPDELi26.MainResults.MultilevelAllocation.source_mlmc_amplitude_cost_attains
    c hcpos ε hε

/-- **Theorem 5.10, eq. (5.27) (amplitude-estimation allocation).**  With per-level weight
`c_ℓ = τ_ℓ h_ℓ^{2-χ} > 0`, there is a precision allocation `ε_ℓ > 0` exhausting the budget
`∑_ℓ ε_ℓ = ε` and attaining the amplitude-estimation cost `(∑_ℓ √c_ℓ)²/ε` of (5.27).

Source: arXiv:2606.01270v2, Section 5.4, Theorem 5.10, page 21, eq. (5.27). -/
theorem source_multilevel_amplitude_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ hcost : ι → ℝ) (χ ε : ℝ) (hτ : ∀ l, 0 < τ l) (hh : ∀ l, 0 < hcost l) (hε : 0 < ε) :
    ∃ budget : ι → ℝ,
      (∀ l, 0 < budget l) ∧ (∑ l, budget l = ε) ∧
        (∑ l, (τ l * Real.rpow (hcost l) (2 - χ)) / budget l
          = (∑ l, Real.sqrt (τ l * Real.rpow (hcost l) (2 - χ))) ^ 2 / ε) := by
  refine mlmc_amplitude_cost_attains
    (fun l => τ l * Real.rpow (hcost l) (2 - χ)) ?_ ε hε
  intro l
  exact mul_pos (hτ l) (Real.rpow_pos_of_pos (hh l) _)

/-- **Theorem 5.10, eq. (5.28) (direct-sampling allocation).**  With per-level circuit cost `τ_ℓ ≥ 0`
and variance `v_ℓ ≥ 0`, any variance budget `∑_ℓ b_ℓ ≤ ε²` satisfies the lower bound
`(∑_ℓ √(τ_ℓ v_ℓ))²/ε² ≤ ∑_ℓ τ_ℓ v_ℓ / b_ℓ`, which is the sampling cost of (5.28).

Source: arXiv:2606.01270v2, Section 5.4, Theorem 5.10, page 21, eq. (5.28). -/
theorem source_multilevel_sampling_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ v b : ι → ℝ) (ε : ℝ) (hτ : ∀ l, 0 ≤ τ l) (hv : ∀ l, 0 ≤ v l) (hε : 0 < ε)
    (hb_pos : ∀ l, 0 < b l) (hb : ∑ l, b l ≤ ε ^ 2) :
    (∑ l, Real.sqrt (τ l * v l)) ^ 2 / ε ^ 2 ≤ ∑ l, τ l * v l / b l :=
  mlmc_amplitude_cost_lower (fun l => τ l * v l) b (ε ^ 2)
    (fun l => mul_nonneg (hτ l) (hv l)) (pow_pos hε 2) hb_pos hb

end Qatlib.Papers.EllipticPDELi26.MainResults.QuantumEstimator
