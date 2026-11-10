/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.StoppingRule
import Mathlib.Data.Finset.Max
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.StoppingRule
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MatrixWeights.SdpAlgorithm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def mmwSdpGibbsOfSum (D : ℕ) (η : ℝ) (S : Operator D) : Operator D :=
  let W : Operator D := NormedSpace.exp (-η • S)
  ((Matrix.trace W).re : ℂ)⁻¹ • W

private theorem mmwSdp_exists_max_residual (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (ρ : Operator D) :
    ∃ j : Fin m, ∀ i : Fin m,
      (Matrix.trace (C i * ρ)).re - b i ≤ (Matrix.trace (C j * ρ)).re - b j := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin m => (Matrix.trace (C i * ρ)).re - b i) hne
  exact ⟨j, fun i => hmax i (Finset.mem_univ i)⟩

def mmwSdpChoose (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (hm : 0 < m) (ρ : Operator D) : Fin m :=
  Classical.choose (mmwSdp_exists_max_residual D m C b hm ρ)

theorem mmwSdpChoose_spec (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (hm : 0 < m) (ρ : Operator D) (i : Fin m) :
    (Matrix.trace (C i * ρ)).re - b i ≤
      (Matrix.trace (C (mmwSdpChoose D m C b hm ρ) * ρ)).re -
        b (mmwSdpChoose D m C b hm ρ) :=
  Classical.choose_spec (mmwSdp_exists_max_residual D m C b hm ρ) i

def mmwSdpCumulative (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (hm : 0 < m) (η : ℝ) : ℕ → Operator D
  | 0 => 0
  | t+1 =>
      let S := mmwSdpCumulative D m C b hm η t
      S + C (mmwSdpChoose D m C b hm (mmwSdpGibbsOfSum D η S))

def mmwSdpGeneratedState (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (hm : 0 < m) (η : ℝ) (t : ℕ) : Operator D :=
  mmwSdpGibbsOfSum D η (mmwSdpCumulative D m C b hm η t)

def mmwSdpGeneratedSelection (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (hm : 0 < m) (η : ℝ) : ℕ → Fin m :=
  fun t => mmwSdpChoose D m C b hm (mmwSdpGeneratedState D m C b hm η t)

theorem mmwSdpCumulative_eq_sum (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η : ℝ) (t : ℕ) :
    mmwSdpCumulative D m C b hm η t =
      ∑ s ∈ Finset.range t, C (mmwSdpGeneratedSelection D m C b hm η s) := by
  induction t with
  | zero => simp [mmwSdpCumulative]
  | succ t ih =>
      rw [Finset.sum_range_succ]
      change mmwSdpCumulative D m C b hm η t +
        C (mmwSdpGeneratedSelection D m C b hm η t) = _
      rw [ih]

theorem mmwSdpGeneratedState_eq_mmwState (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η : ℝ) (t : ℕ) :
    mmwSdpGeneratedState D m C b hm η t =
      mmwState D (fun s => C (mmwSdpGeneratedSelection D m C b hm η s)) η t := by
  simp only [mmwSdpGeneratedState, mmwSdpGibbsOfSum, mmwState, mmwWeight,
    mmwSdpCumulative_eq_sum]

theorem mmwSdpGeneratedSelection_spec (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η : ℝ) :
    MmwSdpExactSelection D m C b (mmwSdpGeneratedSelection D m C b hm η) η := by
  intro t i
  rw [← mmwSdpGeneratedState_eq_mmwState D m C b hm η t]
  exact mmwSdpChoose_spec D m C b hm (mmwSdpGeneratedState D m C b hm η t) i

theorem mmwSdpGeneratedState_isDensityOperator (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η : ℝ) (t : ℕ) (hD : 0 < D)
    (hC : ∀ i, (C i).IsHermitian) :
    IsDensityOperator (mmwSdpGeneratedState D m C b hm η t) := by
  rw [mmwSdpGeneratedState_eq_mmwState]
  exact (matrix_mw_actual_gibbs_iterates_density D
    (fun s => C (mmwSdpGeneratedSelection D m C b hm η s)) η t hD (fun s => hC _)).2

theorem mmwSdpGeneratedCompletion (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η ε : ℝ) (σ : Operator D)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1) (hηε : η < ε)
    (hC : ∀ i, (C i).IsHermitian ∧ ‖C i‖ ≤ 1) (hσ : IsDensityOperator σ)
    (hfeas : ∀ i, (Matrix.trace (C i * σ)).re ≤ b i) :
    IsDensityOperator (mmwAverage D (mmwSdpStopRounds η ε D)
      (fun s => C (mmwSdpGeneratedSelection D m C b hm η s)) η) ∧
      ∀ i, (Matrix.trace (C i * mmwAverage D (mmwSdpStopRounds η ε D)
        (fun s => C (mmwSdpGeneratedSelection D m C b hm η s)) η)).re ≤ b i + ε :=
  mmwSdpCompletionBranch D m C b (mmwSdpGeneratedSelection D m C b hm η) η ε σ
    hD hη hη1 hηε hC hσ hfeas (mmwSdpGeneratedSelection_spec D m C b hm η)

theorem mmwSdpGeneratedAlternative (D m : ℕ) (C : Fin m → Operator D)
    (b : Fin m → ℝ) (hm : 0 < m) (η ε : ℝ)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1) (hηε : η < ε)
    (hC : ∀ i, (C i).IsHermitian ∧ ‖C i‖ ≤ 1) :
    let a := mmwSdpGeneratedSelection D m C b hm η
    let T := mmwSdpStopRounds η ε D
    (∃ t ∈ Finset.range T,
      IsDensityOperator (mmwState D (fun s => C (a s)) η t) ∧
      ∀ i, (Matrix.trace (C i * mmwState D (fun s => C (a s)) η t)).re < b i + ε) ∨
    (∀ σ : Operator D, IsDensityOperator σ →
      (Matrix.trace ((∑ i, mmwSdpDualWeights m a T i • C i) * σ)).re ≥
        (∑ i, mmwSdpDualWeights m a T i * b i) +
          (ε - η - Real.log D/(η*(T : ℝ))) ∧
      ∃ i, b i < (Matrix.trace (C i * σ)).re) := by
  (try dsimp only)
  let a := mmwSdpGeneratedSelection D m C b hm η
  let T := mmwSdpStopRounds η ε D
  have hselect : MmwSdpExactSelection D m C b a η :=
    mmwSdpGeneratedSelection_spec D m C b hm η
  by_cases hstop : ∃ t ∈ Finset.range T,
      (Matrix.trace (C (a t) * mmwState D (fun s => C (a s)) η t)).re - b (a t) < ε
  · obtain ⟨t, ht, hres⟩ := hstop
    left
    refine ⟨t, ht, (matrix_mw_actual_gibbs_iterates_density D
      (fun s => C (a s)) η t hD (fun s => (hC (a s)).1)).2, ?_⟩
    intro i
    have hi := hselect t i
    linarith
  · right
    have hviol : MmwSdpPersistentViolation D m C b a η ε T := by
      intro t ht
      exact le_of_not_gt (fun hlt => hstop ⟨t, ht, hlt⟩)
    exact mmwSdpLargerBranch D m C b a η ε hD hη hη1 hηε hC hselect hviol

end Qatlib.Concepts.MatrixWeights.SdpAlgorithm
