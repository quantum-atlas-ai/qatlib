/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.SdpAlgorithm.MatrixMultiplicativeWeightsConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.SdpAlgorithm
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MatrixWeights.StoppingRule
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

def mmwSdpStopRounds (η ε : ℝ) (D : ℕ) : ℕ := Nat.ceil (Real.log D/(η*(ε-η))) + 1

def MmwSdpExactSelection (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (a : ℕ → Fin m) (η : ℝ) : Prop :=
  ∀ (t : ℕ) (i : Fin m),
    (Matrix.trace (C i * mmwState D (fun s => C (a s)) η t)).re - b i ≤
      (Matrix.trace (C (a t) * mmwState D (fun s => C (a s)) η t)).re - b (a t)

def MmwSdpPersistentViolation (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (a : ℕ → Fin m) (η ε : ℝ) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.range T,
    ε ≤ (Matrix.trace (C (a t) * mmwState D (fun s => C (a s)) η t)).re - b (a t)

def mmwSdpDualWeights (m : ℕ) (a : ℕ → Fin m) (T : ℕ) : Fin m → ℝ :=
  fun i => (∑ t ∈ Finset.range T, if a t = i then (1:ℝ) else 0)/(T:ℝ)

theorem mmwSdpStopRounds_spec (η ε : ℝ) (D : ℕ) (hη : 0 < η) (hηε : η < ε) :
    0 < mmwSdpStopRounds η ε D ∧
      η+Real.log D/(η*(mmwSdpStopRounds η ε D : ℝ)) < ε := by
  have hT : 0 < mmwSdpStopRounds η ε D := Nat.succ_pos _
  have hTr : 0 < (mmwSdpStopRounds η ε D : ℝ) := by exact_mod_cast hT
  have hceil : Real.log D/(η*(ε-η)) < (mmwSdpStopRounds η ε D : ℝ) := by
    have h := Nat.le_ceil (Real.log D/(η*(ε-η)))
    simpa only [mmwSdpStopRounds, Nat.cast_add, Nat.cast_one] using!
      lt_of_le_of_lt h (lt_add_one _)
  have hbound := (div_lt_iff₀ (mul_pos hη (sub_pos.mpr hηε))).mp hceil
  have hslack : Real.log D/(η*(mmwSdpStopRounds η ε D : ℝ)) < ε-η := by
    apply (div_lt_iff₀ (mul_pos hη hTr)).mpr
    nlinarith
  exact ⟨hT, by linarith⟩

private theorem mmw_dual_module_history {E : Type} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (a : ℕ → Fin m) (T : ℕ) (f : Fin m → E) :
    (∑ i, mmwSdpDualWeights m a T i • f i) = (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, f (a t) := by
  have hterm (i : Fin m) : mmwSdpDualWeights m a T i • f i =
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, if a t=i then f i else 0 := by
    rw [mmwSdpDualWeights, div_eq_mul_inv, mul_comm, mul_smul, Finset.sum_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp

theorem mmwSdpDualWeights_spec (m : ℕ) (a : ℕ → Fin m) (T : ℕ) (hT : 0 < T) :
    (∀ i, 0 ≤ mmwSdpDualWeights m a T i) ∧ (∑ i, mmwSdpDualWeights m a T i)=1 ∧
    ∀ f : Fin m → ℝ,
      (∑ i, mmwSdpDualWeights m a T i*f i) = (∑ t ∈ Finset.range T, f (a t))/(T : ℝ) := by
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hex (f : Fin m → ℝ) : (∑ i, mmwSdpDualWeights m a T i*f i) =
      (∑ t ∈ Finset.range T, f (a t))/(T : ℝ) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using! mmw_dual_module_history m a T f
  refine ⟨?_, ?_, hex⟩
  · intro i
    apply div_nonneg _ (Nat.cast_nonneg T)
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> norm_num
  · have h := hex (fun _ => 1)
    simpa only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, div_self hTr] using! h

theorem mmwSdpDualWeights_smul_history (D m : ℕ) (C : Fin m → Operator D)
    (a : ℕ → Fin m) (T : ℕ) :
    (∑ i, mmwSdpDualWeights m a T i • C i) = (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, C (a t) :=
  mmw_dual_module_history m a T C

private theorem mmw_regret_average (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) (σ : Operator D)
    (hD : 0<D) (hT : 0<T) (hη : 0<η) (hη1 : η≤1)
    (hM : ∀ t, (M t).IsHermitian ∧ ‖M t‖≤1) (hσ : IsDensityOperator σ) :
    (∑ t ∈ Finset.range T, (Matrix.trace (M t*mmwState D M η t)).re)/(T : ℝ) ≤
      (∑ t ∈ Finset.range T, (Matrix.trace (M t*σ)).re)/(T : ℝ) + η + Real.log D/(η*(T : ℝ)) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hr := matrix_mw_noncommuting_regret D T M η σ hD hη hη1 hM hσ
  have hdiv := div_le_div_of_nonneg_right hr (mul_pos hη hTr).le
  convert! hdiv using 1 <;> field_simp

theorem mmwSdpCompletionBranch :
  ∀ (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ) (a : ℕ → Fin m) (η ε : ℝ)
    (σ : Operator D),
    0 < D → 0 < η → η ≤ 1 → η < ε →
    (∀ i, (C i).IsHermitian ∧ ‖C i‖ ≤ 1) →
    IsDensityOperator σ →
    (∀ i, (Matrix.trace (C i * σ)).re ≤ b i) →
    MmwSdpExactSelection D m C b a η →
    IsDensityOperator (mmwAverage D (mmwSdpStopRounds η ε D) (fun s => C (a s)) η) ∧
      ∀ i, (Matrix.trace (C i * mmwAverage D (mmwSdpStopRounds η ε D)
          (fun s => C (a s)) η)).re ≤ b i + ε := by
  intro D m C b a η ε σ hD hη hη1 hηε hC hσ hfeas hselect
  obtain ⟨hT, hslack⟩ := mmwSdpStopRounds_spec η ε D hη hηε
  have h := matrix_mw_same_history_sdp_average_consumer D (mmwSdpStopRounds η ε D) m
    C b a η σ hD hT hη hη1 hC hσ hfeas (fun t _iht i => hselect t i)
  refine ⟨h.1, ?_⟩
  intro i
  have hi := h.2 i
  linarith

theorem mmwSdpLargerBranch :
  ∀ (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ) (a : ℕ → Fin m) (η ε : ℝ),
    0 < D → 0 < η → η ≤ 1 → η < ε →
    (∀ i, (C i).IsHermitian ∧ ‖C i‖ ≤ 1) →
    MmwSdpExactSelection D m C b a η →
    MmwSdpPersistentViolation D m C b a η ε (mmwSdpStopRounds η ε D) →
    ∀ σ : Operator D, IsDensityOperator σ →
      (Matrix.trace ((∑ i, mmwSdpDualWeights m a (mmwSdpStopRounds η ε D) i • C i) * σ)).re ≥
        (∑ i, mmwSdpDualWeights m a (mmwSdpStopRounds η ε D) i * b i) +
          (ε - η - Real.log D/(η*(mmwSdpStopRounds η ε D : ℝ))) ∧
      ∃ i, b i < (Matrix.trace (C i * σ)).re := by
  intro D m C b a η ε hD hη hη1 hηε hC _hselect hviol σ hσ
  let T := mmwSdpStopRounds η ε D
  have hT := (mmwSdpStopRounds_spec η ε D hη hηε).1
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hy := mmwSdpDualWeights_spec m a T hT
  have hreg := mmw_regret_average D T (fun s => C (a s)) η σ hD hT hη hη1
    (fun s => hC (a s)) hσ
  have hv : ε ≤ (∑ t ∈ Finset.range T,
      ((Matrix.trace (C (a t)*mmwState D (fun s => C (a s)) η t)).re-b (a t)))/(T : ℝ) := by
    apply (le_div_iff₀ hTr).mpr
    have hh := Finset.sum_le_sum hviol
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using! hh
  rw [Finset.sum_sub_distrib, sub_div] at hv
  have he : (Matrix.trace ((∑ i, mmwSdpDualWeights m a T i • C i)*σ)).re =
      ∑ i, mmwSdpDualWeights m a T i*(Matrix.trace (C i*σ)).re := by
    simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hmargin : (∑ i, mmwSdpDualWeights m a T i*b i) +
      (ε-η-Real.log D/(η*(T : ℝ))) ≤ (Matrix.trace ((∑ i, mmwSdpDualWeights m a T i • C i)*σ)).re := by
    rw [he, hy.2.2 (fun i => (Matrix.trace (C i*σ)).re), hy.2.2 b]
    linarith
  refine ⟨hmargin, ?_⟩
  by_contra hbad
  push Not at hbad
  have hu : (Matrix.trace ((∑ i, mmwSdpDualWeights m a T i • C i)*σ)).re ≤
      ∑ i, mmwSdpDualWeights m a T i*b i := by
    rw [he]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbad i) (hy.1 i))
  have hslack := (mmwSdpStopRounds_spec η ε D hη hηε).2
  linarith

theorem mmwSdpSameHistoryPrimalDualGap :
  ∀ (D m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ) (a : ℕ → Fin m) (η : ℝ) (T : ℕ)
    (σ : Operator D),
    0 < D → 0 < T → 0 < η → η ≤ 1 →
    (∀ i, (C i).IsHermitian ∧ ‖C i‖ ≤ 1) →
    MmwSdpExactSelection D m C b a η →
    IsDensityOperator σ →
    ∀ i,
      (Matrix.trace (C i * mmwAverage D T (fun s => C (a s)) η)).re - b i ≤
        (∑ t ∈ Finset.range T, ((Matrix.trace (C (a t) * σ)).re - b (a t)))/(T:ℝ) +
          η + Real.log D/(η*(T:ℝ)) := by
  intro D m C b a η T σ hD hT hη hη1 hC hselect hσ i
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hr := mmw_regret_average D T (fun s => C (a s)) η σ hD hT hη hη1
    (fun s => hC (a s)) hσ
  calc
    _ = (∑ t ∈ Finset.range T,
        ((Matrix.trace (C i*mmwState D (fun s => C (a s)) η t)).re-b i))/(T : ℝ) := by
      rw [mmw_trace_average, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    _ ≤ (∑ t ∈ Finset.range T,
        ((Matrix.trace (C (a t)*mmwState D (fun s => C (a s)) η t)).re-b (a t)))/(T : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun t _ => hselect t i)) hTr.le
    _ = (∑ t ∈ Finset.range T, (Matrix.trace (C (a t)*mmwState D (fun s => C (a s)) η t)).re)/(T : ℝ) -
        (∑ t ∈ Finset.range T, b (a t))/(T : ℝ) := by rw [Finset.sum_sub_distrib, sub_div]
    _ ≤ ((∑ t ∈ Finset.range T, (Matrix.trace (C (a t)*σ)).re)/(T : ℝ)+η+Real.log D/(η*(T : ℝ))) -
        (∑ t ∈ Finset.range T, b (a t))/(T : ℝ) := sub_le_sub_right hr _
    _ = _ := by rw [Finset.sum_sub_distrib, sub_div]; ring

end Qatlib.Concepts.MatrixWeights.StoppingRule
