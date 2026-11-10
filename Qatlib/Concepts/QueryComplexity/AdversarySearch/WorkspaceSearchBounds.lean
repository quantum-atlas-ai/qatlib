/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

noncomputable def workspaceLiftStep (s : Step (I × Bool)) : Step ((I × Bool) × W) :=
  match s with
  | Step.gate U => Step.gate (TensorGate U (1 : Matrix W W ℂ))
  | Step.query => Step.query

noncomputable def workspaceLiftCircuit (C : Circuit (I × Bool)) : Circuit ((I × Bool) × W) :=
  C.map workspaceLiftStep

theorem workspaceLiftCircuit_nil :
    workspaceLiftCircuit ([] : Circuit (I × Bool)) = ([] : Circuit ((I × Bool) × W)) := rfl

theorem workspaceLiftCircuit_gate (U : Matrix (I × Bool) (I × Bool) ℂ)
    (C : Circuit (I × Bool)) :
    workspaceLiftCircuit (Step.gate U :: C)
      = Step.gate (TensorGate U (1 : Matrix W W ℂ)) :: workspaceLiftCircuit C := rfl

theorem workspaceLiftCircuit_query (C : Circuit (I × Bool)) :
    workspaceLiftCircuit ((Step.query : Step (I × Bool)) :: C)
      = (Step.query : Step ((I × Bool) × W)) :: workspaceLiftCircuit C := rfl

theorem queryCount_workspaceLiftCircuit (C : Circuit (I × Bool)) :
    QueryCount (workspaceLiftCircuit (W := W) C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [workspaceLiftCircuit_gate, queryCount_gate, queryCount_gate, ih]
    | query => rw [workspaceLiftCircuit_query, queryCount_query, queryCount_query, ih]

theorem gateCount_workspaceLiftCircuit (C : Circuit (I × Bool)) :
    GateCount (workspaceLiftCircuit (W := W) C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [workspaceLiftCircuit_gate, gateCount_gate, gateCount_gate, ih]
    | query => rw [workspaceLiftCircuit_query, gateCount_query, gateCount_query, ih]

theorem isUnitaryCircuit_workspaceLiftCircuit {C : Circuit (I × Bool)}
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (workspaceLiftCircuit (W := W) C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      rw [workspaceLiftCircuit_gate, isUnitaryCircuit_gate]
      exact ⟨tensorGate_unitary hU (Submonoid.one_mem _), ih hC'⟩
    | query =>
      rw [workspaceLiftCircuit_query, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query C).mp hC)

theorem run_workspaceLiftCircuit (O : Matrix (I × Bool) (I × Bool) ℂ) (C : Circuit (I × Bool))
    (φ : QState (I × Bool)) (χ : QState W) :
    Run (TensorGate O (1 : Matrix W W ℂ)) (workspaceLiftCircuit (W := W) C)
        (TensorState φ χ)
      = TensorState (Run O C φ) χ := by
  induction C generalizing φ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [workspaceLiftCircuit_gate]
      show Run (TensorGate O (1 : Matrix W W ℂ)) (workspaceLiftCircuit C)
          (ApplyGate (TensorGate U (1 : Matrix W W ℂ)) (TensorState φ χ)) = _
      rw [applyGate_tensorGate, applyGate_one]
      exact ih _
    | query =>
      rw [workspaceLiftCircuit_query]
      show Run (TensorGate O (1 : Matrix W W ℂ)) (workspaceLiftCircuit C)
          (ApplyGate (TensorGate O (1 : Matrix W W ℂ)) (TensorState φ χ)) = _
      rw [applyGate_tensorGate, applyGate_one]
      exact ih _

noncomputable def workspaceGroverCircuit {W : Type} [Fintype W] [DecidableEq W] (n : ℕ)
    (k : ℕ) : Circuit ((Reg n × Bool) × W) :=
  [Step.gate (TensorGate (TensorGate 1 PauliX) (1 : Matrix W W ℂ)),
    Step.gate (TensorGate (TensorGate 1 Hadamard) (1 : Matrix W W ℂ))] ++
    workspaceLiftCircuit (W := W) (LiftCircuit (preparedAACircuit (HadamardN n) (ZeroStr n) k))

theorem workspaceGroverCircuit_eq {W : Type} [Fintype W] [DecidableEq W] (n k : ℕ) :
    workspaceGroverCircuit (W := W) n k
      = [Step.gate (TensorGate (TensorGate 1 PauliX) (1 : Matrix W W ℂ)),
          Step.gate (TensorGate (TensorGate 1 Hadamard) (1 : Matrix W W ℂ))] ++
        workspaceLiftCircuit (W := W)
          (LiftCircuit (preparedAACircuit (HadamardN n) (ZeroStr n) k)) := rfl

theorem workspaceGroverCircuit_prepare {W : Type} [Fintype W] [DecidableEq W] (n : ℕ)
    (w : W) :
    ApplyGate (TensorGate (TensorGate 1 Hadamard) (1 : Matrix W W ℂ))
        (ApplyGate (TensorGate (TensorGate 1 PauliX) (1 : Matrix W W ℂ))
          (Ket ((ZeroStr n, false), w)))
      = TensorState (TensorState (Ket (ZeroStr n)) Minus) (Ket w) := by
  rw [← tensorState_ket_ket, ← tensorState_ket_ket]
  simp only [applyGate_tensorGate, applyGate_one, applyGate_pauliX_ket, Bool.not_false,
    applyGate_hadamard_ket_true]

theorem workspace_grover_bit_semantics_and_cost {W : Type} [Fintype W] [DecidableEq W]
    (n k : ℕ) (w : W) (f : Reg n → Bool) :
    IsUnitaryCircuit (workspaceGroverCircuit (W := W) n k) ∧
    QueryCount (workspaceGroverCircuit (W := W) n k) = k ∧
    GateCount (workspaceGroverCircuit (W := W) n k) = 3 * k + 3 ∧
    Run (workspaceBitOracle (W := W) f) (workspaceGroverCircuit (W := W) n k)
        (Ket ((ZeroStr n, false), w))
      = TensorState (TensorState
          (Run (PhaseOracle f) (preparedAACircuit (HadamardN n) (ZeroStr n) k)
            (Ket (ZeroStr n))) Minus) (Ket w) := by
  have hprepX : TensorGate (TensorGate 1 PauliX) (1 : Matrix W W ℂ)
      ∈ Matrix.unitaryGroup ((Reg n × Bool) × W) ℂ :=
    tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) pauliX_unitary)
      (Submonoid.one_mem _)
  have hprepH : TensorGate (TensorGate 1 Hadamard) (1 : Matrix W W ℂ)
      ∈ Matrix.unitaryGroup ((Reg n × Bool) × W) ℂ :=
    tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
      (Submonoid.one_mem _)
  have haa := prepared_aa_actual_circuit (HadamardN n) (ZeroStr n)
    ({ZeroStr n} : Finset (Reg n)) k (hadamardN_unitary n)
  have hC : IsUnitaryCircuit (workspaceGroverCircuit (W := W) n k) := by
    rw [workspaceGroverCircuit_eq, isUnitaryCircuit_append, isUnitaryCircuit_gate,
      isUnitaryCircuit_gate]
    exact ⟨⟨hprepX, hprepH, isUnitaryCircuit_nil⟩,
      isUnitaryCircuit_workspaceLiftCircuit haa.1.lift⟩
  have hQ : QueryCount (workspaceGroverCircuit (W := W) n k) = k := by
    rw [workspaceGroverCircuit_eq, queryCount_append, queryCount_workspaceLiftCircuit,
      queryCount_liftCircuit, haa.2.1]
    simp
  have hG : GateCount (workspaceGroverCircuit (W := W) n k) = 3 * k + 3 := by
    rw [workspaceGroverCircuit_eq, gateCount_append, gateCount_workspaceLiftCircuit,
      gateCount_liftCircuit, haa.2.2.1]
    simp only [gateCount_gate, gateCount_nil]
    omega
  refine ⟨hC, hQ, hG, ?_⟩
  rw [workspaceGroverCircuit_eq, run_append, run_gate, run_gate, run_nil,
    workspaceGroverCircuit_prepare]
  exact (run_workspaceLiftCircuit (BitOracleOn f)
      (LiftCircuit (preparedAACircuit (HadamardN n) (ZeroStr n) k))
      (TensorState (Ket (ZeroStr n)) Minus) (Ket w)).trans
    (by rw [run_liftCircuit_bitOracleOn])

noncomputable def singletonSearchAngle (n : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt (1 / (Fintype.card (Reg n) : ℝ)))

noncomputable def singletonSearchIterations (n : ℕ) : ℕ :=
  Nat.floor (Real.pi / (4 * singletonSearchAngle n))

theorem workspace_singleton_angle_and_rounding (n : ℕ) (hn : 2 ≤ n) :
    let N := (Fintype.card (Reg n) : ℝ)
    let θ := singletonSearchAngle n
    let k := singletonSearchIterations n
    0 < θ ∧ θ < Real.pi / 2 ∧ (Real.sin θ) ^ 2 = 1 / N ∧
    |(2 * (k : ℝ) + 1) * θ - Real.pi / 2| ≤ θ ∧
    (k : ℝ) ≤ Real.pi * Real.sqrt N / 4 ∧
    (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≥ 1 - 1 / N := by
  intro N θ k
  have hNeq : (Fintype.card (Reg n) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast card_reg n
  have hN4 : (4 : ℝ) ≤ N := by
    have h : (4 : ℕ) ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    show (4 : ℝ) ≤ (Fintype.card (Reg n) : ℝ)
    rw [hNeq]
    exact_mod_cast h
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < 1 / N := by positivity
  have hN14 : (1 : ℝ) / N ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hN4
  have hsqrt1 : Real.sqrt (1 / N) ≤ 1 / 2 := by
    calc Real.sqrt (1 / N) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hN14
      _ = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  have hsq1 : Real.sqrt (1 / N) < 1 := lt_of_le_of_lt hsqrt1 (by norm_num)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos hN1)
  have hθ1 : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hsq1
  have hsin : Real.sin θ = Real.sqrt (1 / N) :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg (1 / N)]) hsq1.le
  have hsin2 : (Real.sin θ) ^ 2 = 1 / N := by
    rw [hsin, Real.sq_sqrt hN1.le]
  have hk0 : (0 : ℝ) ≤ Real.pi / (4 * θ) :=
    div_nonneg Real.pi_nonneg (by linarith)
  have hk_le : (k : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le hk0
  have hk_lt : Real.pi / (4 * θ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk1 : (k : ℝ) * (4 * θ) ≤ Real.pi :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * θ)).mp hk_le
  have hk2 : Real.pi < ((k : ℝ) + 1) * (4 * θ) :=
    (div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * θ)).mp hk_lt
  have hgap : |(2 * (k : ℝ) + 1) * θ - Real.pi / 2| ≤ θ := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hsinθ_le : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hs1θ : 1 / Real.sqrt N ≤ θ := by
    rw [hsin, Real.sqrt_div' (1 : ℝ) hNpos.le, Real.sqrt_one] at hsinθ_le
    exact hsinθ_le
  have hsqrtNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos_of_pos hNpos
  have hinvθ : (1 : ℝ) / θ ≤ Real.sqrt N := by
    calc (1 : ℝ) / θ ≤ 1 / (1 / Real.sqrt N) :=
          one_div_le_one_div_of_le (one_div_pos.mpr hsqrtNpos) hs1θ
      _ = Real.sqrt N := one_div_one_div _
  have hkk : (k : ℝ) ≤ Real.pi * Real.sqrt N / 4 := by
    calc (k : ℝ) ≤ Real.pi / (4 * θ) := hk_le
      _ = (Real.pi / 4) * (1 / θ) := by ring
      _ ≤ (Real.pi / 4) * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hinvθ (by positivity)
      _ = Real.pi * Real.sqrt N / 4 := by ring
  have hsuccess : (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≥ 1 - 1 / N := by
    set e := (2 * (k : ℝ) + 1) * θ - Real.pi / 2 with hedef
    have hang : (2 * (k : ℝ) + 1) * θ = e + Real.pi / 2 := by
      rw [hedef]
      ring
    have hsinE : Real.sin ((2 * (k : ℝ) + 1) * θ) = Real.cos e := by
      rw [hang, Real.sin_add_pi_div_two]
    have hθleπ : θ ≤ Real.pi := by linarith [Real.pi_pos]
    have hcos : Real.cos θ ≤ Real.cos |e| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg e) hθleπ hgap
    have hcosθ0 : 0 ≤ Real.cos θ :=
      (Real.cos_pos_of_mem_Ioo
        (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
          ⟨by linarith [Real.pi_pos], hθ1⟩)).le
    have hsqe : (Real.cos θ) ^ 2 ≤ (Real.cos e) ^ 2 := by
      rw [← Real.cos_abs e]
      exact pow_le_pow_left₀ hcosθ0 hcos 2
    have hcos2 : (Real.cos θ) ^ 2 = 1 - 1 / N := by
      have h := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hsinE]
    linarith
  exact ⟨hθ0, hθ1, hsin2, hgap, hkk, hsuccess⟩

theorem preparedMark_singleton_eq_phaseOracle {I : Type} [Fintype I] [DecidableEq I]
    (x : I) :
    preparedMark {x} = PhaseOracle (fun y => decide (y = x)) := by
  ext i j
  simp only [preparedMark, PhaseOracle, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Projector, Matrix.diagonal_apply, Finset.mem_singleton]
  by_cases h : i = j
  · subst h
    by_cases hx : i = x
    · simp [hx]
      norm_num
    · simp [hx]
  · simp [h]

theorem preparedAAState_uniform_singleton_mass {n : ℕ} (x : Reg n) :
    MeasureProb (preparedAAState (HadamardN n) (ZeroStr n)) {x}
      = 1 / (Fintype.card (Reg n) : ℝ) := by
  show MeasureProb (ApplyGate (HadamardN n) (Ket (ZeroStr n))) {x} = _
  rw [applyGate_hadamardN_ket_zero, measureProb_uniform, Finset.card_singleton,
    Nat.cast_one]

theorem workspaceQueryFiber_eq_prod {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] (x : I) :
    workspaceQueryFiber (W := W) x
      = ({x} ×ˢ (Finset.univ : Finset Bool)) ×ˢ (Finset.univ : Finset W) := by
  ext ⟨⟨i, b⟩, w⟩
  simp only [workspaceQueryFiber, Finset.mem_filter, Finset.mem_univ, Finset.mem_product,
    Finset.mem_singleton, and_true, true_and]

theorem workspace_singleton_search_actual_upper {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (x : Reg n) (hn : 2 ≤ n) :
    let k := singletonSearchIterations n
    let C := workspaceGroverCircuit (W := W) n k
    MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))) C
        (Ket ((ZeroStr n, false), w)))
      (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ) ∧
    (QueryCount C : ℝ) ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 ∧
    QueryCount C = k ∧ GateCount C = 3 * k + 3 ∧ IsUnitaryCircuit C ∧
    preparedDataQueries (preparedAAWord (ZeroStr n) k) = k ∧
    preparedInputQueries (preparedAAWord (ZeroStr n) k) = 2 * k + 1 ∧
    preparedFixedGates (preparedAAWord (ZeroStr n) k) + 2 = k + 2 := by
  intro k C
  obtain ⟨hθ0, hθ1, hsin2, _, hkk, hsuccess⟩ := workspace_singleton_angle_and_rounding n hn
  obtain ⟨hClegal, hQC, hGC, hrun⟩ := workspace_grover_bit_semantics_and_cost n k w
    (fun y : Reg n => decide (y = x))
  have hborn := prepared_aa_born_success (HadamardN n) (ZeroStr n) {x}
    (singletonSearchAngle n) k (hadamardN_unitary n) hθ0 hθ1
    (by rw [preparedAAState_uniform_singleton_mass, hsin2])
  rw [preparedMark_singleton_eq_phaseOracle] at hborn
  have hmain : MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n k) (Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) x)
      = (Real.sin ((2 * (k : ℝ) + 1) * singletonSearchAngle n)) ^ 2 := by
    rw [hrun, workspaceQueryFiber_eq_prod, measureProb_tensorState_prod,
      measureProb_univ (normalized_ket w), mul_one, measureProb_tensorState_prod,
      measureProb_univ normalized_minus, mul_one, hborn]
  have hword := prepared_aa_separate_access_word (HadamardN n) (ZeroStr n)
    ({ZeroStr n} : Finset (Reg n)) k (hadamardN_unitary n)
  refine ⟨?_, ?_, hQC, hGC, hClegal, hword.2.1, hword.2.2.1, ?_⟩
  · show MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n k) (Ket ((ZeroStr n, false), w)))
        (workspaceQueryFiber (W := W) x) ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ)
    rw [hmain]
    exact hsuccess
  · show (QueryCount (workspaceGroverCircuit (W := W) n k) : ℝ)
        ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4
    rw [hQC]
    exact hkk
  · rw [hword.2.2.2.1]

end Qatlib.Concepts.QueryComplexity.AdversarySearch
