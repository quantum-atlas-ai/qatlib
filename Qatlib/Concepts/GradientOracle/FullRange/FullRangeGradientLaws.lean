/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterLaws

/-!
# Full-range gradient circuit laws

This module relates the lifted value-oracle circuit to phase-oracle gradient readout, with a
reusable character register. It proves normalization, resource counts, phase precision, and
data-register marginal identities for the finite-grid construction associated with
[Jordan2005Gradient].

## Main statements

* `full_range_program_clean`: the output factors into gradient readout and the character state.
* `full_range_program_resources`: the unitary program uses one query and `2*d+1` gates.
* `full_range_phase_precision`: the encoded phase differs from the scaled value by at most
  `2^(-k)`.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical BigOperators

/-- The value-oracle gradient word is the lift of the data-register gradient word to the dyadic
target register. -/
theorem full_range_word_eq_lift (d M K k : ℕ) :
    gradientValueWord d M (2^(K+k)) = LiftCircuitTo (ZMod (2^(K+k))) (gradientWord d M) := by
  have he : ∀ C : Circuit (GradientGrid d M),
      C.map (fun st => match st with
        | .query => Step.query
        | .gate U => Step.gate (TensorGate U (1 : Matrix (ZMod (2^(K+k))) (ZMod (2^(K+k))) ℂ))) =
      LiftCircuitTo (ZMod (2^(K+k))) C := by
    intro C
    induction C with
    | nil => rfl
    | cons st C ih => cases st <;> simp only [List.map_cons,LiftCircuitTo] <;> rw [ih]
  exact he (gradientWord d M)

/-- Running a lifted circuit with the value oracle on the full-range character state equals
running the corresponding diagonal phase oracle on the data register, with the character
state unchanged. -/
theorem full_range_lift_run {X : Type} [Fintype X] [DecidableEq X] (K k : ℕ)
    (v : X → ZMod (2^(K+k))) (C : Circuit X) (ψ : QState X) :
    Run (gradientValueOracle (2^(K+k)) v) (LiftCircuitTo (ZMod (2^(K+k))) C)
      (TensorState ψ (fullRangeKickState K k)) =
    TensorState (Run (Matrix.diagonal (fun x => Complex.exp
      (2*Real.pi*Complex.I*(fullRangePhase K k v x:ℂ)))) C ψ) (fullRangeKickState K k) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons st C ih =>
    cases st with
    | gate U =>
      simp only [LiftCircuitTo,run_gate]
      rw [applyGate_tensorGate,applyGate_one]
      exact ih _
    | query =>
      simp only [LiftCircuitTo,run_query]
      rw [full_range_query_kickback]
      exact ih _

/-- The full-range gradient output factors as the encoded-phase gradient readout tensor the
full-range character state. -/
theorem full_range_program_clean (d M : ℕ) (hM : 0<M) (K k : ℕ)
    (f : GradientGrid d M → ℝ) (lo s : ℝ) :
    fullRangeGradientOutput d M hM K k f lo s =
      TensorState (gradientReadout d M hM (fullRangePhase K k (fullRangeValueTable K k f lo s)))
        (fullRangeKickState K k) := by
  unfold fullRangeGradientOutput fullRangeGradientProgram gradientValueProgram
  rw [run_append]
  simp only [gradientCharPrep,run_gate,run_nil]
  rw [applyGate_tensorGate,applyGate_one,full_range_character_preparation,full_range_word_eq_lift,full_range_lift_run]
  rfl

/-- For a positive grid size, the full-range gradient program is unitary and uses exactly one
oracle query and `2*d+1` gates. -/
theorem full_range_program_resources (d M : ℕ) (hM : 0<M) (K k : ℕ) :
    IsUnitaryCircuit (fullRangeGradientProgram d M K k) ∧
    QueryCount (fullRangeGradientProgram d M K k)=1 ∧ GateCount (fullRangeGradientProgram d M K k)=2*d+1 := by
  have hc := gradient_coordinate_qft_word_unitarity d M hM
  have hqft := zmodQFTGate_unitary (by positivity : 0<2^(K+k))
  have hinv : ((zmodQFTGate (N:=2^(K+k)))ᴴ) ∈ Matrix.unitaryGroup (ZMod (2^(K+k))) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] at hqft
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    exact hqft
  unfold fullRangeGradientProgram gradientValueProgram
  rw [full_range_word_eq_lift]
  constructor
  · rw [isUnitaryCircuit_append]
    refine ⟨?_,isUnitaryCircuit_liftCircuitTo hc.1⟩
    simp only [gradientCharPrep,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
    exact tensorGate_unitary (Submonoid.one_mem _) hinv
  · rw [queryCount_append,gateCount_append,queryCount_liftCircuitTo,gateCount_liftCircuitTo,hc.2.1,hc.2.2]
    simp [gradientCharPrep,QueryCount,GateCount,Nat.add_comm]

/-- The full-range gradient output is normalized for every value table and positive grid size. -/
theorem full_range_output_normalized (d M : ℕ) (hM : 0<M) (K k : ℕ)
    (f : GradientGrid d M → ℝ) (lo s : ℝ) : Normalized (fullRangeGradientOutput d M hM K k f lo s) := by
  rw [full_range_program_clean]
  apply normalized_tensorState ?_ (full_range_character_normalized K k)
  unfold gradientReadout
  exact normalized_run _ (gradientPhase_unitary _ _ _) _
    (gradient_coordinate_qft_word_unitarity d M hM).1 (normalized_ket _)

/-- Under the positive scaling and strict range guard, the encoded phase differs from `s*(f
x-lo)` by at most `1/2^k` at every input. -/
theorem full_range_phase_precision {X : Type} (K k : ℕ) (f : X → ℝ) (lo s R : ℝ)
    (hs : 0<s) (hR : 0≤R) (hguard : s*R<(2:ℝ)^K)
    (hf : ∀ x,lo≤f x ∧ f x≤lo+R) (x : X) :
    |fullRangePhase K k (fullRangeValueTable K k f lo s) x-s*(f x-lo)|≤1/(2:ℝ)^k := by
  let y := (2:ℝ)^k*s*(f x-lo)
  have hv : ((fullRangeValueTable K k f lo s x).val:ℝ)=(fullRangeInteger k f lo s x:ℝ) := by
    exact_mod_cast (full_range_integer_bounds K k f lo s R hs hR hguard hf x).2.2
  have hl : (fullRangeInteger k f lo s x:ℝ)≤y := Int.floor_le y
  have hu : y<(fullRangeInteger k f lo s x:ℝ)+1 := Int.lt_floor_add_one y
  have hQ : (0:ℝ)<(2:ℝ)^k := by positivity
  have he : s*(f x-lo)-fullRangePhase K k (fullRangeValueTable K k f lo s) x =
      (y-(fullRangeInteger k f lo s x:ℝ))/(2:ℝ)^k := by
    unfold fullRangePhase
    rw [hv]
    dsimp only [y]
    field_simp
  rw [abs_sub_comm,he,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hl) hQ.le)]
  exact ((div_lt_div_iff_of_pos_right hQ).mpr (by linarith)).le

/-- Marginalizing the full-range output over the entire character register gives the event
probability of the encoded-phase gradient readout. -/
theorem full_range_output_marginal (d M : ℕ) (hM : 0<M) (K k : ℕ)
    (f : GradientGrid d M → ℝ) (lo s : ℝ) (E : Finset (GradientGrid d M)) :
    MeasureProb (fullRangeGradientOutput d M hM K k f lo s) (E ×ˢ Finset.univ) =
      MeasureProb (gradientReadout d M hM (fullRangePhase K k (fullRangeValueTable K k f lo s))) E := by
  rw [full_range_program_clean]
  exact measureProb_tensorState_left (full_range_character_normalized K k) _ E

end Qatlib.Concepts.GradientOracle.FullRange
