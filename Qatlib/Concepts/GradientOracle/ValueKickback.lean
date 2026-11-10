/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.GridGradientConsumers
import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.GradientOracle.ValueKickback
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def gradientValueOracle {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) : Matrix (X × ZMod Q) (X × ZMod Q) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2 = y.2 + v y.1 then 1 else 0

noncomputable def gradientKickState (Q : ℕ) [NeZero Q] : ZMod Q → ℂ :=
  fun y => (Real.sqrt (Q : ℝ) : ℂ)⁻¹ * star (ZMod.stdAddChar y)

noncomputable def gradientValuePhase {X : Type} (Q : ℕ) [NeZero Q]
    (v : X → ZMod Q) : X → ℝ := fun x => ((v x).val : ℝ) / Q

noncomputable def gradientValueWord (d M Q : ℕ) [NeZero Q] :
    Circuit (GradientGrid d M × ZMod Q) :=
  (gradientWord d M).map (fun s => match s with
    | .query => Step.query
    | .gate U => Step.gate (TensorGate U (1 : Matrix (ZMod Q) (ZMod Q) ℂ)))

private theorem gradientValueOracle_eq_addOracle {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) : gradientValueOracle Q v = AddOracle v := by
  rw [addOracle_eq_permMatrix]
  ext x y
  simp [gradientValueOracle, permMatrix, addOracleEquiv, Prod.ext_iff]

private theorem gradient_character_shift (Q : ℕ) [NeZero Q] (y a : ZMod Q) :
    star (ZMod.stdAddChar (y - a)) = ZMod.stdAddChar a * star (ZMod.stdAddChar y) := by
  have hmul : ZMod.stdAddChar (y - a) * ZMod.stdAddChar a = ZMod.stdAddChar y := by
    rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  have hunit : ZMod.stdAddChar a * star (ZMod.stdAddChar a) = 1 := by
    change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar a) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ZMod.stdAddChar_apply, Circle.norm_coe]
    norm_num
  calc
    _ = 1 * star (ZMod.stdAddChar (y - a)) := (one_mul _).symm
    _ = (ZMod.stdAddChar a * star (ZMod.stdAddChar a)) *
        star (ZMod.stdAddChar (y - a)) := by rw [hunit]
    _ = ZMod.stdAddChar a * star (ZMod.stdAddChar (y - a) * ZMod.stdAddChar a) := by
      rw [star_mul]
      ring
    _ = _ := by rw [hmul]

theorem gradient_value_query_actual_kickback :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (Q : ℕ) [NeZero Q]
      (v : X → ZMod Q) (ψ : X → ℂ),
      gradientValueOracle Q v ∈ Matrix.unitaryGroup (X × ZMod Q) ℂ ∧
      (gradientValueOracle Q v).mulVec (fun xy => ψ xy.1 * gradientKickState Q xy.2) =
        (fun xy => ZMod.stdAddChar (v xy.1) * ψ xy.1 * gradientKickState Q xy.2) := by
  intro X _ _ Q _ v ψ
  rw [gradientValueOracle_eq_addOracle]
  refine ⟨addOracle_unitary v, ?_⟩
  funext xy
  rcases xy with ⟨x, y⟩
  change ApplyGate (AddOracle v) _ (x, y) = _
  rw [applyGate_addOracle]
  (try dsimp only)
  unfold gradientKickState
  rw [gradient_character_shift]
  ring

private theorem gradient_std_character_phase (Q : ℕ) [NeZero Q] (a : ZMod Q) :
    ZMod.stdAddChar a = Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / Q)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  field_simp

private noncomputable def gradientValueLift {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (C : Circuit X) : Circuit (X × ZMod Q) :=
  C.map (fun s => match s with
    | .query => Step.query
    | .gate U => Step.gate (TensorGate U (1 : Matrix (ZMod Q) (ZMod Q) ℂ)))

private theorem gradientValueLift_eq {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (C : Circuit X) :
    gradientValueLift Q C = LiftCircuitTo (ZMod Q) C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [gradientValueLift, List.map_cons, LiftCircuitTo]
    all_goals exact congrArg (List.cons _) ih

private theorem gradientValueLift_run {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) (C : Circuit X) (ψ : QState X) :
    Run (gradientValueOracle Q v) (gradientValueLift Q C)
      (TensorState ψ (gradientKickState Q)) =
      TensorState (Run (Matrix.diagonal (fun x => ZMod.stdAddChar (v x))) C ψ)
        (gradientKickState Q) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [gradientValueLift, List.map_cons, run_gate]
      rw [applyGate_tensorGate, applyGate_one]
      exact ih _
    | query =>
      simp only [gradientValueLift, List.map_cons, run_query]
      have hquery : ApplyGate (gradientValueOracle Q v) (TensorState ψ (gradientKickState Q)) =
          TensorState (ApplyGate (Matrix.diagonal (fun x => ZMod.stdAddChar (v x))) ψ)
            (gradientKickState Q) := by
        have h := (gradient_value_query_actual_kickback X Q v ψ).2
        change (gradientValueOracle Q v).mulVec
          (fun xy => ψ xy.1 * gradientKickState Q xy.2) = _
        rw [h]
        funext xy
        simp only [TensorState, ApplyGate, Matrix.mulVec_diagonal]
      rw [hquery]
      exact ih _

theorem gradient_value_one_query_clean_fourier_consumer :
    ∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (v : GradientGrid d M → ZMod Q),
      Run (gradientValueOracle Q v) (gradientValueWord d M Q)
        (fun xy => Ket (gradientZero d M hM) xy.1 * gradientKickState Q xy.2) =
          (fun xy => gradientReadout d M hM (gradientValuePhase Q v) xy.1 *
            gradientKickState Q xy.2) ∧
      QueryCount (gradientValueWord d M Q) = 1 ∧ GateCount (gradientValueWord d M Q) = 2 * d := by
  intro d M Q hM _ v
  have hdiag : Matrix.diagonal (fun x => ZMod.stdAddChar (v x)) =
      gradientPhase d M (gradientValuePhase Q v) := by
    congr 1
    funext x
    simpa only [gradientValuePhase, Complex.ofReal_div, Complex.ofReal_natCast] using!
      gradient_std_character_phase Q (v x)
  have hrun := gradientValueLift_run Q v (gradientWord d M) (Ket (gradientZero d M hM))
  rw [hdiag] at hrun
  unfold Qatlib.Foundations.PureStateMath.TensorState at hrun
  have hword : gradientValueWord d M Q = gradientValueLift Q (gradientWord d M) := by
    unfold gradientValueWord gradientValueLift
    apply List.map_congr_left
    intro s _
    cases s with
    | query => rfl
    | gate U =>
      congr 1
  refine ⟨?_, ?_⟩
  · rw [hword]
    simpa only [gradientReadout] using! hrun
  rw [hword]
  rw [gradientValueLift_eq, queryCount_liftCircuitTo, gateCount_liftCircuitTo]
  exact (gradient_coordinate_qft_word_unitarity d M hM).2

theorem gradientKickState_normalized (Q : ℕ) [NeZero Q] : Normalized (gradientKickState Q) := by
  have hQ : 0 < (Q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hn (y : ZMod Q) : ‖gradientKickState Q y‖ ^ 2 = (Q : ℝ)⁻¹ := by
    simp only [gradientKickState, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_star,
      ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
    rw [inv_pow, Real.sq_sqrt hQ.le]
  unfold Normalized
  simp [hn, ZMod.card, hQ.ne']

theorem gradient_value_actual_data_marginal (d M Q : ℕ) (hM : 0 < M) [NeZero Q]
    (v : GradientGrid d M → ZMod Q) (S : Finset (GradientGrid d M)) :
    MeasureProb (Run (gradientValueOracle Q v) (gradientValueWord d M Q)
      (fun xy => Ket (gradientZero d M hM) xy.1 * gradientKickState Q xy.2))
      (S ×ˢ Finset.univ) =
      MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S := by
  rw [(gradient_value_one_query_clean_fourier_consumer d M Q hM v).1]
  exact measureProb_tensorState_left (gradientKickState_normalized Q) _ S

theorem gradient_value_precision_actual_readout_event :
    ∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q]
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ)
      (δ : ℝ) (S : Finset (GradientGrid d M)), 0 ≤ δ →
      (∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ) →
      |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S -
        MeasureProb (gradientReadout d M hM φ) S| ≤ 4 * Real.pi * δ := by
  intro d M Q hM _ v φ δ S hδ hprecision
  let κ := fun x => Classical.choose (hprecision x)
  let ψ := fun x => gradientValuePhase Q v x - (κ x : ℝ)
  have hψ : ∀ x, |ψ x - φ x| ≤ δ := by
    intro x
    have h := Classical.choose_spec (hprecision x)
    convert! h using 1
    congr 1
    dsimp [ψ, κ]
    ring
  have hphase : gradientPhase d M ψ = gradientPhase d M (gradientValuePhase Q v) := by
    unfold gradientPhase
    congr 1
    funext x
    dsimp [ψ]
    rw [Complex.ofReal_sub, mul_sub, Complex.exp_sub]
    have hi : Complex.exp (2 * Real.pi * Complex.I * ((κ x : ℝ) : ℂ)) = 1 :=
      exp_two_pi_I_int (κ x)
    rw [hi, div_one]
  have h := gradient_actual_phase_event_error d M hM ψ φ δ hδ hψ S
  unfold gradientReadout at h
  rw [hphase] at h
  exact h

end Qatlib.Concepts.GradientOracle.ValueKickback
