/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.ComputedSignalConsumers
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ClockDefinitions

/-!
# Signal simulation words for binary clock midpoints

This module builds coherent binary clock evolution from guarded quantum signal processing words
[LowChuang2017]. Each `atomWord` implements one dyadic pulse, and `program` concatenates the
pulses while retaining a common simulator frame.

`instructions` uses all dyadic axes to select the desired midpoint evolution on every clock
label. Full-state error bounds compose additively, and the resource theorems give exact query
and gate sums for the forward and adjoint words.

## Main statements

* `target_midpoint`: the complete dyadic target selects evolution at each rational midpoint.
* `instructions_full_output_error`: the complete framed error is at most `(q+1)*2⁻ᵏ` times the
  input norm.
* `instructions_resources`: the compiled word is well formed and its costs are sums of pulse
  costs.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The signal simulator register consisting of three Boolean flags and the underlying register
`H`. -/
abbrev SimulatorSpace (H : Type) := Bool × (Bool × (Bool × H))
/-- The binary clock register together with an enable flag and the signal simulator register. -/
abbrev Physical (q : ℕ) (H : Type) := Reg q × (Bool × SimulatorSpace H)

/-- Rectangular complex matrix multiplication with its finite intermediate index type specified
explicitly. -/
private noncomputable abbrev matmul {X Y Z : Type} [Fintype Y]
    (A : Matrix X Y ℂ) (B : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

section Spectator

variable {C W : Type} [Fintype C] [DecidableEq C] [Fintype W] [DecidableEq W]

/-- Extend an explicit gate by an untouched register `C`, preserving forward and backward oracle
instructions. -/
noncomputable def spectatorStep : AdjointStep W → AdjointStep (C × W)
  | .gate V => .gate (parallelOracle (J := C) V)
  | .forward => .forward
  | .backward => .backward

/-- Extend every instruction of an adjoint word by an untouched register `C`. -/
noncomputable def spectatorWord (cs : List (AdjointStep W)) : List (AdjointStep (C × W)) :=
  cs.map spectatorStep

/-- Evaluating a spectator-extended word with the extended oracle gives the spectator extension
of its original evaluation. -/
theorem spectatorWord_evaluate (O : Matrix W W ℂ) (cs : List (AdjointStep W)) :
    evaluate (parallelOracle (J := C) O) (spectatorWord cs) =
      parallelOracle (J := C) (evaluate O cs) := by
  induction cs with
  | nil => simp [spectatorWord, evaluate, parallelOracle, parallel_select_one]
  | cons c cs ih =>
    change instructionMatrix (parallelOracle O) (spectatorStep c) *
      evaluate (parallelOracle O) (spectatorWord cs) = _
    rw [ih]
    cases c with
    | gate V =>
      change parallelOracle V * parallelOracle (evaluate O cs) =
        parallelOracle (V * evaluate O cs)
      exact parallel_select_mul _ _
    | forward =>
      change parallelOracle O * parallelOracle (evaluate O cs) =
        parallelOracle (O * evaluate O cs)
      exact parallel_select_mul _ _
    | backward =>
      change (parallelOracle O)ᴴ * parallelOracle (evaluate O cs) =
        parallelOracle (Oᴴ * evaluate O cs)
      rw [parallelOracle_adjoint]
      exact parallel_select_mul _ _

omit [Fintype C] [Fintype W] [DecidableEq W] in

/-- Adding a spectator register preserves the adjoint query count. -/
theorem spectatorWord_queryCount (cs : List (AdjointStep W)) :
    adjointQueryCount (spectatorWord (C := C) cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change adjointQueryCount (spectatorStep c :: spectatorWord cs) = adjointQueryCount (c :: cs)
    cases c <;> simp [spectatorStep, adjointQueryCount, ih]

omit [Fintype C] [Fintype W] [DecidableEq W] in

/-- Adding a spectator register preserves the explicit gate count. -/
theorem spectatorWord_gateCount (cs : List (AdjointStep W)) :
    adjointGateCount (spectatorWord (C := C) cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change adjointGateCount (spectatorStep c :: spectatorWord cs) = adjointGateCount (c :: cs)
    cases c <;> simp [spectatorStep, adjointGateCount, ih]

/-- Adding a spectator register preserves well-formedness of an adjoint word. -/
theorem spectatorWord_wellFormed (cs : List (AdjointStep W))
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (spectatorWord (C := C) cs) := by
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    cases c <;>
      simp only [spectatorWord, List.map_cons, spectatorStep,
        WellFormedAdjointCircuit.gate_cons_iff,
        WellFormedAdjointCircuit.forward_cons_iff,
        WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨parallelOracle_unitary hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

/-- Flip the enable flag on precisely those control labels for which `g` is true. -/
noncomputable def guardToggle (g : C → Bool) : Matrix (C × (Bool × W)) (C × (Bool × W)) ℂ :=
  select (fun c => if g c then controlFlip else 1)

/-- Surround a spectator extension of the controlled word by two guard toggles. -/
noncomputable def guardedWord (g : C → Bool) (cs : List (AdjointStep W)) :
    List (AdjointStep (C × (Bool × W))) :=
  [.gate (guardToggle g)] ++ spectatorWord (compileControlled cs) ++ [.gate (guardToggle g)]

/-- The controlled matrix `V`, conjugated by the control flip when `b` is true. -/
noncomputable def enabledMatrix (b : Bool) (V : Matrix W W ℂ) :
    Matrix (Bool × W) (Bool × W) ℂ :=
  if b then controlFlip * controlOracle V * controlFlip else controlOracle V

/-- The conditional enable-flag toggle is unitary. -/
theorem guardToggle_unitary (g : C → Bool) :
    guardToggle (W := W) g ∈ Matrix.unitaryGroup _ ℂ := by
  change select (fun c : C => if g c then controlFlip (H := W) else 1) ∈
    Matrix.unitaryGroup (C × (Bool × W)) ℂ
  exact Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    (fun c : C => if g c then controlFlip (H := W) else 1) (by
      intro c
      change (if g c then controlFlip (H := W) else 1) ∈ Matrix.unitaryGroup (Bool × W) ℂ
      by_cases hc : g c = true
      · rw [if_pos hc]
        exact controlFlip_unitary (H := W)
      · rw [if_neg hc]
        exact Submonoid.one_mem _)

/-- The guarded word evaluates to the clock selection of `enabledMatrix (g c)` applied to the
original word's evaluation. -/
theorem guardedWord_evaluate (g : C → Bool) (O : Matrix W W ℂ)
    (cs : List (AdjointStep W)) :
    evaluate (parallelOracle (J := C) (controlOracle O)) (guardedWord g cs) =
      select (fun c => enabledMatrix (g c) (evaluate O cs)) := by
  simp only [guardedWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_one]
  rw [spectatorWord_evaluate, evaluate_compileControlled]
  unfold guardToggle parallelOracle
  rw [parallel_select_mul, parallel_select_mul]
  congr 1
  funext c
  cases g c <;> simp [enabledMatrix]

/-- Guarding a well-formed adjoint word preserves well-formedness. -/
theorem guardedWord_wellFormed (g : C → Bool) (cs : List (AdjointStep W))
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (guardedWord g cs) := by
  have ht : WellFormedAdjointCircuit ([.gate (guardToggle (W := W) g)] :
      List (AdjointStep (C × (Bool × W)))) := by
    simpa using! guardToggle_unitary (W := W) g
  exact (ht.append (spectatorWord_wellFormed _ (compileControlled_wellFormed hcs))).append ht

omit [Fintype C] [Fintype W] in

/-- Guarding a word preserves its adjoint query count. -/
theorem guardedWord_queryCount (g : C → Bool) (cs : List (AdjointStep W)) :
    adjointQueryCount (guardedWord g cs) = adjointQueryCount cs := by
  simp [guardedWord, spectatorWord_queryCount, queryCount_compileControlled, adjointQueryCount]

omit [Fintype C] [Fintype W] in

/-- Guarding a word adds exactly two explicit gates. -/
theorem guardedWord_gateCount (g : C → Bool) (cs : List (AdjointStep W)) :
    adjointGateCount (guardedWord g cs) = adjointGateCount cs + 2 := by
  simp only [guardedWord, adjointGateCount_append, spectatorWord_gateCount,
    gateCount_compileControlled, adjointGateCount]
  omega

/-- On a fixed Boolean fiber, a controlled oracle applies `V` when the fiber is true and the
identity otherwise. -/
theorem controlOracle_fiber (b : Bool) (V : Matrix W W ℂ) :
    matmul (controlOracle V) (encodingFiber (I := W) b) =
      matmul (encodingFiber b) (if b then V else 1) := by
  ext ⟨c, i⟩ j
  cases b <;> cases c <;>
    simp [matmul, controlOracle, select, encodingFiber, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

/-- The control flip sends the Boolean fiber `b` to the fiber `!b`. -/
theorem controlFlip_fiber (b : Bool) :
    matmul (controlFlip (H := W)) (encodingFiber (I := W) b) = encodingFiber (!b) := by
  ext ⟨c, i⟩ j
  cases b <;> cases c <;>
    simp [matmul, controlFlip, encodingFiber, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite]

/-- On the false enable fiber, `enabledMatrix b V` applies `V` if `b` is true and the identity
otherwise. -/
theorem enabledMatrix_fiber (b : Bool) (V : Matrix W W ℂ) :
    matmul (enabledMatrix b V) (encodingFiber (I := W) false) =
      matmul (encodingFiber false) (if b then V else 1) := by
  cases b
  · simpa [enabledMatrix] using! controlOracle_fiber false V
  · change matmul (controlFlip * controlOracle V * controlFlip) (encodingFiber false) =
      matmul (encodingFiber false) V
    calc
      _ = matmul controlFlip (matmul (controlOracle V) (matmul controlFlip (encodingFiber false))) := by
        simp only [matmul, Matrix.mul_assoc]
      _ = matmul controlFlip (matmul (controlOracle V) (encodingFiber true)) := by
        rw [controlFlip_fiber]
        simp only [Bool.not_false]
      _ = matmul controlFlip (matmul (encodingFiber true) V) := by
        rw [controlOracle_fiber]
        simp only [if_true]
      _ = matmul (matmul controlFlip (encodingFiber true)) V := by
        simp only [matmul, Matrix.mul_assoc]
      _ = matmul (encodingFiber false) V := by
        rw [controlFlip_fiber]
        simp only [Bool.not_true]

/-- Applying the enabled matrix to a state in the false enable fiber conditionally applies `V`
while preserving that fiber. -/
theorem enabledMatrix_apply (b : Bool) (V : Matrix W W ℂ) (ψ : QState W) :
    enabledMatrix b V *ᵥ (encodingFiber false *ᵥ ψ) =
      encodingFiber false *ᵥ ((if b then V else 1) *ᵥ ψ) := by
  calc
    _ = matmul (enabledMatrix b V) (encodingFiber false) *ᵥ ψ :=
      Matrix.mulVec_mulVec _ _ _
    _ = matmul (encodingFiber false) (if b then V else 1) *ᵥ ψ := by
      rw [enabledMatrix_fiber]
    _ = _ := (Matrix.mulVec_mulVec _ _ _).symm

end Spectator

section JointError

variable {C O I : Type} [Fintype C] [DecidableEq C]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- Extend a rectangular frame by the identity on the control register `C`. -/
noncomputable def liftFrame (F : Matrix O I ℂ) : Matrix (C × O) (C × I) ℂ :=
  (1 : Matrix C C ℂ) ⊗ₖ F

omit [Fintype O] [DecidableEq O] [DecidableEq I] in

/-- Applying a lifted frame acts independently on each control slice. -/
theorem liftFrame_mulVec (F : Matrix O I ℂ) (Ψ : QState (C × I)) (c : C) (o : O) :
    (liftFrame F *ᵥ Ψ) (c, o) = (F *ᵥ (fun i => Ψ (c, i))) o := by
  simp [liftFrame, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul]

omit [DecidableEq O] in

/-- Applying a selected matrix acts on each control slice by the matrix selected by that label. -/
theorem select_mulVec (M : C → Matrix O O ℂ) (Ψ : QState (C × O)) (c : C) (o : O) :
    (select M *ᵥ Ψ) (c, o) = (M c *ᵥ (fun i => Ψ (c, i))) o := by
  simp [select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

omit [DecidableEq C] [DecidableEq I] in

/-- The squared Euclidean norm of a joint state is the sum of the squared norms of its control
slices. -/
theorem joint_norm_sq (Ψ : QState (C × I)) :
    ‖toEuclidean_fromVec Ψ‖ ^ 2 =
      ∑ c : C, ‖toEuclidean_fromVec (fun i => Ψ (c, i))‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, toEuclidean_fromVec_apply, Fintype.sum_prod_type]

omit [DecidableEq O] [DecidableEq I] in

/-- A uniform framed error bound on every control slice gives the same relative error bound for
the coherent selected operation. -/
theorem selected_full_output_error (M : C → Matrix O O ℂ) (F : Matrix O I ℂ)
    (V : C → Matrix I I ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ c (ψ : QState I),
      ‖toEuclidean_fromVec (M c *ᵥ (F *ᵥ ψ) - F *ᵥ (V c *ᵥ ψ))‖ ≤
        δ * ‖toEuclidean_fromVec ψ‖) (Ψ : QState (C × I)) :
    ‖toEuclidean_fromVec
      (select M *ᵥ (liftFrame F *ᵥ Ψ) - liftFrame F *ᵥ (select V *ᵥ Ψ))‖ ≤
      δ * ‖toEuclidean_fromVec Ψ‖ := by
  have hslice (c : C) :
      (fun o => (select M *ᵥ (liftFrame F *ᵥ Ψ) -
        liftFrame F *ᵥ (select V *ᵥ Ψ)) (c, o)) =
      M c *ᵥ (F *ᵥ (fun i => Ψ (c, i))) -
        F *ᵥ (V c *ᵥ (fun i => Ψ (c, i))) := by
    funext o
    simp only [Pi.sub_apply, select_mulVec, liftFrame_mulVec]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
  rw [joint_norm_sq, mul_pow, joint_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [hslice]
  simpa only [mul_pow] using!
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mpr (h c (fun i => Ψ (c, i)))

omit [DecidableEq O] [Fintype I] in

/-- Extending an isometric frame by the identity on a control register preserves the isometry
property. -/
theorem liftFrame_isometry (F : Matrix O I ℂ) (hF : IsIsometry F) :
    IsIsometry (liftFrame (C := C) F) := by
  change Fᴴ * F = 1 at hF
  change ((1 : Matrix C C ℂ) ⊗ₖ F)ᴴ * ((1 : Matrix C C ℂ) ⊗ₖ F) = 1
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hF, Matrix.one_mul, Matrix.one_kronecker_one]

end JointError

section EnabledError

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

/-- Embed a frame into the false enable-flag fiber. -/
noncomputable def enableFrame (R : Matrix W I ℂ) : Matrix (Bool × W) I ℂ :=
  matmul (encodingFiber (I := W) false) R

/-- A framed relative error bound remains valid after adding a false enable flag and
conditionally enabling the operation. -/
theorem enabled_full_output_error (b : Bool) (E : Matrix W W ℂ) (R : Matrix W I ℂ)
    (V : Matrix I I ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ ψ : QState I,
      ‖toEuclidean_fromVec (E *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ))‖ ≤
        δ * ‖toEuclidean_fromVec ψ‖) (ψ : QState I) :
    ‖toEuclidean_fromVec
      (enabledMatrix b E *ᵥ (enableFrame R *ᵥ ψ) -
        enableFrame R *ᵥ ((if b then V else 1) *ᵥ ψ))‖ ≤
      δ * ‖toEuclidean_fromVec ψ‖ := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    have hz : enabledMatrix false E *ᵥ (enableFrame R *ᵥ ψ) = enableFrame R *ᵥ ψ := by
      simp only [enableFrame, matmul, ← Matrix.mulVec_mulVec, enabledMatrix_apply,
        Bool.false_eq_true, if_false, Matrix.one_mulVec]
    rw [hz, Matrix.one_mulVec, sub_self]
    simp only [show toEuclidean_fromVec (0 : QState (Bool × W)) = 0 from rfl, norm_zero]
    exact mul_nonneg hδ (norm_nonneg _)
  · simp only [if_true]
    have hs : enabledMatrix true E *ᵥ (enableFrame R *ᵥ ψ) -
        enableFrame R *ᵥ (V *ᵥ ψ) =
        encodingFiber false *ᵥ (E *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ)) := by
      simp only [enableFrame, matmul, ← Matrix.mulVec_mulVec, enabledMatrix_apply,
        if_true, Matrix.mulVec_sub]
    rw [hs, isometry_mulVec_norm (encodingFiber_isIsometry false)]
    exact h ψ

end EnabledError

/-- The rational simulation time of a dyadic pulse, obtained by multiplying `τ` by its midpoint
coefficient. -/
def atomTime (q : ℕ) (τ : ℚ) (a : Option (Fin q)) : ℚ :=
  τ * DyadicClockPulses.midpointCoefficient q a

/-- The sum of the times of pulses enabled by a given binary clock label. -/
def activeTime {q : ℕ} (τ : ℚ) (as : List (Option (Fin q))) (x : Reg q) : ℚ :=
  (as.map (fun a => if DyadicClockPulses.axisEnabled a x then atomTime q τ a else 0)).sum

/-- Using all dyadic axes gives total active time equal to `τ` times the clock label's rational
midpoint. -/
theorem midpoint_activeTime (q : ℕ) (τ : ℚ) (x : Reg q) :
    activeTime τ (DyadicClockPulses.axes q) x =
      τ * Clock.rationalMidpoint (2 ^ q) (Clock.clockLabel q x) := by
  rw [activeTime, DyadicClockPulses.axes_sum]
  simp only [DyadicClockPulses.axisEnabled, atomTime, DyadicClockPulses.midpointCoefficient,
      if_true]
  have ht (i : Fin q) :
      (if x i then τ * ((2 : ℚ) ^ i.val / DyadicClockPulses.denominator q) else 0) =
      (τ / DyadicClockPulses.denominator q) * (if x i then (2 : ℚ) ^ i.val else 0) := by
    cases x i
    · simp
    · dsimp
      ring
  simp_rw [ht]
  rw [← Finset.mul_sum, ← DyadicClockPulses.raw_label_sum]
  simp only [Clock.rationalMidpoint, Nat.cast_pow, Nat.cast_ofNat]
  change τ * (1 / (2 * DyadicClockPulses.denominator q)) +
    (τ / DyadicClockPulses.denominator q) * ((Clock.clockLabel q x).val : ℚ) =
    τ * ((((Clock.clockLabel q x).val : ℚ) + 1 / 2) / DyadicClockPulses.denominator q)
  field_simp [(DyadicClockPulses.denominator_pos q).ne']
  ring

/-- The sum of absolute pulse times equals `|τ|*(1-1/(2*denominator q))`. -/
theorem midpoint_absolute_time (q : ℕ) (τ : ℚ) :
    ((DyadicClockPulses.axes q).map (fun a => |atomTime q τ a|)).sum =
      |τ| * (1 - 1 / (2 * DyadicClockPulses.denominator q)) := by
  have hc (a : Option (Fin q)) : 0 ≤ DyadicClockPulses.midpointCoefficient q a := by
    cases a <;> dsimp [DyadicClockPulses.midpointCoefficient,
        DyadicClockPulses.denominator] <;> positivity
  simp only [atomTime, abs_mul]
  simp_rw [abs_of_nonneg (hc _)]
  rw [List.sum_map_mul_left, DyadicClockPulses.axes_sum]
  simp only [DyadicClockPulses.midpointCoefficient]
  have hp : (∑ i : Fin q, (2 : ℚ) ^ i.val) = DyadicClockPulses.denominator q - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [DyadicClockPulses.denominator, show (2 : ℚ) - 1 = 1 by norm_num, mul_one]
      using! geom_sum_mul (2 : ℚ) q
  have ht (i : Fin q) : (2 : ℚ) ^ i.val / DyadicClockPulses.denominator q =
      (1 / DyadicClockPulses.denominator q) * (2 : ℚ) ^ i.val := by ring
  simp_rw [ht]
  rw [← Finset.mul_sum, hp]
  congr 1
  field_simp [(DyadicClockPulses.denominator_pos q).ne']
  ring

/-- The sum of absolute dyadic pulse times is at most `|τ|`. -/
theorem midpoint_absolute_time_le (q : ℕ) (τ : ℚ) :
    ((DyadicClockPulses.axes q).map (fun a => |atomTime q τ a|)).sum ≤ |τ| := by
  rw [midpoint_absolute_time]
  have hd := DyadicClockPulses.denominator_pos q
  have hh : 0 ≤ 1 / (2 * DyadicClockPulses.denominator q) := by positivity
  nlinarith [mul_nonneg (abs_nonneg τ) hh]

section Actual

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The oracle on the three-flag signal simulator register, with the specified controlled and
identity extensions of `U`. -/
noncomputable def signalOracle (U : Matrix H H ℂ) :
    Matrix (SimulatorSpace H) (SimulatorSpace H) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J := Bool) U))

/-- The signal oracle with an additional enable control and an untouched binary clock register. -/
noncomputable def nestedOracle (q : ℕ) (U : Matrix H H ℂ) :
    Matrix (Physical q H) (Physical q H) ℂ :=
  parallelOracle (J := Reg q) (controlOracle (signalOracle U))

/-- The simulator frame obtained by applying `scaleEightFrame` to the Hamiltonian frame of `F`. -/
noncomputable def simulatorFrame (F : Matrix H I ℂ) : Matrix (SimulatorSpace H) I ℂ :=
  scaleEightFrame (hamiltonianFrame F)

/-- Extend the simulator frame by a false enable flag and the clock identity to obtain the
common pulse frame. -/
noncomputable def commonFrame (q : ℕ) (F : Matrix H I ℂ) :
    Matrix (Physical q H) (Reg q × I) ℂ :=
  liftFrame (enableFrame (simulatorFrame F))

/-- The computed signal word for one dyadic pulse, guarded by that pulse's clock-enable
function. -/
noncomputable def atomWord (q : ℕ) (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (a : Option (Fin q)) : List (AdjointStep (Physical q H)) :=
  guardedWord (DyadicClockPulses.axisEnabled a) (computedSignalWord F (atomTime q τ a) k)

/-- Concatenate the guarded signal words for a list of dyadic pulse axes. -/
noncomputable def program (q : ℕ) (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) :
    List (Option (Fin q)) → List (AdjointStep (Physical q H))
  | [] => []
  | a :: as => atomWord q F τ k a ++ program q F τ k as

/-- The guarded signal program containing every dyadic midpoint pulse axis. -/
noncomputable def instructions (q : ℕ) (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) :
    List (AdjointStep (Physical q H)) := program q F τ k (DyadicClockPulses.axes q)

/-- The computed segment count multiplied by the per-segment query cost
`27*(4*computedSignalCutoff t k+1)`. -/
def queryCost (t : ℚ) (k : ℕ) : ℕ :=
  computedSignalSegments t * (27 * (4 * computedSignalCutoff t k + 1))

/-- The explicit gate cost of a guarded computed signal pulse, including its two guard toggles. -/
def macroCost (t : ℚ) (k : ℕ) : ℕ :=
  computedSignalSegments t * (27 * (4 * computedSignalCutoff t k + 6) + 79) + 2

/-- The clock-selected evolution for a single enabled dyadic pulse, with the identity on
disabled labels. -/
noncomputable def atomTarget (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ)
    (a : Option (Fin q)) : Matrix (Reg q × I) (Reg q × I) ℂ :=
  select (fun x => if DyadicClockPulses.axisEnabled a x then
    hamiltonianEvolution A (atomTime q τ a : ℝ) else 1)

/-- The clock-selected Hamiltonian evolution at the total active time of a pulse list. -/
noncomputable def target (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ)
    (as : List (Option (Fin q))) : Matrix (Reg q × I) (Reg q × I) ℂ :=
  select (fun x => hamiltonianEvolution A (activeTime τ as x : ℝ))

/-- The target for the empty pulse list is the identity matrix. -/
theorem target_nil (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ) : target q A τ [] = 1 := by
  simp [target, activeTime, parallel_select_one]

/-- The target for a leading pulse and a tail factors as the pulse target times the tail target. -/
theorem target_cons (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ)
    (a : Option (Fin q)) (as : List (Option (Fin q))) :
    target q A τ (a :: as) = atomTarget q A τ a * target q A τ as := by
  simp only [target, atomTarget, parallel_select_mul]
  congr 1
  funext x
  cases hx : DyadicClockPulses.axisEnabled a x
  · simp [activeTime, hx]
  · simp only [if_true]
    change HamiltonianEvolution A (activeTime τ (a :: as) x : ℝ) =
      HamiltonianEvolution A (atomTime q τ a : ℝ) *
        HamiltonianEvolution A (activeTime τ as x : ℝ)
    rw [← hamiltonianEvolution_add]
    congr 1
    simp [activeTime, hx]

/-- Every pulse-list target is unitary when the encoded matrix is Hermitian. -/
theorem target_unitary (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ)
    (as : List (Option (Fin q))) (hA : A.IsHermitian) :
    target q A τ as ∈ Matrix.unitaryGroup _ ℂ := by
  change select (fun x : Reg q => hamiltonianEvolution A (activeTime τ as x : ℝ)) ∈
    Matrix.unitaryGroup (Reg q × I) ℂ
  exact Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    (fun x : Reg q => hamiltonianEvolution A (activeTime τ as x : ℝ))
    (fun _ => hamiltonianEvolution_unitary hA _)

/-- The nested signal oracle is unitary when its underlying oracle `U` is unitary. -/
theorem nestedOracle_unitary (q : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : nestedOracle q U ∈ Matrix.unitaryGroup _ ℂ :=
  parallelOracle_unitary (controlOracle_unitary
    (tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary (parallelOracle_unitary hU))))

/-- The common clock and enable frame is an isometry for the stated projected unitary encoding. -/
theorem commonFrame_isometry (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (_hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    IsIsometry (commonFrame q F) := by
  have hR : IsIsometry (simulatorFrame F) :=
    scaleEightFrame_isometry (hamiltonianFrame F)
      (averageFrame_isIsometry (averageFrame_isIsometry h.right_isometry))
  exact liftFrame_isometry _ (Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul
    (encodingFiber_isIsometry false) hR)

/-- Each guarded pulse word is well formed and has query count `queryCost` and gate count
`macroCost` at its pulse time. -/
theorem atomWord_resources (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) (a : Option (Fin q))
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    WellFormedAdjointCircuit (atomWord q F τ k a) ∧
    adjointQueryCount (atomWord q F τ k a) = queryCost (atomTime q τ a) k ∧
    adjointGateCount (atomWord q F τ k a) = macroCost (atomTime q τ a) k := by
  obtain ⟨hw, hq, hg, _⟩ :=
    computed_signal_full_segmented_program_and_cost H I A U F (atomTime q τ a) k hA h
  refine ⟨guardedWord_wellFormed _ _ hw, ?_, ?_⟩
  · simpa only [atomWord, guardedWord_queryCount, queryCost] using! hq
  · simpa only [atomWord, guardedWord_gateCount, macroCost] using! congrArg (fun n => n + 2) hg

/-- A pulse program is well formed and its query and gate counts are the sums of the
corresponding pulse costs. -/
theorem program_resources (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) (as : List (Option (Fin q)))
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    WellFormedAdjointCircuit (program q F τ k as) ∧
    adjointQueryCount (program q F τ k as) = (as.map (fun a => queryCost (atomTime q τ a) k)).sum ∧
    adjointGateCount (program q F τ k as) = (as.map (fun a => macroCost (atomTime q τ a) k)).sum := by
  induction as with
  | nil => simp [program, WellFormedAdjointCircuit.nil, adjointQueryCount, adjointGateCount]
  | cons a as ih =>
    obtain ⟨hw, hq, hg⟩ := atomWord_resources q A U F τ k a hA h
    refine ⟨hw.append ih.1, ?_, ?_⟩
    · simp only [program, adjointQueryCount_append, hq, ih.2.1, List.map_cons, List.sum_cons]
    · simp only [program, adjointGateCount_append, hg, ih.2.2, List.map_cons, List.sum_cons]

/-- A single guarded pulse approximates its target on the common frame within `2⁻ᵏ` times the
input Euclidean norm. -/
theorem atomWord_full_output_error (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) (a : Option (Fin q))
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (Ψ : QState (Reg q × I)) :
    ‖toEuclidean_fromVec
      (evaluate (nestedOracle q U) (atomWord q F τ k a) *ᵥ (commonFrame q F *ᵥ Ψ) -
        commonFrame q F *ᵥ (atomTarget q A τ a *ᵥ Ψ))‖ ≤
      (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec Ψ‖ := by
  obtain ⟨_, _, _, he⟩ :=
    computed_signal_full_segmented_program_and_cost H I A U F (atomTime q τ a) k hA h
  change ‖toEuclidean_fromVec
    (evaluate (parallelOracle (J := Reg q) (controlOracle (signalOracle U)))
      (guardedWord (DyadicClockPulses.axisEnabled a) (computedSignalWord F (atomTime q τ a) k)) *ᵥ
        (liftFrame (enableFrame (simulatorFrame F)) *ᵥ Ψ) -
      liftFrame (enableFrame (simulatorFrame F)) *ᵥ (atomTarget q A τ a *ᵥ Ψ))‖ ≤ _
  rw [guardedWord_evaluate]
  apply selected_full_output_error _ _ _ _ (by positivity)
  intro x ψ
  exact enabled_full_output_error (DyadicClockPulses.axisEnabled a x) _ _ _ _ (by positivity) he ψ

end Actual

section Composition

variable {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- Two framed relative error bounds combine with error at most `ε+δ` when the first implemented
matrix and second target are unitary. -/
theorem compose_full_output_error (W E : Matrix O O ℂ) (R : Matrix O I ℂ)
    (V Z : Matrix I I ℂ) (δ ε : ℝ)
    (hW : W ∈ Matrix.unitaryGroup O ℂ) (hZ : Z ∈ Matrix.unitaryGroup I ℂ)
    (hfirst : ∀ ψ, ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ψ) - R *ᵥ (V *ᵥ ψ))‖ ≤
      δ * ‖toEuclidean_fromVec ψ‖)
    (hsecond : ∀ ψ, ‖toEuclidean_fromVec (E *ᵥ (R *ᵥ ψ) - R *ᵥ (Z *ᵥ ψ))‖ ≤
      ε * ‖toEuclidean_fromVec ψ‖) (ψ : QState I) :
    ‖toEuclidean_fromVec ((W * E) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V * Z) *ᵥ ψ))‖ ≤
      (ε + δ) * ‖toEuclidean_fromVec ψ‖ := by
  have hs : (W * E) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V * Z) *ᵥ ψ) =
      W *ᵥ (E *ᵥ (R *ᵥ ψ) - R *ᵥ (Z *ᵥ ψ)) +
        (W *ᵥ (R *ᵥ (Z *ᵥ ψ)) - R *ᵥ (V *ᵥ (Z *ᵥ ψ))) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel
  have hf := hfirst (Z *ᵥ ψ)
  rw [computed_signal_unitary_vector_norm hZ ψ] at hf
  rw [hs, computed_signal_wrap_add]
  calc
    _ ≤ ‖toEuclidean_fromVec (W *ᵥ (E *ᵥ (R *ᵥ ψ) - R *ᵥ (Z *ᵥ ψ)))‖ +
        ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ (Z *ᵥ ψ)) - R *ᵥ (V *ᵥ (Z *ᵥ ψ)))‖ :=
      norm_add_le _ _
    _ = ‖toEuclidean_fromVec (E *ᵥ (R *ᵥ ψ) - R *ᵥ (Z *ᵥ ψ))‖ +
        ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ (Z *ᵥ ψ)) - R *ᵥ (V *ᵥ (Z *ᵥ ψ)))‖ := by
      rw [computed_signal_unitary_vector_norm hW]
    _ ≤ ε * ‖toEuclidean_fromVec ψ‖ + δ * ‖toEuclidean_fromVec ψ‖ :=
      add_le_add (hsecond ψ) hf
    _ = _ := by ring

end Composition

section FullConsumer

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- A pulse program's framed output error is at most its list length times `2⁻ᵏ` times the input
Euclidean norm. -/
theorem program_full_output_error (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) (as : List (Option (Fin q)))
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (Ψ : QState (Reg q × I)) :
    ‖toEuclidean_fromVec
      (evaluate (nestedOracle q U) (program q F τ k as) *ᵥ (commonFrame q F *ᵥ Ψ) -
        commonFrame q F *ᵥ (target q A τ as *ᵥ Ψ))‖ ≤
      (as.length : ℝ) * (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec Ψ‖ := by
  induction as generalizing Ψ with
  | nil => simp [program, evaluate, target_nil, Matrix.one_mulVec, toEuclidean_fromVec]
  | cons a as ih =>
    rw [program, evaluate_append, target_cons]
    have hW := (atomWord_resources q A U F τ k a hA h).1.evaluate_unitary
      (nestedOracle_unitary q U h.unitary)
    have he := compose_full_output_error
      (evaluate (nestedOracle q U) (atomWord q F τ k a))
      (evaluate (nestedOracle q U) (program q F τ k as)) (commonFrame q F)
      (atomTarget q A τ a) (target q A τ as) ((1 / 2 : ℝ) ^ k)
      ((as.length : ℝ) * (1 / 2 : ℝ) ^ k) hW (target_unitary q A τ as hA)
      (atomWord_full_output_error q A U F τ k a hA h) ih Ψ
    calc
      _ ≤ ((as.length : ℝ) * (1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ k) *
          ‖toEuclidean_fromVec Ψ‖ := he
      _ = _ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- The target for all dyadic axes selects Hamiltonian evolution at `τ` times each clock label's
rational midpoint. -/
theorem target_midpoint (q : ℕ) (A : Matrix I I ℂ) (τ : ℚ) :
    target q A τ (DyadicClockPulses.axes q) =
      select (fun x : Reg q => hamiltonianEvolution A
        ((τ * Clock.rationalMidpoint (2 ^ q) (Clock.clockLabel q x) : ℚ) : ℝ)) := by
  unfold target
  congr 1
  funext x
  rw [midpoint_activeTime]

/-- The complete binary clock word approximates its midpoint target on the common frame within
`(q+1)*2⁻ᵏ` times the input norm. -/
theorem instructions_full_output_error (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (Ψ : QState (Reg q × I)) :
    ‖toEuclidean_fromVec
      (evaluate (nestedOracle q U) (instructions q F τ k) *ᵥ (commonFrame q F *ᵥ Ψ) -
        commonFrame q F *ᵥ
          (select (fun x : Reg q => hamiltonianEvolution A
            ((τ * Clock.rationalMidpoint (2 ^ q) (Clock.clockLabel q x) : ℚ) : ℝ)) *ᵥ Ψ))‖ ≤
      ((q + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec Ψ‖ := by
  simpa only [instructions, target_midpoint, DyadicClockPulses.axes_length] using!
    program_full_output_error q A U F τ k (DyadicClockPulses.axes q) hA h Ψ

/-- The complete binary clock word is well formed, with exact query and gate counts given by
sums of its dyadic pulse costs. -/
theorem instructions_resources (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    WellFormedAdjointCircuit (instructions q F τ k) ∧
    adjointQueryCount (instructions q F τ k) =
      ((DyadicClockPulses.axes q).map (fun a => queryCost (atomTime q τ a) k)).sum ∧
    adjointGateCount (instructions q F τ k) =
      ((DyadicClockPulses.axes q).map (fun a => macroCost (atomTime q τ a) k)).sum :=
  program_resources q A U F τ k (DyadicClockPulses.axes q) hA h

/-- The complete binary clock instruction word evaluates to a unitary matrix for the stated
Hermitian encoding. -/
theorem instructions_unitary (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    evaluate (nestedOracle q U) (instructions q F τ k) ∈ Matrix.unitaryGroup _ ℂ :=
  (instructions_resources q A U F τ k hA h).1.evaluate_unitary
    (nestedOracle_unitary q U h.unitary)

/-- The adjoint binary clock word is well formed and has the same dyadic query and gate sums as
the forward word. -/
theorem inverse_resources (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    WellFormedAdjointCircuit (adjointCircuit (instructions q F τ k)) ∧
    adjointQueryCount (adjointCircuit (instructions q F τ k)) =
      ((DyadicClockPulses.axes q).map (fun a => queryCost (atomTime q τ a) k)).sum ∧
    adjointGateCount (adjointCircuit (instructions q F τ k)) =
      ((DyadicClockPulses.axes q).map (fun a => macroCost (atomTime q τ a) k)).sum := by
  obtain ⟨hw, hq, hg⟩ := instructions_resources q A U F τ k hA h
  exact ⟨hw.adjointCircuit, (adjointQueryCount_adjointCircuit _).trans hq,
    (adjointGateCount_adjointCircuit _).trans hg⟩

/-- Evaluating the adjoint binary clock word gives the conjugate transpose of the forward
evaluation. -/
theorem inverse_evaluate (q : ℕ) (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (U : Matrix H H ℂ) :
    evaluate (nestedOracle q U) (adjointCircuit (instructions q F τ k)) =
      (evaluate (nestedOracle q U) (instructions q F τ k))ᴴ :=
  evaluate_adjointCircuit _ _

end FullConsumer

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
