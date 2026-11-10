/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCompilation
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
set_option maxRecDepth 100000 in
noncomputable section

theorem phase_observed_decoded_binary_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (hP : observedWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (ψ : QState ((Fin n × Fin q) × W)) (hψ : Normalized ψ)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2) (hc : Fintype.card Y=2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ observedEventMass (phaseOracle (W := W) (input x)) P ψ
      (fun t => decide (decode t.accepted t.outcomes = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (observedQueryDepth P : ℝ) * maxFilterNorm input Gamma := by
  obtain ⟨R,C,hC,hq,_,hstates⟩ := phase_observed_full_branch_purification P hP
  let ψ' := phaseHistoryInput (H := Fin (R+1)) (fun z => if z.2 = 0 then ψ z.1 else 0)
  let out := labelPovm (phaseObservedDecodedLabel P R decode)
  have hrun : IsBoundedErrorRun input f C ψ' out eps := by
    refine ⟨?_,phaseHistory_initial_normalized R ψ hψ,isPovm_labelPovm _,he0,he1,?_⟩
    · convert! hC using 1
    intro x
    have ht := phase_observed_decode_transport P R decode C (input x) ψ (f x)
      (hstates (input x) ψ).1 (hstates (input x) ψ).2
    exact ht.symm ▸ hsuccess x
  have hb := phase_povm_binary_query_lower_bound q n X (W × Fin (R+1) × Fin q) Y
    input f Gamma C ψ' out eps hG hz hrun hc
  simpa only [hq] using! hb
end
noncomputable section

theorem phase_observed_mixed_binary_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit (Fin d)) (hP : observedWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2) (hc : Fintype.card Y=2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ mixedObservedEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (observedQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  obtain ⟨psi,hpsi,hmarginal⟩ := density_purification_normalized rho hrho
  let Q := relabelObserved (phaseKrausLayout (s := d) e) (liftObservedEnvironment (E := Fin d) P)
  let psi0 := relabelState (phaseKrausLayout (s := d) e) psi
  have hQ : observedWellFormed Q := relabelObserved_wellFormed _ _
    (liftObservedEnvironment_wellFormed P hP)
  have hs (x : X) : 1-eps ≤ observedEventMass (phaseOracle (W := W × Fin d) (input x)) Q psi0
      (fun t => decide (decode t.accepted t.outcomes = f x)) := by
    have hp := observed_purification_event (phaseKrausOracle e (input x)) P psi
      (fun b rec => decide (decode b rec = f x))
    have hl := relabelObserved_event (phaseKrausLayout (s := d) e)
      (TensorGate (phaseKrausOracle e (input x)) (1 : Operator d))
      (liftObservedEnvironment (E := Fin d) P) psi (fun b rec => decide (decode b rec = f x))
    rw [phaseKrausOracle_extend] at hl
    rw [hmarginal] at hp
    exact (hl.trans hp).symm ▸ hsuccess x
  let D0 : DecidableEq ((Fin n × Fin q) × (W × Fin d)) := inferInstance
  have hs' (D : DecidableEq ((Fin n × Fin q) × (W × Fin d))) :
      ∀ x, 1-eps ≤ @observedEventMass ((Fin n × Fin q) × (W × Fin d)) _ D
        (phaseOracle (W := W × Fin d) (input x)) Q psi0
        (fun t => decide (decode t.accepted t.outcomes = f x)) := by
    have hD : D = D0 := Subsingleton.elim _ _
    rw [hD]
    exact hs
  have hb := phase_observed_decoded_binary_query_lower_bound input f Gamma Q
    (by convert! hQ using 1) decode psi0 (normalized_relabelState _ hpsi) eps he0 he1 hc hG hz (hs' _)
  have hq : observedQueryDepth Q = observedQueryBudget P := by
    rw [observedQueryDepth_eq_budget,relabelObserved_budget,liftObservedEnvironment_budget]
  simpa only [hq] using! hb
end
noncomputable section

theorem phase_kraus_mixed_binary_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2) (hc : Fintype.card Y=2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ krausCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (krausCircuitBudget P : ℝ) * maxFilterNorm input Gamma := by
  let flat : (Fin d × Fin s) ≃ Fin (d*s) := finProdFinEquiv
  let Q := relabelObserved flat (compileKrausCircuit zero P hP)
  let rho0 := relabelGate flat (TensorGate rho (outerProduct (Ket zero)))
  have hk := outerProduct_density (normalized_ket zero)
  have hrho0 : IsDensityOperator rho0 := by
    refine ⟨(Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hrho.1 hk.1).submatrix flat.symm,?_⟩
    change Matrix.trace
        ((TensorGate rho (outerProduct (Ket zero))).submatrix flat.symm flat.symm) = 1
    rw [Matrix.trace_submatrix,Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate,hrho.2,hk.2,mul_one]
  have hQ : observedWellFormed Q := relabelObserved_wellFormed flat _
    (compileKrausCircuit_wellFormed zero P hP)
  have hs (x : X) : 1-eps ≤ mixedObservedEventMass
      (phaseKrausOracle (phaseKrausFlatLayout (s := s) e) (input x)) Q rho0
      (fun b rec => decide (decode b rec = f x)) := by
    rw [phaseKrausFlatOracle]
    exact (kraus_compiled_event flat zero (phaseKrausOracle e (input x)) P hP rho
      (fun b rec => decide (decode b rec = f x))).symm ▸ hsuccess x
  have hb := phase_observed_mixed_binary_query_lower_bound (phaseKrausFlatLayout (s := s) e)
    input f Gamma Q hQ decode rho0 hrho0 eps he0 he1 hc hG hz hs
  have hq : observedQueryBudget Q = krausCircuitBudget P := by
    rw [relabelObserved_budget,compileKrausCircuit_budget]
  simpa only [hq] using! hb
end
noncomputable section

theorem phase_instrument_mixed_binary_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2) (hc : Fintype.card Y=2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (instrumentCircuitQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  let V := compileInstrumentCircuit P
  let S := variableKrausWidth V + 1
  have hfit : variableKrausFits S V := variableKraus_fits_of_width_le V S (Nat.le_add_right _ _)
  have hK := padVariableKraus_wellFormed V S hfit (compileInstrumentCircuit_wellFormed P hP)
  let decK := fun b rec => decode b (restoreInstrumentRecord P (restoreVariableKrausRecord V rec))
  have hs (x : X) : 1-eps ≤ krausCircuitEventMass (phaseKrausOracle e (input x))
      (padVariableKraus S V) rho (fun b rec => decide (decK b rec = f x)) := by
    have hp := variableKraus_padding_event (phaseKrausOracle e (input x)) V S hfit rho
      (fun b rec => decide (decode b (restoreInstrumentRecord P rec) = f x))
    have hi := instrumentCircuit_compile_event (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))
    exact (hp.trans hi).symm ▸ hsuccess x
  have hb := phase_kraus_mixed_binary_query_lower_bound e (0 : Fin S) input f Gamma
    (padVariableKraus S V) hK decK rho hrho eps he0 he1 hc hG hz hs
  have hq : krausCircuitBudget (padVariableKraus S V) ≤ instrumentCircuitQueryBudget P := by
    rw [padVariableKraus_budget V S hfit]
    exact instrument_compile_budget_le P
  have hqr : (krausCircuitBudget (padVariableKraus S V) : ℝ) ≤ instrumentCircuitQueryBudget P :=
    Nat.cast_le.mpr hq
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end
noncomputable section

theorem phase_instrument_mixed_binary_value_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2) (hc : Fintype.card Y=2)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    ENNReal.ofReal ((1-2*Real.sqrt (eps*(1-eps)))/2) * advPmValue input f ≤
      (instrumentCircuitQueryBudget P : ℝ≥0∞) := by
  exact adversary_value_of_multiplicative_bound input f _ _ (fun Gamma hG hz =>
    phase_instrument_mixed_binary_query_lower_bound e input f Gamma P hP decode rho hrho eps he0 he1 hc hG hz hsuccess)
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
set_option maxRecDepth 100000 in
variable {n q d : ℕ} [NeZero q] {W : Type} [Fintype W]
noncomputable section

def instrumentMachineOutputDecoder {C Y : Type} (M : InstrumentMachine d C) (T : ℕ) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (b : Bool) (rec : List (ℕ×ℕ)) : Y :=
  match instrumentMachineReplay M T c rec with
  | none => decode c false []
  | some e => if e.halted then decode e.control b rec else decode c false []
end
noncomputable section

theorem source_event_sum_mono {A : Type} (xs : List A) (f g : A → ℝ)
    (h : ∀ x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
end
noncomputable section

theorem instrumentMachineHaltMass_le_decoded_unroll {C Y : Type} [DecidableEq Y]
    (M : InstrumentMachine d C) (O : Operator d) (T : ℕ) (c : C) (rho : Operator d)
    (hrho : rho.PosSemidef) (decode : C → Bool → List (ℕ×ℕ) → Y) (y : Y) :
    instrumentMachineHaltMass M O T c rho (fun c b rec => decide (decode c b rec=y))≤
      instrumentCircuitEventMass O (unrollInstrumentMachine M T c) rho
        (fun b rec => decide (instrumentMachineOutputDecoder M T c decode b rec=y)) := by
  unfold instrumentMachineHaltMass instrumentCircuitEventMass
  rw [← unrollInstrumentMachine_traces M O T c rho]
  simp only [List.map_map,Function.comp_def]
  apply source_event_sum_mono
  intro t ht
  have hn : 0≤ mixedMass t.toMixedBranchTrace :=
    (RCLike.nonneg_iff.mp (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
  simp only [instrumentMachineOutputDecoder,instrumentMachineReplay_correct M O T c rho t ht]
  cases hh : t.endpoint.halted
  · simp only [Bool.false_and,Bool.false_eq_true,if_false]
    split_ifs
    · exact hn
    · exact le_rfl
  · simp only [Bool.true_and,if_true]
    exact le_rfl
end
noncomputable section
omit [Fintype W] in

theorem phase_machine_finite_approx
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps delta Q : ℝ) (he : eps<1) (hd : 0< delta) (hQ : 0≤ Q)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps)≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)))
    (hqueries : ∀ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ ENNReal.ofReal Q) :
    ∃ T : ℕ,instrumentCircuitWellFormed (unrollInstrumentMachine M T c) ∧
      (∀ x,1-(eps+delta)≤ instrumentCircuitEventMass (phaseKrausOracle e (input x))
        (unrollInstrumentMachine M T c) rho
        (fun b rec => decide (instrumentMachineOutputDecoder M T c decode b rec=f x))) ∧
      (∀ x,instrumentCircuitExpectedQueries (phaseKrausOracle e (input x))
        (unrollInstrumentMachine M T c) rho≤ Q) := by
  have hpos : 0<1-eps := by linarith
  have hth (x : X) : ENNReal.ofReal (1-(eps+delta))< instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)) :=
    ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)).trans_le (hsuccess x)
  obtain ⟨T,hT⟩ := instrumentMachineHaltMass_finite_approx M
    (fun x => phaseKrausOracle e (input x)) c rho hrho.1
    (fun x c b rec => decide (decode c b rec=f x)) (fun _ => ENNReal.ofReal (1-(eps+delta))) hth
  refine ⟨T,unrollInstrumentMachine_wellFormed M hM T c,?_,?_⟩
  · intro x
    have hp : 1-(eps+delta)< instrumentMachineHaltMass M (phaseKrausOracle e (input x)) T c rho
        (fun c b rec => decide (decode c b rec=f x)) := (ENNReal.ofReal_lt_ofReal_iff'.mp (hT x)).1
    exact hp.le.trans (instrumentMachineHaltMass_le_decoded_unroll M _ T c rho hrho.1 decode (f x))
  · intro x
    rw [unrollInstrumentMachine_expected]
    exact (ENNReal.ofReal_le_ofReal_iff hQ).mp
      ((instrumentMachineExpectedQueries_le_infinite M _ T c rho).trans (hqueries x))
end
noncomputable section

theorem phase_machine_small_error_expected_lower_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (G : Matrix X X ℂ)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps Q : ℝ) (he0 : 0≤ eps) (he : eps≤1/32) (hQ : 0≤ Q)
    (hG : G.IsHermitian) (hz : ∀ x y,f x=f y → G x y=0)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps)≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)))
    (hqueries : ∀ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ ENNReal.ofReal Q) :
    ‖G‖≤512*Q*maxFilterNorm input G := by
  obtain ⟨T,hT,hS,hE⟩ := phase_machine_finite_approx e input f M hM c decode rho hrho eps (1/32) Q
    (by linarith) (by norm_num) hQ hsuccess hqueries
  exact phase_instrument_small_error_expected_lower_bound e input f G (unrollInstrumentMachine M T c)
    hT (instrumentMachineOutputDecoder M T c decode) rho hrho (eps+1/32) Q
    (by linarith) (by linarith) hQ hG hz hS hE
end
noncomputable section

theorem phase_machine_small_error_expected_value_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps Q : ℝ) (he0 : 0≤ eps) (he : eps≤1/32) (hQ : 0≤ Q)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps)≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)))
    (hqueries : ∀ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ ENNReal.ofReal Q) :
    advPmValue input f≤ ENNReal.ofReal (512*Q) := by
  obtain ⟨T,hT,hS,hE⟩ := phase_machine_finite_approx e input f M hM c decode rho hrho eps (1/32) Q
    (by linarith) (by norm_num) hQ hsuccess hqueries
  exact phase_instrument_small_error_expected_value_bound e input f (unrollInstrumentMachine M T c)
    hT (instrumentMachineOutputDecoder M T c decode) rho hrho (eps+1/32) Q
    (by linarith) (by linarith) hQ hS hE
end
noncomputable section

theorem phase_instrument_expected_binary_truncation_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps T : ℝ) (he0 : 0 ≤ eps) (hc : Fintype.card Y=2) (hT : 0 ≤ T)
    (K : ℕ) (hdelta : eps + T/(K+1 : ℕ) ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    (1-2*Real.sqrt ((eps+T/(K+1 : ℕ))*(1-(eps+T/(K+1 : ℕ))))) * ‖Gamma‖ ≤
      2 * (K : ℝ) * maxFilterNorm input Gamma := by
  let delta := eps + T/(K+1 : ℕ)
  have hd0 : 0 ≤ delta := add_nonneg he0 (div_nonneg hT (Nat.cast_nonneg _))
  have hs (x : X) : 1-delta ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x))
      (truncateInstrumentQueries P K) rho (fun b rec => decide (decode b rec = f x)) := by
    have hl := instrument_event_sub_expected_le_truncate (phaseKrausOracle e (input x)) P rho hrho.1 K
      (fun b rec => decide (decode b rec = f x))
    have he := div_le_div_of_nonneg_right (hexpected x) (show (0 : ℝ) ≤ (K+1 : ℕ) by positivity)
    have hsuccessx := hsuccess x
    dsimp only [delta]
    linarith
  have hb := phase_instrument_mixed_binary_query_lower_bound e input f Gamma (truncateInstrumentQueries P K)
    (truncateInstrumentQueries_legal P hP K) decode rho hrho delta hd0 hdelta hc hG hz hs
  have hkr : (instrumentCircuitQueryBudget (truncateInstrumentQueries P K) : ℝ) ≤ K :=
    Nat.cast_le.mpr (truncateInstrumentQueries_budget P K)
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end
noncomputable section

theorem binary_unbounded_progress_pos (eps : ℝ) (he0 : 0≤eps) (he : eps<1/2) :
    0<((1/2-eps)/4)*(1-2*Real.sqrt (((eps+1/2)/2)*(1-(eps+1/2)/2))) := by
  have hη : (eps+1/2)/2<1/2 := by linarith
  have hp : 0<(1/2-eps)/4 := by linarith
  have hη0 : 0≤(eps+1/2)/2 := by linarith
  have hprod : 0≤((eps+1/2)/2)*(1-(eps+1/2)/2) := mul_nonneg hη0 (by linarith)
  have hs : Real.sqrt (((eps+1/2)/2)*(1-(eps+1/2)/2))<1/2 := by
    have hsq := Real.sq_sqrt hprod
    have hn := Real.sqrt_nonneg (((eps+1/2)/2)*(1-(eps+1/2)/2))
    nlinarith [sq_pos_of_pos (sub_pos.mpr hη)]
  exact mul_pos hp (by linarith)
end
noncomputable section

theorem phase_machine_binary_expected_lower_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (G : Matrix X X ℂ)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps Q : ℝ) (he0 : 0≤eps) (he : eps<1/2) (hQ : 0≤Q) (hcard : Fintype.card Y=2)
    (hG : G.IsHermitian) (hz : ∀ x y,f x=f y → G x y=0)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps) ≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)))
    (hqueries : ∀ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ENNReal.ofReal Q) :
    (((1/2-eps)/4)*(1-2*Real.sqrt (((eps+1/2)/2)*(1-(eps+1/2)/2))))*‖G‖≤2*Q*maxFilterNorm input G := by
  let delta : ℝ := (1/2-eps)/4
  let eta : ℝ := (eps+1/2)/2
  have hd : 0<delta := by dsimp [delta]; linarith
  have hη : eta<1/2 := by dsimp [eta]; linarith
  have heq : eps+2*delta=eta := by dsimp [delta,eta]; ring
  obtain ⟨T,hT,hS,hE⟩ := phase_machine_finite_approx e input f M hM c decode rho hrho eps delta Q
    (by linarith) hd hQ hsuccess hqueries
  let K := Nat.floor (Q/delta)
  have hfloor : (K : ℝ)≤Q/delta := Nat.floor_le (div_nonneg hQ hd.le)
  have hfloor' : Q/delta<(K : ℝ)+1 := Nat.lt_floor_add_one (Q/delta)
  have hden : (0 : ℝ)<(K+1 : ℕ) := by positivity
  have htail : Q/(K+1 : ℕ)≤delta := by
    apply (div_le_iff₀ hden).mpr
    have hh := (div_lt_iff₀ hd).mp hfloor'
    push_cast
    nlinarith
  let z : ℝ := eps+delta+Q/(K+1 : ℕ)
  have hz0 : 0≤z := by dsimp [z]; positivity
  have hzη : z≤eta := by dsimp only [z]; linarith
  have hprod : z*(1-z)≤eta*(1-eta) := by
    have hh : 0≤(eta-z)*(1-eta-z) := mul_nonneg (sub_nonneg.mpr hzη) (by linarith)
    nlinarith
  have hroot := Real.sqrt_le_sqrt hprod
  have hcoef : 1-2*Real.sqrt (eta*(1-eta))≤1-2*Real.sqrt (z*(1-z)) := by linarith
  have hb := phase_instrument_expected_binary_truncation_bound e input f G
    (unrollInstrumentMachine M T c) hT (instrumentMachineOutputDecoder M T c decode) rho hrho
    (eps+delta) Q (add_nonneg he0 hd.le) hcard hQ K (by dsimp only [z] at hzη; linarith) hG hz hS hE
  have hh : (1-2*Real.sqrt (eta*(1-eta)))*‖G‖≤2*(K : ℝ)*maxFilterNorm input G :=
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg G)).trans hb
  have hKQ : delta*(K : ℝ)≤Q := by
    have hk := (le_div_iff₀ hd).mp hfloor
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hh hd.le
  have hcap := mul_le_mul_of_nonneg_right hKQ (maxFilterNorm_nonneg input G)
  change (delta*(1-2*Real.sqrt (eta*(1-eta))))*‖G‖≤2*Q*maxFilterNorm input G
  nlinarith
end
noncomputable section

theorem adversary_value_of_real_multiplicative_bound
    {X Y : Type} [Fintype X] [DecidableEq X] {n q : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y) (a : ℝ) (Q : ℝ)
    (hall : ∀ G : Matrix X X ℂ, G.IsHermitian → (∀ x y, f x = f y → G x y = 0) →
      a * ‖G‖ ≤ 2 * Q * maxFilterNorm input G) :
    ENNReal.ofReal (a / 2) * advPmValue input f ≤ ENNReal.ofReal Q := by
  by_cases ha : 0 < a
  · unfold advPmValue
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro G
    have hnorm : 0 < ‖G.val‖ := norm_pos_iff.mpr G.property.2.2
    have h := hall G.val G.property.1 G.property.2.1
    have hm : 0 < maxFilterNorm input G.val := by
      by_contra hh
      have hz := le_antisymm (not_lt.mp hh) (maxFilterNorm_nonneg input G.val)
      rw [hz, mul_zero] at h
      exact (not_le_of_gt (mul_pos ha hnorm)) h
    have hr : (a / 2) * (‖G.val‖ / maxFilterNorm input G.val) ≤ Q := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2 * maxFilterNorm input G.val by positivity)).mp
      calc
        _ = a * ‖G.val‖ := by field_simp
        _ ≤ 2 * (Q : ℝ) * maxFilterNorm input G.val := h
        _ = _ := by ring
    rw [advPmWitnessValue, ← ENNReal.ofReal_div_of_pos hm,
        ← ENNReal.ofReal_mul (le_of_lt (div_pos ha (by norm_num)))]
    exact ENNReal.ofReal_le_ofReal hr
  · rw [ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg (not_lt.mp ha) (by norm_num)), zero_mul]
    exact bot_le
end
noncomputable section

theorem phase_machine_binary_expected_value_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps Q : ℝ) (he0 : 0≤eps) (he : eps<1/2) (hQ : 0≤Q) (hcard : Fintype.card Y=2)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps) ≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x)))
    (hqueries : ∀ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ENNReal.ofReal Q) :
    ENNReal.ofReal ((((1/2-eps)/4)*(1-2*Real.sqrt (((eps+1/2)/2)*(1-(eps+1/2)/2))))/2)*advPmValue input f≤ENNReal.ofReal Q := by
  exact adversary_value_of_real_multiplicative_bound input f _ Q (fun G hG hz =>
    phase_machine_binary_expected_lower_bound e input f G M hM c decode rho hrho eps Q he0 he hQ hcard hG hz hsuccess hqueries)
end
noncomputable section

theorem phase_machine_small_error_actual_expected_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps : ℝ) (he0 : 0≤eps) (he : eps≤1/32)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps) ≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x))) :
    advPmValue input f≤(512 : ℝ≥0∞)*⨆ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho := by
  let Q : ℝ≥0∞ :=
      ⨆ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho
  change advPmValue input f≤512*Q
  by_cases hQ : Q=⊤
  · rw [hQ,ENNReal.mul_top (by norm_num : (512 : ℝ≥0∞)≠0)]
    exact le_top
  have hqueries (x : X) : instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ENNReal.ofReal Q.toReal := by
    rw [ENNReal.ofReal_toReal hQ]
    exact le_iSup
        (fun x => instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho) x
  have hb := phase_machine_small_error_expected_value_bound e input f M hM c decode rho hrho eps Q.toReal
    he0 he ENNReal.toReal_nonneg hsuccess hqueries
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤512),ENNReal.ofReal_toReal hQ] at hb
  simpa using! hb
end
noncomputable section

theorem phase_machine_binary_actual_expected_bound
    {X Y C : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (M : InstrumentMachine d C) (hM : instrumentMachineWellFormed M) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → Y) (rho : Operator d) (hrho : IsDensityOperator rho)
    (eps : ℝ) (he0 : 0≤eps) (he : eps<1/2) (hcard : Fintype.card Y=2)
    (hsuccess : ∀ x,ENNReal.ofReal (1-eps) ≤ instrumentMachineInfiniteHaltMass M
      (phaseKrausOracle e (input x)) c rho (fun c b rec => decide (decode c b rec=f x))) :
    ENNReal.ofReal ((((1/2-eps)/4)*(1-2*Real.sqrt (((eps+1/2)/2)*(1-(eps+1/2)/2))))/2)*advPmValue input f≤
      ⨆ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho := by
  let Q : ℝ≥0∞ :=
      ⨆ x,instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho
  change _≤Q
  by_cases hQ : Q=⊤
  · rw [hQ]
    exact le_top
  have hqueries (x : X) : instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho≤ENNReal.ofReal Q.toReal := by
    rw [ENNReal.ofReal_toReal hQ]
    exact le_iSup
        (fun x => instrumentMachineInfiniteExpectedQueries M (phaseKrausOracle e (input x)) c rho) x
  have hb := phase_machine_binary_expected_value_bound e input f M hM c decode rho hrho eps Q.toReal
    he0 he ENNReal.toReal_nonneg hcard hsuccess hqueries
  rwa [ENNReal.ofReal_toReal hQ] at hb
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
