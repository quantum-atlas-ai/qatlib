/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidPhysicalLaw

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Same-record physical receipts for every selected branch

The complete measured record determines its current, Bell or unused-copy
trace. Impossible tags have zero actual probability; every supported
execution requests exactly two copies and pays its native words, measured
cleanup, register width and measurement/reset bounds.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- Unused directions still request, fully measure and actually reset each of their two observed copies. -/
def discardedPhysicalTrace (n : ℕ) (z : Reg n × Reg n) : List (PairPhysicalAction n) :=
  [.supply,.measure (allPhysicalWires n) z.1,.cleanup (allPhysicalWires n) z.1,
    .supply,.measure (allPhysicalWires n) z.2,.cleanup (allPhysicalWires n) z.2]

/-- The discarded branch charges its real observed conditional native cleanup words. -/
theorem discardedPhysicalTrace_resources (n : ℕ) (z : Reg n × Reg n) :
    ((discardedPhysicalTrace n z).map PairPhysicalAction.copies).sum=2 ∧
    ((discardedPhysicalTrace n z).map PairPhysicalAction.queries).sum=0 ∧
    ((discardedPhysicalTrace n z).map PairPhysicalAction.gates).sum≤12*n ∧
    ((discardedPhysicalTrace n z).map PairPhysicalAction.measurements).sum=2*n ∧
    ((discardedPhysicalTrace n z).map PairPhysicalAction.resets).sum=2*n := by
  have h1 := measuredClearProgram_counts (allPhysicalWires n) z.1
  have h2 := measuredClearProgram_counts (allPhysicalWires n) z.2
  simp only [allPhysicalWires,List.length_ofFn] at h1 h2
  simp only [discardedPhysicalTrace,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    PairPhysicalAction.copies,PairPhysicalAction.queries,PairPhysicalAction.gates,
    PairPhysicalAction.measurements,PairPhysicalAction.resets,PairPhysicalAction.gateProgram,
    h1.2,h2.2,allPhysicalWires,List.length_ofFn,add_zero,zero_add]
  exact ⟨trivial,trivial,by omega,by omega,by omega⟩

/-- One conservative width accommodates both the unchanged current workspace and the fixed Bell storage slots. -/
def pairPhysicalWidth (d r : ℕ) : ℕ := d*r+3+(r-2)

/-- The actual selected native words pay their worst gate count plus every possible six-gate measured reset. -/
def pairPhysicalGateBudget (d r : ℕ) : ℕ :=
  max (2*(15*(r-1)^2+5)) 8+12*pairPhysicalWidth d r

/-- This predicate measures the supplied trace itself; it accepts no independent gate, query or copy certificates. -/
def pairTraceBudget (d r : ℕ) (t : (n : ℕ) × List (PairPhysicalAction n)) : Prop :=
  t.1≤pairPhysicalWidth d r ∧
  (t.2.map PairPhysicalAction.copies).sum=2 ∧
  (t.2.map PairPhysicalAction.queries).sum=0 ∧
  (t.2.map PairPhysicalAction.gates).sum≤pairPhysicalGateBudget d r ∧
  (t.2.map PairPhysicalAction.measurements).sum≤4*pairPhysicalWidth d r ∧
  (t.2.map PairPhysicalAction.resets).sum≤2*pairPhysicalWidth d r

/-- The current trace fits the common physical budget by its actual word counts. -/
theorem currentPhysicalTrace_budget (d r : ℕ) (j : Fin d) (hr : 2≤r)
    (z : CurrentObservation d r × CurrentObservation d r) :
    pairTraceBudget d r ⟨registerWidth d r,currentPhysicalTrace d r j z⟩ := by
  dsimp only [pairTraceBudget]
  rcases currentPhysicalTrace_resources d r j hr z with ⟨hc,hq,hg,hm,hs⟩
  have hw : registerWidth d r≤pairPhysicalWidth d r := by unfold registerWidth pairPhysicalWidth; omega
  have hmax := le_max_left (2*(15*(r-1)^2+5)) 8
  exact ⟨hw,hc,hq,by unfold pairPhysicalGateBudget; omega,by omega,by omega⟩

/-- The actual canonical Bell trace uses the same common worst budget on both matches and misses. -/
theorem canonicalBellPhysicalTrace_budget (d r : ℕ) (j : Fin d)
    (x y : PairGrid d r) (out : Reg 2) :
    pairTraceBudget d r ⟨d*r+3,canonicalBellPhysicalTrace d r j x y out⟩ := by
  dsimp only [pairTraceBudget]
  rcases canonicalBellPhysicalTrace_resources d r j x y out with ⟨hc,hq,hg,hm,hs⟩
  have hw : d*r+3≤pairPhysicalWidth d r := by unfold pairPhysicalWidth; omega
  have ht : (if y=pairDoubleShift d r j x then 2 else 0)≤2 := by split_ifs <;> omega
  have hmax := le_max_right (2*(15*(r-1)^2+5)) 8
  exact ⟨hw,hc,hq,by unfold pairPhysicalGateBudget; omega,by omega,by omega⟩

/-- The actual unused-copy readouts and cleanups fit the same budget. -/
theorem discardedPhysicalTrace_budget (d r : ℕ) (z : Reg (d*r+3) × Reg (d*r+3)) :
    pairTraceBudget d r ⟨d*r+3,discardedPhysicalTrace (d*r+3) z⟩ := by
  dsimp only [pairTraceBudget]
  rcases discardedPhysicalTrace_resources (d*r+3) z with ⟨hc,hq,hg,hm,hs⟩
  have hw : d*r+3≤pairPhysicalWidth d r := by unfold pairPhysicalWidth; omega
  exact ⟨hw,hc,hq,by unfold pairPhysicalGateBudget; omega,by omega,by omega⟩

/-- The actual outer branch and its full recorded outcomes determine the physical execution trace. Inconsistent tags have no execution. -/
def physicalPairSelectedTrace (d r : ℕ)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r) :
    Option ((n : ℕ) × List (PairPhysicalAction n)) :=
  if h : z.1.2.val<d then
    if z.1.1 then
      match z.2 with
      | .inr (.inl current) => some ⟨registerWidth d r,currentPhysicalTrace d r ⟨z.1.2.val,h⟩ current⟩
      | _ => none
    else
      match z.2 with
      | .inr (.inr bell) => some ⟨d*r+3,canonicalBellPhysicalTrace d r ⟨z.1.2.val,h⟩ bell.1 bell.2.1 bell.2.2⟩
      | _ => none
  else
    match z.2 with
    | .inl discarded => some ⟨d*r+3,discardedPhysicalTrace (d*r+3) discarded⟩
    | _ => none

/-- Every possible actual physical outcome has exactly its selected trace and the full paid worst-case budget, with no external resource premise. -/
theorem physicalPairLaw_selected_trace_budget (d r : ℕ) (hr : 2≤r)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r)
    (hp : (physicalPairLaw d r ψ hψ).prob z≠0) :
    ∃ t,physicalPairSelectedTrace d r z=some t ∧ pairTraceBudget d r t := by
  rcases z with ⟨⟨b,dir⟩,o⟩
  by_cases h : dir.val<d
  · cases b with
    | false =>
      cases o with
      | inl _ => simp [physicalPairLaw,physicalBranchLaw,h,physicalBellTaggedLaw] at hp
      | inr o => cases o with
        | inl _ => simp [physicalPairLaw,physicalBranchLaw,h,physicalBellTaggedLaw] at hp
        | inr bell =>
          exact ⟨_,by simp [physicalPairSelectedTrace,h],
            canonicalBellPhysicalTrace_budget d r ⟨dir.val,h⟩ bell.1 bell.2.1 bell.2.2⟩
    | true =>
      cases o with
      | inl _ => simp [physicalPairLaw,physicalBranchLaw,h,physicalCurrentTaggedLaw] at hp
      | inr o => cases o with
        | inl current =>
          exact ⟨_,by simp [physicalPairSelectedTrace,h],
            currentPhysicalTrace_budget d r ⟨dir.val,h⟩ hr current⟩
        | inr _ => simp [physicalPairLaw,physicalBranchLaw,h,physicalCurrentTaggedLaw] at hp
  · cases o with
    | inl discarded => exact ⟨_,by simp [physicalPairSelectedTrace,h],discardedPhysicalTrace_budget d r discarded⟩
    | inr _ => simp [physicalPairLaw,physicalBranchLaw,h,physicalDiscardTaggedLaw] at hp


open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Transfer fees inspect the actual native capture operation, including both mismatch captures. -/
def PairPhysicalAction.captureGates {n : ℕ} : PairPhysicalAction n → ℕ
  | .capture a b => GateCount (captureSwapProgram n a b)
  | _ => 0

/-- Test fees inspect the actual fixed-storage native Bell circuit. -/
def PairPhysicalAction.testGates {n : ℕ} : PairPhysicalAction n → ℕ
  | .bell a b matched => GateCount (physicalBellProgram a b matched)
  | _ => 0

/-- The current branch has no spin-storage transfer. -/
theorem currentPhysicalTrace_capture (d r : ℕ) (j : Fin d)
    (z : CurrentObservation d r × CurrentObservation d r) :
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.captureGates).sum=0 := rfl

/-- Current native CX gates are current measurements, not stored-pair Bell tests. -/
theorem currentPhysicalTrace_test (d r : ℕ) (j : Fin d)
    (z : CurrentObservation d r × CurrentObservation d r) :
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.testGates).sum=0 := rfl

/-- Unused copies are measured and reset without any spin transfer. -/
theorem discardedPhysicalTrace_capture (n : ℕ) (z : Reg n × Reg n) :
    ((discardedPhysicalTrace n z).map PairPhysicalAction.captureGates).sum=0 := rfl

/-- Unused copies perform no stored-pair Bell test. -/
theorem discardedPhysicalTrace_test (n : ℕ) (z : Reg n × Reg n) :
    ((discardedPhysicalTrace n z).map PairPhysicalAction.testGates).sum=0 := rfl

/-- Both native transfers cost six gates on every Bell trace, including an address miss. -/
theorem bellPhysicalTrace_capture {n : ℕ} (a b c : Fin n) (ws : List (Fin n))
    (x y : Reg n) (matched : Bool) (out : Reg 2) :
    ((bellPhysicalTrace a b c ws x y matched out).map PairPhysicalAction.captureGates).sum=6 := rfl

/-- The actual conditional native Bell test pays precisely its two-or-zero elementary gates. -/
theorem bellPhysicalTrace_test {n : ℕ} (a b c : Fin n) (ws : List (Fin n))
    (x y : Reg n) (matched : Bool) (out : Reg 2) :
    ((bellPhysicalTrace a b c ws x y matched out).map PairPhysicalAction.testGates).sum=
      GateCount (postCaptureProgram matched) := by
  cases matched <;> rfl

/-- A capture fee is read from the exact selected trace of the same complete physical outcome. -/
def physicalCaptureFee (d r : ℕ) (z : (Bool × Fin 4) × PhysicalPairObservation d r) : ℝ :=
  match physicalPairSelectedTrace d r z with
  | none => 0
  | some t => ((t.2.map PairPhysicalAction.captureGates).sum : ℝ)

/-- A test fee is read from the same selected native trace and its actual observed addresses. -/
def physicalTestFee (d r : ℕ) (z : (Bool × Fin 4) × PhysicalPairObservation d r) : ℝ :=
  match physicalPairSelectedTrace d r z with
  | none => 0
  | some t => ((t.2.map PairPhysicalAction.testGates).sum : ℝ)

/-- The statistical capture counter keeps only the selected active Bell tag, after all hidden cleanup details are retained physically. -/
def statisticalCaptureFee (d r : ℕ) (z : (Bool × Fin 4) × PairObservation.{0} d r) : ℝ :=
  if z.1.2.val<d then
    if z.1.1 then 0 else
      match z.2 with | .inr (.inr _) => 6 | _ => 0
  else 0

/-- The statistical test counter retains the original actual conditional native test program. -/
def statisticalTestFee (d r : ℕ) (z : (Bool × Fin 4) × PairObservation.{0} d r) : ℝ :=
  if h : z.1.2.val<d then
    if z.1.1 then 0 else
      match z.2 with
      | .inr (.inr bell) => (GateCount (postCaptureProgram (decide
          (bell.2.1=pairDoubleShift d r ⟨z.1.2.val,h⟩ bell.1))) : ℝ)
      | _ => 0
  else 0

/-- Coarsening unused classical details preserves the actual paid capture counter pointwise. -/
theorem physicalCaptureFee_coarsen (d r : ℕ)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r) :
    physicalCaptureFee d r z=statisticalCaptureFee d r
      (z.1,physicalPairObservationCoarsen d r z.2) := by
  rcases z with ⟨⟨b,dir⟩,o⟩
  by_cases h : dir.val<d
  · cases b <;> cases o with
    | inl _ => simp [physicalCaptureFee,physicalPairSelectedTrace,statisticalCaptureFee,h,physicalPairObservationCoarsen]
    | inr o => cases o <;>
      simp [physicalCaptureFee,physicalPairSelectedTrace,statisticalCaptureFee,h,physicalPairObservationCoarsen,
        currentPhysicalTrace_capture,canonicalBellPhysicalTrace,bellPhysicalTrace_capture]
  · cases o with
    | inl _ => simp [physicalCaptureFee,physicalPairSelectedTrace,statisticalCaptureFee,h,
        discardedPhysicalTrace_capture]
    | inr o => cases o <;>
      simp [physicalCaptureFee,physicalPairSelectedTrace,statisticalCaptureFee,h]

/-- The exact observed-address native test fee is preserved, including every zero-fee mismatch. -/
theorem physicalTestFee_coarsen (d r : ℕ)
    (z : (Bool × Fin 4) × PhysicalPairObservation d r) :
    physicalTestFee d r z=statisticalTestFee d r
      (z.1,physicalPairObservationCoarsen d r z.2) := by
  rcases z with ⟨⟨b,dir⟩,o⟩
  by_cases h : dir.val<d
  · cases b <;> cases o with
    | inl _ => simp [physicalTestFee,physicalPairSelectedTrace,statisticalTestFee,h,physicalPairObservationCoarsen]
    | inr o => cases o <;>
      simp [physicalTestFee,physicalPairSelectedTrace,statisticalTestFee,h,physicalPairObservationCoarsen,
        currentPhysicalTrace_test,canonicalBellPhysicalTrace,bellPhysicalTrace_test,factoryAddressMatch_eq]
  · cases o with
    | inl _ => simp [physicalTestFee,physicalPairSelectedTrace,statisticalTestFee,h,
        discardedPhysicalTrace_test]
    | inr o => cases o <;>
      simp [physicalTestFee,physicalPairSelectedTrace,statisticalTestFee,h]

/-- The active Bell alternative always pays both transfers, while current and padded directions pay none. -/
theorem statisticalCaptureFee_branch_mean (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (velocity : Bool) (dir : Fin 4) :
    (pairBranchLaw.{0} d r ψ hψ velocity dir).expect
      (fun o => statisticalCaptureFee d r ((velocity,dir),o)) =
      if dir.val<d then if velocity then 0 else 6 else 0 := by
  unfold pairBranchLaw
  by_cases h : dir.val<d
  · rw [dite_eq_left h]
    cases velocity with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [bellPairTaggedLaw_expect]
      simp only [statisticalCaptureFee,ite_eq_left h,Bool.false_eq_true,ite_false]
      unfold FinDist.expect
      rw [← Finset.sum_mul,FinDist.sum_one,one_mul]
    | true =>
      simp only [ite_true]
      rw [currentPairTaggedLaw_expect]
      simp [statisticalCaptureFee,h,FinDist.expect]
  · rw [dite_eq_right h,discardedPairLaw_expect]
    simp [statisticalCaptureFee,h]

/-- The matching probability and the same actual conditional native test give 2/M gates in each active Bell alternative. -/
theorem statisticalTestFee_branch_mean (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (velocity : Bool) (dir : Fin 4) :
    (pairBranchLaw.{0} d r ψ hψ velocity dir).expect
      (fun o => statisticalTestFee d r ((velocity,dir),o)) =
      if dir.val<d then if velocity then 0 else 2/(Fintype.card (PairGrid d r) : ℝ) else 0 := by
  unfold pairBranchLaw
  by_cases h : dir.val<d
  · rw [dite_eq_left h]
    cases velocity with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [bellPairTaggedLaw_expect]
      simpa [statisticalTestFee,h] using
        pairedBell_expected_test_gates ψ hψ (pairDoubleShift d r ⟨dir.val,h⟩)
    | true =>
      simp only [ite_true]
      rw [currentPairTaggedLaw_expect]
      simp [statisticalTestFee,h,FinDist.expect]
  · rw [dite_eq_right h,discardedPairLaw_expect]
    simp [statisticalTestFee,h]

/-- The actual complete-record protocol pays exactly 3d/4 expected capture CX gates, including all mismatches. -/
theorem physicalPairLaw_expected_capture_gates (d r : ℕ) (hd : d=2 ∨ d=3)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    (physicalPairLaw d r ψ hψ).expect (physicalCaptureFee d r)=3*(d : ℝ)/4 := by
  have he : (physicalPairLaw d r ψ hψ).expect (physicalCaptureFee d r)=
      (paidPairLaw.{0} d r ψ hψ).expect (statisticalCaptureFee d r) := by
    calc _ = (physicalPairLaw d r ψ hψ).expect
          (fun z => statisticalCaptureFee d r (z.1,physicalPairObservationCoarsen d r z.2)) := by
             unfold FinDist.expect
             apply Finset.sum_congr rfl
             intro z _
             rw [physicalCaptureFee_coarsen]
         _ = _ := physicalPairLaw_coarsen_expect d r ψ hψ (statisticalCaptureFee d r)
  rw [he,paidPairLaw_expect]
  simp_rw [statisticalCaptureFee_branch_mean]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,ite_self,
    Finset.sum_const_zero,zero_add]
  have hs : (∑ dir : Fin 4, if dir.val<d then (6 : ℝ) else 0)=∑ _ : Fin d,(6 : ℝ) := by
    simpa only [dite_eq_ite] using pair_padded_direction_sum d hd (fun _ => (6 : ℝ))
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The actual selected fixed-storage Bell word has expected fee d/(4M), separately from its always-paid captures. -/
theorem physicalPairLaw_expected_Bell_gates (d r : ℕ) (hd : d=2 ∨ d=3)
    (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1) :
    (physicalPairLaw d r ψ hψ).expect (physicalTestFee d r)=
      (d : ℝ)/(4*(paidGridSize d r : ℝ)) := by
  have he : (physicalPairLaw d r ψ hψ).expect (physicalTestFee d r)=
      (paidPairLaw.{0} d r ψ hψ).expect (statisticalTestFee d r) := by
    calc _ = (physicalPairLaw d r ψ hψ).expect
          (fun z => statisticalTestFee d r (z.1,physicalPairObservationCoarsen d r z.2)) := by
             unfold FinDist.expect
             apply Finset.sum_congr rfl
             intro z _
             rw [physicalTestFee_coarsen]
         _ = _ := physicalPairLaw_coarsen_expect d r ψ hψ (statisticalTestFee d r)
  rw [he,paidPairLaw_expect]
  simp_rw [statisticalTestFee_branch_mean]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,ite_self,
    Finset.sum_const_zero,zero_add]
  have hs : (∑ dir : Fin 4, if dir.val<d then 2/(Fintype.card (PairGrid d r) : ℝ) else 0)=
      ∑ _ : Fin d,2/(Fintype.card (PairGrid d r) : ℝ) := by
    simpa only [dite_eq_ite] using
      pair_padded_direction_sum d hd (fun _ => 2/(Fintype.card (PairGrid d r) : ℝ))
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,paidGridSize_card]
  ring


end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
