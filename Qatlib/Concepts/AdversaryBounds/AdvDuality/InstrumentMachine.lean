/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped ComplexOrder ENNReal

inductive InstrumentInstruction (D : ℕ) (C : Type*) where
  | halt (accepted : Bool)
  | gate (G : Operator D) (next : C)
  | query (next : C)
  | instrument (s : ℕ) (I : Instrument (Fin s) D D) (next : Fin s → C)

abbrev InstrumentMachine (D : ℕ) (C : Type*) := C → InstrumentInstruction D C

def instrumentMachineWellFormed {D : ℕ} {C : Type*} (M : InstrumentMachine D C) : Prop :=
  ∀ c, match M c with
    | .gate G _ => G ∈ Matrix.unitaryGroup (Fin D) ℂ
    | _ => True

structure InstrumentMachineEndpoint (C : Type*) where
  control : C
  halted : Bool

structure InstrumentMachineTrace (D : ℕ) (C : Type*) extends MixedBranchTrace D where
  endpoint : InstrumentMachineEndpoint C

noncomputable def instrumentMachineTraces {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) :
    ℕ → C → Operator D → List (InstrumentMachineTrace D C)
  | 0, c, rho => [⟨⟨rho, false, 0, 0, 0, []⟩, ⟨c, false⟩⟩]
  | T+1, c, rho => match M c with
    | .halt b => [⟨⟨rho, b, 0, 0, 0, []⟩, ⟨c, true⟩⟩]
    | .gate G next =>
        (instrumentMachineTraces M O T next (conjBranch G rho)).map fun t =>
          {t with gates := t.gates + 1}
    | .query next =>
        (instrumentMachineTraces M O T next (conjBranch O rho)).map fun t =>
          {t with queries := t.queries + 1}
    | .instrument s I next =>
        (List.ofFn fun o : Fin s =>
          (instrumentMachineTraces M O T (next o) (I.branch o rho)).map fun t =>
            {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s,o.val) :: t.outcomes}).flatten

noncomputable def instrumentMachineHaltMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    if t.endpoint.halted && event t.endpoint.control t.accepted t.outcomes then
      mixedMass t.toMixedBranchTrace else 0).sum

noncomputable def instrumentMachinePendingMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    if t.endpoint.halted then 0 else mixedMass t.toMixedBranchTrace).sum

noncomputable def instrumentMachineExpectedQueries {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) : ℝ :=
  ((instrumentMachineTraces M O T c rho).map fun t =>
    mixedMass t.toMixedBranchTrace * t.queries).sum

theorem instrumentMachineTraces_posSemidef {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (t : InstrumentMachineTrace D C)
    (ht : t ∈ instrumentMachineTraces M O T c rho) : t.state.PosSemidef := by
  induction T generalizing c rho t with
  | zero =>
    simp only [instrumentMachineTraces, List.mem_singleton] at ht
    subst t
    exact hrho
  | succ T ih =>
    cases h : M c with
    | halt b =>
      simp only [instrumentMachineTraces, h, List.mem_singleton] at ht
      subst t
      exact hrho
    | gate G next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho) u hu
    | query next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ ((completelyPositive_conjBranch O).positive hrho) u hu
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih (next o) _ ((I.cp o).positive hrho) u hu

theorem instrumentMachinePendingMass_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) : 0 ≤ instrumentMachinePendingMass M O T c rho := by
  unfold instrumentMachinePendingMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact le_rfl
  · exact (RCLike.nonneg_iff.mp
      (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1

theorem instrumentMachineExpectedQueries_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) : 0 ≤ instrumentMachineExpectedQueries M O T c rho := by
  unfold instrumentMachineExpectedQueries
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg ((RCLike.nonneg_iff.mp
    (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1)
    (Nat.cast_nonneg _)

theorem instrumentMachineTraces_total {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    ((instrumentMachineTraces M O T c rho).map fun t => mixedMass t.toMixedBranchTrace).sum =
      (trace rho).re := by
  induction T generalizing c rho with
  | zero => simp [instrumentMachineTraces, mixedMass]
  | succ T ih =>
    cases h : M c with
    | halt b => simp [instrumentMachineTraces, h, mixedMass]
    | gate G next =>
      have hG : G ∈ Matrix.unitaryGroup (Fin D) ℂ := by
        simpa [instrumentMachineWellFormed, h] using hM c
      simpa only [instrumentMachineTraces, h, List.map_map, Function.comp_def] using!
        (ih next (conjBranch G rho)).trans (congrArg Complex.re (trace_conjBranch_unitary G hG rho))
    | query next =>
      simpa only [instrumentMachineTraces, h, List.map_map, Function.comp_def] using!
        (ih next (conjBranch O rho)).trans (congrArg Complex.re (trace_conjBranch_unitary O hO rho))
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.map_flatten, List.sum_flatten,
        List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def]
      change (∑ o : Fin s, ((instrumentMachineTraces M O T (next o) (I.branch o rho)).map
        fun t => mixedMass t.toMixedBranchTrace).sum) = (trace rho).re
      simp_rw [ih]
      exact sum_instrumentProb I rho

theorem instrumentMachinePendingMass_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachinePendingMass M O (T+1) c rho = match M c with
      | .halt _ => 0
      | .gate G next => instrumentMachinePendingMass M O T next (conjBranch G rho)
      | .query next => instrumentMachinePendingMass M O T next (conjBranch O rho)
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachinePendingMass M O T (next o) (I.branch o rho) := by
  cases h : M c <;>
    simp [instrumentMachinePendingMass, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]

private theorem machine_sum_map_add {A : Type*} (xs : List A) (f g : A → ℝ) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]

theorem instrumentMachineExpectedQueries_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachineExpectedQueries M O (T+1) c rho = match M c with
      | .halt _ => 0
      | .gate G next => instrumentMachineExpectedQueries M O T next (conjBranch G rho)
      | .query next => (trace rho).re +
          instrumentMachineExpectedQueries M O T next (conjBranch O rho)
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachineExpectedQueries M O T (next o) (I.branch o rho) := by
  cases h : M c with
  | halt b => simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h]
  | gate G next =>
    simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h, Function.comp_def,
        mixedMass]
  | instrument s I next =>
    simp [instrumentMachineExpectedQueries, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]
  | query next =>
    simp only [instrumentMachineExpectedQueries, instrumentMachineTraces, h, List.map_map,
      Function.comp_def, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    rw [machine_sum_map_add]
    change instrumentMachineExpectedQueries M O T next (conjBranch O rho) +
      ((instrumentMachineTraces M O T next (conjBranch O rho)).map
        fun t => mixedMass t.toMixedBranchTrace).sum = _
    rw [instrumentMachineTraces_total M hM O hO, trace_conjBranch_unitary O hO]
    exact add_comm _ _

private theorem machine_sum_map_mono {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem instrumentMachinePendingMass_le_trace {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    instrumentMachinePendingMass M O T c rho ≤ (trace rho).re := by
  calc
    _ ≤ ((instrumentMachineTraces M O T c rho).map
        fun t => mixedMass t.toMixedBranchTrace).sum := by
      apply machine_sum_map_mono
      intro t ht
      split_ifs
      · exact (RCLike.nonneg_iff.mp
          (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
      · exact le_rfl
    _ = _ := instrumentMachineTraces_total M hM O hO T c rho

theorem instrumentMachineHaltMass_nonneg {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : C → Bool → List (ℕ×ℕ) → Bool) :
    0 ≤ instrumentMachineHaltMass M O T c rho event := by
  unfold instrumentMachineHaltMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (RCLike.nonneg_iff.mp
      (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
  · exact le_rfl

theorem instrumentMachineHaltMass_succ {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) :
    instrumentMachineHaltMass M O (T+1) c rho event = match M c with
      | .halt b => if event c b [] then (trace rho).re else 0
      | .gate G next => instrumentMachineHaltMass M O T next (conjBranch G rho) event
      | .query next => instrumentMachineHaltMass M O T next (conjBranch O rho) event
      | .instrument s I next => ∑ o : Fin s,
          instrumentMachineHaltMass M O T (next o) (I.branch o rho)
            (fun c b rec => event c b ((s,o.val)::rec)) := by
  cases h : M c <;>
    simp [instrumentMachineHaltMass, instrumentMachineTraces, h, Function.comp_def,
      List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn, mixedMass]

theorem instrumentMachineHaltMass_monotone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : C → Bool → List (ℕ×ℕ) → Bool) :
    Monotone (fun T => instrumentMachineHaltMass M O T c rho event) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing c rho event with
  | zero =>
    simpa only [instrumentMachineHaltMass, instrumentMachineTraces, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, add_zero] using instrumentMachineHaltMass_nonneg M O 1 c rho hrho event
  | succ T ih =>
    rw [instrumentMachineHaltMass_succ, instrumentMachineHaltMass_succ]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next => exact ih next _ ((completelyPositive_conjBranch G).positive hrho) event
    | query next => exact ih next _ ((completelyPositive_conjBranch O).positive hrho) event
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)
        (fun c b rec => event c b ((s,o.val)::rec))

theorem instrumentMachineHaltMass_add_pending {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (T : ℕ) (c : C) (rho : Operator D) :
    instrumentMachineHaltMass M O T c rho (fun _ _ _ => true) +
      instrumentMachinePendingMass M O T c rho = (trace rho).re := by
  unfold instrumentMachineHaltMass instrumentMachinePendingMass
  rw [← machine_sum_map_add]
  have hsum : ((instrumentMachineTraces M O T c rho).map fun t =>
      (if t.endpoint.halted && true then mixedMass t.toMixedBranchTrace else 0) +
      (if t.endpoint.halted then 0 else mixedMass t.toMixedBranchTrace)) =
      (instrumentMachineTraces M O T c rho).map (fun t => mixedMass t.toMixedBranchTrace) := by
    apply List.map_congr_left
    intro t ht
    cases h : t.endpoint.halted <;> simp [h]
  rw [hsum]
  exact instrumentMachineTraces_total M hM O hO T c rho

theorem instrumentMachinePendingMass_antitone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    Antitone (fun T => instrumentMachinePendingMass M O T c rho) := by
  apply antitone_nat_of_succ_le
  intro T
  induction T generalizing c rho with
  | zero =>
    simpa only [instrumentMachinePendingMass, instrumentMachineTraces,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Bool.false_eq_true,
      ↓reduceIte, add_zero, mixedMass] using
        instrumentMachinePendingMass_le_trace M hM O hO 1 c rho hrho
  | succ T ih =>
    rw [instrumentMachinePendingMass_succ, instrumentMachinePendingMass_succ]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next =>
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho)
    | query next =>
      exact ih next _ ((completelyPositive_conjBranch O).positive hrho)
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)

theorem instrumentMachineExpectedQueries_monotone {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (hM : instrumentMachineWellFormed M)
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : C) (rho : Operator D) (hrho : rho.PosSemidef) :
    Monotone (fun T => instrumentMachineExpectedQueries M O T c rho) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing c rho with
  | zero =>
    simpa only [instrumentMachineExpectedQueries, instrumentMachineTraces,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_zero,
      mul_zero, add_zero] using instrumentMachineExpectedQueries_nonneg M O 1 c rho hrho
  | succ T ih =>
    rw [instrumentMachineExpectedQueries_succ M hM O hO,
      instrumentMachineExpectedQueries_succ M hM O hO]
    cases h : M c with
    | halt b => exact le_rfl
    | gate G next =>
      exact ih next _ ((completelyPositive_conjBranch G).positive hrho)
    | query next =>
      exact add_le_add le_rfl (ih next _ ((completelyPositive_conjBranch O).positive hrho))
    | instrument s I next =>
      exact Finset.sum_le_sum fun o _ => ih (next o) _ ((I.cp o).positive hrho)

noncomputable def instrumentMachineInfiniteHaltMass {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D)
    (event : C → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineHaltMass M O T c rho event)

theorem instrumentMachineHaltMass_finite_approx {D : ℕ} {C J : Type*} [Fintype J]
    (M : InstrumentMachine D C) (O : J → Operator D) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (event : J → C → Bool → List (ℕ×ℕ) → Bool)
    (threshold : J → ℝ≥0∞)
    (hthreshold : ∀ j, threshold j < instrumentMachineInfiniteHaltMass M (O j) c rho (event j)) :
    ∃ T : ℕ, ∀ j, threshold j < ENNReal.ofReal (instrumentMachineHaltMass M (O j) T c rho (event j)) := by
  classical
  have hchoose (j : J) : ∃ T : ℕ, threshold j <
      ENNReal.ofReal (instrumentMachineHaltMass M (O j) T c rho (event j)) := by
    exact lt_iSup_iff.mp (hthreshold j)
  choose cutoff hcutoff using hchoose
  let T := Finset.univ.sup cutoff
  refine ⟨T, fun j => (hcutoff j).trans_le ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact instrumentMachineHaltMass_monotone M (O j) c rho hrho (event j)
    (Finset.le_sup (f := cutoff) (Finset.mem_univ j))

noncomputable def instrumentMachineInfiniteExpectedQueries {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D) : ℝ≥0∞ :=
  ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho)

theorem instrumentMachineExpectedQueries_le_infinite {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D) :
    ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho) ≤
      instrumentMachineInfiniteExpectedQueries M O c rho := by
  unfold instrumentMachineInfiniteExpectedQueries
  exact le_iSup (fun S => ENNReal.ofReal (instrumentMachineExpectedQueries M O S c rho)) T

theorem instrumentMachineInfiniteExpectedQueries_le_iff {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (c : C) (rho : Operator D) (Q : ℝ≥0∞) :
    instrumentMachineInfiniteExpectedQueries M O c rho ≤ Q ↔
      ∀ T : ℕ, ENNReal.ofReal (instrumentMachineExpectedQueries M O T c rho) ≤ Q :=
  iSup_le_iff

end Qatlib.Concepts.AdversaryBounds.AdvDuality
