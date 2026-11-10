/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceEmbedding
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit
import Qatlib.Concepts.Execution.WorkspaceCP.InstrumentIsometryPadding
import Mathlib.Logic.Equiv.Fin.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.WorkspaceCP

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical ComplexOrder

structure WorkspaceTrace (d : ℕ) where
  width : ℕ
  state : Operator (d*width)
  accepted : Bool
  queries : ℕ
  outcomes : List (ℕ×ℕ)

inductive WorkspaceCircuit (d : ℕ) : ℕ → Type where
  | halt {k : ℕ} (accepted : Bool) : WorkspaceCircuit d k
  | gate {k : ℕ} (G : Operator (d*k)) (next : WorkspaceCircuit d k) : WorkspaceCircuit d k
  | query {k : ℕ} (next : WorkspaceCircuit d k) : WorkspaceCircuit d k
  | instrument {k : ℕ} (s l : ℕ) (I : Instrument (Fin s) (d*k) (d*l))
      (next : Fin s → WorkspaceCircuit d l) : WorkspaceCircuit d k

def workspaceCircuitWellFormed {d : ℕ} : {k : ℕ} → WorkspaceCircuit d k → Prop
  | _, .halt _ => True
  | _, .gate G next => G ∈ Matrix.unitaryGroup _ ℂ ∧ workspaceCircuitWellFormed next
  | _, .query next => workspaceCircuitWellFormed next
  | _, .instrument _ _ _ next => ∀ o, workspaceCircuitWellFormed (next o)

noncomputable def workspaceTraces {d : ℕ} (U : Operator d) :
    {k : ℕ} → WorkspaceCircuit d k → Operator (d*k) → List (WorkspaceTrace d)
  | k, .halt b, rho => [⟨k, rho, b, 0, []⟩]
  | _, .gate G next, rho => workspaceTraces U next (conjBranch G rho)
  | k, .query next, rho =>
      (workspaceTraces U next (conjBranch (forwardWorkspaceOracle k U) rho)).map fun t =>
        {t with queries := t.queries+1}
  | _, .instrument s _ I next, rho =>
      (List.ofFn fun o : Fin s => (workspaceTraces U (next o) (I.branch o rho)).map fun t =>
        {t with outcomes := (s,o.val)::t.outcomes}).flatten

noncomputable def workspaceMass {d : ℕ} (t : WorkspaceTrace d) : ℝ :=
  (trace t.state).re

noncomputable def workspaceCircuitStatistic {d k : ℕ} (U : Operator d)
    (P : WorkspaceCircuit d k) (rho : Operator (d*k))
    (f : Bool → List (ℕ×ℕ) → ℝ) : ℝ :=
  ((workspaceTraces U P rho).map fun t => workspaceMass t * f t.accepted t.outcomes).sum

noncomputable def workspaceCircuitExpectedQueries {d k : ℕ} (U : Operator d)
    (P : WorkspaceCircuit d k) (rho : Operator (d*k)) : ℝ :=
  ((workspaceTraces U P rho).map fun t => workspaceMass t * t.queries).sum

theorem workspaceTraces_posSemidef {d k : ℕ} (U : Operator d)
    (P : WorkspaceCircuit d k) (rho : Operator (d*k)) (hrho : rho.PosSemidef)
    (t : WorkspaceTrace d) (ht : t ∈ workspaceTraces U P rho) : t.state.PosSemidef := by
  induction P generalizing t with
  | halt b =>
      simp only [workspaceTraces, List.mem_singleton] at ht
      subst t
      exact hrho
  | gate G next ih =>
      exact ih _ ((completelyPositive_conjBranch G).positive hrho) t ht
  | query next ih =>
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih _ ((completelyPositive_conjBranch _).positive hrho) u hu
  | instrument s l I next ih =>
      simp only [workspaceTraces, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih o _ ((I.cp o).positive hrho) u hu

theorem workspaceTraces_total {d k : ℕ} (U : Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : WorkspaceCircuit d k) (hP : workspaceCircuitWellFormed P) (rho : Operator (d*k)) :
    ((workspaceTraces U P rho).map workspaceMass).sum = (trace rho).re := by
  induction P with
  | halt b => simp [workspaceTraces, workspaceMass]
  | gate G next ih =>
      exact (ih hP.2 _).trans (congrArg Complex.re (trace_conjBranch_unitary G hP.1 rho))
  | query next ih =>
      simpa only [workspaceTraces, List.map_map, Function.comp_def, workspaceMass] using!
        (ih hP (conjBranch (forwardWorkspaceOracle _ U) rho)).trans
          (congrArg Complex.re (trace_conjBranch_unitary _ (forwardWorkspaceOracle_unitary _ U hU) rho))
  | instrument s l I next ih =>
      simp only [workspaceTraces, List.map_flatten, List.sum_flatten,
        List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def]
      change (∑ o : Fin s,
          ((workspaceTraces U (next o) (I.branch o rho)).map workspaceMass).sum) = _
      simp_rw [ih _ (hP _)]
      exact sum_instrumentProb I rho

theorem workspaceCircuitExpectedQueries_nonneg {d k : ℕ} (U : Operator d)
    (P : WorkspaceCircuit d k) (rho : Operator (d*k)) (hrho : rho.PosSemidef) :
    0 ≤ workspaceCircuitExpectedQueries U P rho := by
  unfold workspaceCircuitExpectedQueries
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg ((RCLike.nonneg_iff.mp
    (workspaceTraces_posSemidef U P rho hrho t ht).trace_nonneg).1) (Nat.cast_nonneg _)

def workspaceCapacity {d : ℕ} : {k : ℕ} → WorkspaceCircuit d k → ℕ
  | k, .halt _ => k
  | k, .gate _ next => max k (workspaceCapacity next)
  | k, .query next => max k (workspaceCapacity next)
  | k, .instrument _ l _ next => max k (max l (Finset.univ.sup fun o => workspaceCapacity (next o)))

def workspaceFits {d : ℕ} (K : ℕ) : {k : ℕ} → WorkspaceCircuit d k → Prop
  | k, .halt _ => k ≤ K
  | k, .gate _ next => k ≤ K ∧ workspaceFits K next
  | k, .query next => k ≤ K ∧ workspaceFits K next
  | k, .instrument _ l _ next => k ≤ K ∧ l ≤ K ∧ ∀ o, workspaceFits K (next o)

theorem workspaceFits_input_le {d k K : ℕ} (P : WorkspaceCircuit d k)
    (hfit : workspaceFits K P) : k ≤ K := by
  cases P with
  | halt b => exact hfit
  | gate G next => exact hfit.1
  | query next => exact hfit.1
  | instrument s l I next => exact hfit.1

theorem workspaceFits_of_capacity_le {d k : ℕ} (P : WorkspaceCircuit d k) (K : ℕ)
    (h : workspaceCapacity P ≤ K) : workspaceFits K P := by
  induction P with
  | halt b => exact h
  | gate G next ih => exact ⟨(Nat.le_max_left _ _).trans h, ih ((Nat.le_max_right _ _).trans h)⟩
  | query next ih => exact ⟨(Nat.le_max_left _ _).trans h, ih ((Nat.le_max_right _ _).trans h)⟩
  | instrument s l I next ih =>
      refine ⟨(Nat.le_max_left _ _).trans h,
        (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans h), ?_⟩
      intro o
      apply ih o
      exact (Finset.le_sup (f := fun o => workspaceCapacity (next o)) (Finset.mem_univ o)).trans
        ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans h))

private noncomputable def workspacePaddedInstrument {d k l K s : ℕ}
    (hk : k ≤ K) (hl : l ≤ K) (I : Instrument (Fin s) (d*k) (d*l)) :
    Instrument (Fin (s+1)) (d*K) (d*K) :=
  Instrument.ofBranches
    (fun a => ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
      (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl)).branch (finSuccEquiv s a))
    (fun a => ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
      (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl)).cp (finSuccEquiv s a))
    (by
      intro A
      let J := (Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
        (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl)
      change trace (∑ a : Fin (s+1), J.branch (finSuccEquiv s a) A) = trace A
      exact (congrArg trace ((finSuccEquiv s).sum_comp (fun o => J.branch o A))).trans (J.total A))

private theorem workspacePaddedInstrument_none {d k l K s : ℕ}
    (hk : k ≤ K) (hl : l ≤ K) (I : Instrument (Fin s) (d*k) (d*l)) (A : Operator (d*k)) :
    (workspacePaddedInstrument hk hl I).branch 0 (conjBranch (workspaceEmbedding (d := d) hk) A) = 0 := by
  change ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
    (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl)).branch
      (finSuccEquiv s 0) (conjBranch (workspaceEmbedding (d := d) hk) A) = 0
  rw [finSuccEquiv_zero]
  exact Qatlib.Concepts.Execution.WorkspaceCP.isometryPad_none_onEmbedding I
    (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
    (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl) A

private theorem workspacePaddedInstrument_some {d k l K s : ℕ}
    (hk : k ≤ K) (hl : l ≤ K) (I : Instrument (Fin s) (d*k) (d*l))
    (o : Fin s) (A : Operator (d*k)) :
    (workspacePaddedInstrument hk hl I).branch o.succ (conjBranch (workspaceEmbedding (d := d) hk) A) =
      conjBranch (workspaceEmbedding (d := d) hl) (I.branch o A) := by
  change ((Qatlib.Concepts.Execution.WorkspaceCP.isometryPad I) (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
    (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl)).branch
      (finSuccEquiv s o.succ) (conjBranch (workspaceEmbedding (d := d) hk) A) =
        conjBranch (workspaceEmbedding (d := d) hl) (I.branch o A)
  rw [finSuccEquiv_succ]
  exact Qatlib.Concepts.Execution.WorkspaceCP.isometryPad_some_onEmbedding I
    (workspaceEmbedding (d := d) hk) (workspaceEmbedding_isometry (d := d) hk)
    (workspaceEmbedding (d := d) hl) (workspaceEmbedding_isometry (d := d) hl) o A

noncomputable def compileWorkspaceCircuit {d : ℕ} (K : ℕ) :
    {k : ℕ} → (P : WorkspaceCircuit d k) → workspaceFits K P → InstrumentCircuit (d*K)
  | _, .halt b, _ => .halt b
  | _, .gate G next, hfit =>
      .step (.gate (workspaceGate hfit.1 G)) (compileWorkspaceCircuit K next hfit.2)
  | _, .query next, hfit => .step .query (compileWorkspaceCircuit K next hfit.2)
  | _, .instrument s _ I next, hfit =>
      .instrument (s+1) (workspacePaddedInstrument hfit.1 hfit.2.1 I)
        (fun a => match finSuccEquiv s a with
          | none => .halt false
          | some o => compileWorkspaceCircuit K (next o) (hfit.2.2 o))

def restoreWorkspaceRecord {d : ℕ} : {k : ℕ} → WorkspaceCircuit d k →
    List (ℕ×ℕ) → List (ℕ×ℕ)
  | _, .halt _, rec => rec
  | _, .gate _ next, rec => restoreWorkspaceRecord next rec
  | _, .query next, rec => restoreWorkspaceRecord next rec
  | _, .instrument _ _ _ _, [] => []
  | _, .instrument s _ _ next, (_,a)::rec =>
      if h : a < s+1 then match finSuccEquiv s ⟨a,h⟩ with
        | none => []
        | some o => (s,o.val)::restoreWorkspaceRecord (next o) rec
      else []

theorem compileWorkspaceCircuit_wellFormed {d k : ℕ} (K : ℕ) (P : WorkspaceCircuit d k)
    (hfit : workspaceFits K P) (hP : workspaceCircuitWellFormed P) :
    instrumentCircuitWellFormed (compileWorkspaceCircuit K P hfit) := by
  induction P with
  | halt b => trivial
  | gate G next ih => exact ⟨workspaceGate_unitary hfit.1 G hP.1, ih hfit.2 hP.2⟩
  | query next ih => exact ih hfit.2 hP
  | instrument s l I next ih =>
      simp only [compileWorkspaceCircuit, instrumentCircuitWellFormed]
      intro a
      cases h : finSuccEquiv s a with
      | none => simp only [h, instrumentCircuitWellFormed]
      | some o => simpa only [h] using! ih o (hfit.2.2 o) (hP o)

private theorem workspace_compile_payoff {d k : ℕ} (U : Operator d) (K : ℕ)
    (P : WorkspaceCircuit d k) (hfit : workspaceFits K P)
    (rho : Operator (d*k)) (f : Bool → ℕ → List (ℕ×ℕ) → ℝ) :
    ((instrumentCircuitMixedTraces (forwardWorkspaceOracle K U)
      (compileWorkspaceCircuit K P hfit) (conjBranch (workspaceEmbedding (d := d)
        (workspaceFits_input_le P hfit)) rho)).map
      (fun t => mixedMass t * f t.accepted t.queries (restoreWorkspaceRecord P t.outcomes))).sum =
    ((workspaceTraces U P rho).map fun t => workspaceMass t * f t.accepted t.queries t.outcomes).sum := by
  induction P generalizing f with
  | halt b =>
      simp only [compileWorkspaceCircuit, instrumentCircuitMixedTraces, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, restoreWorkspaceRecord,
        workspaceTraces, mixedMass, workspaceMass]
      rw [workspaceEmbedding_trace]
  | gate G next ih =>
      simpa only [compileWorkspaceCircuit, instrumentCircuitMixedTraces, List.map_map,
        Function.comp_def, restoreWorkspaceRecord, workspaceTraces, workspaceGate_conjBranch,
        mixedMass, workspaceMass] using! ih hfit.2 (conjBranch G rho) f
  | query next ih =>
      simpa only [compileWorkspaceCircuit, instrumentCircuitMixedTraces, List.map_map,
        Function.comp_def, restoreWorkspaceRecord, workspaceTraces, workspaceEmbedding_conjBranch,
        mixedMass, workspaceMass] using!
          ih hfit.2 (conjBranch (forwardWorkspaceOracle _ U) rho)
            (fun b q rec => f b (q+1) rec)
  | instrument s l I next ih =>
      simp only [compileWorkspaceCircuit, instrumentCircuitMixedTraces,
        List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        List.map_map, Function.comp_def, workspaceTraces]
      rw [Fin.sum_univ_succ]
      simp only [finSuccEquiv_zero, finSuccEquiv_succ, workspacePaddedInstrument_none,
        workspacePaddedInstrument_some, instrumentCircuitMixedTraces, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, mixedMass, Matrix.trace_zero,
        Complex.zero_re, zero_mul, add_zero, zero_add]
      apply Finset.sum_congr rfl
      intro o _
      have h := ih o (hfit.2.2 o) (I.branch o rho)
        (fun b q rec => f b q ((s,o.val)::rec))
      simpa only [restoreWorkspaceRecord, Fin.val_succ, Fin.isLt, Nat.succ_lt_succ_iff,
        dif_pos, finSuccEquiv_succ, workspaceMass] using! h

theorem workspaceCircuit_compile_statistic {d k : ℕ} (U : Operator d) (K : ℕ)
    (P : WorkspaceCircuit d k) (hfit : workspaceFits K P)
    (rho : Operator (d*k)) (f : Bool → List (ℕ×ℕ) → ℝ) :
    ((instrumentCircuitMixedTraces (forwardWorkspaceOracle K U)
      (compileWorkspaceCircuit K P hfit)
      (conjBranch (workspaceEmbedding (d := d) (workspaceFits_input_le P hfit)) rho)).map
      (fun t => mixedMass t * f t.accepted (restoreWorkspaceRecord P t.outcomes))).sum =
    workspaceCircuitStatistic U P rho f :=
  workspace_compile_payoff U K P hfit rho (fun b _ rec => f b rec)

theorem workspaceCircuit_compile_expected {d k : ℕ} (U : Operator d) (K : ℕ)
    (P : WorkspaceCircuit d k) (hfit : workspaceFits K P)
    (rho : Operator (d*k)) :
    instrumentCircuitExpectedQueries (forwardWorkspaceOracle K U)
      (compileWorkspaceCircuit K P hfit)
      (conjBranch (workspaceEmbedding (d := d) (workspaceFits_input_le P hfit)) rho) =
    workspaceCircuitExpectedQueries U P rho := by
  exact workspace_compile_payoff U K P hfit rho (fun _ q _ => q)

end Qatlib.Concepts.Execution.WorkspaceCP
