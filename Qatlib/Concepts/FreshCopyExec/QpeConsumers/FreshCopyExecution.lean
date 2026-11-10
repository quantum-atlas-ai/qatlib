/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyExecutionDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped BigOperators ComplexOrder
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

@[simp] theorem seqCost_zero (a : Cost) : seqCost a zeroCost = a := by
  ext <;> simp [seqCost, zeroCost]

@[simp] theorem zero_seqCost (a : Cost) : seqCost zeroCost a = a := by
  ext <;> simp [seqCost, zeroCost]

theorem seqCost_assoc (a b c : Cost) :
    seqCost (seqCost a b) c = seqCost a (seqCost b c) := by
  ext <;> simp [seqCost, Nat.add_assoc, max_assoc]

def wordCost {n M : ℕ} (p : List (Op n M)) : Cost :=
  (p.map stepCost).foldr seqCost zeroCost

@[simp] theorem run_cost {n M : ℕ} (p : List (Op n M)) (X : State n M) :
    (run p X).2 = wordCost p := by
  induction p generalizing X with
  | nil => rfl
  | cons a p ih => simp [run, wordCost, ih]

theorem run_append {n M : ℕ} (p q : List (Op n M)) (X : State n M) :
    run (p ++ q) X =
      ((run q (run p X).1).1, seqCost (run p X).2 (run q (run p X).1).2) := by
  induction p generalizing X with
  | nil =>
    apply Prod.ext
    · rfl
    · simp [run]
  | cons a p ih => simp [run, ih, seqCost_assoc]

theorem wordCost_append {n M : ℕ} (p q : List (Op n M)) :
    wordCost (p ++ q) = seqCost (wordCost p) (wordCost q) := by
  simpa using! congrArg Prod.snd (run_append p q (0 : State n M))

theorem run_repeat {n M : ℕ} (k : ℕ) (p : List (Op n M)) (X : State n M) :
    (run ((List.replicate k p).flatten) X).1 = (fun Y => (run p Y).1)^[k] X ∧
    (run ((List.replicate k p).flatten) X).2 =
      (List.replicate k (run p X).2).foldr seqCost zeroCost := by
  induction k generalizing X with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, run_append,
      Function.iterate_succ_apply, List.foldr_cons]
    constructor
    · exact (ih (run p X).1).1
    · simpa only [run_cost] using! congrArg (seqCost (wordCost p)) (ih (run p X).1).2

def tally (fresh macros gates clean : ℕ) : Cost :=
  ⟨fresh,fresh,fresh*gates,macros,fresh,0,
    if fresh=0 then 0 else 1, if fresh=0 then 0 else clean⟩

@[simp] theorem tally_zero (g c : ℕ) : tally 0 0 g c = zeroCost := by
  ext <;> simp [tally, zeroCost]

theorem tally_add (a b m l g c : ℕ) :
    seqCost (tally a m g c) (tally b l g c) = tally (a+b) (m+l) g c := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    ext <;> simp [tally, seqCost, ha, hb, Nat.add_mul, Nat.add_eq_zero_iff, max_self]

@[simp] theorem freshCost_tally (g c : ℕ) : freshCost g c = tally 1 0 g c := by
  ext <;> simp [freshCost, tally]

theorem macroCost_tally (g c : ℕ) : macroCost = tally 0 1 g c := by
  ext <;> simp [macroCost, tally]

theorem repeat_cost {n M : ℕ} (p : List (Op n M)) (s k g c : ℕ)
    (hp : wordCost p = tally s 0 g c) :
    wordCost ((List.replicate k p).flatten) = tally (k*s) 0 g c := by
  induction k with
  | zero => simp [wordCost, tally, zeroCost]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, wordCost_append, hp, ih,
      tally_add]
    simp [Nat.add_mul, Nat.add_comm]

def compileBlock {n M : ℕ} (p : List (Op n M)) : Circuit (Register n M) → List (Op n M)
  | [] => []
  | .gate U :: C => .gate U :: compileBlock p C
  | .query :: C => p ++ compileBlock p C

theorem compileBlock_cost {n M : ℕ} (p : List (Op n M)) (s g c : ℕ)
    (hp : wordCost p = tally s 0 g c) (C : Circuit (Register n M)) :
    wordCost (compileBlock p C) = tally (QueryCount C*s) (GateCount C) g c := by
  induction C with
  | nil => simp [compileBlock, wordCost, QueryCount, GateCount, tally, zeroCost]
  | cons a C ih =>
    cases a with
    | gate U =>
      change seqCost macroCost (wordCost (compileBlock p C)) = _
      rw [ih, macroCost_tally g c, tally_add]
      simp [QueryCount, GateCount, Nat.add_comm]
    | query =>
      rw [compileBlock, wordCost_append, hp, ih, tally_add]
      simp [QueryCount, GateCount, Nat.add_mul, Nat.add_comm]

def execute {n M : ℕ} (Q : State n M → State n M) :
    Circuit (Register n M) → State n M → State n M
  | [], X => X
  | .gate U :: C, X => execute Q C (MatrixMap.conj U X)
  | .query :: C, X => execute Q C (Q X)

theorem compileBlock_state {n M : ℕ} (p : List (Op n M))
    (Q : State n M → State n M) (hp : ∀ X, (run p X).1 = Q X)
    (C : Circuit (Register n M)) (X : State n M) :
    (run (compileBlock p C) X).1 = execute Q C X := by
  induction C generalizing X with
  | nil => rfl
  | cons a C ih =>
    cases a <;> simp [compileBlock, run, execute, run_append, hp, ih, stepMap]

theorem liftMap_comp (n M : ℕ) (T S : Operator (2*(2^n)) → Operator (2*(2^n)))
    (X : State n M) : liftMap n M T (liftMap n M S X) = liftMap n M (T ∘ S) X := by
  unfold liftMap
  have h (Y : Matrix (Fin M × Fin (2*(2^n))) (Fin M × Fin (2*(2^n))) ℂ) :
      relabelGate (copyQPERegisterEquiv (2^n) M)
        (relabelGate (copyQPERegisterEquiv (2^n) M).symm Y) = Y := by
    simpa only [Equiv.symm_symm] using!
      relabelGate_relabelGate (copyQPERegisterEquiv (2^n) M).symm Y
  rw [h]
  rfl

theorem liftMap_iterate (n M k : ℕ) (T : Operator (2*(2^n)) → Operator (2*(2^n)))
    (X : State n M) : (liftMap n M T)^[k] X = liftMap n M (T^[k]) X := by
  induction k with
  | zero =>
    change X = relabelGate _ (numericAmplification id M (relabelGate _ X))
    have h (Y : Matrix (Fin M × Fin (2*(2^n))) (Fin M × Fin (2*(2^n))) ℂ) :
        numericAmplification id M Y = Y := by ext a b; rfl
    rw [h, relabelGate_relabelGate]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, liftMap_comp, Function.iterate_succ']

theorem mapPower_iterate {d : ℕ} (T : Operator d →ₗ[ℂ] Operator d) (k : ℕ)
    (X : Operator d) : copyMapPower T k X = T^[k] X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact congrArg T ih

theorem replicate_state {n M : ℕ} (op : Op n M) (k : ℕ) (X : State n M) :
    (run (List.replicate k op) X).1 = (stepMap op)^[k] X := by
  induction k generalizing X with
  | zero => rfl
  | succ k ih => simpa [run, Function.iterate_succ_apply] using! ih (stepMap op X)

theorem replicate_cost {n M : ℕ} (op : Op n M) (k g c : ℕ)
    (h : stepCost op = freshCost g c) : wordCost (List.replicate k op) = tally k 0 g c := by
  induction k with
  | zero => simp [wordCost, tally, zeroCost]
  | succ k ih =>
    change seqCost (stepCost op) (wordCost (List.replicate k op)) = _
    rw [h, freshCost_tally, ih, tally_add]
    congr 1; omega

private theorem compileDirect_block (n M s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) :
    compileDirect n M s ρ C = compileBlock (List.replicate s (.direct ρ (Real.pi/(s:ℝ)))) C := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [compileDirect, compileBlock, ih]

private theorem compileLocal_block (n M s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) :
    compileLocal n M s ρ C = compileBlock (List.replicate s (.localStep ρ (Real.pi/(s:ℝ)))) C := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [compileLocal, compileBlock, ih]

private theorem compileNumeric_block (n M b k : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) :
    compileNumeric n M b k ρ C = compileBlock (List.replicate (2^b) (.numeric ρ b k)) C := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [compileNumeric, compileBlock, ih]

private theorem compileTwo_block (n M s : ℕ) (ρ σ : Operator (2^n)) (C : Circuit (Register n M)) :
    compileTwo n M s ρ σ C = compileBlock
      ((List.replicate s [.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))]).flatten) C := by
  induction C with
  | nil => rfl
  | cons a C ih => cases a <;> simp [compileTwo, compileBlock, ih]

theorem g1 :
    (∀ (n M : ℕ) (p q : List (Op n M)) (X : State n M),
      run (p ++ q) X = ((run q (run p X).1).1,
        seqCost (run p X).2 (run q (run p X).1).2)) ∧
    (∀ (n M : ℕ) (p : List (Op n M)) (X Y : State n M), (run p X).2 = (run p Y).2) ∧
    (∀ (n M k : ℕ) (p : List (Op n M)) (X : State n M),
      (run ((List.replicate k p).flatten) X).1 = (fun Y => (run p Y).1)^[k] X ∧
      (run ((List.replicate k p).flatten) X).2 =
        (List.replicate k (run p X).2).foldr seqCost zeroCost) :=
  ⟨fun _ _ => run_append, fun _ _ p X Y => by simp, fun _ _ => run_repeat⟩

private theorem direct_state (n M s : ℕ) (ρ : Operator (2^n)) (X : State n M) :
    (run (List.replicate s (.direct ρ (Real.pi/(s:ℝ)) : Op n M)) X).1 =
      copyQPEQuery (2^n) M s ρ X := by
  rw [replicate_state]
  change (liftMap n M (controlledCopyChannelMap ρ (Real.pi/(s:ℝ))))^[s] X = _
  rw [liftMap_iterate]
  unfold copyQPEQuery controlledCopyRunMap liftMap
  congr 1
  ext a b
  exact congrArg (fun Y => Y a.2 b.2) (mapPower_iterate _ s _).symm

private theorem local_state (n M s : ℕ) (ρ : Operator (2^n)) (X : State n M) :
    (run (List.replicate s (.localStep ρ (Real.pi/(s:ℝ)) : Op n M)) X).1 =
      localCopyQPEQuery n M s ρ X := by
  rw [replicate_state]
  change (liftMap n M (localControlledCopyChannelMap n ρ (Real.pi/(s:ℝ))))^[s] X = _
  rw [liftMap_iterate]
  unfold localCopyQPEQuery localCopyRunMap liftMap
  congr 1
  ext a b
  exact congrArg (fun Y => Y a.2 b.2) (mapPower_iterate _ s _).symm

private theorem numeric_state (n M b k : ℕ) (ρ : Operator (2^n)) (X : State n M) :
    (run (List.replicate (2^b) (.numeric ρ b k : Op n M)) X).1 =
      numericCopyQPEQuery n M b k ρ X := by
  rw [replicate_state]
  exact liftMap_iterate n M (2^b) (numericCopyFinStep n ρ b k) X

private theorem local_fee (n : ℕ) (θ : ℝ) :
    GateCount (reflectionCompile (localControlledSwapSteps n θ)) = 36*n+7 := by
  rw [gateCount_reflectionCompile, localControlledSwapSteps_length]

private theorem numeric_fee (n b k : ℕ) :
    GateCount (reflectionCompile (numericControlledSwapSteps n b k)) = 36*n+4 := by
  rw [gateCount_reflectionCompile]
  exact (numerical_controlled_swap_clean_and_error n b k).2.1

theorem g2 : ∀ (n M s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) (X : State n M),
    (run (compileDirect n M s ρ C) X).1 = copyQPEProgram (2^n) M s ρ C X ∧
    (run (compileDirect n M s ρ C) X).2 =
      ⟨QueryCount C*s, QueryCount C*s, 0, GateCount C, QueryCount C*s, 0,
        if QueryCount C*s=0 then 0 else 1, 0⟩ ∧
    (run (compileDirect n M s ρ C) X).2.copies = (copyQPEProgramResources s C).1 ∧
    (run (compileDirect n M s ρ C) X).2.partialSwaps = (copyQPEProgramResources s C).2.1 ∧
    (IsDensityOperator ρ → IsUnitaryCircuit C → X.PosSemidef →
      ((run (compileDirect n M s ρ C) X).1).PosSemidef ∧
      Matrix.trace ((run (compileDirect n M s ρ C) X).1) = Matrix.trace X) := by
  intro n M s ρ C X
  have he : execute (copyQPEQuery (2^n) M s ρ) C X = copyQPEProgram (2^n) M s ρ C X := by
    induction C generalizing X with
    | nil => rfl
    | cons a C ih => cases a <;> simp only [execute, copyQPEProgram, ih]
  have hs := (compileBlock_state _ _ (direct_state n M s ρ) C X).trans he
  rw [← compileDirect_block] at hs
  have hc := compileBlock_cost
    (List.replicate s (.direct ρ (Real.pi/(s:ℝ)) : Op n M)) s 0 0
    (replicate_cost (.direct ρ (Real.pi/(s:ℝ)) : Op n M) s 0 0 rfl) C
  rw [← compileDirect_block] at hc
  have hc' : (run (compileDirect n M s ρ C) X).2 = _ := (run_cost _ _).trans hc
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · simpa [tally] using! hc'
  · rw [hc', copyQPEProgramResources_eq]; rfl
  · rw [hc', copyQPEProgramResources_eq]; rfl
  · intro hρ hC hX
    rw [hs]
    exact copyQPEProgram_positive_trace (2^n) M s ρ hρ C hC X hX

theorem g3 : ∀ (n M s : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) (X : State n M),
    (run (compileLocal n M s ρ C) X).1 = localCopyQPEProgram n M s ρ C X ∧
    (run (compileLocal n M s ρ C) X).2 =
      ⟨QueryCount C*s, QueryCount C*s, QueryCount C*s*(36*n+7), GateCount C,
        QueryCount C*s, 0, if QueryCount C*s=0 then 0 else 1,
        if QueryCount C*s=0 then 0 else n+1⟩ ∧
    (run (compileLocal n M s ρ C) X).2.localGates = (localCopyQPEProgramResources n s C).1 ∧
    (run (compileLocal n M s ρ C) X).2.copies = (localCopyQPEProgramResources n s C).2.1 ∧
    (run (compileLocal n M s ρ C) X).2.discards = (localCopyQPEProgramResources n s C).2.2.1 ∧
    (run (compileLocal n M s ρ C) X).2.bitQueries = (localCopyQPEProgramResources n s C).2.2.2 ∧
    (run (compileLocal n M s ρ C) X).2.localGates = QueryCount C*s*
      GateCount (reflectionCompile (localControlledSwapSteps n (Real.pi/(s:ℝ)))) := by
  intro n M s ρ C X
  have he : execute (localCopyQPEQuery n M s ρ) C X = localCopyQPEProgram n M s ρ C X := by
    induction C generalizing X with
    | nil => rfl
    | cons a C ih => cases a <;> simp only [execute, localCopyQPEProgram, ih]
  have hs := (compileBlock_state _ _ (local_state n M s ρ) C X).trans he
  rw [← compileLocal_block] at hs
  have hf : stepCost (.localStep ρ (Real.pi/(s:ℝ)) : Op n M) = freshCost (36*n+7) (n+1) := by
    simp [stepCost, local_fee]
  have hc := compileBlock_cost
    (List.replicate s (.localStep ρ (Real.pi/(s:ℝ)) : Op n M)) s (36*n+7) (n+1)
    (replicate_cost (.localStep ρ (Real.pi/(s:ℝ)) : Op n M) s _ _ hf) C
  rw [← compileLocal_block] at hc
  have hc' := (run_cost (compileLocal n M s ρ C) X).trans hc
  refine ⟨hs, hc', ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hc, tally, localCopyQPEProgramResources_eq, local_fee]

theorem g4 : ∀ (n M b k : ℕ) (ρ : Operator (2^n)) (C : Circuit (Register n M)) (X : State n M),
    (run (compileNumeric n M b k ρ C) X).1 = numericCopyQPEProgram n M b k ρ C X ∧
    (run (compileNumeric n M b k ρ C) X).2 =
      ⟨QueryCount C*(2^b), QueryCount C*(2^b), QueryCount C*(2^b)*(36*n+4),
        GateCount C, QueryCount C*(2^b), 0,
        if QueryCount C=0 then 0 else 1, if QueryCount C=0 then 0 else n+1⟩ ∧
    (run (compileNumeric n M b k ρ C) X).2.localGates = (numericCopyResources n b C).1 ∧
    (run (compileNumeric n M b k ρ C) X).2.copies = (numericCopyResources n b C).2.1 ∧
    (run (compileNumeric n M b k ρ C) X).2.discards = (numericCopyResources n b C).2.2.1 ∧
    (run (compileNumeric n M b k ρ C) X).2.bitQueries = (numericCopyResources n b C).2.2.2 ∧
    (run (compileNumeric n M b k ρ C) X).2.localGates = QueryCount C*(2^b)*
      GateCount (reflectionCompile (numericControlledSwapSteps n b k)) := by
  intro n M b k ρ C X
  have he : execute (numericCopyQPEQuery n M b k ρ) C X = numericCopyQPEProgram n M b k ρ C X := by
    induction C generalizing X with
    | nil => rfl
    | cons a C ih => cases a <;> simp only [execute, numericCopyQPEProgram, ih]
  have hs := (compileBlock_state _ _ (numeric_state n M b k ρ) C X).trans he
  rw [← compileNumeric_block] at hs
  have hf : stepCost (.numeric ρ b k : Op n M) = freshCost (36*n+4) (n+1) := by
    simp [stepCost, numeric_fee]
  have hc := compileBlock_cost
    (List.replicate (2^b) (.numeric ρ b k : Op n M)) (2^b) (36*n+4) (n+1)
    (replicate_cost (.numeric ρ b k : Op n M) (2^b) _ _ hf) C
  rw [← compileNumeric_block] at hc
  have hc' := (run_cost (compileNumeric n M b k ρ C) X).trans hc
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hc, tally, numericCopyResources_eq, numeric_fee]

private theorem two_state (n M s : ℕ) (ρ σ : Operator (2^n)) (X : State n M) :
    (run ((List.replicate s [.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))] : List (List (Op n M))).flatten) X).1 =
      twoSpeciesQPEQuery (2^n) M s ρ σ X := by
  rw [(run_repeat s _ X).1]
  have hp : (fun Y : State n M =>
      (run [.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))] Y).1) =
      liftMap n M (twoSpeciesPairChannelMap (2^n) ρ σ (Real.pi/(s:ℝ))) := by
    funext Y
    change liftMap n M _ (liftMap n M _ Y) = _
    exact liftMap_comp n M _ _ Y
  rw [hp, liftMap_iterate]
  unfold twoSpeciesQPEQuery twoSpeciesRunMap liftMap
  congr 1
  ext a b
  exact congrArg (fun Y => Y a.2 b.2) (mapPower_iterate _ s _).symm

theorem g5 : ∀ (n M s : ℕ) (ρ σ : Operator (2^n)) (C : Circuit (Register n M)) (X : State n M),
    (run (compileTwo n M s ρ σ C) X).1 = twoSpeciesQPEProgram (2^n) M s ρ σ C X ∧
    (run (compileTwo n M s ρ σ C) X).2 =
      ⟨2*QueryCount C*s, 2*QueryCount C*s, 0, GateCount C,
        2*QueryCount C*s, 0, if QueryCount C*s=0 then 0 else 1, 0⟩ ∧
    (0 < M →
      (run (compileTwo n M s ρ σ (countedPhaseCircuit M)) (copyQPEInput (2^n) M ρ)).2.copies =
        (twoSpeciesQPEResources M s).1) := by
  intro n M s ρ σ C X
  have he : execute (twoSpeciesQPEQuery (2^n) M s ρ σ) C X = twoSpeciesQPEProgram (2^n) M s ρ σ C X := by
    induction C generalizing X with
    | nil => rfl
    | cons a C ih => cases a <;> simp only [execute, twoSpeciesQPEProgram, ih]
  have hs := (compileBlock_state _ _ (two_state n M s ρ σ) C X).trans he
  rw [← compileTwo_block] at hs
  have hb : wordCost ([.direct σ (-(Real.pi/(s:ℝ))), .direct ρ (Real.pi/(s:ℝ))] : List (Op n M)) = tally 2 0 0 0 := by
    rfl
  have hc (C : Circuit (Register n M)) (X : State n M) :
      (run (compileTwo n M s ρ σ C) X).2 = tally (QueryCount C*(s*2)) (GateCount C) 0 0 := by
    rw [run_cost, compileTwo_block]
    exact compileBlock_cost _ (s*2) 0 0 (repeat_cost _ 2 s 0 0 hb) C
  refine ⟨hs, ?_, ?_⟩
  · simpa [tally, Nat.mul_eq_zero, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using! hc C X
  · intro hM
    rw [hc]
    have hq :=
        (counted_offgrid_qpe_clean_flag M hM (1 : Operator (2^n)) (0 : QState (Fin (2^n)))).2.1
    simp only [tally, twoSpeciesQPEResources, hq]
    ring

private theorem plain_append {D : ℕ} (p q : List (Operator D × ℝ)) (X : Operator D) :
    runPlain (p++q) X = ((runPlain q (runPlain p X).1).1,
      seqCost (runPlain p X).2 (runPlain q (runPlain p X).1).2) := by
  induction p generalizing X with
  | nil => simp [runPlain]
  | cons a p ih => rcases a with ⟨ρ,θ⟩; simp [runPlain, ih, seqCost_assoc]

private theorem plain_cost {D : ℕ} (p : List (Operator D × ℝ)) (X : Operator D) :
    (runPlain p X).2 = tally p.length 0 0 0 := by
  induction p generalizing X with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨ρ,θ⟩
    simp only [runPlain, ih, freshCost_tally, tally_add, List.length_cons]
    congr 1; omega

private theorem plain_reference {D r : ℕ} (p : List (Operator D × ℝ))
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hp : ∀ a ∈ p, IsDensityOperator a.1) :
    (X.PosSemidef → (p.foldl (fun Y a => partialSwapReferenceOutput a.1 a.2 r Y) X).PosSemidef) ∧
    Matrix.trace (p.foldl (fun Y a => partialSwapReferenceOutput a.1 a.2 r Y) X) = Matrix.trace X := by
  induction p generalizing X with
  | nil => exact ⟨fun h => h, rfl⟩
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht := ih (partialSwapReferenceOutput a.1 a.2 r X) (fun b hb => hp b (by simp [hb]))
    have hs := (partial_swap_reference_output_formula a.1 ha a.2 r X).2
    exact ⟨fun h => ht.1 (hs.1 h), ht.2.trans hs.2⟩

theorem g6 :
    (∀ (D : ℕ) (ρ X : Operator D) (angles : List ℝ),
      (runPlain (angles.map (fun θ => (ρ,θ))) X).1 = freshCopyRun ρ angles X ∧
      (runPlain (angles.map (fun θ => (ρ,θ))) X).2 =
        ⟨angles.length,angles.length,0,0,angles.length,0,if angles.length=0 then 0 else 1,0⟩ ∧
      (runPlain (angles.map (fun θ => (ρ,θ))) X).2.copies = (freshCopyResourceCounts D angles).1 ∧
      (runPlain (angles.map (fun θ => (ρ,θ))) X).2.partialSwaps = (freshCopyResourceCounts D angles).2.1) ∧
    (∀ (D : ℕ) (p q : List (Operator D × ℝ)) (X : Operator D),
      runPlain (p++q) X = ((runPlain q (runPlain p X).1).1,
        seqCost (runPlain p X).2 (runPlain q (runPlain p X).1).2)) ∧
    (∀ (D r : ℕ) (p : List (Operator D × ℝ))
      (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      (∀ a ∈ p, IsDensityOperator a.1) →
      (X.PosSemidef → (p.foldl (fun Y a => partialSwapReferenceOutput a.1 a.2 r Y) X).PosSemidef) ∧
      Matrix.trace (p.foldl (fun Y a => partialSwapReferenceOutput a.1 a.2 r Y) X) = Matrix.trace X) := by
  refine ⟨?_, fun _ => plain_append, fun _ _ => plain_reference⟩
  intro D ρ X angles
  have hs : (runPlain (angles.map (fun θ => (ρ,θ))) X).1 = freshCopyRun ρ angles X := by
    induction angles generalizing X with
    | nil => rfl
    | cons θ angles ih => simpa [runPlain, freshCopyRun] using! ih (partialSwapOutput ρ θ X)
  refine ⟨hs, ?_, ?_, ?_⟩ <;>
    simp [plain_cost, tally, freshCopyResourceCounts_eq]

end
end Qatlib.Concepts.FreshCopyExec.QpeConsumers
