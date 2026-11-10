/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmCellPhi3CompilationStat
import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmPhi3RoundCompilation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Matrix
open scoped Classical

theorem qtmPhi3_compilation_zeroRounds
    (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
    (b t : ℕ) (e : CellState Q A → Reg b)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    ∃ gs : List (Phi3Gate ((2*t+1)*b+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧ gs.length ≤ 0 ∧
      ∀ ψ : QState (WReg t Q A), Run 1 (phi3Compile gs) (qtmPhi3State t b e ψ) =
        qtmPhi3State t b e (Run 1 (RepeatCircuit (kRoundCircuit t G) 0) ψ) := by
  refine ⟨[], isUnitaryCircuit_phi3Compile [], rfl, rfl, by simp, ?_⟩
  intro ψ
  rfl

theorem qtmRound_local_table (Q : Type) [Fintype Q] [DecidableEq Q]
    (A : Type) [Fintype A] [DecidableEq A] (t b : ℕ) (hb : 0 < b)
    (e : CellState Q A → Reg b) (he : Function.Injective e)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (hG : G ∈ unitaryGroup (GWindow Q A) ℂ) :
    ∃ gs : List (ReflectionGate ((2*t+1)*b)), reflectionLegal gs ∧
      gs.length ≤ (2*t-1)*phi3PaddingBudget (3*b)+(2*t+1)*phi3PaddingBudget b ∧
      ∀ ψ : QState (WReg t Q A),
        Run 1 (reflectionCompile gs) (finiteBasisPadState (qtmWindowBasisCode t b e) ψ) =
          finiteBasisPadState (qtmWindowBasisCode t b e) (Run 1 (kRoundCircuit t G) ψ) := by
  let embed := finiteBasisPadState (qtmBlockBasisCode (2*t+1) b e)
  let gus : List (Matrix (WReg t Q A) (WReg t Q A) ℂ) :=
    (List.finRange (2*t-1)).map (gUnitFull G)
  have hgLocal : ∀ U ∈ gus, ∃ gs : List (ReflectionGate ((2*t+1)*b)),
      reflectionLegal gs ∧ gs.length ≤ phi3PaddingBudget (3*b) ∧
        ∀ ψ, Run 1 (reflectionCompile gs) (embed ψ) = embed (ApplyGate U ψ) := by
    intro U hU
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hU
    obtain ⟨gs,hgs,hlen,hr⟩ := qtmCell_local_table (qtmGCells t j) b
      (by decide) hb e he G hG
    refine ⟨gs,hgs,hlen,?_⟩
    intro ψ
    simpa only [qtmGCells_matrix] using! hr ψ
  obtain ⟨fs,hfs,hflen,hf⟩ := qtmMatrices_table_compose ((2*t+1)*b)
    (phi3PaddingBudget (3*b)) embed gus hgLocal
  let mus : List (Matrix (WReg t Q A) (WReg t Q A) ℂ) :=
    (List.finRange (2*t+1)).map (fun j => qtmMarkerCell j)
  have hmLocal : ∀ U ∈ mus, ∃ gs : List (ReflectionGate ((2*t+1)*b)),
      reflectionLegal gs ∧ gs.length ≤ phi3PaddingBudget b ∧
        ∀ ψ, Run 1 (reflectionCompile gs) (embed ψ) = embed (ApplyGate U ψ) := by
    intro U hU
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hU
    obtain ⟨gs,hgs,hlen,hr⟩ := qtmCell_local_table (qtmSingleCell j) b
      (by decide) hb e he qtmLocalMarker qtmLocalMarker_unitary
    refine ⟨gs,hgs,by simpa only [Nat.one_mul] using! hlen,hr⟩
  obtain ⟨ms,hms,hmlen,hm⟩ := qtmMatrices_table_compose ((2*t+1)*b)
    (phi3PaddingBudget b) embed mus hmLocal
  refine ⟨fs++ms,(reflectionLegal_append fs ms).mpr ⟨hfs,hms⟩,?_,?_⟩
  · have hf' : fs.length ≤ (2*t-1)*phi3PaddingBudget (3*b) := by simpa [gus] using! hflen
    have hm' : ms.length ≤ (2*t+1)*phi3PaddingBudget b := by simpa [mus] using! hmlen
    simpa only [List.length_append] using! Nat.add_le_add hf' hm'
  · intro ψ
    change Run 1 (reflectionCompile (fs++ms)) (embed ψ) = embed (Run 1 (kRoundCircuit t G) ψ)
    rw [reflectionCompile_append,run_append,hf,hm]
    simp only [gus,mus,List.map_map,Function.comp_def]
    rw [qtmMarker_sweep]
    simp only [kRoundCircuit,run_append,run_gate,run_nil]

private def qtmRepeatRef {N : ℕ} (gs : List (ReflectionGate N)) : ℕ → List (ReflectionGate N)
  | 0 => []
  | k+1 => gs++qtmRepeatRef gs k

private theorem qtmRepeatRef_legal {N : ℕ} (gs : List (ReflectionGate N))
    (hgs : reflectionLegal gs) (k : ℕ) : reflectionLegal (qtmRepeatRef gs k) := by
  induction k with
  | zero => simp [qtmRepeatRef,reflectionLegal]
  | succ k ih => exact (reflectionLegal_append gs (qtmRepeatRef gs k)).mpr ⟨hgs,ih⟩

private theorem qtmRepeatRef_length {N : ℕ} (gs : List (ReflectionGate N)) (k : ℕ) :
    (qtmRepeatRef gs k).length = k*gs.length := by
  induction k with
  | zero => simp [qtmRepeatRef]
  | succ k ih => simp [qtmRepeatRef,ih,Nat.succ_mul,Nat.add_comm]

private theorem qtmRepeatRef_run {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (embed : QState I → QState (Reg N)) (C : Circuit I) (gs : List (ReflectionGate N))
    (hr : ∀ ψ, Run 1 (reflectionCompile gs) (embed ψ) = embed (Run 1 C ψ))
    (k : ℕ) (ψ : QState I) :
    Run 1 (reflectionCompile (qtmRepeatRef gs k)) (embed ψ) =
      embed (Run 1 (RepeatCircuit C k) ψ) := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih =>
    simp only [qtmRepeatRef,reflectionCompile_append,RepeatCircuit,run_append]
    rw [hr,ih]

theorem qtmCellPhi3Compilation : QtmCellPhi3Compilation := by
  intro Q _ _ A _ _ b t k e G he hG
  rcases isEmpty_or_nonempty (CellState Q A) with hEmpty | hNonempty
  · letI : IsEmpty (CellState Q A) := hEmpty
    have hsame (ψ : QState (WReg t Q A)) :
        Run 1 (RepeatCircuit (kRoundCircuit t G) k) ψ = ψ := by
      funext r
      exact isEmptyElim (r ⟨0,by omega⟩)
    refine ⟨[],isUnitaryCircuit_phi3Compile [],rfl,rfl,by simp,?_⟩
    intro ψ
    simp only [phi3Compile,List.map_nil,run_nil]
    rw [hsame]
  · obtain ⟨r⟩ := hNonempty
    have hb : 0 < b := by
      by_contra hn
      have hz : b=0 := Nat.eq_zero_of_not_pos hn
      subst b
      have hh : (0 : Fin 3) = 1 := congrArg Prod.fst
        (he (Subsingleton.elim (e (0,r.2)) (e (1,r.2))))
      norm_num at hh
    obtain ⟨fs,hfs,hlen,hr⟩ := qtmRound_local_table Q A t b hb e he G hG
    let rs := qtmRepeatRef fs k
    have hrs : reflectionLegal rs := qtmRepeatRef_legal fs hfs k
    have hrlen : rs.length ≤
        k*((2*t-1)*phi3PaddingBudget (3*b)+(2*t+1)*phi3PaddingBudget b) := by
      rw [qtmRepeatRef_length]
      exact Nat.mul_le_mul_left k hlen
    obtain ⟨gs,hgslen,hcompile⟩ := qtmPhi3_translate_table rs hrs
    obtain ⟨hq,hc⟩ := phi3Compile_count gs
    refine ⟨gs,isUnitaryCircuit_phi3Compile gs,hq,hc,hgslen.le.trans hrlen,?_⟩
    intro ψ
    unfold qtmPhi3State
    rw [hcompile,knownWireProgram_embed (knownPrefixWires ((2*t+1)*b) 3) rs hrs]
    exact congrArg (knownWireEmbed (knownPrefixWires ((2*t+1)*b) 3))
      (qtmRepeatRef_run (finiteBasisPadState (qtmWindowBasisCode t b e))
        (kRoundCircuit t G) fs hr k ψ)

end Qatlib.Concepts.QtmSimulation.Phi3Compilation
