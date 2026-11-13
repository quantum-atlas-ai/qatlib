/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmPhi3LocalTransport

/-!
# Assembly of QTM round compilation tables

This module assembles local matrix simulation tables and identifies the local gates of a QTM
window round. It proves that sweeping the single-cell marker gates implements the full marker
swap, as required for the circuit simulation constructions of [Yao1993].

## Main statements

* `qtmMatrices_table_compose`: Composition of bounded legal local reflection tables.
* `qtmGCells_matrix`: Identification of a three-cell update with its full-window matrix.
* `qtmMarker_sweep`: A sweep of local marker gates equals the full marker operation.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Matrix
open scoped Classical BigOperators

/-- Local legal reflection tables of length at most `L` compose into a table of length at most
`Us.length * L` simulating the matrix-gate list through the given embedding. -/
theorem qtmMatrices_table_compose {I : Type} [Fintype I] [DecidableEq I]
    (N L : ℕ) (embed : QState I → QState (Reg N)) (Us : List (Matrix I I ℂ))
    (hlocal : ∀ U ∈ Us, ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ L ∧ ∀ ψ, Run 1 (reflectionCompile gs) (embed ψ) = embed (ApplyGate U ψ)) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ Us.length*L ∧
      ∀ ψ, Run 1 (reflectionCompile gs) (embed ψ) = embed (Run 1 (Us.map Step.gate) ψ) := by
  induction Us with
  | nil =>
    refine ⟨[],by simp [reflectionLegal],by simp,?_⟩
    intro ψ
    rfl
  | cons U Us ih =>
    obtain ⟨fs,hfs,hflen,hf⟩ := hlocal U List.mem_cons_self
    obtain ⟨gs,hgs,hlen,hg⟩ := ih (fun V hV => hlocal V (List.mem_cons_of_mem U hV))
    refine ⟨fs++gs,(reflectionLegal_append fs gs).mpr ⟨hfs,hgs⟩,?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      nlinarith
    · intro ψ
      rw [reflectionCompile_append,run_append,hf,hg]
      rfl

/-- The embedding of the three cells selected by the `k`th local QTM update into the full
window. -/
def qtmGCells (t : ℕ) (k : Fin (2*t-1)) : Fin 3 ↪ Fin (2*t+1) :=
  { toFun := gUnitCells t k
    inj' := by
      intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      have he (q : Fin 3) : (gUnitCells t k q).val = k.val+q.val := by
        fin_cases q <;> rfl
      rw [he,he] at hv
      omega }

/-- Extending `G` along its three selected cells gives the full-window local update matrix
`gUnitFull G k`. -/
theorem qtmGCells_matrix {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {t : ℕ}
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (k : Fin (2*t-1)) :
    qtmCellGate (qtmGCells t k) G = gUnitFull G k := by
  ext x y
  by_cases h : ∀ j : Fin (2*t+1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → x j = y j <;>
    simp [qtmCellGate,qtmGCells,gUnitFull,h]

/-- Swapping a cell's marker twice returns the original cell state. -/
private theorem qtmMarkSwap_invol {Q A : Type} :
    Function.Involutive (markSwap : CellState Q A → CellState Q A) := by
  intro r
  rcases r with ⟨m,o,a⟩
  fin_cases m <;> simp [markSwap]

/-- The embedding selecting the single cell at position `j`. -/
def qtmSingleCell {c : ℕ} (j : Fin c) : Fin 1 ↪ Fin c :=
  ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩

/-- The permutation matrix that swaps the marker of a one-cell configuration. -/
def qtmLocalMarker {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A] :
    Matrix (Fin 1 → CellState Q A) (Fin 1 → CellState Q A) ℂ :=
  permMatrix (fun r => fun _ => markSwap (r 0))

/-- The marker update on one-cell configurations is involutive. -/
private theorem qtmLocalMarker_invol {Q A : Type} :
    Function.Involutive (fun r : Fin 1 → CellState Q A => fun _ => markSwap (r 0)) := by
  intro r
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  simpa only [hi] using! qtmMarkSwap_invol (r 0)

/-- The one-cell marker permutation matrix is unitary. -/
theorem qtmLocalMarker_unitary {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] :
    (qtmLocalMarker : Matrix (Fin 1 → CellState Q A) (Fin 1 → CellState Q A) ℂ) ∈
      unitaryGroup (Fin 1 → CellState Q A) ℂ :=
  permMatrix_unitary qtmLocalMarker_invol

/-- The full-configuration gate applying the local marker swap at cell `j`. -/
def qtmMarkerCell {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    {c : ℕ} (j : Fin c) : Matrix (Fin c → CellState Q A) (Fin c → CellState Q A) ℂ :=
  qtmCellGate (qtmSingleCell j) qtmLocalMarker

/-- The configuration obtained by swapping the marker at cell `j` and retaining all other cells. -/
def qtmMarkerUpdate {Q A : Type} {c : ℕ} (j : Fin c) (r : Fin c → CellState Q A) :
    Fin c → CellState Q A := Function.update r j (markSwap (r j))

/-- Applying the marker gate at `j` to a basis state gives the basis state of `qtmMarkerUpdate j
r`. -/
theorem qtmMarkerCell_ket {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {c : ℕ} (j : Fin c) (r : Fin c → CellState Q A) :
    ApplyGate (qtmMarkerCell j) (Qatlib.Foundations.PureStateMath.Ket r) = Qatlib.Foundations.PureStateMath.Ket (qtmMarkerUpdate j r) := by
  have hcoeff (s : Fin 1 → CellState Q A) : qtmLocalMarker s (fun _ => r j) =
      Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin 1 => markSwap (r j)) s := by
    have h := congrFun (applyGate_permMatrix_ket qtmLocalMarker_invol
      (fun _ : Fin 1 => r j)) s
    simpa [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,qtmLocalMarker] using! h
  rw [qtmMarkerCell,qtmCellGate_ket]
  simp only [qtmSingleCell,Function.Embedding.coeFn_mk,hcoeff]
  simp only [Qatlib.Foundations.PureStateMath.Ket,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  funext i
  by_cases hi : i=j
  · subst i
    change qtmCellContextExtend (qtmSingleCell j) r _ (qtmSingleCell j 0) = _
    rw [qtmCellContextExtend_at]
    simp [qtmMarkerUpdate]
  · have hn : ¬∃ u : Fin 1, qtmSingleCell j u = i := by
      rintro ⟨u,hu⟩
      exact hi hu.symm
    change Function.extend (fun _ : Fin 1 => j) (fun _ : Fin 1 => markSwap (r j)) r i = _
    have hn' : ¬∃ u : Fin 1, (fun _ : Fin 1 => j) u = i := hn
    rw [Function.extend_apply' _ _ _ hn']
    simp [qtmMarkerUpdate,hi]

/-- Apply the marker updates in `js` successively to a cell configuration. -/
private def qtmMarkerTransform {Q A : Type} {c : ℕ} (js : List (Fin c))
    (r : Fin c → CellState Q A) : Fin c → CellState Q A :=
  js.foldl (fun s j => qtmMarkerUpdate j s) r

/-- For a list of distinct positions, the marker transform swaps exactly the listed cells. -/
private theorem qtmMarkerTransform_at {Q A : Type} {c : ℕ} (js : List (Fin c))
    (hjs : js.Nodup) (r : Fin c → CellState Q A) (j : Fin c) :
    qtmMarkerTransform js r j = if j ∈ js then markSwap (r j) else r j := by
  induction js generalizing r with
  | nil => simp [qtmMarkerTransform]
  | cons a js ih =>
    obtain ⟨ha,hnd⟩ := List.nodup_cons.mp hjs
    change qtmMarkerTransform js (qtmMarkerUpdate a r) j = _
    rw [ih hnd]
    by_cases hja : j=a
    · subst j
      simp [ha,qtmMarkerUpdate]
    · simp [qtmMarkerUpdate,hja]

/-- Updating every finite cell position once swaps all markers pointwise. -/
private theorem qtmMarkerTransform_full {Q A : Type} (c : ℕ) (r : Fin c → CellState Q A) :
    qtmMarkerTransform (List.finRange c) r = fun j => markSwap (r j) := by
  funext j
  rw [qtmMarkerTransform_at _ (List.nodup_finRange c)]
  simp [List.mem_finRange]

/-- Running the listed marker gates on a basis state gives the basis state of the corresponding
marker transform. -/
private theorem qtmMarker_run_ket {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {c : ℕ} (js : List (Fin c)) (r : Fin c → CellState Q A) :
    Run 1 (js.map (fun j => Step.gate (qtmMarkerCell j))) (Qatlib.Foundations.PureStateMath.Ket r) =
      Qatlib.Foundations.PureStateMath.Ket (qtmMarkerTransform js r) := by
  induction js generalizing r with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,run_gate,qtmMarkerCell_ket]
    exact ih _

/-- Circuit execution with identity oracle distributes over finite sums of states. -/
private theorem qtmRun_sum {I : Type} [Fintype I] [DecidableEq I] (C : Circuit I)
    {J : Type} [Fintype J] (ψ : J → QState I) :
    Run (1 : Matrix I I ℂ) C (∑ j, ψ j) = ∑ j, Run 1 C (ψ j) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run,ApplyGate,Matrix.mulVec_sum] <;> exact ih _

/-- Circuit execution with identity oracle commutes with complex scalar multiplication. -/
private theorem qtmRun_smul {I : Type} [Fintype I] [DecidableEq I] (C : Circuit I) (z : ℂ) (ψ : QState I) :
    Run (1 : Matrix I I ℂ) C (z • ψ) = z • Run 1 C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run,ApplyGate,Matrix.mulVec_smul] <;> exact ih _

/-- Sweeping the marker gate over every cell of the QTM window equals applying `iSwapFull` to
any state. -/
theorem qtmMarker_sweep {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t : ℕ) (ψ : QState (WReg t Q A)) :
    Run 1 ((List.finRange (2*t+1)).map (fun j => Step.gate (qtmMarkerCell j))) ψ =
      ApplyGate (iSwapFull t) ψ := by
  have hinv : Function.Involutive (fun r : WReg t Q A => fun j => markSwap (r j)) := by
    intro r
    funext j
    exact qtmMarkSwap_invol _
  rw [state_ket_expansion ψ,qtmRun_sum]
  simp only [ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [qtmRun_smul,qtmMarker_run_ket,qtmMarkerTransform_full]
  exact congrArg (fun v => ψ r • v) (applyGate_permMatrix_ket hinv r).symm

end Qatlib.Concepts.QtmSimulation.Phi3Compilation
