/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical
variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

def vtForwardWord (n : ℕ) : List (StructuralVtStep W C) :=
  (List.range n).map StructuralVtStep.stageF

omit [DecidableEq C] in

theorem vt_forward_word_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (n : ℕ) (hn : n ≤ stages.length) : StructuralWordLegal (W := W) stages (vtForwardWord n) := by
  intro s hs
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hs
  exact (List.mem_range.mp hk).trans_le hn

omit [Fintype W] [DecidableEq W] [DecidableEq C] in

theorem vt_forward_word_cost (n : ℕ) : structuralWordTime (vtForwardWord (W := W) (C := C) n)=2^n-1 := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    have hpos : 0 < 2^n := by positivity
    simp only [vtForwardWord,List.range_succ,List.map_append,List.map_cons,List.map_nil,
      structuralWordTime,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,structuralStepTime,add_zero] at ih ⊢
    rw [ih,pow_succ]
    omega

theorem vt_forward_word_state (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (w₀ : W) (ψ : QState (VtSpace C))
    (n : ℕ) (hn : n ≤ stages.length) :
    Run 1 (compileStructuralWord stages history j₀ (vtForwardWord n))
      (TensorState (Ket w₀) (TensorState (Ket false) ψ))=
      TensorState (Ket w₀) (TensorState (Ket false) (vtState stages n ψ)) := by
  induction n with
  | zero=>simp [vtForwardWord,compileStructuralWord,vtState,vtRunMatrix]
  | succ n ih=>
    have hk : n < stages.length := by omega
    have hstep : vtState stages (n+1) ψ=ApplyGate stages[n] (vtState stages n ψ) := by
      rw [vtState,vt_prefix_step stages n hk,← Matrix.mulVec_mulVec]
      rfl
    have hword : vtForwardWord (W := W) (C := C) (n+1)=vtForwardWord n++[.stageF n] := by
      simp [vtForwardWord,List.range_succ]
    rw [hword,compileStructuralWord,List.map_append,run_append]
    have hip:=ih (by omega)
    change Run 1 (compileStructuralWord stages history j₀ [.stageF n])
      (Run 1 (compileStructuralWord stages history j₀ (vtForwardWord n)) _)=_
    rw [hip]
    simp [compileStructuralWord,structuralStepMatrix,stepMatrix,Run,applyGate_tensorGate,
      applyGate_one,List.getElem?_eq_getElem hk,hstep]

theorem vt_forward_prefix_program (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (w₀ : W) (ψ : QState (VtSpace C))
    (n : ℕ) (hn : n ≤ stages.length) :
    StructuralWordLegal stages (vtForwardWord (W := W) n) ∧
    structuralWordTime (vtForwardWord (W := W) (C := C) n)=2^n-1 ∧
    Run 1 (compileStructuralWord stages history j₀ (vtForwardWord n))
      (TensorState (Ket w₀) (TensorState (Ket false) ψ))=
      TensorState (Ket w₀) (TensorState (Ket false) (vtState stages n ψ)) :=
  ⟨vt_forward_word_legal stages n hn,vt_forward_word_cost n,vt_forward_word_state stages history j₀ w₀ ψ n hn⟩
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
