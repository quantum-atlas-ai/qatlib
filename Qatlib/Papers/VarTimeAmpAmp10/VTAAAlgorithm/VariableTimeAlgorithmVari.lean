/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.ForwardProgram
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeAlgorithmContracts
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix

set_option maxHeartbeats 1200000

noncomputable section

theorem vt_endpoint_premises_impossible {C : Type} [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (hm : 1 ≤ stages.length)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag)
    (hfloor : 1 / (10 ^ 12 * (stages.length : ℝ) ^ 3) ≤
      MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)) : False := by
  have hmpos : (0 : ℝ) < stages.length := by exact_mod_cast (by omega : 0 < stages.length)
  have hpos : (0 : ℝ) < 1 / (10 ^ 12 * (stages.length : ℝ) ^ 3) := by positivity
  rw [vt_running_source_good_mass_zero stages hs j₀ hj] at hfloor
  linarith

theorem vt_any_unitary_free_word {C W : Type} [Fintype C] [DecidableEq C]
    [Fintype W] [DecidableEq W]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (U : Matrix (VtReg W C) (VtReg W C) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (VtReg W C) ℂ) :
    WordLegal stages [VtStep.fixGate U] ∧
      wordStageTime [VtStep.fixGate U] = 0 ∧
      ∀ ψ, Run 1 (compileWord stages [VtStep.fixGate U]) ψ = ApplyGate U ψ := by
  refine ⟨?_, rfl, ?_⟩
  · simpa [WordLegal] using hU
  · intro ψ
    simp [compileWord, stepMatrix, Run]

section DeterministicEndpoint

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

def vtBackwardWord (n : ℕ) : List (StructuralVtStep W C) :=
  (List.range n).reverse.map StructuralVtStep.stageB

def vtAARound (n : ℕ) : List (StructuralVtStep W C) :=
  StructuralVtStep.goodReflection ::
    (vtBackwardWord n ++ (StructuralVtStep.sourceReflection :: vtForwardWord n))

def vtAAWord (n k : ℕ) : List (StructuralVtStep W C) :=
  vtForwardWord n ++ (List.replicate k (vtAARound n)).flatten

theorem vt_backward_word_succ (n : ℕ) :
    vtBackwardWord (W := W) (C := C) (n+1)
      = StructuralVtStep.stageB n :: vtBackwardWord (W := W) (C := C) n := by
  simp [vtBackwardWord, List.range_succ]

theorem vt_stepTime_stageB (j : ℕ) :
    structuralStepTime (StructuralVtStep.stageB j : StructuralVtStep W C) = 2^j := rfl

theorem vt_stepTime_goodReflection :
    structuralStepTime (StructuralVtStep.goodReflection : StructuralVtStep W C) = 0 := rfl

theorem vt_stepTime_sourceReflection :
    structuralStepTime (StructuralVtStep.sourceReflection : StructuralVtStep W C) = 0 := rfl

theorem structuralWordTime_cons (s : StructuralVtStep W C) (w : List (StructuralVtStep W C)) :
    structuralWordTime (s :: w) = structuralStepTime s + structuralWordTime w := rfl

theorem structuralWordTime_append (w₁ w₂ : List (StructuralVtStep W C)) :
    structuralWordTime (w₁ ++ w₂) = structuralWordTime w₁ + structuralWordTime w₂ := by
  simp only [structuralWordTime, List.map_append, List.sum_append]

theorem vt_backward_word_cost (n : ℕ) :
    structuralWordTime (vtBackwardWord (W := W) (C := C) n) = 2^n-1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 0 < 2^n := by positivity
    rw [vt_backward_word_succ, structuralWordTime_cons, vt_stepTime_stageB, ih, pow_succ]
    omega

theorem vt_round_cost (n : ℕ) :
    structuralWordTime (vtAARound (W := W) (C := C) n) = 2*(2^n-1) := by
  have hpos : 0 < 2^n := by positivity
  rw [vtAARound, structuralWordTime_cons, structuralWordTime_append, structuralWordTime_cons,
    vt_stepTime_goodReflection, vt_stepTime_sourceReflection, vt_forward_word_cost,
    vt_backward_word_cost]
  omega

theorem vt_aa_word_cost (n k : ℕ) :
    structuralWordTime (vtAAWord (W := W) (C := C) n k) = (2*k+1)*(2^n-1) := by
  have hpos : 0 < 2^n := by positivity
  have hflat : ∀ j : ℕ,
      structuralWordTime ((List.replicate j (vtAARound (W := W) (C := C) n)).flatten)
        = j * (2*(2^n-1)) := by
    intro j
    induction j with
    | zero => simp [structuralWordTime]
    | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, structuralWordTime_append, vt_round_cost, ih]
      ring
  rw [vtAAWord, structuralWordTime_append, vt_forward_word_cost, hflat]
  ring

theorem vt_backward_word_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (n : ℕ) (hn : n ≤ stages.length) :
    StructuralWordLegal (W := W) stages (vtBackwardWord (W := W) (C := C) n) := by
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  simp only [List.mem_reverse, List.mem_range] at hj
  exact hj.trans_le hn

theorem vt_aa_word_legal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (n : ℕ) (hn : n ≤ stages.length) (k : ℕ) :
    StructuralWordLegal (W := W) stages (vtAAWord (W := W) (C := C) n k) := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact vt_forward_word_legal stages n hn s hs
  · obtain ⟨r, hr, hsr⟩ := List.mem_flatten.mp hs
    have hrw : r = vtAARound (W := W) (C := C) n := (List.mem_replicate.mp hr).2
    subst hrw
    rcases List.mem_cons.mp hsr with rfl | hsrest
    · trivial
    · rcases List.mem_append.mp hsrest with hsrest | hsrest
      · exact vt_backward_word_legal stages n hn s hsrest
      · rcases List.mem_cons.mp hsrest with rfl | hsrest
        · trivial
        · exact vt_forward_word_legal stages n hn s hsrest

def vtStepMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (j₀ : VtSpace C) :
    StructuralVtStep W C → Matrix (VtSpace C) (VtSpace C) ℂ
  | .stageF j => stages.getD j 0
  | .stageB j => (stages.getD j 0)ᴴ
  | .goodReflection => preparedMark (goodSet C)
  | .sourceReflection => ReflectionAbout (outerProduct (Ket j₀))
  | _ => 1

def vtWordMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (j₀ : VtSpace C) :
    List (StructuralVtStep W C) → Matrix (VtSpace C) (VtSpace C) ℂ
  | [] => 1
  | s :: w => vtWordMatrix stages j₀ w * vtStepMatrix stages j₀ s

def vtBasicStep (s : StructuralVtStep W C) : Prop :=
  match s with
  | .stageF _ | .stageB _ | .goodReflection | .sourceReflection => True
  | _ => False

theorem vt_step_matrix_eq (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (s : StructuralVtStep W C)
    (hs : vtBasicStep s) :
    structuralStepMatrix stages history j₀ s
      = TensorGate (1 : Matrix W W ℂ) (TensorGate (1 : Matrix Bool Bool ℂ)
          (vtStepMatrix stages j₀ s)) := by
  cases s with
  | stageF j => rfl
  | stageB j => rfl
  | cstageF j => exact hs.elim
  | cstageB j => exact hs.elim
  | workspaceGate U => exact hs.elim
  | sourceReflection => rfl
  | csourceReflection => exact hs.elim
  | goodReflection => rfl
  | cgoodReflection => exact hs.elim
  | reachedReflection k => exact hs.elim
  | creachedReflection k => exact hs.elim

theorem applyGate_double_tensorGate (M : Matrix (VtSpace C) (VtSpace C) ℂ)
    (a : QState W) (b : QState Bool) (ψ : QState (VtSpace C)) :
    ApplyGate (TensorGate (1 : Matrix W W ℂ) (TensorGate (1 : Matrix Bool Bool ℂ) M))
        (TensorState a (TensorState b ψ)) = TensorState a (TensorState b (M *ᵥ ψ)) := by
  rw [applyGate_tensorGate, applyGate_tensorGate, applyGate_one, applyGate_one]
  rfl

theorem vt_word_matrix_append (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (w₁ w₂ : List (StructuralVtStep W C)) :
    vtWordMatrix stages j₀ (w₁ ++ w₂)
      = vtWordMatrix stages j₀ w₂ * vtWordMatrix stages j₀ w₁ := by
  induction w₁ with
  | nil => simp [vtWordMatrix]
  | cons s w ih => rw [List.cons_append, vtWordMatrix, vtWordMatrix, ih, ← Matrix.mul_assoc]

theorem vt_basic_word_transport (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (w₀ : W)
    (w : List (StructuralVtStep W C)) (hw : ∀ s ∈ w, vtBasicStep s)
    (ψ : QState (VtSpace C)) :
    Run 1 (compileStructuralWord stages history j₀ w)
        (TensorState (Ket w₀) (TensorState (Ket false) ψ))
      = TensorState (Ket w₀) (TensorState (Ket false) (vtWordMatrix stages j₀ w *ᵥ ψ)) := by
  induction w generalizing ψ with
  | nil => simp [compileStructuralWord, vtWordMatrix]
  | cons s w ih =>
    have hs : vtBasicStep s := hw s List.mem_cons_self
    have hmem : ∀ t ∈ w, vtBasicStep t := fun t ht => hw t (List.mem_cons_of_mem _ ht)
    have hcomp : compileStructuralWord stages history j₀ (s :: w)
        = [Step.gate (structuralStepMatrix stages history j₀ s)]
          ++ compileStructuralWord stages history j₀ w := rfl
    rw [hcomp, run_append, run_gate, run_nil, vt_step_matrix_eq stages history j₀ s hs,
      applyGate_double_tensorGate, ih hmem, vtWordMatrix, ← Matrix.mulVec_mulVec]

theorem vt_word_matrix_singleton (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (s : StructuralVtStep W C) :
    vtWordMatrix stages j₀ [s] = vtStepMatrix stages j₀ s := by
  simp [vtWordMatrix]

theorem vt_forward_word_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (n : ℕ) (hn : n ≤ stages.length) :
    vtWordMatrix stages j₀ (vtForwardWord (W := W) n) = vtRunMatrix stages n := by
  induction n with
  | zero => simp [vtForwardWord, vtWordMatrix, vtRunMatrix]
  | succ n ih =>
    have hk : n < stages.length := by omega
    have hword : vtForwardWord (W := W) (C := C) (n+1)
        = vtForwardWord (W := W) (C := C) n ++ [StructuralVtStep.stageF n] := by
      simp [vtForwardWord, List.range_succ]
    rw [hword, vt_word_matrix_append, ih (by omega), vt_word_matrix_singleton]
    rw [vt_prefix_step stages n hk]
    congr 1
    simp only [vtStepMatrix]
    exact List.getD_eq_getElem stages 0 hk

theorem vt_backward_word_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (n : ℕ) (hn : n ≤ stages.length) :
    vtWordMatrix stages j₀ (vtBackwardWord (W := W) (C := C) n) = (vtRunMatrix stages n)ᴴ := by
  induction n with
  | zero => simp [vtBackwardWord, vtWordMatrix, vtRunMatrix]
  | succ n ih =>
    have hk : n < stages.length := by omega
    rw [vt_backward_word_succ, vtWordMatrix, ih (by omega), vt_prefix_step stages n hk,
      Matrix.conjTranspose_mul]
    congr 1
    simp only [vtStepMatrix]
    rw [List.getD_eq_getElem stages 0 hk]

theorem vt_round_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (n : ℕ) (hn : n ≤ stages.length) :
    vtWordMatrix stages j₀ (vtAARound (W := W) (C := C) n)
      = preparedAAIterate (vtRunMatrix stages n) j₀ (goodSet C) := by
  have hw : vtAARound (W := W) (C := C) n
      = [StructuralVtStep.goodReflection] ++ (vtBackwardWord (W := W) (C := C) n
        ++ [StructuralVtStep.sourceReflection] ++ vtForwardWord (W := W) (C := C) n) := by
    simp [vtAARound]
  rw [hw, vt_word_matrix_append, vt_word_matrix_singleton, vt_word_matrix_append,
    vt_word_matrix_append, vt_word_matrix_singleton,
    vt_forward_word_matrix stages j₀ n hn, vt_backward_word_matrix stages j₀ n hn]
  simp only [Matrix.mul_assoc, vtStepMatrix, preparedAAIterate]

theorem vt_aa_word_matrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (j₀ : VtSpace C) (n : ℕ) (hn : n ≤ stages.length) (k : ℕ) :
    vtWordMatrix stages j₀ (vtAAWord (W := W) (C := C) n k)
      = (preparedAAIterate (vtRunMatrix stages n) j₀ (goodSet C))^k * vtRunMatrix stages n := by
  induction k with
  | zero =>
    have h0 : vtAAWord (W := W) (C := C) n 0 = vtForwardWord (W := W) (C := C) n := by
      simp [vtAAWord]
    rw [h0, vt_forward_word_matrix stages j₀ n hn, pow_zero, Matrix.one_mul]
  | succ k _ih =>
    have hflatM : ∀ j : ℕ, vtWordMatrix stages j₀
        ((List.replicate j (vtAARound (W := W) (C := C) n)).flatten)
        = (preparedAAIterate (vtRunMatrix stages n) j₀ (goodSet C))^j := by
      intro j
      induction j with
      | zero => simp [vtWordMatrix]
      | succ j ihj =>
        rw [List.replicate_succ, List.flatten_cons, vt_word_matrix_append,
          vt_round_matrix stages j₀ n hn, ihj, ← pow_succ]
    have hr : (List.replicate (k+1) (vtAARound (W := W) (C := C) n)).flatten
        = vtAARound (W := W) (C := C) n ++ (List.replicate k (vtAARound (W := W) (C := C) n)).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    rw [vtAAWord, hr, vt_word_matrix_append, vt_word_matrix_append,
      vt_forward_word_matrix stages j₀ n hn, vt_round_matrix stages j₀ n hn,
      hflatM, ← pow_succ]

theorem embedState_eq_tensor (w₀ : W) (χ : QState (VtSpace C)) :
    embedState w₀ χ = TensorState (Ket w₀) (TensorState (Ket false) χ) := by
  funext p
  simp only [embedState, TensorState]
  by_cases h1 : p.1 = w₀ <;> by_cases h2 : p.2.1 = false <;>
    simp [h1, h2, Ket]

theorem measureProb_tensor_embed_sector (w₀ : W) (φ : QState (VtSpace C)) (f : Fin 3) :
    MeasureProb (TensorState (Ket w₀) (TensorState (Ket false) φ))
        (Finset.univ.filter fun p : VtReg W C => p.2.2.1 = f) =
      MeasureProb φ (Finset.univ.filter fun q : VtSpace C => q.1 = f) := by
  have hset : (Finset.univ.filter fun p : VtReg W C => p.2.2.1 = f)
      = Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ.filter fun q : VtSpace C => q.1 = f)) := by
    ext p
    obtain ⟨w, b, x⟩ := p
    simp [Finset.mem_filter, Finset.mem_product]
  rw [hset, measureProb_tensorState_right (normalized_ket w₀),
    measureProb_tensorState_right (normalized_ket false)]

theorem collapse_embed_sector (w₀ : W) (φ : QState (VtSpace C)) :
    Collapse (TensorState (Ket w₀) (TensorState (Ket false) φ))
        (Finset.univ.filter fun p : VtReg W C => p.2.2.1 = vtGoodFlag)
      = embedState w₀ (Collapse φ (goodSet C)) := by
  funext p
  simp only [collapse_apply, embedState, goodSet, Finset.mem_filter, Finset.mem_univ, TensorState,
    Ket]
  by_cases h1 : p.1 = w₀ <;> by_cases h2 : p.2.1 = false <;>
    by_cases h3 : p.2.2.1 = vtGoodFlag <;> simp [h1, h2, h3]

theorem collapse_add_smul (c d : ℂ) (u v : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    Collapse (c • u + d • v) S = c • Collapse u S + d • Collapse v S := by
  funext i
  simp only [collapse_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  by_cases h : i ∈ S <;> simp [h]

theorem collapse_sub_self (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    Collapse (ψ - Collapse ψ S) S = 0 := by
  funext i
  simp only [collapse_apply, Pi.sub_apply]
  by_cases h : i ∈ S <;> simp [h]

theorem collapse_idem (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    Collapse (Collapse ψ S) S = Collapse ψ S := by
  funext i
  simp only [collapse_apply]
  by_cases h : i ∈ S <;> simp [h]

theorem embedState_smul (w₀ : W) (c : ℂ) (χ : QState (VtSpace C)) :
    embedState w₀ (c • χ) = c • embedState w₀ χ := by
  funext p
  simp only [embedState, Pi.smul_apply, smul_eq_mul]
  by_cases h : p.1 = w₀ ∧ p.2.1 = false <;> simp [h]

theorem vt_forward_word_basic (n : ℕ) :
    ∀ s ∈ vtForwardWord (W := W) (C := C) n, vtBasicStep s := by
  intro s hs
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
  trivial

theorem vt_backward_word_basic (n : ℕ) :
    ∀ s ∈ vtBackwardWord (W := W) (C := C) n, vtBasicStep s := by
  intro s hs
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
  trivial

theorem vt_round_basic (n : ℕ) :
    ∀ s ∈ vtAARound (W := W) (C := C) n, vtBasicStep s := by
  intro s hs
  simp only [vtAARound, List.mem_cons, List.mem_append] at hs
  rcases hs with rfl | hs | hs
  · trivial
  · exact vt_backward_word_basic n s hs
  · rcases hs with rfl | hs
    · trivial
    · exact vt_forward_word_basic n s hs

theorem vt_aa_word_basic (n k : ℕ) :
    ∀ s ∈ vtAAWord (W := W) (C := C) n k, vtBasicStep s := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact vt_forward_word_basic n s hs
  · obtain ⟨r, hr, hsr⟩ := List.mem_flatten.mp hs
    have hrw : r = vtAARound (W := W) (C := C) n := (List.mem_replicate.mp hr).2
    subst hrw
    exact vt_round_basic n s hsr

theorem vt_sqrt_le_arcsin {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt p ≤ Real.arcsin (Real.sqrt p) := by
  by_contra hlt
  have hs1 : Real.sqrt p ≤ 1 := (Real.sqrt_le_one).mpr hp1
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hlt2 : Real.sin (Real.arcsin (Real.sqrt p)) < Real.sin (Real.sqrt p) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (Real.arcsin_mem_Icc _).1
      (hs1.trans Real.one_le_pi_div_two) (lt_of_not_ge hlt)
  rw [Real.sin_arcsin (by linarith) hs1] at hlt2
  exact not_lt_of_ge (Real.sin_le hs0) hlt2

theorem vt_theta0_le_pi_div_four : Real.arcsin (Real.sqrt (2/5)) ≤ Real.pi / 4 := by
  have hm : Real.sqrt (2/5) ∈ Set.Icc (-1:ℝ) 1 :=
    ⟨by have := Real.sqrt_nonneg (2/5); linarith, by exact (Real.sqrt_le_one).mpr (by norm_num)⟩
  have hpim : Real.pi / 4 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.arcsin_le_iff_le_sin hm hpim, Real.sin_pi_div_four]
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem vt_sin_ge_of_arc {x θ₀ : ℝ} (hθ0 : 0 ≤ θ₀) (hx1 : θ₀ ≤ x) (hx2 : x ≤ Real.pi - θ₀) :
    Real.sin θ₀ ≤ Real.sin x := by
  rcases le_total x (Real.pi/2) with hx | hx
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hx1
  · have h1 : Real.sin θ₀ ≤ Real.sin (Real.pi - x) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by have := Real.pi_pos; linarith)
        (by have := Real.pi_pos; linarith) (by linarith)
    rwa [Real.sin_pi_sub] at h1

theorem variableTimeAlgorithm_answer : VariableTimeAlgorithm := by
  intro C _iC _dC stages history hlegal hm j₀ hj hsup hΨ hstop hfloor
  classical
  have hA : vtRunMatrix stages stages.length ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
    growing_prefix_unitary stages history hlegal stages.length
  have hΨnorm : Normalized (preparedAAState (vtRunMatrix stages stages.length) j₀) :=
    normalized_applyGate hA (normalized_ket j₀)
  have hpnorm : Normalized (vtState stages stages.length (Ket j₀)) := hΨnorm
  have hp1 : MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C) ≤ 1 :=
    measureProb_le_one hpnorm (goodSet C)
  have hTT : (0:ℝ) ≤ vtTmax stages := by
    have : (0:ℝ) ≤ (2:ℝ)^stages.length := by positivity
    exact this
  have hdn : (0:ℝ) ≤ reachedTav stages history j₀
      / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hL1 : (1:ℝ) ≤ (stages.length:ℝ) := by exact_mod_cast hm
  have hLs : (1:ℝ) ≤ Real.sqrt (stages.length:ℝ) := by
    have h := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h

  have hbd : ∀ c : ℝ, 0 ≤ c → c ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ) →
      c * vtTmax stages ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)*
        (vtTmax stages + reachedTav stages history j₀
          / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C))) := by
    intro c hc0 hc
    have h1 : c * vtTmax stages ≤ c * (vtTmax stages + reachedTav stages history j₀
        / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C))) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hdn) hc0
    have h2 : c * (vtTmax stages + reachedTav stages history j₀
        / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)))
        ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)*
          (vtTmax stages + reachedTav stages history j₀
            / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C))) := by
      exact mul_le_mul hc (le_refl _)
        (add_nonneg hTT hdn)
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4000000) (Nat.cast_nonneg stages.length))
          (Real.sqrt_nonneg _))
    exact le_trans h1 h2
  have hc1le : (1:ℝ) ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ) := by
    have h12 : (1:ℝ)*(1:ℝ) ≤ (stages.length:ℝ)*Real.sqrt (stages.length:ℝ) :=
      mul_le_mul hL1 hLs (by norm_num) (by norm_num)
    nlinarith [h12]
  by_cases hcase : 2/5 ≤ MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C)
  · refine ⟨Unit, inferInstance, fun _ => 1, Finset.univ, Unit, inferInstance, inferInstance, (),
      fun _ => vtAAWord stages.length 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro ω; norm_num
    · intro ω; exact vt_aa_word_legal stages stages.length (le_refl _) 0
    · intro ω
      have hp2 : (1:ℕ) ≤ 2^stages.length := Nat.one_le_two_pow
      have hcast : (((2:ℕ)^stages.length - 1 : ℕ):ℝ) = (2:ℝ)^stages.length - 1 := by
        rw [Nat.cast_sub hp2]; push_cast; ring
      have hmul : ((2*0+1)*(2^stages.length-1) : ℕ) = 2^stages.length - 1 := by norm_num
      have hkey := hbd 1 (by norm_num) hc1le
      rw [vt_aa_word_cost, hmul, hcast]
      have hTeq : vtTmax stages = (2:ℝ)^stages.length := rfl
      rw [hTeq] at hkey
      calc ((2:ℝ)^stages.length - 1) = 1 * ((2:ℝ)^stages.length - 1) := by ring
        _ ≤ 1 * (2:ℝ)^stages.length := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            linarith
        _ ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)*
              ((2:ℝ)^stages.length + reachedTav stages history j₀
                / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C))) := hkey
        _ = 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)*
              (vtTmax stages + reachedTav stages history j₀
                / Real.sqrt (MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C))) := by
            rw [hTeq]
    · simp
    · intro ω _
      have h0 : vtAAWord (W := Unit) (C := C) stages.length 0 = vtForwardWord stages.length := by
        simp [vtAAWord]
      have hket : Ket ((), false, j₀) = TensorState (Ket ()) (TensorState (Ket false) (Ket j₀)) := by
        rw [← tensorState_ket_ket, ← tensorState_ket_ket]
      have htr := vt_forward_word_state stages history j₀ () (Ket j₀) stages.length (le_refl _)
      constructor
      · show 2/5 ≤ MeasureProb (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length 0)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun p : VtReg Unit C => p.2.2.1 = vtGoodFlag)
        rw [h0, hket, htr, measureProb_tensor_embed_sector]
        exact hcase
      constructor
      · show MeasureProb (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length 0)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun p : VtReg Unit C => p.2.2.1 = vtRunningFlag) ≤ 3/5
        rw [h0, hket, htr, measureProb_tensor_embed_sector]
        have hz : MeasureProb (vtState stages stages.length (Ket j₀))
            (Finset.univ.filter fun q : VtSpace C => q.1 = vtRunningFlag) = 0 := hstop
        rw [hz]
        norm_num
      · refine ⟨1, ?_⟩
        show Collapse (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length 0)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun p : VtReg Unit C => p.2.2.1 = vtGoodFlag)
          = (1:ℂ) • embedState () (Collapse (vtState stages stages.length (Ket j₀)) (goodSet C))
        rw [h0, hket, htr, collapse_embed_sector, one_smul]
  · have hp' : MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C) < 2/5 :=
      lt_of_not_ge hcase
    have hfloorpos : (0:ℝ) < 1/(10^12*(stages.length:ℝ)^3) := by positivity
    have hp0 : (0:ℝ) < MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C) :=
      lt_of_lt_of_le hfloorpos hfloor
    set p := MeasureProb (vtState stages stages.length (Ket j₀)) (goodSet C) with hpdef
    have hsp1 : Real.sqrt p ≤ 1 := (Real.sqrt_le_one).mpr hp1
    have hsinθ : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
      Real.sin_arcsin (by have := Real.sqrt_nonneg p; linarith) hsp1
    have hsinθ₀ : Real.sin (Real.arcsin (Real.sqrt (2/5))) = Real.sqrt (2/5) :=
      Real.sin_arcsin (by have := Real.sqrt_nonneg (2/5); linarith)
        (by exact (Real.sqrt_le_one).mpr (by norm_num))
    have hθpos : 0 < Real.arcsin (Real.sqrt p) :=
      (Real.arcsin_pos).mpr (Real.sqrt_pos.mpr hp0)
    have hθlt : Real.arcsin (Real.sqrt p) < Real.pi/2 := by
      have h1 : p < 1 := lt_of_lt_of_le hp' (by norm_num)
      have hlt1 : Real.sqrt p < 1 :=
        (Real.sqrt_lt (le_of_lt hp0) (by norm_num : (0:ℝ) ≤ 1)).mpr (by rw [one_pow]; exact h1)
      exact (Real.arcsin_lt_pi_div_two).mpr hlt1
    have hθθ₀ : Real.arcsin (Real.sqrt p) < Real.arcsin (Real.sqrt (2/5)) :=
      Real.arcsin_lt_arcsin (by have := Real.sqrt_nonneg p; linarith)
        (Real.sqrt_lt_sqrt (le_of_lt hp0) hp')
        (by exact (Real.sqrt_le_one).mpr (by norm_num))
    have hex : ∃ n : ℕ, Real.arcsin (Real.sqrt (2/5)) ≤ (2*n+1)*Real.arcsin (Real.sqrt p) := by
      refine ⟨Nat.ceil (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)), ?_⟩
      have hc : Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)
          ≤ Nat.ceil (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)) := Nat.le_ceil _
      have hce : (0:ℝ) ≤ ((Nat.ceil (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)) : ℕ):ℝ) :=
        Nat.cast_nonneg _
      calc Real.arcsin (Real.sqrt (2/5))
          = (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p))*Real.arcsin (Real.sqrt p) := by
            field_simp
        _ ≤ (Nat.ceil (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)) : ℝ)*Real.arcsin (Real.sqrt p) :=
            mul_le_mul_of_nonneg_right hc (le_of_lt hθpos)
        _ ≤ (2*(Nat.ceil (Real.arcsin (Real.sqrt (2/5)) / Real.arcsin (Real.sqrt p)))+1)*Real.arcsin (Real.sqrt p) := by
            nlinarith [hce, hθpos]
    have hk : ∃ k : ℕ, Real.arcsin (Real.sqrt (2/5)) ≤ (2*k+1)*Real.arcsin (Real.sqrt p)
        ∧ ∀ j < k, ¬(Real.arcsin (Real.sqrt (2/5)) ≤ (2*j+1)*Real.arcsin (Real.sqrt p)) := by
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      intro j hj
      exact Nat.find_min hex hj
    obtain ⟨k, hkspec, hkmin⟩ := hk
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      have hle : Real.arcsin (Real.sqrt (2/5)) ≤ Real.arcsin (Real.sqrt p) := by
        simpa using hkspec
      exact absurd hle (not_le.mpr hθθ₀)
    have hkprev : (2*((k:ℕ):ℝ)-1)*Real.arcsin (Real.sqrt p) < Real.arcsin (Real.sqrt (2/5)) := by
      have h := hkmin (k-1) (by omega)
      push_neg at h
      have hsplit : (2*((k-1:ℕ):ℝ)+1) = 2*((k:ℕ):ℝ)-1 := by
        rw [Nat.cast_sub hk1]
        push_cast
        ring
      rwa [hsplit] at h
    have hqlt : (2*k+1)*Real.arcsin (Real.sqrt p)
        < Real.arcsin (Real.sqrt (2/5)) + 2*Real.arcsin (Real.sqrt p) := by
      have hsplit : (2*k+1)*Real.arcsin (Real.sqrt p)
          = (2*k-1)*Real.arcsin (Real.sqrt p) + 2*Real.arcsin (Real.sqrt p) := by ring
      rw [hsplit]
      linarith
    have hθ₀pi : 4*Real.arcsin (Real.sqrt (2/5)) ≤ Real.pi := by
      have h := vt_theta0_le_pi_div_four
      linarith
    have hqarc : (2*k+1)*Real.arcsin (Real.sqrt p) ≤ Real.pi - Real.arcsin (Real.sqrt (2/5)) := by
      have h2θ : 2*Real.arcsin (Real.sqrt p) ≤ 2*Real.arcsin (Real.sqrt (2/5)) := by linarith
      linarith
    have hθ₀pos : 0 ≤ Real.arcsin (Real.sqrt (2/5)) :=
      (Real.arcsin_nonneg).mpr (Real.sqrt_nonneg _)
    have hsinq : Real.sqrt (2/5) ≤ Real.sin ((2*k+1)*Real.arcsin (Real.sqrt p)) := by
      have h := vt_sin_ge_of_arc hθ₀pos hkspec hqarc
      rwa [hsinθ₀] at h
    have hgood : 2/5 ≤ (Real.sin ((2*k+1)*Real.arcsin (Real.sqrt p)))^2 := by
      have hsq : (Real.sqrt (2/5))^2
          ≤ (Real.sin ((2*k+1)*Real.arcsin (Real.sqrt p)))^2 :=
        sq_le_sq' (by have hnn := Real.sqrt_nonneg (2/5); linarith) hsinq
      rwa [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/5)] at hsq

    have hprob : MeasureProb (preparedAAState (vtRunMatrix stages stages.length) j₀) (goodSet C)
        = (Real.sin (Real.arcsin (Real.sqrt p)))^2 := by
      have hL : MeasureProb (preparedAAState (vtRunMatrix stages stages.length) j₀) (goodSet C) = p :=
        hpdef.symm
      rw [hL, hsinθ, Real.sq_sqrt (measureProb_nonneg _ _)]
    have hθcast : (2*((k:ℕ):ℝ)+1)*Real.arcsin (Real.sqrt p)
        = ((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p) := by
      push_cast; ring
    have hborn := prepared_aa_born_success (vtRunMatrix stages stages.length) j₀ (goodSet C)
      (Real.arcsin (Real.sqrt p)) k hA hθpos hθlt hprob
    rw [hθcast] at hborn
    rw [hθcast] at hgood
    have hrot := prepared_aa_actual_rotation (vtRunMatrix stages stages.length) j₀ (goodSet C)
      (Real.arcsin (Real.sqrt p)) k hA hθpos hθlt hprob
    rw [hθcast] at hrot

    have hqub : ((2*(k:ℕ)+1 : ℕ):ℝ) < 3/Real.sqrt p := by
      have hθge : Real.sqrt p ≤ Real.arcsin (Real.sqrt p) := vt_sqrt_le_arcsin (le_of_lt hp0) hp1
      have e1 : ((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p)
          < 3*Real.arcsin (Real.sqrt (2/5)) := by
        have h2θ : 2*Real.arcsin (Real.sqrt p) < 2*Real.arcsin (Real.sqrt (2/5)) := by linarith
        have hcast1 : ((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p)
            < Real.arcsin (Real.sqrt (2/5)) + 2*Real.arcsin (Real.sqrt p) := by
          have := hqlt
          exact_mod_cast this
        linarith
      have e2 : 3*Real.arcsin (Real.sqrt (2/5)) ≤ 3*Real.pi/4 := by
        have h := vt_theta0_le_pi_div_four; linarith
      have e3 : ((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p) < 3*Real.pi/4 :=
        lt_of_lt_of_le e1 e2
      have e4 : ((2*(k:ℕ)+1 : ℕ):ℝ) < (3*Real.pi/4)/Real.arcsin (Real.sqrt p) :=
        (lt_div_iff₀ hθpos).mpr e3
      have hinv1 : (Real.arcsin (Real.sqrt p))⁻¹ ≤ (Real.sqrt p)⁻¹ :=
        (inv_le_inv₀ hθpos (Real.sqrt_pos.mpr hp0)).mpr hθge
      have e5 : (3*Real.pi/4)/Real.arcsin (Real.sqrt p) ≤ (3*Real.pi/4)/Real.sqrt p := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv1 (by positivity)
      have e6 : (3*Real.pi/4)/Real.sqrt p < 3/Real.sqrt p := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_lt_mul_of_pos_right (by linarith [Real.pi_lt_four])
          (inv_pos.mpr (Real.sqrt_pos.mpr hp0))
      exact lt_trans (lt_of_lt_of_le e4 e5) e6
    have hsplb : 1/(10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)) ≤ Real.sqrt p := by
      have hx : (0:ℝ) < 10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ) := by positivity
      have hden : ((10^6:ℝ)*(stages.length:ℝ)*Real.sqrt ((stages.length:ℝ)))^2
          = ((10^6:ℝ)^2)*((stages.length:ℝ)^3) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring
      have hle : (1/(10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)))^2 ≤ p := by
        have h1 : (1/(10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)))^2
            = 1/(((10:ℝ)^12)*((stages.length:ℝ)^3)) := by
          have h10 : ((10:ℝ)^6)^2 = (10:ℝ)^12 := by rw [← pow_mul]
          rw [div_pow, one_pow, hden, h10]
        rw [h1]
        exact hfloor
      exact (Real.le_sqrt' (by positivity)).mpr hle
    have hinv : 1/Real.sqrt p ≤ 10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ) :=
      (one_div_le (Real.sqrt_pos.mpr hp0)
        (by positivity : (0:ℝ) < 10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ))).mpr hsplb
    have hcoef' : 3/Real.sqrt p ≤ 4000000*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ) := by
      rw [one_div] at hinv
      have hm1 : 3*((Real.sqrt p)⁻¹)
          ≤ 3*(10^6*(stages.length:ℝ)*Real.sqrt (stages.length:ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      have hnn : (0:ℝ) ≤ (stages.length:ℝ)*Real.sqrt (stages.length:ℝ) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      rw [div_eq_mul_inv]
      nlinarith [hm1, hnn]

    have hket : Ket ((), false, j₀) = TensorState (Ket ()) (TensorState (Ket false) (Ket j₀)) := by
      rw [← tensorState_ket_ket, ← tensorState_ket_ket]
    have htrans := vt_basic_word_transport stages history j₀ () (vtAAWord stages.length k)
      (vt_aa_word_basic (W := Unit) (C := C) stages.length k) (Ket j₀)
    have hmat := vt_aa_word_matrix (W := Unit) stages j₀ stages.length (le_refl _) k
    have hvec : ((preparedAAIterate (vtRunMatrix stages stages.length) j₀ (goodSet C))^k
          * vtRunMatrix stages stages.length) *ᵥ (Ket j₀)
        = Run (preparedMark (goodSet C))
            (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀) := by
      rw [(prepared_aa_actual_circuit (vtRunMatrix stages stages.length) j₀ (goodSet C) k hA).2.2.2,
        ← Matrix.mulVec_mulVec]
      rfl

    have hiterU : (preparedAAIterate (vtRunMatrix stages stages.length) j₀ (goodSet C))^k
        ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
      (Matrix.unitaryGroup (VtSpace C) ℂ).pow_mem
        ((prepared_aa_reflection_and_access (vtRunMatrix stages stages.length) j₀ (goodSet C) hA).2.2.2) k
    have hφnorm : Normalized (Run (preparedMark (goodSet C))
        (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀)) := by
      rw [(prepared_aa_actual_circuit (vtRunMatrix stages stages.length) j₀ (goodSet C) k hA).2.2.2]
      exact normalized_applyGate hiterU hΨnorm
    have hφ' : Normalized (((preparedAAIterate (vtRunMatrix stages stages.length) j₀ (goodSet C))^k
        * vtRunMatrix stages stages.length) *ᵥ (Ket j₀)) := by
      rw [← Matrix.mulVec_mulVec]
      exact normalized_applyGate hiterU (normalized_applyGate hA (normalized_ket j₀))
    have houtnorm : Normalized (Run 1 (compileStructuralWord stages history j₀
        (vtAAWord stages.length k)) (Ket ((), false, j₀))) := by
      rw [hket, htrans, hmat]
      exact normalized_tensorState (normalized_ket ())
        (normalized_tensorState (normalized_ket false) hφ')
    have hdisj : Disjoint (Finset.univ.filter fun q : VtSpace C => q.1 = vtGoodFlag)
        (Finset.univ.filter fun q : VtSpace C => q.1 = vtRunningFlag) := by
      rw [Finset.disjoint_right]
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ] at ha ⊢
      rw [ha.2]
      intro h
      exact (by decide : vtGoodFlag ≠ vtRunningFlag) h.2.symm
    refine ⟨Unit, inferInstance, fun _ => 1, Finset.univ, Unit, inferInstance, inferInstance, (),
      fun _ => vtAAWord stages.length k, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro ω; norm_num
    · intro ω; exact vt_aa_word_legal stages stages.length (le_refl _) k
    · intro ω
      have hp2 : (1:ℕ) ≤ 2^stages.length := Nat.one_le_two_pow
      have hcastm : (((2*k+1)*(2^stages.length-1) : ℕ):ℝ)
          = ((2*(k:ℕ)+1 : ℕ):ℝ)*(((2:ℕ)^stages.length-1 : ℕ):ℝ) := by
        push_cast; ring
      have hcast2 : (((2:ℕ)^stages.length-1 : ℕ):ℝ) = vtTmax stages - 1 := by
        rw [Nat.cast_sub hp2]; push_cast; ring_nf; rfl
      have hsub : (((2:ℕ)^stages.length-1 : ℕ):ℝ) ≤ vtTmax stages := by
        rw [hcast2]; linarith
      have hcst : ((2*(k:ℕ)+1 : ℕ):ℝ)*(((2:ℕ)^stages.length-1 : ℕ):ℝ)
          ≤ 3/Real.sqrt p*vtTmax stages :=
        mul_le_mul hqub.le hsub (by positivity)
          (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      have hfin := hbd (3/Real.sqrt p)
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hcoef'
      rw [vt_aa_word_cost, hcastm]
      linarith
    · simp
    · intro ω _
      constructor
      · show 2/5 ≤ MeasureProb (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length k)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun q : VtReg Unit C => q.2.2.1 = vtGoodFlag)
        rw [hket, htrans, hmat, hvec, measureProb_tensor_embed_sector]
        rw [show (Finset.univ.filter fun q : VtSpace C => q.1 = vtGoodFlag) = goodSet C from rfl]
        rw [hborn]
        exact hgood
      constructor
      · show MeasureProb (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length k)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun q : VtReg Unit C => q.2.2.1 = vtRunningFlag) ≤ 3/5
        rw [hket, htrans, hmat, hvec, measureProb_tensor_embed_sector]
        have hunion := measureProb_union
          (Run (preparedMark (goodSet C))
            (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀)) hdisj
        have htot := measureProb_univ hφnorm
        have hgrun : MeasureProb (Run (preparedMark (goodSet C))
            (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀))
            (Finset.univ.filter fun q : VtSpace C => q.1 = vtGoodFlag)
            + MeasureProb (Run (preparedMark (goodSet C))
            (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀))
            (Finset.univ.filter fun q : VtSpace C => q.1 = vtRunningFlag) ≤ 1 := by
          have h1 := measureProb_le_one hφnorm
            ((Finset.univ.filter fun q : VtSpace C => q.1 = vtGoodFlag) ∪
             (Finset.univ.filter fun q : VtSpace C => q.1 = vtRunningFlag))
          rwa [hunion] at h1
        have h2 : MeasureProb (Run (preparedMark (goodSet C))
            (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀))
            (Finset.univ.filter fun q : VtSpace C => q.1 = vtGoodFlag) ≥ 2/5 := by
          have h2' : MeasureProb (Run (preparedMark (goodSet C))
              (preparedAACircuit (vtRunMatrix stages stages.length) j₀ k) (Ket j₀))
              (goodSet C) ≥ 2/5 := by rw [hborn]; exact hgood
          exact h2'
        linarith
      · refine ⟨((Real.sin (((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p))
            /Real.sin (Real.arcsin (Real.sqrt p)) : ℝ):ℂ), ?_⟩
        show Collapse (Run 1 (compileStructuralWord stages history j₀
            (vtAAWord stages.length k)) (Ket ((), false, j₀)))
            (Finset.univ.filter fun q : VtReg Unit C => q.2.2.1 = vtGoodFlag)
          = ((Real.sin (((2*(k:ℕ)+1 : ℕ):ℝ)*Real.arcsin (Real.sqrt p))
              /Real.sin (Real.arcsin (Real.sqrt p)) : ℝ):ℂ)
            • embedState () (Collapse (vtState stages stages.length (Ket j₀)) (goodSet C))
        rw [hket, htrans, hmat, hvec, collapse_embed_sector, hrot,
          collapse_add_smul, collapse_sub_self, smul_zero, zero_add, collapse_idem,
          embedState_smul]
        rfl

end DeterministicEndpoint

end

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
