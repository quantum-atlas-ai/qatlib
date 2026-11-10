/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkSpectralDefs
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilation
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Matrix
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander
open scoped Kronecker

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.FrameSpectral
open Matrix
open Qatlib
open scoped Kronecker

private theorem evaluate_cons {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (s : DetectionStep I)
    (ss : List (DetectionStep I)) (w : QState (DetectionSpace I)) :
    (detectionEvaluate U S (s :: ss) *ᵥ w)
      = (detectionInstruction U S s) *ᵥ (detectionEvaluate U S ss *ᵥ w) := by
  have h : detectionEvaluate U S (s :: ss)
      = detectionInstruction U S s * detectionEvaluate U S ss := rfl
  rw [h, ← Matrix.mulVec_mulVec w]

private theorem evaluate_cons3 {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I)
    (s1 s2 s3 : DetectionStep I) (ss : List (DetectionStep I)) (w : QState (DetectionSpace I)) :
    (detectionEvaluate U S (s1 :: s2 :: s3 :: ss) *ᵥ w)
      = (detectionInstruction U S s1 *ᵥ
          (detectionInstruction U S s2 *ᵥ
            (detectionInstruction U S s3 *ᵥ (detectionEvaluate U S ss *ᵥ w)))) := by
  rw [evaluate_cons U S s1 (s2 :: s3 :: ss) w,
    evaluate_cons U S s2 (s3 :: ss) w,
    evaluate_cons U S s3 ss w]

private theorem evaluate_cons2 {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I)
    (s1 s2 : DetectionStep I) (ss : List (DetectionStep I)) (w : QState (DetectionSpace I)) :
    (detectionEvaluate U S (s1 :: s2 :: ss) *ᵥ w)
      = (detectionInstruction U S s1 *ᵥ
          (detectionInstruction U S s2 *ᵥ (detectionEvaluate U S ss *ᵥ w))) := by
  rw [evaluate_cons U S s1 (s2 :: ss) w, evaluate_cons U S s2 ss w]

private theorem evaluate_reflection {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (j : I) (w : QState (DetectionSpace I)) :
    (detectionEvaluate U S (plusIReflectionWord j) *ᵥ w)
      = (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))) := by
  have hlist : plusIReflectionWord j
      = .rowForward :: (.marker :: (.rowBackward :: [])) := rfl
  have hmarker : detectionInstruction U S .marker = detectionMarkGate S := rfl
  have hnil : detectionEvaluate U S [] = 1 := rfl
  rw [hlist, evaluate_cons3 U S .rowForward .marker .rowBackward [] w, hmarker, hnil,
    Matrix.one_mulVec]

private theorem evaluate_walk {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (j : I) (w : QState (DetectionSpace I)) :
    (detectionEvaluate U S (plusIWalkWord j) *ᵥ w)
      = (detectionControlledSwap *ᵥ
          (detectionInstruction U S .rowForward *ᵥ
            (detectionMarkGate S *ᵥ
              (detectionInstruction U S .rowBackward *ᵥ
                (detectionControlledSwap *ᵥ
                  (detectionInstruction U S .rowForward *ᵥ
                    (detectionMarkGate S *ᵥ
                      (detectionInstruction U S .rowBackward *ᵥ w)))))))) := by
  have hlist : plusIWalkWord j
      = .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: [] := rfl
  have hmarker : detectionInstruction U S .marker = detectionMarkGate S := rfl
  have hfixed : detectionInstruction U S (.fixed detectionControlledSwap)
      = detectionControlledSwap := rfl
  have hnil : detectionEvaluate U S [] = 1 := rfl
  rw [hlist,
    evaluate_cons3 U S (.fixed detectionControlledSwap) .rowForward .marker
      (.rowBackward :: (.fixed detectionControlledSwap :: .rowForward :: .marker
        :: .rowBackward :: [])) w,
    evaluate_cons3 U S .rowBackward (.fixed detectionControlledSwap) .rowForward
      (.marker :: .rowBackward :: []) w,
    evaluate_cons2 U S .marker .rowBackward [] w,
    hmarker, hfixed, hnil, Matrix.one_mulVec]

private theorem select_uncontrolled {D : Type} [Fintype D] [DecidableEq D]
    (f : Bool → Matrix D D ℂ) (hf : f false = 1) (v : QState (Bool × D)) :
    ∀ (d : D), (Qatlib.Concepts.BlockEncoding.LCU.select f *ᵥ v) (false, d) = v (false, d) := by
  classical
  intro d
  have hpoint : ∀ (b : Bool) (e : D),
      (Qatlib.Concepts.BlockEncoding.LCU.select f) (false, d) (b, e)
        = if b = false then (if d = e then 1 else 0) else 0 := by
    intro b e
    by_cases hb : b = false
    · subst hb
      simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, hf,
          Matrix.one_apply]
    · have hbe : ¬ ((false, d).1 = (b, e).1) := by
        intro h
        exact hb h.symm
      simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, if_neg hbe,
          if_neg hb]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (false, d)]
  · rw [hpoint false d, if_pos rfl, if_pos rfl]
    exact one_mul _
  · intro q hq
    rcases q with ⟨b, e⟩
    rw [hpoint b e]
    by_cases hb : b = false
    · have hne : d ≠ e := by
        intro hde
        exact hq (Prod.ext hb hde.symm)
      simp [hne]
    · simp [hb]

private theorem rowForward_uncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (w : QState (DetectionSpace I))
    (d : Bool × (I × I)) :
    (detectionInstruction U S .rowForward *ᵥ w) (false, d) = w (false, d) := by
  have hrf : detectionInstruction U S .rowForward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖU else 1) := rfl
  rw [hrf]
  exact select_uncontrolled _ (by rfl) w d

private theorem rowBackward_uncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (w : QState (DetectionSpace I))
    (d : Bool × (I × I)) :
    (detectionInstruction U S .rowBackward *ᵥ w) (false, d) = w (false, d) := by
  have hrb : detectionInstruction U S .rowBackward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ else 1) := rfl
  rw [hrb]
  exact select_uncontrolled _ (by rfl) w d

private theorem cs_uncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (w : QState (DetectionSpace I)) (d : Bool × (I × I)) :
    (detectionControlledSwap *ᵥ w) (false, d) = w (false, d) := by
  have hcs : detectionControlledSwap
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then
          (1 : Matrix Bool Bool ℂ)⊗ₖ(SwapGate : Matrix (I × I) (I × I) ℂ) else 1) := rfl
  rw [hcs]
  exact select_uncontrolled _ (by rfl) w d

theorem marker_apply {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (w : QState (DetectionSpace I)) (p : DetectionSpace I) :
    (detectionMarkGate S *ᵥ w) p = w (detectionMarkPermutation S p) := by
  have h : detectionMarkGate S *ᵥ w
      = ApplyGate (permMatrix (detectionMarkPermutation S)) w := rfl
  rw [h]
  exact applyGate_permMatrix (detectionMarkPermutation_involutive S) w p

private theorem reflection_marker {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (w : QState (DetectionSpace I))
    (d : Bool × (I × I)) :
    (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))) (false, d)
      = (detectionMarkGate S *ᵥ w) (false, d) := by
  obtain ⟨c, xy⟩ := d
  obtain ⟨x, y⟩ := xy
  have hσ : detectionMarkPermutation S (false, c, (x, y))
      = (false, c ^^ decide (x ∈ S), (x, y)) := rfl
  have hrf : (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))) (false, c, (x, y))
      = (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w)) (false, c, (x, y)) :=
    rowForward_uncontrolled U S _ (c, (x, y))
  rw [hrf]
  have hmk : (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))
      (false, c, (x, y))
      = (detectionInstruction U S .rowBackward *ᵥ w) (detectionMarkPermutation S (false, c, (x, y))) :=
    marker_apply S _ _
  rw [hmk, hσ]
  have hrb : (detectionInstruction U S .rowBackward *ᵥ w) (false, c ^^ decide (x ∈ S), (x, y))
      = w (false, c ^^ decide (x ∈ S), (x, y)) :=
    rowBackward_uncontrolled U S w (c ^^ decide (x ∈ S), (x, y))
  rw [hrb]
  rw [marker_apply S w (false, c, (x, y)), hσ]

theorem plusIReflectionWord_uncontrolled_marker {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIReflectionWord j) *ᵥ v) (false, c, xy)
        = (detectionMarkGate S *ᵥ v) (false, c, xy) := by
  intro c xy
  rw [evaluate_reflection U S j v]
  exact reflection_marker U S v (c, xy)

theorem plusIWalkWord_uncontrolled_identity {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ v) (false, c, xy)
        = v (false, c, xy) := by
  intro c xy
  obtain ⟨x, y⟩ := xy
  have hσ : detectionMarkPermutation S (false, c, (x, y))
      = (false, c ^^ decide (x ∈ S), (x, y)) := rfl
  rw [evaluate_walk U S j v]
  have hcs1 : (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ
            (detectionControlledSwap *ᵥ
              (detectionInstruction U S .rowForward *ᵥ
                (detectionMarkGate S *ᵥ
                  (detectionInstruction U S .rowBackward *ᵥ v)))))))) (false, c, (x, y))
      = (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ
            (detectionControlledSwap *ᵥ
              (detectionInstruction U S .rowForward *ᵥ
                (detectionMarkGate S *ᵥ
                  (detectionInstruction U S .rowBackward *ᵥ v))))))) (false, c, (x, y)) :=
    cs_uncontrolled _ (c, (x, y))
  rw [hcs1]
  have hr1 : (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ
        (detectionInstruction U S .rowBackward *ᵥ
          (detectionControlledSwap *ᵥ
            (detectionInstruction U S .rowForward *ᵥ
              (detectionMarkGate S *ᵥ
                (detectionInstruction U S .rowBackward *ᵥ v))))))) (false, c, (x, y))
      = (detectionMarkGate S *ᵥ
        (detectionControlledSwap *ᵥ
          (detectionInstruction U S .rowForward *ᵥ
            (detectionMarkGate S *ᵥ
              (detectionInstruction U S .rowBackward *ᵥ v))))) (false, c, (x, y)) :=
    reflection_marker U S _ (c, (x, y))
  rw [hr1]
  have hmk : (detectionMarkGate S *ᵥ
      (detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ v))))) (false, c, (x, y))
      = (detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ v))))
        (detectionMarkPermutation S (false, c, (x, y))) :=
    marker_apply S _ _
  rw [hmk, hσ]
  have hcs2 : (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ v))))
        (false, c ^^ decide (x ∈ S), (x, y))
      = (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ v)))
        (false, c ^^ decide (x ∈ S), (x, y)) :=
    cs_uncontrolled _ (c ^^ decide (x ∈ S), (x, y))
  rw [hcs2]
  have hr2 : (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ
        (detectionInstruction U S .rowBackward *ᵥ v)))
        (false, c ^^ decide (x ∈ S), (x, y))
      = (detectionMarkGate S *ᵥ v) (false, c ^^ decide (x ∈ S), (x, y)) :=
    reflection_marker U S v (c ^^ decide (x ∈ S), (x, y))
  rw [hr2]
  have hmk2 : (detectionMarkGate S *ᵥ v) (false, c ^^ decide (x ∈ S), (x, y))
      = v (detectionMarkPermutation S (false, c ^^ decide (x ∈ S), (x, y))) :=
    marker_apply S v _
  rw [hmk2]
  rw [← hσ, detectionMarkPermutation_involutive S (false, c, (x, y))]

private theorem phase_uncontrolled {I : Type} [Fintype I] [DecidableEq I] (j : I)
    (w : QState (DetectionSpace I)) (d : Bool × (I × I)) :
    (detectionPhase j *ᵥ w) (false, d) = w (false, d) := by
  classical
  have hdiag : ∀ p : DetectionSpace I,
      (detectionPhase j *ᵥ w) p
        = (if p.1 then if p.2.1 = false ∧ p.2.2.2 = j then 1 else -1 else 1) * w p := by
    intro p
    unfold detectionPhase
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_eq_single p]
    · simp only [Matrix.diagonal_apply, reduceIte]
    · intro q hq
      simp only [Matrix.diagonal_apply, if_neg (Ne.symm hq), zero_mul]
  rw [hdiag]
  simp

theorem correctedReflectionWord_uncontrolled_identity {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (detectionReflectionWord j) *ᵥ v) (false, c, xy)
        = v (false, c, xy) := by
  intro c xy
  obtain ⟨x, y⟩ := xy
  have hσ : detectionMarkPermutation S (false, c, (x, y))
      = (false, c ^^ decide (x ∈ S), (x, y)) := rfl
  have hlist : detectionReflectionWord j
      = .rowForward :: (.marker :: (.fixed (detectionPhase j)
        :: (.marker :: (.rowBackward :: [])))) := rfl
  have hmarker : detectionInstruction U S .marker = detectionMarkGate S := rfl
  have hphase : detectionInstruction U S (.fixed (detectionPhase j)) = detectionPhase j := rfl
  have hnil : detectionEvaluate U S [] = 1 := rfl
  rw [hlist,
    evaluate_cons3 U S .rowForward .marker (.fixed (detectionPhase j))
      (.marker :: (.rowBackward :: [])) v,
    evaluate_cons2 U S .marker .rowBackward [] v,
    hmarker, hphase, hnil, Matrix.one_mulVec]

  have hrf : (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ (detectionPhase j *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v)))))
        (false, c, (x, y))
      = (detectionMarkGate S *ᵥ (detectionPhase j *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v))))
        (false, c, (x, y)) :=
    rowForward_uncontrolled U S _ (c, (x, y))
  rw [hrf]
  have hmk1 : (detectionMarkGate S *ᵥ (detectionPhase j *ᵥ
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v))))
      (false, c, (x, y))
      = (detectionPhase j *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v)))
        (detectionMarkPermutation S (false, c, (x, y))) :=
    marker_apply S _ _
  rw [hmk1, hσ]
  have hph : (detectionPhase j *ᵥ
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v)))
      (false, c ^^ decide (x ∈ S), (x, y))
      = (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v))
        (false, c ^^ decide (x ∈ S), (x, y)) :=
    phase_uncontrolled j _ (c ^^ decide (x ∈ S), (x, y))
  rw [hph]
  have hmk2 : (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ v))
      (false, c ^^ decide (x ∈ S), (x, y))
      = (detectionInstruction U S .rowBackward *ᵥ v)
        (detectionMarkPermutation S (false, c ^^ decide (x ∈ S), (x, y))) :=
    marker_apply S _ _
  rw [hmk2]
  have hrb : (detectionInstruction U S .rowBackward *ᵥ v)
      (detectionMarkPermutation S (false, c ^^ decide (x ∈ S), (x, y)))
      = v (detectionMarkPermutation S (false, c ^^ decide (x ∈ S), (x, y))) :=
    rowBackward_uncontrolled U S v _
  rw [hrb]
  rw [← hσ, detectionMarkPermutation_involutive S (false, c, (x, y))]

private theorem halfWalk_uncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (w : QState (DetectionSpace I))
    (c : Bool) (xy : I × I) :
    (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))))
        (false, c, xy)
      = w (detectionMarkPermutation S (false, c, xy)) := by
  obtain ⟨x, y⟩ := xy
  have hσ : detectionMarkPermutation S (false, c, (x, y))
      = (false, c ^^ decide (x ∈ S), (x, y)) := rfl
  have hcs : (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))))
        (false, c, (x, y))
      = (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w)))
        (false, c, (x, y)) := cs_uncontrolled _ (c, (x, y))
  rw [hcs]
  have hrf : (detectionInstruction U S .rowForward *ᵥ
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))) (false, c, (x, y))
      = (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w)) (false, c, (x, y)) :=
    rowForward_uncontrolled U S _ (c, (x, y))
  rw [hrf]
  have hmk : (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))
      (false, c, (x, y))
      = (detectionInstruction U S .rowBackward *ᵥ w) (detectionMarkPermutation S (false, c, (x, y))) :=
    marker_apply S _ _
  rw [hmk, hσ]
  have hrb : (detectionInstruction U S .rowBackward *ᵥ w) (false, c ^^ decide (x ∈ S), (x, y))
      = w (false, c ^^ decide (x ∈ S), (x, y)) :=
    rowBackward_uncontrolled U S w (c ^^ decide (x ∈ S), (x, y))
  rw [hrb]

private theorem walkWord_append_uncontrolled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (rest : List (DetectionStep I)) (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIWalkWord j ++ rest) *ᵥ v) (false, c, xy)
        = (detectionEvaluate U S rest *ᵥ v) (false, c, xy) := by
  intro c xy
  obtain ⟨x, y⟩ := xy
  have hσ : detectionMarkPermutation S (false, c, (x, y))
      = (false, c ^^ decide (x ∈ S), (x, y)) := rfl
  have hcons : plusIWalkWord j ++ rest
      = .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: rest := rfl
  have hmarker : detectionInstruction U S .marker = detectionMarkGate S := rfl
  have hfixed : detectionInstruction U S (.fixed detectionControlledSwap)
      = detectionControlledSwap := rfl
  rw [hcons,
    evaluate_cons3 U S (.fixed detectionControlledSwap) .rowForward .marker
      (.rowBackward :: (.fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: rest)) v,
    evaluate_cons3 U S .rowBackward (.fixed detectionControlledSwap) .rowForward
      (.marker :: .rowBackward :: rest) v,
    evaluate_cons2 U S .marker .rowBackward rest v,
    hmarker, hfixed]

  have hinner : (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ
            (detectionControlledSwap *ᵥ
              (detectionInstruction U S .rowForward *ᵥ
                (detectionMarkGate S *ᵥ
                  (detectionInstruction U S .rowBackward *ᵥ
                    (detectionEvaluate U S rest *ᵥ v))))))))) (false, c, (x, y))
      = (detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ
              (detectionEvaluate U S rest *ᵥ v)))))
        (detectionMarkPermutation S (false, c, (x, y))) :=
    halfWalk_uncontrolled S U
      (detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ
              (detectionEvaluate U S rest *ᵥ v))))) c (x, y)
  rw [hinner, hσ]

  have houter : (detectionControlledSwap *ᵥ
      (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ
            (detectionEvaluate U S rest *ᵥ v))))) (false, c ^^ decide (x ∈ S), (x, y))
      = (detectionEvaluate U S rest *ᵥ v) (false, c, (x, y)) := by
    have h := halfWalk_uncontrolled S U (detectionEvaluate U S rest *ᵥ v)
      (c ^^ decide (x ∈ S)) (x, y)
    rw [h]
    rw [← hσ, detectionMarkPermutation_involutive S (false, c, (x, y))]
  rw [houter]

theorem printedWalkBlock_uncontrolled_identity {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I) (K : ℕ)
    (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (List.replicate K (plusIWalkWord j)).flatten *ᵥ v) (false, c, xy)
        = v (false, c, xy) := by
  intro c xy
  induction K with
  | zero =>
      have hnil : detectionEvaluate U S [] = 1 := rfl
      simp only [List.replicate_zero, List.flatten_nil, hnil, Matrix.one_mulVec]
  | succ K ih =>
      have hlist : List.flatten (List.replicate (Nat.succ K) (plusIWalkWord j))
          = plusIWalkWord j ++ List.flatten (List.replicate K (plusIWalkWord j)) := by
        simp [List.replicate_succ, List.flatten_cons]
      rw [hlist]
      rw [walkWord_append_uncontrolled S U j (List.flatten (List.replicate K (plusIWalkWord j))) v
        c xy]
      exact ih

theorem rowAccess_reverse_matrix {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (S : Finset I) :
    (detectionInstruction U S .rowForward) * (detectionInstruction U S .rowBackward) = 1 := by
  have hUstar : U * Uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa only [Matrix.star_eq_conjTranspose] using! h
  have hrf : detectionInstruction U S .rowForward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖU else 1) := rfl
  have hrb : detectionInstruction U S .rowBackward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ else 1) := rfl
  rw [hrf, hrb]
  have hone : (1 : Matrix Bool Bool ℂ)⊗ₖ(1 : Matrix (I × I) (I × I) ℂ)
      = 1 := kroneckerMap_one_one (· * ·) (by simp) (by simp) (by simp)
  have hkron : ((1 : Matrix Bool Bool ℂ)⊗ₖU) * ((1 : Matrix Bool Bool ℂ)⊗ₖUᴴ) = 1 := by
    have h1 := mul_kronecker_mul (1 : Matrix Bool Bool ℂ) (1 : Matrix Bool Bool ℂ) U Uᴴ
    rw [Matrix.one_mul, hUstar, hone] at h1
    exact h1.symm
  have hf0 : (fun bb : Bool => if bb then (1 : Matrix Bool Bool ℂ)⊗ₖU else 1) false = 1 := by
    simp
  have hf1 : (fun bb : Bool => if bb then (1 : Matrix Bool Bool ℂ)⊗ₖU else 1) true
      = (1 : Matrix Bool Bool ℂ)⊗ₖU := by
    simp
  have hg0 : (fun bb : Bool => if bb then (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ else 1) false = 1 := by
    simp
  have hg1 : (fun bb : Bool => if bb then (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ else 1) true
      = (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ := by
    simp
  apply Matrix.ext
  intro i j
  obtain ⟨b, d⟩ := i
  obtain ⟨b', d'⟩ := j
  simp only [Matrix.mul_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single b]
  · by_cases hbb : b = b'
    · subst hbb
      cases b with
      | false =>
        have hsum : ∑ y : Bool × (I × I),
            (1 : Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ) d y
              * (1 : Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ) y d'
            = (1 : Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ) d d' := by
          have h := Matrix.mul_apply
            (M := (1 : Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ))
            (N := (1 : Matrix (Bool × (I × I)) (Bool × (I × I)) ℂ)) (i := d) (k := d')
          rw [Matrix.one_mul] at h
          exact h.symm
        simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, if_true, hf0,
            hg0]
        rw [hsum, Matrix.one_apply]
        simp
      | true =>
        have hsum : ∑ y : Bool × (I × I),
            ((1 : Matrix Bool Bool ℂ)⊗ₖU) d y * ((1 : Matrix Bool Bool ℂ)⊗ₖUᴴ) y d'
            = (((1 : Matrix Bool Bool ℂ)⊗ₖU) * ((1 : Matrix Bool Bool ℂ)⊗ₖUᴴ)) d d' := by
          have h := Matrix.mul_apply
            (M := ((1 : Matrix Bool Bool ℂ)⊗ₖU))
            (N := ((1 : Matrix Bool Bool ℂ)⊗ₖUᴴ)) (i := d) (k := d')
          exact h.symm
        simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, if_true]
        rw [hsum, hkron, Matrix.one_apply]
        simp
    · simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, if_neg hbb]
      simp [hbb]
  · intro b'' hb''
    simp only [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply,
        if_neg (Ne.symm hb'')]
    simp

private theorem kronecker_one_mulVec {D E : Type} [Fintype D] [Fintype E] [DecidableEq D]
    (M : Matrix E E ℂ) (g : D × E → ℂ) (b : D) (q : E) :
    (((1 : Matrix D D ℂ) ⊗ₖ M) *ᵥ g) (b, q) = (M *ᵥ (fun e ↦ g (b, e))) q := by
  classical
  have h2 : ∀ (j₂ : E), ((1 : Matrix D D ℂ) ⊗ₖ M) (b, q) (b, j₂) = M q j₂ := by
    intro j₂
    simp
  have h0 : ∀ (j₁ : D) (j₂ : E), j₁ ≠ b →
      ((1 : Matrix D D ℂ) ⊗ₖ M) (b, q) (j₁, j₂) = 0 := by
    intro j₁ j₂ h
    simp [Ne.symm h]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single b]
  · refine Finset.sum_congr rfl ?_
    intro j₂ _
    rw [h2 j₂]
  · intro j hj
    refine Finset.sum_eq_zero ?_
    intro j₂ _
    rw [h0 j j₂ hj]
    simp

private theorem select_controlled {D : Type} [Fintype D] [DecidableEq D]
    (f : Bool → Matrix D D ℂ) (w : QState (Bool × D)) (d : D) :
    (Qatlib.Concepts.BlockEncoding.LCU.select f *ᵥ w) (true, d) = (f true *ᵥ (fun e ↦ w (true, e))) d := by
  classical
  have hT : ∀ (e : D), (Qatlib.Concepts.BlockEncoding.LCU.select f) (true, d) (true, e) = f true d e := by
    intro e
    simp [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply]
  have hF : ∀ (b : Bool) (e : D), b ≠ true →
      (Qatlib.Concepts.BlockEncoding.LCU.select f) (true, d) (b, e) = 0 := by
    intro b e hb
    have hbe : ¬ ((true, d).1 = (b, e).1) := by
      intro h
      exact hb h.symm
    simp [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply, hbe]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single true]
  · refine Finset.sum_congr rfl ?_
    intro e _
    rw [hT e]
  · intro b hb
    refine Finset.sum_eq_zero ?_
    intro e _
    rw [hF b e hb]
    simp

private theorem swapGate_mulVec {I : Type} [Fintype I] [DecidableEq I]
    (f : I × I → ℂ) (p : I × I) :
    (SwapGate *ᵥ f) p = f (Prod.swap p) := by
  classical
  have hT : ∀ (q : I × I), q = Prod.swap p → SwapGate p q = 1 := by
    intro q hq
    subst hq
    simp [SwapGate, permMatrix, Matrix.of_apply, Prod.swap_swap]
  have hF : ∀ (q : I × I), q ≠ Prod.swap p → SwapGate p q = 0 := by
    intro q hq
    have hne : ¬ (p = Prod.swap q) := by
      intro hh
      have hq' : Prod.swap p = q := by rw [hh]; exact Prod.swap_swap q
      exact hq hq'.symm
    simp [SwapGate, permMatrix, Matrix.of_apply, hne]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (Prod.swap p)]
  · rw [hT (Prod.swap p) rfl]
    simp
  · intro q hq
    rw [hF q hq]
    simp

private theorem evaluate_append {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I)
    (xs ys : List (DetectionStep I)) :
    detectionEvaluate U S (xs ++ ys) = detectionEvaluate U S xs * detectionEvaluate U S ys := by
  induction xs with
  | nil => simp [detectionEvaluate]
  | cons x xs ih => simp [detectionEvaluate, ih, Matrix.mul_assoc]

private theorem rowAccess_roundtrip {I : Type} [Fintype I] [DecidableEq I]
    (V W : Matrix I I ℂ) (hVW : V * W = 1) (f : I → ℂ) (y : I) :
    (V *ᵥ (W *ᵥ f)) y = f y := by
  rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]

private theorem cs_controlled {I : Type} [Fintype I] [DecidableEq I]
    (w : QState (DetectionSpace I)) :
    ∀ (c : Bool) (x y : I),
      (detectionControlledSwap *ᵥ w) (true, c, (x, y)) = w (true, c, (y, x)) := by
  intro c x y
  have hcs : detectionControlledSwap
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then
          (1 : Matrix Bool Bool ℂ)⊗ₖ(SwapGate : Matrix (I × I) (I × I) ℂ) else 1) := rfl
  rw [hcs]
  rw [select_controlled]
  simp only [eq_self, ite_true]
  rw [kronecker_one_mulVec]
  rw [swapGate_mulVec]
  rfl

private theorem rowForward_controlled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (V : Matrix I I ℂ)
    (hVf : ∀ (f : I × I → ℂ) (x y : I), (U *ᵥ f) (x, y) = (V *ᵥ (fun e ↦ f (x, e))) y)
    (w : QState (DetectionSpace I)) :
    ∀ (c : Bool) (x y : I),
      (detectionInstruction U S .rowForward *ᵥ w) (true, c, (x, y))
        = (V *ᵥ (fun e ↦ w (true, c, (x, e)))) y := by
  intro c x y
  have hrf : detectionInstruction U S .rowForward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖU else 1) := rfl
  rw [hrf]
  rw [select_controlled]
  simp only [eq_self, ite_true]
  rw [kronecker_one_mulVec]
  exact hVf _ _ _

private theorem rowBackward_controlled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (W : Matrix I I ℂ)
    (hWb : ∀ (f : I × I → ℂ) (x y : I), (Uᴴ *ᵥ f) (x, y) = (W *ᵥ (fun e ↦ f (x, e))) y)
    (w : QState (DetectionSpace I)) :
    ∀ (c : Bool) (x y : I),
      (detectionInstruction U S .rowBackward *ᵥ w) (true, c, (x, y))
        = (W *ᵥ (fun e ↦ w (true, c, (x, e)))) y := by
  intro c x y
  have hrb : detectionInstruction U S .rowBackward
      = Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖUᴴ else 1) := rfl
  rw [hrb]
  rw [select_controlled]
  simp only [eq_self, ite_true]
  rw [kronecker_one_mulVec]
  exact hWb _ _ _

noncomputable def halfWalkOp {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) :
    Matrix (DetectionSpace I) (DetectionSpace I) ℂ :=
  detectionControlledSwap * detectionInstruction U S .rowForward
    * detectionMarkGate S * detectionInstruction U S .rowBackward

private theorem walkWord_eq_halfSquared {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I × I) (I × I) ℂ) (S : Finset I) (j : I) :
    detectionEvaluate U S (plusIWalkWord j) = halfWalkOp U S * halfWalkOp U S := by
  have hlist : plusIWalkWord j
      = .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: .fixed detectionControlledSwap :: .rowForward :: .marker :: .rowBackward
        :: [] := rfl
  rw [hlist]
  simp only [detectionEvaluate, detectionInstruction, halfWalkOp, Matrix.mul_assoc,
    Matrix.mul_one]

private theorem halfWalk_controlled {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (V W : Matrix I I ℂ)
    (hVf : ∀ (f : I × I → ℂ) (x y : I), (U *ᵥ f) (x, y) = (V *ᵥ (fun e ↦ f (x, e))) y)
    (hWb : ∀ (f : I × I → ℂ) (x y : I), (Uᴴ *ᵥ f) (x, y) = (W *ᵥ (fun e ↦ f (x, e))) y)
    (hVW : V * W = 1)
    (w : QState (DetectionSpace I)) :
    ∀ (c : Bool) (x y : I),
      (halfWalkOp U S *ᵥ w) (true, c, (x, y))
        = w (true, c ^^ decide (y ∈ S), (y, x)) := by
  intro c x y
  have hnest : halfWalkOp U S *ᵥ w
      = detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ w))) := by
    simp only [halfWalkOp]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hnest]
  have h1 : (detectionControlledSwap *ᵥ
        (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ w)))) (true, c, (x, y))
      = (detectionInstruction U S .rowForward *ᵥ
          (detectionMarkGate S *ᵥ
            (detectionInstruction U S .rowBackward *ᵥ w))) (true, c, (y, x)) :=
    cs_controlled _ c x y
  rw [h1]
  have h2 : (detectionInstruction U S .rowForward *ᵥ
        (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ w))) (true, c, (y, x))
      = (V *ᵥ (fun e ↦ (detectionMarkGate S *ᵥ
          (detectionInstruction U S .rowBackward *ᵥ w)) (true, c, (y, e)))) x :=
    rowForward_controlled S U V hVf _ c y x
  rw [h2]
  have h3 : ∀ (e : I),
      (detectionMarkGate S *ᵥ (detectionInstruction U S .rowBackward *ᵥ w))
        (true, c, (y, e))
        = (detectionInstruction U S .rowBackward *ᵥ w) (true, c ^^ decide (y ∈ S), (y, e)) := by
    intro e
    rw [marker_apply S _ _]
    rfl
  simp only [h3]
  have h4 : ∀ (e : I),
      (detectionInstruction U S .rowBackward *ᵥ w) (true, c ^^ decide (y ∈ S), (y, e))
        = (W *ᵥ (fun e' ↦ w (true, c ^^ decide (y ∈ S), (y, e')))) e := by
    intro e
    exact rowBackward_controlled S U W hWb _ (c ^^ decide (y ∈ S)) y e
  simp only [h4]
  have heta : (fun e ↦ (W *ᵥ (fun e' ↦ w (true, c ^^ decide (y ∈ S), (y, e')))) e)
      = W *ᵥ (fun e' ↦ w (true, c ^^ decide (y ∈ S), (y, e'))) := by
    funext e
    rfl
  rw [heta]
  rw [rowAccess_roundtrip V W hVW (fun e' ↦ w (true, c ^^ decide (y ∈ S), (y, e'))) x]
set_option maxHeartbeats 800000 in

theorem plusIWalkWord_flagShear {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (hU : RowPreservingAccess U) (v : QState (DetectionSpace I)) :
    ∀ (c : Bool) (xy : I × I),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ v) (true, c, xy)
        = v (printedFlagShear S (true, c, xy)) := by
  obtain ⟨V, W, hVf, hWb, hVW⟩ := hU
  intro c xy
  obtain ⟨x, y⟩ := xy
  rw [walkWord_eq_halfSquared U S j]
  rw [← Matrix.mulVec_mulVec]
  rw [halfWalk_controlled S U V W hVf hWb hVW]
  rw [halfWalk_controlled S U V W hVf hWb hVW]
  have h3 : v (printedFlagShear S (true, c, (x, y)))
      = v (true, (c ^^ decide (y ∈ S)) ^^ decide (x ∈ S), (x, y)) := by
    congr 1
    cases hx : decide (x ∈ S) <;> cases hy : decide (y ∈ S) <;>
      simp [printedFlagShear, hx, hy]
  rw [h3]
open Matrix
open Qatlib
open scoped Kronecker
set_option maxHeartbeats 800000 in

private theorem printedFlagShear_preserves_label {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (p : DetectionSpace I) : (printedFlagShear S p).1 = p.1 := by
  by_cases h : p.1 = false
  · simp [printedFlagShear, h]
  · by_cases h2 : decide (p.2.2.1 ∈ S) != decide (p.2.2.2 ∈ S)
    · simp [printedFlagShear, h, h2]
    · simp [printedFlagShear, h, h2]

private theorem plusIWalkWord_operator {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (hU : RowPreservingAccess U) :
    ∀ (z : QState (DetectionSpace I)),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ z) = fun p =>
        if p.1 = false then z p else z (printedFlagShear S p) := by
  intro z
  funext p
  rcases p with ⟨b, c, xy⟩
  cases b with
  | false =>
      simp only [if_pos]
      exact plusIWalkWord_uncontrolled_identity S U j z c xy
  | true =>
      simp only [if_neg (by simp : (true : Bool) ≠ false)]
      exact plusIWalkWord_flagShear S U j hU z c xy

theorem plusIWalkWord_involutive {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (hU : RowPreservingAccess U) :
    ∀ (y : QState (DetectionSpace I)),
      (detectionEvaluate U S (plusIWalkWord j) *ᵥ
          (detectionEvaluate U S (plusIWalkWord j) *ᵥ y)) = y := by
  intro y
  funext p
  have hop := plusIWalkWord_operator S U j hU
  rw [hop (detectionEvaluate U S (plusIWalkWord j) *ᵥ y)]
  by_cases hb : p.1 = false
  · simp only [if_pos hb]
    rw [hop y]
    simp only [if_pos hb]
  · simp only [if_neg hb]
    rw [hop y]
    have hsb : (printedFlagShear S p).1 = p.1 := printedFlagShear_preserves_label S p
    have hnb : (printedFlagShear S p).1 ≠ false := by
      intro hc
      rw [hsb] at hc
      exact hb hc
    simp only [if_neg hnb]
    congr 1
    exact printedFlagShear_involutive S p
set_option maxHeartbeats 400000 in

theorem printedWalkBlock_period_two {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (U : Matrix (I × I) (I × I) ℂ) (j : I)
    (hU : RowPreservingAccess U) :
    ∀ (K : ℕ) (v : QState (DetectionSpace I)),
      (detectionEvaluate U S (List.replicate K (plusIWalkWord j)).flatten *ᵥ v)
        = if K % 2 = 0 then v
          else (detectionEvaluate U S (plusIWalkWord j) *ᵥ v) := by

  have hcons : ∀ (xs : List (List (DetectionStep I))) (z : QState (DetectionSpace I)),
      (detectionEvaluate U S (plusIWalkWord j :: xs).flatten *ᵥ z)
        = (detectionEvaluate U S (plusIWalkWord j) *ᵥ
            (detectionEvaluate U S xs.flatten *ᵥ z)) := by
    intro xs z
    have hfl : (plusIWalkWord j :: xs).flatten = plusIWalkWord j ++ xs.flatten := rfl
    rw [hfl, evaluate_append, ← Matrix.mulVec_mulVec]

  have hgen : ∀ (K : ℕ) (z : QState (DetectionSpace I)),
      (detectionEvaluate U S (List.replicate K (plusIWalkWord j)).flatten *ᵥ z)
        = if K % 2 = 0 then z
          else (detectionEvaluate U S (plusIWalkWord j) *ᵥ z) := by
    intro K z
    induction K generalizing z with
    | zero =>
        have h0 : (0 : ℕ) % 2 = 0 := by omega
        rw [if_pos h0]
        simp [detectionEvaluate, Matrix.one_mulVec]
    | succ K ih =>
        have hrep : List.replicate (K + 1) (plusIWalkWord j)
            = plusIWalkWord j :: List.replicate K (plusIWalkWord j) := by
          simp [List.replicate_succ]
        rw [hrep, hcons]
        rw [ih z]
        by_cases hK : K % 2 = 0
        · rw [if_pos hK]
          have h1 : (K + 1) % 2 ≠ 0 := by omega
          rw [if_neg h1]
        · rw [if_neg hK]
          have h1 : (K + 1) % 2 = 0 := by omega
          rw [if_pos h1]
          exact plusIWalkWord_involutive S U j hU z
  intro K v
  exact hgen K v
end Qatlib.Concepts.WalkSearch.FrameSpectral
