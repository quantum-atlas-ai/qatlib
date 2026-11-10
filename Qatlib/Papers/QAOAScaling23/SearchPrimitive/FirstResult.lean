/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.SampledLaw
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

theorem event_isSome {I : Type} [Fintype I] (p : PMF (Option I)) :
    event p (fun x=>x.isSome)=∑i,p (some i) := by
  simp [event,expectation,tsum_fintype,Fintype.sum_option]

def firstBind {I : Type} (p q : PMF (Option I)) : PMF (Option I) :=
  p.bind fun x=>match x with | none=>q | some i=>PMF.pure (some i)

theorem firstBind_point {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) (i : I) :
    firstBind p q (some i)=p (some i)+p none*q (some i) := by
  simp [firstBind,PMF.bind_apply,tsum_fintype,Fintype.sum_option,add_comm]

theorem firstBind_success {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) :
    event (firstBind p q) (fun x=>x.isSome)=event p (fun x=>x.isSome)+p none*event q (fun x=>x.isSome) := by
  simp only [event_isSome,firstBind_point,Finset.sum_add_distrib,Finset.mul_sum]

theorem firstBind_factor {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) (i : I) (c : ℝ≥0∞)
    (hp : p (some i)=event p (fun x=>x.isSome)*c)
    (hq : q (some i)=event q (fun x=>x.isSome)*c) :
    firstBind p q (some i)=event (firstBind p q) (fun x=>x.isSome)*c := by
  rw [firstBind_point,firstBind_success,hp,hq]
  ring

def firstResult {I : Type} (F : ℕ→PMF (Option I)) : List ℕ→PMF (Option I)
  | []=>PMF.pure none
  | m::ms=>firstBind (F m) (firstResult F ms)

theorem firstResult_factor {I : Type} [Fintype I] [DecidableEq I]
    (F : ℕ→PMF (Option I)) (ms : List ℕ) (i : I) (c : ℝ≥0∞)
    (hF : ∀m,F m (some i)=event (F m) (fun x=>x.isSome)*c) :
    firstResult F ms (some i)=event (firstResult F ms) (fun x=>x.isSome)*c := by
  induction ms with
  | nil => simp [firstResult,event,expectation]
  | cons m ms ih => exact firstBind_factor (F m) (firstResult F ms) i c (hF m) ih
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
