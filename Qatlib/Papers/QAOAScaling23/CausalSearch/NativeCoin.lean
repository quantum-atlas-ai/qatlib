/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedLaws
import Qatlib.Concepts.LchsSimulation.StaticLchs.CountedPlanSampling
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

def coinCode (I : Type) (k m : ℕ) : ℕ → Code I (Configuration Unit (Fin m)×ℕ)
  | 0 => .ret (Sum.inr (),0)
  | fuel+1 => .pay k (drawF (finiteCoinNext k m ()) (fun cfg =>
      match cfg with
      | .inl i => .ret (.inl i,k)
      | .inr _ => mapCode (fun out => (out.1,k+out.2)) (coinCode I k m fuel)))

theorem native_coin_succ (k m fuel : ℕ) :
    finiteCoinRun k m (fuel+1)=
      (finiteCoinNext k m ()).bind (fun cfg => match cfg with
        | .inl i => PMF.pure (.inl i,k)
        | .inr _ => (finiteCoinRun k m fuel).map (fun out => (out.1,k+out.2))) := by
  unfold finiteCoinRun
  rw [runFor,tick]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,
    PMF.map_bind,PMF.bind_map,PMF.map_comp,Function.comp_def]
  congr 1
  funext cfg
  cases cfg with
  | inl i => simp [runFor_halted,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,PMF.pure_map]
  | inr u =>
    cases u
    congr 1
    funext out
    simp only [Prod.mk.injEq,true_and]
    ring

theorem coinCode_actual_law (I : Type) (cost : I → ℝ) (current : I) (k m fuel : ℕ) :
    valueLaw cost current (coinCode I k m fuel)=finiteCoinRun k m fuel := by
  induction fuel with
  | zero => simp [coinCode,valueLaw,finiteCoinRun,runFor,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,PMF.pure_map]
  | succ fuel ih =>
    rw [coinCode,valueLaw,valueLaw_drawF,native_coin_succ]
    congr 1
    funext cfg
    cases cfg with
    | inl i => rfl
    | inr u =>
      cases u
      rw [valueLaw_mapCode,ih]
end Qatlib.Papers.QAOAScaling23.CausalSearch
