/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeTrial
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
variable {I : Type} [Fintype I] [DecidableEq I]

theorem coinCode_noSave (I : Type) (k m fuel : ℕ) : NoSave (coinCode I k m fuel) := by
  induction fuel with
  | zero => trivial
  | succ fuel ih =>
    rw [coinCode,NoSave,noSave_drawF]
    intro cfg
    cases cfg with
    | inl i => trivial
    | inr u => exact (noSave_mapCode _ _).2 ih

theorem coinCode_returns (I : Type) (cost : I → ℝ) (current : I) (k m fuel : ℕ) :
    Returns cost current (coinCode I k m fuel) (fun out fee => fee=out.2) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [coinCode,Returns,returns_drawF]
    intro cfg
    cases cfg with
    | inl i => simp [Returns]
    | inr u =>
      rw [returns_mapCode]
      simpa only [Nat.add_left_cancel_iff] using ih

def sampledCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (b m fuel : ℕ) : Code I (Option (I×ℕ)×ℕ×ℕ) :=
  bindCode (coinCode I b m fuel) (fun out =>
    match out.1 with
    | .inl j => mapCode (fun tr => (some tr.1,out.2,tr.2)) (trialCode U hU seed S j)
    | .inr _ => .ret (none,out.2,0))

theorem sampledCode_actual_law (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (b m fuel : ℕ) :
    valueLaw cost current (sampledCode U hU seed S b m fuel)=preparedAASampled U hU seed S b m fuel := by
  rw [sampledCode,valueLaw_bindCode cost current _ (coinCode_noSave I b m fuel),coinCode_actual_law]
  unfold preparedAASampled finiteCoinThenAttempt
  congr 1
  funext out
  rcases out with ⟨cfg,bits⟩
  cases cfg with
  | inl j => rw [valueLaw_mapCode,trialCode_actual_law]; rfl
  | inr u => rfl

theorem sampledCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) (b m fuel : ℕ) :
    NoSave (sampledCode U hU seed S b m fuel) := by
  unfold sampledCode
  apply noSave_bindCode _ (coinCode_noSave I b m fuel)
  intro out
  cases out.1 with
  | inl j => exact (noSave_mapCode _ _).2 (trialCode_noSave U hU seed S j)
  | inr u => trivial

def sampledWordFee (out : Option (I×ℕ)×ℕ×ℕ) : ℕ :=
  out.2.1 + out.2.2 + match out.1 with
    | none => 0
    | some yg => (2*out.2.2+1)+yg.2

theorem sampledCode_returns (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (b m fuel : ℕ) :
    Returns cost current (sampledCode U hU seed S b m fuel) (fun out fee => fee=sampledWordFee out) := by
  unfold sampledCode
  apply returns_bindCode cost current _ (coinCode_noSave I b m fuel)
  apply returns_mono _ _ _ (coinCode_returns I cost current b m fuel)
  intro out fee hfee
  rcases out with ⟨cfg,bits⟩
  cases cfg with
  | inr u => simpa only [Returns,sampledWordFee,Nat.add_zero] using hfee
  | inl j =>
    rw [returns_mapCode]
    apply returns_mono _ _ _ (trialCode_returns cost current U hU seed S j)
    intro tr wordFee hword
    obtain ⟨hf,hg,hq⟩:=hword
    simp only [sampledWordFee]
    rw [hfee,hf,hg,hq]
    simp only [trialWordFee]
    ring
end Qatlib.Papers.QAOAScaling23.CausalSearch
