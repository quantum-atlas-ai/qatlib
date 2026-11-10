/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUCorrectedFibers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

def lcuListWeight {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ))) : ℝ := (L.map fun t=>t.2.1).sum

def lcuListWeighted {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ))) : Matrix I I ℂ :=
  (L.map fun t=>t.2.1 • t.2.2).sum

omit [Fintype I] [DecidableEq I] in

theorem lcuListWeight_nonneg {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (hL : ∀ t∈L,0<t.2.1) : 0≤lcuListWeight L := by
  induction L with
  | nil => simp [lcuListWeight]
  | cons t L ih =>
    change 0≤t.2.1+lcuListWeight L
    exact add_nonneg (hL t (List.mem_cons_self)).le
      (ih (fun t ht=>hL t (List.mem_cons_of_mem _ ht)))

omit [DecidableEq I] in

theorem liftSys_zero_corner (k : ℕ) (U : Matrix I I ℂ) (ψ : QState I) (x : I) :
    (liftSys k U*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=(U*ᵥψ) x := by
  rw [mask_zero_corner]
  simp only [liftSys,Matrix.of_apply]
  rfl

theorem chainGateCorrected_zero_corner {k : ℕ} (bit : Fin k) (W w : ℝ) (hW : 0<W) (hw : 0<w)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (U : Matrix I I ℂ)
    (ψ : QState I) (x : I) :
    (chainGateCorrected k bit W w acc U*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      ((W:ℂ)/(W+w))*(acc*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)+
      ((w:ℂ)/(W+w))*(U*ᵥψ) x := by
  unfold chainGateCorrected
  rw [lcuLevelGateCorrected_zero_corner bit (W/w) (div_nonneg hW.le hw.le) acc (liftSys k U)
    (independentLCUBit_liftSys bit U),liftSys_zero_corner]
  have hκ : (W/w)/(W/w+1)=W/(W+w) := by field_simp
  have hκ' : (1:ℝ)/(W/w+1)=w/(W+w) := by field_simp
  have hc : (((W/w:ℝ):ℂ))/(((W/w:ℝ):ℂ)+1)=(W:ℂ)/(W+w) := by exact_mod_cast hκ
  have hc' : (1:ℂ)/(((W/w:ℝ):ℂ)+1)=(w:ℂ)/(W+w) := by exact_mod_cast hκ'
  rw [hc,hc']

theorem chainFoldCorrected_zero_corner {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (W : ℝ) (hW : 0<W) (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hL : ∀ t∈L,0<t.2.1) (ψ : QState I) (x : I) :
    (chainFoldCorrected k W acc L*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      ((W:ℂ)*(acc*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)+
        (lcuListWeighted L*ᵥψ) x)/((W+lcuListWeight L:ℝ):ℂ) := by
  induction L generalizing W acc with
  | nil =>
    have hWC : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
    simp [chainFoldCorrected,lcuListWeight,lcuListWeighted,hWC]
  | cons t L ih =>
    rcases t with ⟨bit,w,U⟩
    have hw : 0<w := hL _ (List.mem_cons_self)
    have hL' : ∀ t∈L,0<t.2.1 := fun t ht=>hL t (List.mem_cons_of_mem _ ht)
    rw [chainFoldCorrected,ih (W+w) (by linarith) (chainGateCorrected k bit W w acc U) hL',
      chainGateCorrected_zero_corner bit W w hW hw]
    have hc : ((W+w:ℝ):ℂ)≠0 := by exact_mod_cast (show W+w≠0 by linarith)
    have hs : ((W+w+lcuListWeight L:ℝ):ℂ)≠0 := by
      exact_mod_cast (ne_of_gt (by linarith [lcuListWeight_nonneg L hL'] : 0<W+w+lcuListWeight L))
    simp only [lcuListWeight,lcuListWeighted,List.map_cons,List.sum_cons,Matrix.add_mulVec,
      Matrix.smul_mulVec,Pi.add_apply,Pi.smul_apply,Complex.real_smul]
    push_cast at hc hs ⊢
    simp only [lcuListWeight] at hs
    ring_nf at hc hs ⊢
    field_simp [hc,hs]; ring

theorem chainCircuitCorrected_zero_corner {k : ℕ} (L : List (Fin k×(ℝ×Matrix I I ℂ)))
    (hne : L≠[]) (hL : ∀ t∈L,0<t.2.1) (ψ : QState I) (x : I) :
    (chainCircuitCorrected k L*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      (lcuListWeighted L*ᵥψ) x/(lcuListWeight L:ℂ) := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons t L =>
    rcases t with ⟨bit,w,U⟩
    rw [chainCircuitCorrected,chainFoldCorrected_zero_corner L w (hL _ (List.mem_cons_self))
      (liftSys k U) (fun t ht=>hL t (List.mem_cons_of_mem _ ht)),liftSys_zero_corner]
    simp only [lcuListWeight,lcuListWeighted,List.map_cons,List.sum_cons,Matrix.add_mulVec,
      Matrix.smul_mulVec,Pi.add_apply,Pi.smul_apply,Complex.real_smul]
end Qatlib.Papers.HamLCUSim12.LCUDeferred
