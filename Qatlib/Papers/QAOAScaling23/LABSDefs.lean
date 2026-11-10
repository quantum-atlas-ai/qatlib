/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.SequenceEnergy.Aperiodic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.LABSDefs
open scoped Classical
open Qatlib.Foundations.SequenceEnergy.Aperiodic

def spin (b : Bool) : ℝ := if b then -1 else 1

def lagCorrelation {N : ℕ} (s : Fin N → Bool) (k : Fin N) : ℝ :=
  correlation (fun i => spin (s i)) k

def energy {N : ℕ} (s : Fin N → Bool) : ℝ :=
  squaredSidelobe (fun i => spin (s i))

def meritFactor {N : ℕ} (s : Fin N → Bool) : ℝ := (N:ℝ)^2/(2*energy s)

theorem spin_sq (b : Bool) : spin b^2=1 := by cases b <;> norm_num [spin]

theorem energy_nonneg {N : ℕ} (s : Fin N → Bool) : 0≤energy s := by
  exact squaredSidelobe_nonneg _

theorem last_lag {N : ℕ} (hN : 0<N) (s : Fin N → Bool) :
    lagCorrelation s ⟨N-1,by omega⟩=spin (s ⟨0,hN⟩)*spin (s ⟨N-1,by omega⟩) := by
  exact correlation_last hN _

theorem one_le_energy {N : ℕ} (hN : 2≤N) (s : Fin N → Bool) : 1≤energy s := by
  have h:=endpoint_sq_le_sidelobe hN (fun i => spin (s i))
  simpa only [mul_pow,spin_sq,one_mul] using! h

theorem meritFactor_antitone {N : ℕ} (hN : 2≤N) (s t : Fin N → Bool)
    (hst : energy s≤energy t) : meritFactor t≤meritFactor s := by
  unfold meritFactor
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [one_le_energy hN s])
  linarith

def printed_core (s : Fin 3 → Bool) : ℝ := spin (s 0)*spin (s 2)

theorem energy_three (s : Fin 3 → Bool) : energy s=3+2*printed_core s := by
  let a:=s 0
  let b:=s 1
  let c:=s 2
  have hs : s=![a,b,c] := by funext i; fin_cases i <;> rfl
  rw [hs]
  cases ha : a <;> cases hb : b <;> cases hc : c <;>
    norm_num [energy,squaredSidelobe,correlation,printed_core,Fin.sum_univ_succ,spin,ha,hb,hc,Matrix.cons_val_two]
end Qatlib.Papers.QAOAScaling23.LABSDefs
