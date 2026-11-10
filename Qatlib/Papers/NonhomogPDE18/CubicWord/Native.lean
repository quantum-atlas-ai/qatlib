/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonhomogPDE18.CubicWord.Source
import Qatlib.Papers.NonhomogPDE18.WaveModel.NativePrims
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
namespace Qatlib.Papers.NonhomogPDE18.CubicWord
open Qatlib.Papers.NonhomogPDE18.WaveModel

def gates10 (t : ℝ) : List Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  [sg j k 1 1,sg j l 1 1,pg (t/3) j 3,sg j l 1 (-1),sg j k 1 (-1),
   sg k l 1 1,pg (-(t/3)) k 3,sg k l 1 (-1),sg l j 1 1,pg (-(t/3)) l 3,
   sg l j 1 (-1),sg j k 1 1,pg (-(t/3)) j 3,sg j k 1 (-1),
   pg (t/3) j 3,pg (t/3) k 3,pg (t/3) l 3]

theorem gates10_wave (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord (gates10 t)=Qatlib.Papers.NonhomogPDE18.CubicWord.eq10RHS t := by
  simp only [gates10,Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord]
  rw [sg_pos j k (by decide),sg_pos j l (by decide),sg_neg j l (by decide),sg_neg j k (by decide),
    sg_pos k l (by decide),sg_neg k l (by decide),sg_pos l j (by decide),sg_neg l j (by decide)]
  simp only [pg_wave]
  rfl

def target10 (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseEquiv volume (fun x=>2*t*(x j)*(x k)*(x l)) (by fun_prop)

theorem actual_eq10 (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates10 t)=target10 t := by
  apply LinearIsometryEquiv.ext
  intro ψ
  apply Lp.ext
  have hr := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_repr (gates10 t) ψ
  rw [gates10_wave,Qatlib.Papers.NonhomogPDE18.CubicWord.eq10_decomposition] at hr
  exact hr.trans
      (Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseMap_repr volume _ (by fun_prop) ψ).symm

theorem eq10_normalized (t : ℝ) (ψ : H) (hψ : ‖ψ‖=1) :
    ‖Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates10 t) ψ‖=1 := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_normalized _ ψ hψ
end Qatlib.Papers.NonhomogPDE18.CubicWord
