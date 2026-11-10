/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonhomogPDE18.QuarticWord.Source
import Qatlib.Papers.NonhomogPDE18.WaveModel.NativePrims
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
namespace Qatlib.Papers.NonhomogPDE18.QuarticWord
open Qatlib.Papers.NonhomogPDE18.WaveModel

def gates11 (t : ℝ) : List Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  [sg k l 1 1,sg k j 2 1,pg t k 3,sg k j 2 (-1),sg k l 1 (-1),
   sg k j 2 1,pg (-t) k 3,sg k j 2 (-1),sg k l 1 1,pg (-t) k 3,
   sg k l 1 (-1),sg l j 2 1,pg (-t) l 3,sg l j 2 (-1),
   pg t k 3,pg t j 6,pg t l 3]

theorem gates11_wave (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord (gates11 t)=Qatlib.Papers.NonhomogPDE18.QuarticWord.eq11RHS t := by
  simp only [gates11,Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord]
  rw [sg_pos k l (by decide),sg_neg k l (by decide),sg_square_pos k j (by decide),
    sg_square_neg k j (by decide),sg_square_pos l j (by decide),sg_square_neg l j (by decide)]
  simp only [pg_wave]
  rfl

def target11 (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseEquiv volume (fun x=>6*t*(x j)^2*(x k)*(x l)) (by fun_prop)

theorem actual_eq11 (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates11 t)=target11 t := by
  apply LinearIsometryEquiv.ext
  intro ψ
  apply Lp.ext
  have hr := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_repr (gates11 t) ψ
  rw [gates11_wave,Qatlib.Papers.NonhomogPDE18.QuarticWord.eq11_decomposition] at hr
  exact hr.trans
      (Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseMap_repr volume _ (by fun_prop) ψ).symm

theorem eq11_normalized (t : ℝ) (ψ : H) (hψ : ‖ψ‖=1) :
    ‖Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates11 t) ψ‖=1 := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_normalized _ ψ hψ
end Qatlib.Papers.NonhomogPDE18.QuarticWord
