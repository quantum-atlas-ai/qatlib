/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonhomogPDE18.QuarticWord.Source
import Qatlib.Papers.NonhomogPDE18.WaveModel.NativePrims

/-!
# Native quartic phase decomposition

Lifts the phase and shear word of equation (11) to linear isometric equivalences on `H`. The
native word implements the quartic exponent 6t x_j^2 x_k x_l and preserves normalization. See
[ArrazolaEtAl2019].

## Main statements

* `gates11_wave`: the gate list realizes the source wave operator.
* `actual_eq11`: the native word equals the quartic target phase equivalence.
* `eq11_normalized`: normalized inputs remain normalized.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
namespace Qatlib.Papers.NonhomogPDE18.QuarticWord
open Qatlib.Papers.NonhomogPDE18.WaveModel

/-- The ordered phase and shear gate list implementing the right-hand side of equation (11). -/
def gates11 (t : ℝ) : List Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  [sg k l 1 1,sg k j 2 1,pg t k 3,sg k j 2 (-1),sg k l 1 (-1),
   sg k j 2 1,pg (-t) k 3,sg k j 2 (-1),sg k l 1 1,pg (-t) k 3,
   sg k l 1 (-1),sg l j 2 1,pg (-t) l 3,sg l j 2 (-1),
   pg t k 3,pg t j 6,pg t l 3]

/-- The wave interpretation of `gates11` equals the source operator `eq11RHS`. -/
theorem gates11_wave (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord (gates11 t)=Qatlib.Papers.NonhomogPDE18.QuarticWord.eq11RHS t := by
  simp only [gates11,Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveWord]
  rw [sg_pos k l (by decide),sg_neg k l (by decide),sg_square_pos k j (by decide),
    sg_square_neg k j (by decide),sg_square_pos l j (by decide),sg_square_neg l j (by decide)]
  simp only [pg_wave]
  rfl

/-- The linear isometric phase equivalence on `H` with exponent 6t x_j^2 x_k x_l. -/
def target11 (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseEquiv volume (fun x=>6*t*(x j)^2*(x k)*(x l)) (by fun_prop)

/-- The native interpretation of `gates11` equals the quartic target phase equivalence. See
[Arrazola et al., equation (11)][ArrazolaEtAl2019]. -/
theorem actual_eq11 (t : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates11 t)=target11 t := by
  apply LinearIsometryEquiv.ext
  intro ψ
  apply Lp.ext
  have hr := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_repr (gates11 t) ψ
  rw [gates11_wave,Qatlib.Papers.NonhomogPDE18.QuarticWord.eq11_decomposition] at hr
  exact hr.trans
      (Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseMap_repr volume _ (by fun_prop) ψ).symm

/-- Applying the native quartic gate word to a norm-one vector yields a norm-one vector. See
[ArrazolaEtAl2019]. -/
theorem eq11_normalized (t : ℝ) (ψ : H) (hψ : ‖ψ‖=1) :
    ‖Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord (gates11 t) ψ‖=1 := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.nativeWord_normalized _ ψ hψ
end Qatlib.Papers.NonhomogPDE18.QuarticWord
