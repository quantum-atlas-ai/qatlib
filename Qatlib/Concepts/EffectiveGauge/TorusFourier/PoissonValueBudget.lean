/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.FinitePoissonPlan

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Value Budget

Torus Fourier constructions for Effective Gauge.
Proves `finitePoissonValue_budget`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Joint budget for the executed coefficient, cis and Machin period
approximations together with the actual N^-3 tail. -/
theorem finitePoissonValue_budget (C0 : ℚ) (hC0 : 0 ≤ C0) (N : ℕ) (hN : 0<N)
    (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    let J : ℚ := finitePoissonFrequencyCount N
    let E := tolerance/(24*J)
    let d := finitePoissonModeAccuracy C0 N tolerance
    let ell := finitePoissonPeriodAccuracy C0 N tolerance
    J*(3*E/5+3*(C0+E)*d/5+3*C0*ell/30)+39*tolerance/100 ≤ tolerance/2 := by
  dsimp only
  let J : ℚ := finitePoissonFrequencyCount N
  let E := tolerance/(24*J)
  let d := finitePoissonModeAccuracy C0 N tolerance
  let ell := finitePoissonPeriodAccuracy C0 N tolerance
  have hJ : 0<J := by
    change (0 : ℚ)<finitePoissonFrequencyCount N
    exact_mod_cast finitePoissonFrequencyCount_pos N
  have hJ1 : 1 ≤ J := by
    change (1 : ℚ) ≤ finitePoissonFrequencyCount N
    exact_mod_cast (Nat.succ_le_iff.mpr (finitePoissonFrequencyCount_pos N))
  have hCp : 0<C0+1 := by linarith
  have hNp : 0<(N : ℚ)+1 := by positivity
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hE : E ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0<24*J)).mpr
    linarith
  have hd : 0 ≤ d := (finitePoissonModeAccuracy_spec C0 hC0 N tolerance ht ht1).1.le
  have hell : 0 ≤ ell := (finitePoissonPeriodAccuracy_spec C0 hC0 N tolerance ht ht1).1.le
  have hidE : J*(3*E/5)=tolerance/40 := by
    dsimp only [E]
    field_simp [hJ.ne']
    ring
  have hidD : J*(3*(C0+1)*d/5)=tolerance/320 := by
    dsimp only [d,finitePoissonModeAccuracy]
    change J*(3*(C0+1)*(tolerance/(192*J*(C0+1)))/5)=_
    field_simp [hJ.ne',hCp.ne']
    ring
  have hD : J*(3*(C0+E)*d/5) ≤ tolerance/320 := by
    rw [← hidD]
    apply mul_le_mul_of_nonneg_left _ hJ.le
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : C0+E ≤ C0+1) (by norm_num)) hd)
      (by norm_num)
  have hlarge : C0 ≤ (C0+1)*((N : ℚ)+1)/2 := by
    nlinarith [mul_nonneg hC0 (by linarith : 0 ≤ (N : ℚ)-1)]
  have hidP : J*(3*((C0+1)*((N : ℚ)+1)/2)*ell/30)=tolerance/81920 := by
    dsimp only [ell,finitePoissonPeriodAccuracy]
    change J*(3*((C0+1)*((N : ℚ)+1)/2)*
      (tolerance/(4096*J*(C0+1)*((N : ℚ)+1)))/30)=_
    field_simp [hJ.ne',hCp.ne',hNp.ne']
    ring
  have hP : J*(3*C0*ell/30) ≤ tolerance/81920 := by
    rw [← hidP]
    apply mul_le_mul_of_nonneg_left _ hJ.le
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlarge (by norm_num)) hell)
      (by norm_num)
  change J*(3*E/5+3*(C0+E)*d/5+3*C0*ell/30)+39*tolerance/100 ≤ tolerance/2
  nlinarith

end Qatlib.Concepts.EffectiveGauge.TorusFourier
