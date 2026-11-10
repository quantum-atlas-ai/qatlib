/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.NativeDomination
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination
variable {I : Type*} [Fintype I]

def bornMass (rho : Matrix I I ℂ) (good : I → Bool) (b : Bool) : ℝ :=
  ∑ i, if good i=b then (rho i i).re else 0

theorem bornMass_add (rho sigma : Matrix I I ℂ) (good : I → Bool) (b : Bool) :
    bornMass (rho+sigma) good b=bornMass rho good b+bornMass sigma good b := by
  simp only [bornMass,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem bornMass_smul (rho : Matrix I I ℂ) (c : ℝ) (good : I → Bool) (b : Bool) :
    bornMass ((c:ℂ) • rho) good b=c*bornMass rho good b := by
  simp only [bornMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem bornMass_nonneg (rho : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (good : I → Bool) (b : Bool) : 0≤bornMass rho good b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (Complex.le_def.mp (hrho.diag_nonneg (i := i))).1
  · rfl

theorem bornMass_total (rho : Matrix I I ℂ) (good : I → Bool) :
    bornMass rho good false+bornMass rho good true=(Matrix.trace rho).re := by
  simp only [bornMass,← Finset.sum_add_distrib,Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases good i <;> simp

theorem bornMass_le_trace (rho : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (good : I → Bool) : bornMass rho good true≤(Matrix.trace rho).re := by
  have ht := bornMass_total rho good
  have hn := bornMass_nonneg rho hrho good false
  linarith

theorem density_domination_born_bias (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (htrho : Matrix.trace rho=1) (htrsigma : Matrix.trace sigma=1)
    (delta : ℝ) (hd : 0≤delta)
    (hdom : (sigma-(((1-delta:ℝ):ℂ) • rho)).PosSemidef) (good : I → Bool) :
    bornMass sigma good true-bornMass rho good true≤delta := by
  let R := sigma-(((1-delta:ℝ):ℂ) • rho)
  have htR : (Matrix.trace R).re=delta := by
    simp [R,Matrix.trace_sub,Matrix.trace_smul,htrho,htrsigma]
  have hR := bornMass_le_trace R hdom good
  rw [htR] at hR
  have hρ := bornMass_nonneg rho hrho good true
  have heq : sigma=R+(((1-delta:ℝ):ℂ) • rho) := by dsimp [R]; abel
  rw [heq,bornMass_add,bornMass_smul]
  nlinarith

theorem density_domination_born_success (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (htrho : Matrix.trace rho=1) (htrsigma : Matrix.trace sigma=1)
    (delta : ℝ) (hd : 0≤delta)
    (hdom : (sigma-(((1-delta:ℝ):ℂ) • rho)).PosSemidef) (good : I → Bool) :
    (bornMass rho good false+bornMass sigma good true)/2≤1/2+delta/2 := by
  have hb := density_domination_born_bias rho sigma hrho htrho htrsigma delta hd hdom good
  have ht := bornMass_total rho good
  rw [htrho,Complex.one_re] at ht
  linarith

theorem density_domination_born_bias_lower (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (htrho : Matrix.trace rho=1) (delta : ℝ) (hd : 0≤delta)
    (hdom : (sigma-(((1-delta:ℝ):ℂ) • rho)).PosSemidef) (good : I → Bool) :
    bornMass rho good true-bornMass sigma good true≤delta := by
  let R := sigma-(((1-delta:ℝ):ℂ) • rho)
  have hR := bornMass_nonneg R hdom good true
  have hρ := bornMass_le_trace rho hrho good
  rw [htrho,Complex.one_re] at hρ
  have heq : sigma=R+(((1-delta:ℝ):ℂ) • rho) := by dsimp [R]; abel
  rw [heq,bornMass_add,bornMass_smul]
  nlinarith [mul_le_mul_of_nonneg_left hρ hd]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination
