/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalRatios
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.Rounding.Projection Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.Rounding.Expectation
open Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom

theorem physical_energy_bound {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0 ≤ w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (hA : ρA.PosSemidef) (hAtr : ρA.trace=1)
    (η : ℝ) (hη : 0 < η)
    (hquality : energy (secondaryHamiltonian ends w) ρA ≤ η*energy (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : ρQ.PosSemidef) (hQtr : ρQ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c))
    (hkernel : ∀ e,(∫ ω,∑ a,physicalRound n ρA hA hAtr (R ω) (ends e).1 a*
      physicalRound n ρA hA hAtr (R ω) (ends e).2 a ∂μ)=
      kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat (tParam ρA (ends e).1 (ends e).2))
    (κ p : ℝ) (hκ : 0 ≤ κ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcertificate : ∀ t k : ℝ,-1 ≤ t → k ≤ 1 → k=kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat t →
      κ*max (1-(3/η)*t) 0 ≤ p*(-4*min t 0)+(1-p)*(1-k)) :
    (∫ z,energy (qmcHamiltonian ends w)
      (outputDensity ρA (productCandidate ρA hA hAtr R) z)
      ∂outputLaw μ (qmcHamiltonian ends w) ρA (productCandidate ρA hA hAtr R)) ≤
      κ*energy (qmcHamiltonian ends w) ρQ := by
  let v := fun ω => physicalRound n ρA hA hAtr (R ω)
  let t := fun e => tParam ρA (ends e).1 (ends e).2
  let k := fun e => ∫ ω,∑ a,v ω (ends e).1 a*v ω (ends e).2 a ∂μ
  have hi (e : E) : Integrable (fun ω => ∑ a,v ω (ends e).1 a*v ω (ends e).2 a) μ :=
    round_dot_integrable μ ρA hA hAtr R hR (ends e).1 (ends e).2
  have hk (e : E) : k e ≤ 1 := mean_bloch_dot_le_one μ _ _
    (fun ω => round_ball ρA hA hAtr (R ω) (ends e).1)
    (fun ω => round_ball ρA hA hAtr (R ω) (ends e).2) (hi e)
  have hn (e : E) : κ*max (1-(3/η)*t e) 0 ≤ p*(-4*min (t e) 0)+(1-p)*(1-k e) :=
    hcertificate (t e) (k e) (global_t_range ρA hA hAtr _ _ (hends e)).1 (hk e) (hkernel e)
  have hc := output_expected_convex μ (qmcHamiltonian ends w) ρA (productCandidate ρA hA hAtr R)
    (product_energy_measurable ends hends w ρA hA hAtr R hR)
    (product_energy_integrable μ ends hends w ρA hA hAtr R hR) p hp0 hp1
  refine hc.trans ?_
  exact weighted_energy w t k hw η κ p _ _ _ hκ hp0 hn
    (qmc_energy_upper ends hends w hw ρA hA hAtr)
    (expected_product_energy μ ends hends w v hi)
    (eta_lower_clipped ends hends w hw ρR hgroundR ρA η hη hquality ρQ hQ hQtr)

theorem physical_651 {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0 ≤ w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : ρQ.PosSemidef) (hQtr : ρQ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c))
    (hkernel : ∀ e,(∫ ω,∑ a,physicalRound n ρR hgroundR.1 hgroundR.2.1 (R ω) (ends e).1 a*
      physicalRound n ρR hgroundR.1 hgroundR.2.1 (R ω) (ends e).2 a ∂μ)=
      kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat (tParam ρR (ends e).1 (ends e).2)) :
    (∫ z,energy (qmcHamiltonian ends w)
      (outputDensity ρR (productCandidate ρR hgroundR.1 hgroundR.2.1 R) z)
      ∂outputLaw μ (qmcHamiltonian ends w) ρR (productCandidate ρR hgroundR.1 hgroundR.2.1 R)) ≤
      (651/1000:ℝ)*energy (qmcHamiltonian ends w) ρQ := by
  exact physical_energy_bound μ ends hends w hw ρR hgroundR ρR hgroundR.1 hgroundR.2.1
    1 (by norm_num) (by simp) ρQ hQ hQtr R hR hkernel
    (651/1000) (345/1000) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [div_one,show (1:ℝ)-345/1000=655/1000 by norm_num] using clipped_651)

theorem physical_614 {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0 ≤ w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (hA : ρA.PosSemidef) (hAtr : ρA.trace=1)
    (hquality : energy (secondaryHamiltonian ends w) ρA ≤ (89/100:ℝ)*energy (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : ρQ.PosSemidef) (hQtr : ρQ.trace=1)
    (R : Ω → Fin 3 → Fin 2×MomentIndex n → ℝ)
    (hR : ∀ a c,Measurable (fun ω => R ω a c))
    (hkernel : ∀ e,(∫ ω,∑ a,physicalRound n ρA hA hAtr (R ω) (ends e).1 a*
      physicalRound n ρA hA hAtr (R ω) (ends e).2 a ∂μ)=
      kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat (tParam ρA (ends e).1 (ends e).2)) :
    (∫ z,energy (qmcHamiltonian ends w)
      (outputDensity ρA (productCandidate ρA hA hAtr R) z)
      ∂outputLaw μ (qmcHamiltonian ends w) ρA (productCandidate ρA hA hAtr R)) ≤
      (614/1000:ℝ)*energy (qmcHamiltonian ends w) ρQ := by
  exact physical_energy_bound μ ends hends w hw ρR hgroundR ρA hA hAtr
    (89/100) (by norm_num) hquality ρQ hQ hQtr R hR hkernel
    (614/1000) (153/400) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (1:ℝ)-153/400=247/400 by norm_num] using clipped_614)
end Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalRatios
