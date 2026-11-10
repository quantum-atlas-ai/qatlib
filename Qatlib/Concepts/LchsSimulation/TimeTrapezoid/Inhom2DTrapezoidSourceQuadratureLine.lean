/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.TrapezoidSourceDerivatives
import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.Inhom2DTrapezoidSourceQuadratureStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureLine
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
private def trap2dEuclideanMap {I : Type} [Fintype I] : QState I →L[ℝ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℂ)).symm.toContinuousLinearMap

theorem inhomogeneous_2d_trapezoid_source_of_quadrature
    (hq : HomogeneousKTrapezoidQuadrature) : Inhomogeneous2DTrapezoidSourceQuadrature := by
  intro I _ _ L L' H H' b b' b'' s t K N Mt β β₂ lamL lamH lamLd lamHd bmax
    hL hH hb hPSD hHerm hst hK hN hMt hdL hdH hnLd hnHd hd hd' hβ hβ₂ hbmax hlL hlH
  let A := fun u => L u+Complex.I • H u
  let F := fun u => toEuclidean_fromVec (orderedEvolution A u t *ᵥ b u)
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hE : Continuous (fun u => orderedEvolution A u t) :=
    continuous_iff_continuousAt.mpr (fun u => (orderedEvolution_hasDerivAt_start A hA t u).continuousAt)
  have hF : Continuous F := trap2dEuclideanMap.continuous.comp (hE.matrix_mulVec hb)
  obtain ⟨F', F'', hDF, hDF', hNF''⟩ := inh_trap_source_derivatives
    L L' H H' b b' b'' s t β β₂ lamL lamH lamLd lamHd bmax hL hH hPSD hHerm
    (fun u hu => hdL u hu.1 hu.2) (fun u hu => hdH u hu.1 hu.2)
    (fun u hu => hnLd u hu.1 hu.2) (fun u hu => hnHd u hu.1 hu.2)
    (fun u hu => hd u hu.1 hu.2) (fun u hu => hd' u hu.1 hu.2)
    (fun u hu => hβ u hu.1 hu.2) (fun u hu => hβ₂ u hu.1 hu.2)
    (fun u hu => hbmax u hu.1 hu.2) hlL hlH
  have hleft := inh_trap_grid_error F F' F'' s t
    (((lamL+lamH)^2+(lamLd+lamHd))*bmax+2*(lamL+lamH)*β+β₂)
    Mt hst hMt hF hDF hDF' hNF''
  let η := 2/(Real.pi*(K : ℝ))+(2*(K : ℝ))^3/(12*(N : ℝ)^2)*
    (2*(1+(∫ u in s..t, ‖L u‖)+(∫ u in s..t, ‖L u‖)^2)/Real.pi)
  have hη : 0 ≤ η := by
    have hi : 0 ≤ ∫ u in s..t, ‖L u‖ :=
        intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
    dsimp [η]; positivity
  have hb0 : 0 ≤ bmax := (norm_nonneg _).trans (hbmax s le_rfl hst)
  have hnode (l : Fin (Mt+1)) :
      ‖toEuclidean_fromVec
        (((∑ j : Fin (N+1), kTrapCoeff K N j • inh2dTrapSourceKUnitary L H s t K N Mt j l) *ᵥ
          b (inhTrapNode Mt s t l))-orderedEvolution A (inhTrapNode Mt s t l) t *ᵥ
            b (inhTrapNode Mt s t l))‖ ≤ η*bmax := by
    have hl := inh_trap_node_mem Mt s t hst hMt l
    have hi := intervalIntegral.integral_mono_interval (μ := volume) (f := fun u => ‖L u‖)
      hl.1 hl.2 le_rfl
      (Filter.Eventually.of_forall (fun u => norm_nonneg (L u))) (hL.norm.intervalIntegrable s t)
    have hlocal := hq I L H (inhTrapNode Mt s t l) t K N
      hL hH hPSD hHerm hl.2 hK hN
    have hq' : ‖(∑ j : Fin (N+1), kTrapCoeff K N j • inh2dTrapSourceKUnitary L H s t K N Mt j l)-
        orderedEvolution A (inhTrapNode Mt s t l) t‖ ≤ η :=
      hlocal.trans (by
        have hi0 : 0 ≤ ∫ u in inhTrapNode Mt s t l..t, ‖L u‖ :=
          intervalIntegral.integral_nonneg hl.2 (fun _ _ => norm_nonneg _)
        dsimp [η]; gcongr)
    have hm := l2_norm_mulVec_fromVec_le
      ((∑ j : Fin (N+1), kTrapCoeff K N j • inh2dTrapSourceKUnitary L H s t K N Mt j l)-
        orderedEvolution A (inhTrapNode Mt s t l) t) (b (inhTrapNode Mt s t l))
    rw [Matrix.sub_mulVec] at hm
    exact hm.trans (mul_le_mul hq' (hbmax _ hl.1 hl.2) (norm_nonneg _) hη)
  have hk : ‖toEuclidean_fromVec (inh2dTrapSourceSum L H b s t K N Mt)-
      ∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l)‖ ≤ (t-s)*bmax*η := by
    change ‖trap2dEuclideanMap (∑ l : Fin (Mt+1), (inhTrapWeight Mt s t l : ℂ) • _)-
      ∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l)‖ ≤ _
    simp only [map_sum, Complex.coe_smul, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
      (g := fun l => inhTrapWeight Mt s t l*(η*bmax)) (fun l _ => ?_)).trans_eq ?_)
    · rw [norm_smul, Real.norm_of_nonneg (inh_trap_weight_nonneg Mt s t hst l)]
      exact mul_le_mul_of_nonneg_left (hnode l) (inh_trap_weight_nonneg Mt s t hst l)
    · rw [← Finset.sum_mul, inh_trap_weight_sum Mt s t hMt]
      ring
  have hint : (∫ u in s..t, F u) = toEuclidean_fromVec (inhSourceResponse L H b s t) :=
    trap2dEuclideanMap.intervalIntegral_comp_comm ((hE.matrix_mulVec hb).intervalIntegrable s t)
  rw [hint] at hleft
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (toEuclidean_fromVec (inh2dTrapSourceSum L H b s t K N Mt))
    (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l • F (inhTrapNode Mt s t l))
    (toEuclidean_fromVec (inhSourceResponse L H b s t))
  change ‖toEuclidean_fromVec (inh2dTrapSourceSum L H b s t K N Mt)-
    toEuclidean_fromVec (inhSourceResponse L H b s t)‖ ≤ _
  exact ht.trans ((add_le_add hk hleft).trans_eq (by dsimp [η]; ring))

theorem inhomogeneous2DTrapezoidSourceQuadrature : Inhomogeneous2DTrapezoidSourceQuadrature :=
  inhomogeneous_2d_trapezoid_source_of_quadrature homogeneousKTrapezoidQuadrature

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
