/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedStat
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationLowc
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.SignalPrimitive.SparseSim.Lc17AuxSimulation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.SignalPrimitive.SparseSim

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

theorem sparseSimulationCorrectedRestricted : SparseSimulationCorrectedRestricted := by
  intro I W _ _ _ _ H d b hHerm hd hb hrows hcols hentries L R S hL hR hLR hSu hSd hS2 hSL
    t ε ht hε hεhalf
  let τ : ℝ := t * d * b
  let c : ℝ := ((d : ℝ) * b)⁻¹
  let q := lcCorrectedQ τ (ε / 8)
  let N := 2 * (q - 1)
  have hdb : 0 < (d : ℝ) * b := mul_pos (by exact_mod_cast hd) hb
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hc : 0 < c := inv_pos.mpr hdb
  have hε8 : 0 < ε / 8 := by positivity
  have hε8one : ε / 8 ≤ 1 := by linarith
  have hq4 : 4 ≤ q := by
    dsimp [q, lcCorrectedQ]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hq : 1 ≤ q := by omega
  have hN : Even N := ⟨q - 1, by dsimp [N]; omega⟩
  have hNpos : 0 < N := by dsimp [N]; omega
  obtain ⟨htail, hbudget⟩ := jacobiAngerCorrectedDegree τ (ε / 8) hτ hε8 hε8one
  have hτq : τ ≤ ((q - 1 : ℕ) : ℝ) := by
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq]; norm_num
    rw [hcast]
    change τ + 1 ≤ (q : ℝ) at hbudget
    linarith
  obtain ⟨A, Qt, hA, hQ, hAd, hQd, hApprox⟩ := jacobiAngerTruncation q τ hq hτ hτq
  have happ : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) *
        realEval Qt (Real.cos (θ / 2) : ℂ) -
        Complex.exp (Complex.I * ((-τ * Real.sin θ : ℝ) : ℂ))‖ ≤ ε / 8 := by
    intro θ hθ
    have hh := (hApprox θ hθ).trans (le_trans htail (by linarith : (ε / 8) / 8 ≤ ε / 8))
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using! hh
  obtain ⟨phis, hlen, hamp⟩ := lcSourceCompilation N (fun θ => -τ * Real.sin θ) A Qt (ε / 8)
    hN hNpos (by intro θ; simp [Real.sin_neg]) hA hQ hAd hQd hε8 (by linarith) happ
  have hlenEven : Even phis.length := hlen.symm ▸ hN
  have hampε : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖lcPlusAmp phis θ - Complex.exp (Complex.I * ((-τ * Real.sin θ : ℝ) : ℂ))‖ ≤ ε := by
    intro θ hθ
    have hh := hamp θ hθ
    nlinarith
  refine ⟨phis, hlen, ?_⟩
  intro ψ hψ ev hev
  have hHnorm : ‖(c : ℂ) • H‖ ≤ 1 := by
    rw [← hLR]
    exact lcFrame_cross_norm L R hL hR
  have hs : |c * ev| ≤ 1 := lcFrame_eigen_bound H c ψ ev hHnorm hψ hev
  obtain ⟨wp, wm, ap, am, hwp, hwm, horth, ⟨V, hVU, hVeq, hVp, hVm⟩, hbal⟩ :=
    sparseWalkEigenphasesRestricted I W H c hc hHnorm L R S hL hR hLR hSu hSd hS2 hSL ψ hψ ev hev
  change V = lcWalk S L at hVeq
  subst V
  let θp := lcPositiveEigenAngle (c * ev)
  let θm := Real.pi - Real.arcsin (c * ev)
  have hθp : θp ∈ Set.Icc 0 (2 * Real.pi) := lcPositiveEigenAngle_mem _
  have hθm : θm ∈ Set.Icc 0 (2 * Real.pi) := by
    have ha := Real.arcsin_mem_Icc (c * ev)
    dsimp [θm]
    exact ⟨by linarith [ha.2, Real.pi_pos], by linarith [ha.1, Real.pi_pos]⟩
  have hVp' : lcWalk S L *ᵥ wp = Complex.exp (Complex.I * (θp : ℂ)) • wp := by
    rw [lcPositiveEigenAngle_phase]; exact hVp
  have hVm' : lcWalk S L *ᵥ wm = Complex.exp (Complex.I * (θm : ℂ)) • wm := by
    rw [lcNegativeEigenAngle_phase]; exact hVm
  let e := Complex.exp (Complex.I * (-(ev : ℂ) * t))
  have hphase : ∀ θ : ℝ, Real.sin θ = c * ev →
      Complex.exp (Complex.I * ((-τ * Real.sin θ : ℝ) : ℂ)) = e := by
    intro θ hsin
    have hreal : -τ * (c * ev) = -ev * t := by
      have hcancel : ((d : ℝ) * b) * ((d : ℝ) * b)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hdb)
      dsimp [τ, c]
      linear_combination -(t * ev) * hcancel
    rw [hsin, hreal]
    dsimp [e]
    congr 1
    push_cast
    ring
  have hsin := lcEigenAngles_sin (c * ev) hs
  have hAp : ‖lcPlusAmp phis θp - e‖ ≤ ε := by
    have hh := hampε θp hθp
    rw [hphase θp hsin.1] at hh
    exact hh
  have hAm : ‖lcPlusAmp phis θm - e‖ ≤ ε := by
    have hh := hampε θm hθm
    rw [hphase θm hsin.2] at hh
    exact hh
  let z := ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    ((Complex.exp (Complex.I * (ap : ℂ)) * lcPlusAmp phis θp) • wp +
     (Complex.exp (Complex.I * (am : ℂ)) * lcPlusAmp phis θm) • wm)
  have hy : compress (lcPlusFrame L) (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ =
      Lᴴ *ᵥ z := lcSimWord_frame_action L (lcWalk S L) ψ wp wm ap am θp θm hVU hVp' hVm'
        hbal phis hlenEven
  have hz : z - e • (L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      ((Complex.exp (Complex.I * (ap : ℂ)) * (lcPlusAmp phis θp - e)) • wp +
       (Complex.exp (Complex.I * (am : ℂ)) * (lcPlusAmp phis θm - e)) • wm) := by
    rw [hbal]
    dsimp [z]
    module
  have herrZ : ‖toEuclidean_fromVec (z - e • (L *ᵥ ψ))‖ ≤ ε := by
    by_cases hlt : |c * ev| < 1
    · rw [hz]
      exact lcBalanced_error_bound wp wm ap am ε _ _ hwp hwm (horth hlt) hε.le hAp hAm
    · have hsat : |c * ev| = 1 := le_antisymm hs (le_of_not_gt hlt)
      have hθeq : θp = θm := lcEigenAngles_saturated _ hsat
      have heq : z - e • (L *ᵥ ψ) = (lcPlusAmp phis θp - e) • (L *ᵥ ψ) := by
        rw [hbal]
        dsimp [z]
        rw [← hθeq]
        module
      rw [heq]
      change ‖(lcPlusAmp phis θp - e) • toEuclidean_fromVec (L *ᵥ ψ)‖ ≤ ε
      rw [norm_smul, isometry_mulVec_norm hL ψ,
        (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one]
      exact hAp
  have herrY : ‖toEuclidean_fromVec
      (compress (lcPlusFrame L) (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ - e • ψ)‖ ≤ ε := by
    rw [hy]
    have heq : Lᴴ *ᵥ z - e • ψ = Lᴴ *ᵥ (z - e • (L *ᵥ ψ)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul Lᴴ e (L *ᵥ ψ),
        Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rw [heq]
    exact (lcFrame_adjoint_contraction L hL _).trans herrZ
  have hen : ‖e‖ = 1 := by
    dsimp [e]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  exact lcOutput_guarantee ψ _ e ε hψ hen hε.le hεhalf herrY

end Qatlib.Concepts.SignalPrimitive.SparseSim
