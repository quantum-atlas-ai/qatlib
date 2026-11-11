/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichStat
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichContracts
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationVari

/-!
# Proofs of the amplitude-estimation contracts

This module proves the existential and median estimation statements supporting [Ambainis2012].
The theorem `estimateSandwich_proof` uses the coarse resolution-two error bound for the
existential contract, while `estimateSandwich_answer` establishes the concrete median guarantees
at every prescribed resolution.

## Main statements

* `estimateSandwich_proof`: Establish the existential estimation contract.
* `estimateSandwich_answer`: Establish the concrete median estimation proposition.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

open Matrix
set_option warningAsError false

/-- For `0 ≤ a ≤ 1`, the zero estimate satisfies the stated amplitude-estimation error bound at
resolution two. -/
theorem vt_coarse_estimate_error (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |0 - a| ≤ a / 4 + 8 / (2 : ℝ) * Real.sqrt a + 10 / (2 : ℝ) ^ 2 := by
  rw [zero_sub, abs_neg, abs_of_nonneg ha0]
  nlinarith [Real.sqrt_nonneg a]

/-- The existential contract `estimateSandwich` holds, with a coarse zero estimator satisfying
its resolution-dependent error bound. -/
theorem estimateSandwich_proof : estimateSandwich := by
  classical
  intro I _ _ W hW j₀ S δ hδ _
  let d := aeLaw 2 W j₀ S hW (by omega)
  let law : (Fin 1 → Fin 2) → ℝ := fun ω => d.prob (ω 0)
  have hsum : ∑ ω, law ω = 1 := by
    have he := Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) law d.prob
      (fun ω => by rfl)
    exact he.trans d.sum_one
  refine ⟨2, 1, by omega, (fun _ => 0), law, Finset.univ,
    hsum, (fun ω => d.nonneg (ω 0)), ?_, ?_, ?_, ?_⟩
  · change 1 - δ ≤ ∑ ω, law ω
    rw [hsum]
    linarith
  · intro ω _
    exact vt_coarse_estimate_error _ (vt_prepared_mass_bounds W hW j₀ S).1
      (vt_prepared_mass_bounds W hW j₀ S).2
  · intro _ _
    rfl
  · refine ⟨Fin 2 × (Bool × I), inferInstance,
      aeControlledGate 2 (preparedMark S), countedAECircuit 2 W j₀,
      TensorState (Ket (0 : Fin 2)) (TensorState (Ket false) (Ket j₀)),
      (fun p _ => p.1), ?_, ?_⟩
    · intro ω
      change MeasureProb _
        (Finset.univ.filter (fun p : Fin 2 × (Bool × I) => p.1 = ω 0)) = _
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hp
        funext i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        simpa only [hi] using! hp
      · intro hp
        exact congrFun hp 0
    · have hc := prepared_ae_access_ledger 2 (by omega) W j₀
      rw [hc.1, hc.2.1]

/-- The median amplitude-estimation proposition `EstimateSandwich` holds [Ambainis2012]. -/
theorem estimateSandwich_answer : EstimateSandwich := by
  classical
  intro I _ _ A hA j S M hM δ hδ _
  obtain ⟨r,hr⟩:=vt_median_estimate_good_mass M hM A hA j S δ hδ
  refine ⟨r,(aeLaw M A j S hA hM).sum_probOf _,?_,hr,?_,?_,?_,?_⟩
  · intro ω
    exact Finset.prod_nonneg fun i _=>(aeLaw M A j S hA hM).nonneg _
  · intro ω hω
    exact (Finset.mem_filter.mp hω).2
  · intro ha ω hω
    exact vt_median_estimate_zero_support M hM r A hA j S ha ω hω
  · intro ω
    exact vt_fresh_ae_born_law M hM A hA j S (2*r+1) ω
  · exact vt_fresh_ae_count M hM A hA j S (2*r+1)
end Qatlib.Papers.VarTimeAmpAmp10.Estimate
