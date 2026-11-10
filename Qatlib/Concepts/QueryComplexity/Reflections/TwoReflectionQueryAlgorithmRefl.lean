/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionQueryAlgorithmStat
import Qatlib.Concepts.ConversionCore.WitnessCompile.ReflectionsQueryProgram
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped BigOperators

theorem twoReflectionQueryAlgorithm : TwoReflectionQueryAlgorithm := by
  intro X _ _ n m hn input f v W hv hW
  obtain ⟨Δ, hΔ, hker, _hCS⟩ := reflections_source_full_cs input f v W
  let τ := 4000 * Nat.ceil W
  have hceil : 1 ≤ Nat.ceil W := by
    have h := Nat.le_ceil W
    by_contra hc
    have hz : Nat.ceil W = 0 := by omega
    rw [hz] at h
    norm_num at h
    linarith
  have hτ : 0 < τ := by dsimp [τ]; omega
  let addr := reflectionsVertexAddress (m := m) f hn
  let root : Vertex X f n m := Sum.inr (Sum.inl ())
  let j : (Fin τ × Bool) × Vertex X f n m := ((⟨0, hτ⟩, false), root)
  let S : Finset ((Fin n × Bool) × ((Fin τ × Bool) × Vertex X f n m)) :=
    Finset.univ.filter (fun p => p.2.1.2 = false)
  obtain ⟨C, hC, hQ, hG, hrun⟩ := reflections_actual_trial X n m τ f hn hτ input Δ hΔ
  have hgap (x : X) : if f x then (9 / 10 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (input x)) C (Ket ((⟨0, hn⟩, false), j))) S
    else MeasureProb (Run (workspaceBitOracle (input x)) C
      (Ket ((⟨0, hn⟩, false), j))) S ≤ (3 / 5 : ℝ) := by
    have he := reflections_frame_readout addr
      (reflectionsTrialOutput τ (twoReflectionUnitary input f x Δ) (Ket root))
      (Finset.univ.filter (fun p : (Fin τ × Bool) × Vertex X f n m => p.1.2 = false))
    have hs : Finset.univ.filter
        (fun p : (Fin n × Bool) × ((Fin τ × Bool) × Vertex X f n m) =>
          p.2 ∈ Finset.univ.filter (fun q => q.1.2 = false)) = S := by
      ext p
      simp [S]
    rw [hs, reflections_trial_born] at he
    rw [hrun, he]
    cases hx : f x
    · simp only [Bool.false_eq_true, if_false]
      exact reflections_false_power_mean input f v W hv hW Δ hΔ hker x hx
    · simp only [if_true]
      exact reflections_true_power_mean input f v W hv hW Δ hΔ hker x hx τ hτ
  obtain ⟨r, hr, D, E, hD, hDQ, hDG, hsuccess⟩ :=
    reflections_amplified_actual X n hn input f j C hC S hgap
  refine ⟨r, hr, D, E, hD, ?_, ?_, hsuccess⟩
  · rw [hDQ, hQ]
    dsimp [τ]
    omega
  · rw [hDG, hQ, hG]
    dsimp [τ]
    omega

end Qatlib.Concepts.QueryComplexity.Reflections
