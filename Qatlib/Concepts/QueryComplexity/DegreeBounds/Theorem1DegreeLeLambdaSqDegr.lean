/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem1DegreeLeLambdaSqStat
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.ParityPartition
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.SensitivityCompression

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open scoped BigOperators Matrix.Norms.L2Operator

/-- The exact real polynomial degree of a Boolean function is at most its squared spectral
sensitivity. -/
theorem theorem1DegreeLeLambdaSq : Theorem1DegreeLeLambdaSq := by
  classical
  intro I _ _ f
  by_cases hd : Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f=0
  · simpa only [hd,Nat.cast_zero] using sq_nonneg (spectralSensitivity f)
  obtain ⟨s,hcard,hcorr⟩ := exactDegree_alternating_face f (Nat.pos_of_ne_zero hd)
  have hs : s.card ≠ 0 := by omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hs
  let e : Fin (m+1) ≃ s :=
    (Fintype.equivFinOfCardEq (by simpa using hm) : s ≃ Fin (m+1)).symm
  let F : (s → Bool) → Bool := fun x => f (faceEmbedding s x)
  let g : (Fin (m+1) → Bool) → Bool := fun x => F (cubeMap e x)
  let E : (Fin (m+1) → Bool) ≃ (s → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  have hE (x : Fin (m+1) → Bool) : E x=cubeMap e x := rfl
  have hsum : (∑ x : Fin (m+1) → Bool, cubeSign x * (if g x then (1 : ℝ) else 0))=
      ∑ y : s → Bool, cubeSign y * (if F y then (1 : ℝ) else 0) := by
    calc
      _ = ∑ x : Fin (m+1) → Bool, cubeSign (E x) * (if F (E x) then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hE,cubeMap_sign]
      _ = _ := E.sum_comp (fun y : s → Bool => cubeSign y * (if F y then (1 : ℝ) else 0))
  have hnon : (∑ x : Fin (m+1) → Bool, cubeSign x * (if g x then (1 : ℝ) else 0)) ≠ 0 := by
    rw [hsum]
    exact hcorr
  have hlow := sensitivity_nonzero_parity_norm m g hnon
  have hupper : spectralSensitivity g ≤ spectralSensitivity f :=
    (sensitivity_cubeMap_norm_le e F).trans (sensitivity_face_norm_le f s)
  have hsq : spectralSensitivity g ^ 2 ≤ spectralSensitivity f ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (sensAdjacency g)) (norm_nonneg (sensAdjacency f))).mpr hupper
  have hdim : (Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f : ℝ)=(m+1 : ℝ) := by
    exact_mod_cast hcard.symm.trans hm
  rw [hdim]
  exact hlow.trans hsq

end Qatlib.Concepts.QueryComplexity.DegreeBounds
