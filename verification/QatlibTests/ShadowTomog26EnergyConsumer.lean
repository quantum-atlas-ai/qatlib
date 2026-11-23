module

import Qatlib.Papers.ShadowTomog26.EnergyEstimate.RestrictedContexts
import Mathlib.Tactic.NormNum

/-!
# Consumers of the optimal allocation and restricted Born estimation bounds
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.ShadowTomog26EnergyConsumer

open scoped Classical BigOperators
open Qatlib.Foundations.GraphFraction.CoverLP
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Papers.ShadowTomog26.EnergyEstimate
open Qatlib.Papers.ShadowTomog26.EnergyEstimate

/-- For two negative coefficients, the optimum is attained with a positive allocation of budget two. -/
example :
    let c : Fin 2 → ℝ := fun _ => -1
    (∀ n : Fin 2 → ℝ, (∀ i, 0 < n i) → ∑ i, n i = 2 →
      coeffPowerSum c ^ ((3 : ℝ) / 2) / Real.sqrt 2 ≤ ∑ i, |c i| / Real.sqrt (n i)) ∧
    (∀ i, 0 < powerAllocation c 2 i) ∧ (∑ i, powerAllocation c 2 i) = 2 ∧
      (∑ i, |c i| / Real.sqrt (powerAllocation c 2 i)) =
        coeffPowerSum c ^ ((3 : ℝ) / 2) / Real.sqrt 2 := by
  exact magnitude_allocation_min (fun _ : Fin 2 => -1) (fun _ => by norm_num) 2 (by norm_num)

/-- The same positive coverage scale bounds the one-shot variance for every state. -/
example (G : SimpleGraph (Fin 2)) {S : Fin 2 → HermitianMat (Fin 2) ℂ}
    (M : JointScheme (K := Context G) (Ω := Fin 2) S)
    (hM : ∀ I, M.context I = I.val) (F : Finset (Context G)) (q : Context G → ℝ)
    (hq : q ∈ Qatlib.Foundations.ProbabilityCore.SimplexWeights.weights ℝ (Context G))
    (hsupp : SupportedOn G F q) (c : Fin 2 → ℝ) (hc : ∀ i, c i ≠ 0)
    (T : ℝ) (hT : 0 < T)
    (hcov : ∀ i, powerAllocation c T i ≤ restrictedCoverage G F q i) :
    ∀ ρ : MState (Fin 2),
      mean (shotLaw (bornLaw M q ρ) 1) (shotAverage (energyScore G M q c) 1) =
        ∑ i, c i * ρ.exp_val (S i) ∧
      variance (shotLaw (bornLaw M q ρ) 1) (shotAverage (energyScore G M q c) 1) ≤
        coeffPowerSum c ^ 3 / T := by
  simpa only [Nat.cast_one, one_mul] using
    restricted_family_energy_bound G M hM F q hq hsupp c hc T hT hcov 1 Nat.one_pos

/-- The cover cost can only increase when the supplied subfamily can still meet demand. -/
example (G : SimpleGraph (Fin 2)) (F : Finset (Context G)) (a : Fin 2 → ℝ)
    (h : ∃ x : Context G → ℝ, Feasible G a x ∧ SupportedOn G F x) :
    coverValue G a ≤ restrictedCoverValue G F a :=
  cover_value_le_restricted_cover_value G F a h

end QatlibTests.ShadowTomog26EnergyConsumer
