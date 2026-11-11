/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot

/-!
# Pilot-adaptive quantum mean records

The dependent record type `PilotMeanRecord` combines a classical pilot sample with repeated
signed quantum mean records at a pilot-selected precision. The definitions `pilotMeanMass`,
`pilotMeanReadout`, and `pilotMeanResources` give the joint mass, median readout, and resource
ledger.

For bounded rational payoffs, the joint law is normalized and the error probability is at most
2/(Nν²) + (8/9)^r under the stated pilot hypotheses. This composes variance certification with
quantum mean estimation in the framework of [Montanaro2015].

## Main statements

* `pilotMeanMass_sum_one`: the dependent joint record masses sum to one.
* `unknown_variance_pilot_actual_conditional_resource_ledger`: the resource vector is explicit
  for each pilot record.
* `unknown_variance_pilot_same_joint_quantum_mean_probability`: pilot and conditional quantum
  errors share one joint-law bound.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.MonteCarloMean.PilotVariance
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
set_option warningAsError false
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A pilot observation record together with `2 * r + 1` signed mean records whose layer
precision depends on that pilot record. -/
abbrev PilotMeanRecord (I : Type) (N h r : ℕ) (f : I  → ℚ) (nu eps : ℚ) :=
  Σ omega : Fin N  → I,Fin (2*r+1)  → I ×
    (LayerRecord (pilotPrecision N h f nu eps omega) ×LayerRecord (pilotPrecision N h f nu eps omega))

/-- The joint mass of a pilot record and its repeated conditional signed mean records at the
pilot-selected scale and precision. -/
noncomputable def pilotMeanMass {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (N h r : ℕ) (f : I  → ℚ) (nu eps : ℚ) (hA : A∈Matrix.unitaryGroup I ℂ)
    (z : PilotMeanRecord I N h r f nu eps) : ℝ :=
  (signedMeanSource A j hA).probOf z.1 *
    (signedMeanLaw (pilotPrecision N h f nu eps z.1) A j (fun i => (f i:ℝ))
      (pilotScale N h f nu z.1) hA).probOf z.2

/-- The signed mean median readout evaluated with the scale and precision selected from the
pilot observations. -/
noncomputable def pilotMeanReadout {I : Type} (N h r : ℕ) (f : I  → ℚ) (nu eps : ℚ)
    (z : PilotMeanRecord I N h r f nu eps) : ℝ :=
  signedMeanMedian (pilotPrecision N h f nu eps z.1) r (fun i => (f i:ℝ)) (pilotScale N h f nu z.1) z.2

/-- The conditional signed mean resource ledger with `N` additional pilot source preparations,
measurements, and gates. -/
noncomputable def pilotMeanResources {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (N h r : ℕ) (f : I  → ℚ) (nu eps : ℚ) (z : PilotMeanRecord I N h r f nu eps) : QuantumMeanResources :=
  let k := pilotPrecision N h f nu eps z.1
  let v :=
      signedMeanMedianResources k r A j (fun i => (z.2 i).1) (fun i => (f i:ℝ))
      (pilotScale N h f nu z.1)
  {v with sourcePreparations:=N+v.sourcePreparations,measurements:=N+v.measurements,gates:=N+v.gates}

/-- For a unitary source preparation, the masses of all dependent pilot and conditional quantum
mean records sum to one. -/
theorem pilotMeanMass_sum_one {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (N h r : ℕ) (f : I → ℚ) (nu eps : ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (∑ z : PilotMeanRecord I N h r f nu eps, pilotMeanMass A j N h r f nu eps hA z) = 1 := by
  classical
  unfold PilotMeanRecord
  rw [Fintype.sum_sigma]
  dsimp only [pilotMeanMass]
  calc
    _ = ∑ omega : Fin N → I, (signedMeanSource A j hA).probOf omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [← Finset.mul_sum, (signedMeanLaw (pilotPrecision N h f nu eps omega) A j
        (fun i => (f i : ℝ)) (pilotScale N h f nu omega) hA).sum_probOf (2*r+1), mul_one]
    _ = 1 := (signedMeanSource A j hA).sum_probOf N

/-- For each pilot and quantum record, the full resource vector equals the stated expression in
the selected precision, grid, and repetition counts, including the `N` pilot costs. -/
theorem unknown_variance_pilot_actual_conditional_resource_ledger
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (N h r : ℕ)
    (f : I → ℚ) (nu eps : ℚ) (z : PilotMeanRecord I N h r f nu eps) :
    let k := pilotPrecision N h f nu eps z.1;
    let q := (k+2)*(2*layerRepetitions k+1);
    pilotMeanResources A j N h r f nu eps z =
      ⟨N+(2*r+1),(2*r+1)*(2*q),N+(2*r+1)*(1+2*q),
        (2*r+1)*(2*q*layerGrid k),(2*r+1)*(2*q*(layerGrid k-1)),
        (2*r+1)*(2*q*(layerGrid k-1)),N+(2*r+1)*(1+2*q*(5*(layerGrid k-1)+3))⟩ := by
  (try dsimp only)
  dsimp only [pilotMeanResources]
  rw [signed_centered_fresh_full_resources]

/-- For bounded rational payoffs, positive `N` and `eps`, and 0 < nu ≤ 1/4, the joint record
masses are nonnegative and normalized, with readout error probability at most 2/(N·nu²) +
(8/9)^r. -/
theorem unknown_variance_pilot_same_joint_quantum_mean_probability
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (N h r : ℕ)
    (f : I → ℚ) (nu eps : ℚ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    (∑ z : PilotMeanRecord I N h r f nu eps, pilotMeanMass A j N h r f nu eps hA z) = 1 ∧
    (∀ z : PilotMeanRecord I N h r f nu eps, 0 ≤ pilotMeanMass A j N h r f nu eps hA z) ∧
    (∑ z ∈ Finset.univ.filter (fun z : PilotMeanRecord I N h r f nu eps =>
      (eps : ℝ) < |pilotMeanReadout N h r f nu eps z -
        (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|), pilotMeanMass A j N h r f nu eps hA z)
      ≤ 2/((N : ℝ)*(nu : ℝ)^2)+(8/9:ℝ)^r := by
  classical
  let p := signedMeanSource A j hA
  let B :=
      fun omega : Fin N → I => (pilotScale N h f nu omega : ℝ)^2 < p.variance (fun i => (f i : ℝ))
  let v := fun omega : Fin N → I =>
    (signedMeanLaw (pilotPrecision N h f nu eps omega) A j (fun i => (f i : ℝ))
      (pilotScale N h f nu omega) hA).probEvent
      (fun w => (eps : ℝ) < |signedMeanMedian (pilotPrecision N h f nu eps omega) r
        (fun i => (f i : ℝ)) (pilotScale N h f nu omega) w - p.expect (fun i => (f i : ℝ))|)
  have hp : ∀ omega : Fin N → I, 0 ≤ p.probOf omega :=
      fun omega => Finset.prod_nonneg fun i _ => p.nonneg _
  refine ⟨pilotMeanMass_sum_one A j N h r f nu eps hA, ?_, ?_⟩
  · intro z; exact mul_nonneg (hp z.1)
      (Finset.prod_nonneg fun i _ => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.nonneg _ _)
  have hv1 : ∀ omega, v omega ≤ 1 := by
    intro omega
    unfold v Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    calc
      _ ≤ ∑ w : Fin (2*r+1) → _, (signedMeanLaw (pilotPrecision N h f nu eps omega) A j
        (fun i => (f i : ℝ)) (pilotScale N h f nu omega) hA).probOf w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun w _ _ => Finset.prod_nonneg fun i _ => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.nonneg _ _)
      _ = 1 := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf _ _
  have hgood : ∀ omega, ¬B omega → v omega ≤ (8/9:ℝ)^r := by
    intro omega hb
    have hg := unknown_variance_pilot_native_moments_and_scale I N h f nu omega hN hf hnu hnu1
    have hk :=
        unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps omega hN hf hnu hnu1 heps
    have hs : (0 : ℝ) < pilotScale N h f nu omega := by exact_mod_cast hg.2.2.2.2.1
    have hh := signed_centered_fresh_median_failure I (pilotPrecision N h f nu eps omega) r A j
      (fun i => (f i : ℝ)) (pilotScale N h f nu omega) hA hk.1 hs (le_of_not_gt hb)
    refine le_trans ?_ hh
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_lt hk.2.1 (Finset.mem_filter.mp hw).2⟩
    · intro w _ _; exact Finset.prod_nonneg fun i _ => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.nonneg _ _
  have hsplit : (∑ z ∈ Finset.univ.filter (fun z : PilotMeanRecord I N h r f nu eps =>
      (eps : ℝ) < |pilotMeanReadout N h r f nu eps z - p.expect (fun i => (f i : ℝ))|),
      pilotMeanMass A j N h r f nu eps hA z) = ∑ omega, p.probOf omega * v omega := by
    rw [Finset.sum_filter, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro omega _
    unfold v Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [pilotMeanMass, pilotMeanReadout, mul_ite, mul_zero]
    rfl
  rw [hsplit]
  calc
    _ ≤ ∑ omega : Fin N → I, p.probOf omega * (if B omega then 1 else (8/9:ℝ)^r) := by
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_left _ (hp omega)
      split_ifs with hb
      · exact hv1 omega
      · exact hgood omega hb
    _ = (∑ omega ∈ Finset.univ.filter B, p.probOf omega) +
        (∑ omega ∈ Finset.univ.filter (fun omega => ¬B omega), p.probOf omega) * (8/9:ℝ)^r := by
      simp_rw [mul_ite, mul_one]
      rw [Finset.sum_ite, Finset.sum_mul]
    _ ≤ 2/((N : ℝ)*(nu : ℝ)^2)+(8/9:ℝ)^r := by
      have hb :=
          unknown_variance_pilot_actual_born_certificate_failure I A j N h f nu hA hN hf hnu hnu1
      have hc : (∑ omega ∈ Finset.univ.filter (fun omega => ¬B omega), p.probOf omega) ≤ 1 := calc
        _ ≤ ∑ omega : Fin N → I, p.probOf omega := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun omega _ _ => hp omega)
        _ = 1 := p.sum_probOf N
      exact add_le_add hb
          (by simpa using! mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (8/9:ℝ)^r))

end Qatlib.Concepts.MonteCarloMean.PilotVariance
