/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShadowTomog26.EnergyEstimate.OptimalBorn
public import Qatlib.Papers.ShadowTomog26.EnergyEstimate.AllocationInequality

@[expose] public section

/-!
# Energy estimation from restricted context families

A measurement architecture may allow only a subfamily `F` of the independent-set contexts.
Write `C = ∑ i, |c i|^(2/3)`. A supported probability law with vertex coverage at least
`T · |c i|^(2/3) / C` gives an unbiased iid `N`-shot estimate with variance at most
`C^3 / (N · T)`. Only the coverage of the supplied law enters the bound.

For example, take the three single-qubit Pauli Z observables on separate qubits, all
with coefficient one, and the equal mixture of the all-zero and all-one states. The
full joint context has one-shot score `±3` and variance `9`. For the restricted
contexts `{1, 2}` and `{3}`, the equal mixture maximizes minimum vertex coverage.
Its inverse-inclusion score is `±4` or `±2`, each with probability `1/4`, giving
variance `10` and showing that the full-family guarantee need not hold. This law
has `T = 3/2` and bound `18`. This example uses arbitrary independent-set contexts;
the theorem does not require them to be maximal.

## References

* [XuEtAl2026], [arXiv:2608.08429v1](https://arxiv.org/abs/2608.08429v1)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ShadowTomog26.EnergyEstimate

open scoped Classical BigOperators
open Qatlib.Foundations.GraphFraction.CoverLP
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Papers.ShadowTomog26.EnergyEstimate

variable {V Ω d : Type*} [Fintype V] [DecidableEq V]
  [Fintype Ω] [Fintype d] [DecidableEq d]

/-- A context law is supported on the subfamily `F` when it vanishes outside `F`. -/
def SupportedOn (G : SimpleGraph V) (F : Finset (Context G)) (q : Context G → ℝ) : Prop :=
  ∀ I ∉ F, q I = 0

/-- Vertex coverage of a law restricted to the subfamily `F`. -/
def restrictedCoverage (G : SimpleGraph V) (F : Finset (Context G))
    (q : Context G → ℝ) (i : V) : ℝ :=
  ∑ I ∈ F, q I * incidence G I i

/-- The fractional-cover cost over a restricted context family: the infimum total mass of
feasible covers supported on `F`. -/
def restrictedCoverValue (G : SimpleGraph V) (F : Finset (Context G)) (a : V → ℝ) : ℝ :=
  sInf ((fun x : Context G → ℝ => ∑ I, x I) '' {x | Feasible G a x ∧ SupportedOn G F x})

/-- A supported law has the same full and restricted vertex coverage. -/
theorem coverage_eq_restrictedCoverage (G : SimpleGraph V) (F : Finset (Context G))
    (q : Context G → ℝ) (hsupp : SupportedOn G F q) (i : V) :
    coverage G q i = restrictedCoverage G F q i := by
  unfold coverage restrictedCoverage
  exact (Finset.sum_subset (Finset.subset_univ F)
    (fun I _ hI => by rw [hsupp I hI, zero_mul])).symm

/-- Any feasible cover supported on `F` is a feasible cover of the full family, and the
restricted fractional-cover cost is therefore at least the unrestricted cost. -/
theorem cover_value_le_restricted_cover_value [Nonempty V] (G : SimpleGraph V)
    (F : Finset (Context G)) (a : V → ℝ)
    (hne : ∃ x : Context G → ℝ, Feasible G a x ∧ SupportedOn G F x) :
    coverValue G a ≤ restrictedCoverValue G F a := by
  have hbelow : BddBelow ((fun x : Context G → ℝ => ∑ I, x I) ''
      {x | Feasible G a x}) := by
    refine ⟨0, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact Finset.sum_nonneg fun I _ => hz.1 I
  have hcv_le : ∀ y : Context G → ℝ, Feasible G a y → coverValue G a ≤ ∑ I, y I := by
    intro y hy
    exact csInf_le hbelow ⟨y, hy, rfl⟩
  obtain ⟨y, hy⟩ := hne
  refine le_csInf ⟨∑ I, y I, ⟨y, hy, rfl⟩⟩ ?_
  rintro t ⟨z, hz, rfl⟩
  exact hcv_le z hz.1

/-- Any feasible cover supported on `F` has total mass at least the restricted cover cost. -/
theorem restricted_cover_value_le_total [Nonempty V] (G : SimpleGraph V) (F : Finset (Context G))
    (a : V → ℝ) (y : Context G → ℝ)
    (hy : Feasible G a y ∧ SupportedOn G F y) :
    restrictedCoverValue G F a ≤ ∑ I, y I := by
  have hbelow : BddBelow ((fun x : Context G → ℝ => ∑ I, x I) ''
      {x | Feasible G a x ∧ SupportedOn G F x}) := by
    refine ⟨0, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact Finset.sum_nonneg fun I _ => hz.1.1 I
  exact csInf_le hbelow ⟨y, hy, rfl⟩
omit [DecidableEq V] in
/-- If a law's vertex coverage dominates `T · |c i|^(2/3) / C` with `T > 0`, its inverse-
inclusion amplitude sum is at most `C^(3/2) / √T`. -/
theorem amplitude_sum_le_of_coverage_scale [Nonempty V] (c : V → ℝ) (hc : ∀ i, c i ≠ 0)
    (cov : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hcov : ∀ i, powerAllocation c T i ≤ cov i) :
    (∑ i, |c i| / Real.sqrt (cov i)) ≤ coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T := by
  obtain ⟨_, hpos, _, hassigned⟩ := magnitude_allocation_attains c hc T hT
  have hterm : ∀ i, |c i| / Real.sqrt (cov i)
      ≤ |c i| / Real.sqrt (powerAllocation c T i) := by
    intro i
    exact div_le_div_of_nonneg_left (abs_nonneg _)
      (Real.sqrt_pos.mpr (hpos i)) (Real.sqrt_le_sqrt (hcov i))
  calc (∑ i, |c i| / Real.sqrt (cov i))
      ≤ ∑ i, |c i| / Real.sqrt (powerAllocation c T i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T := hassigned

/-- For a law supported on the subfamily `F` whose restricted coverage meets the scale-`T`
coefficient-power demands, the `N`-shot inverse-inclusion energy estimator is unbiased and
has variance at most `C^3/(N·T)` [XuEtAl2026]. -/
theorem restricted_family_energy_bound [Nonempty V] [Nonempty d]
    (G : SimpleGraph V) {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=Context G) (Ω:=Ω) S) (hM : ∀ I, M.context I = I.val)
    (F : Finset (Context G)) (q : Context G → ℝ)
    (hq : q ∈ Qatlib.Foundations.ProbabilityCore.SimplexWeights.weights ℝ (Context G))
    (hsupp : SupportedOn G F q) (c : V → ℝ) (hc : ∀ i, c i ≠ 0)
    (T : ℝ) (hT : 0 < T)
    (hcov : ∀ i, powerAllocation c T i ≤ restrictedCoverage G F q i)
    (N : ℕ) (hN : 0 < N) :
    ∀ ρ : MState d,
      mean (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)
        = ∑ i, c i * ρ.exp_val (S i) ∧
      variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)
        ≤ coeffPowerSum c ^ 3 / ((N : ℝ) * T) := by
  obtain ⟨hC, hpos, _, _⟩ := magnitude_allocation_attains c hc T hT
  have hcovered : ∀ i, powerAllocation c T i ≤ inclusion M q i := by
    intro i
    rw [inclusion_eq_coverage G M hM, coverage_eq_restrictedCoverage G F q hsupp]
    exact hcov i
  have hin : ∀ i, 0 < inclusion M q i := fun i => (hpos i).trans_le (hcovered i)
  have hamp : (∑ i, |c i| / Real.sqrt (inclusion M q i))
      ≤ coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T :=
    amplitude_sum_le_of_coverage_scale c hc _ T hT hcovered
  intro ρ
  have hnorm : ∑ ω, bornLaw M q ρ ω = 1 := bornLaw_normalized M q hq.2 ρ
  have hmean := born_score_unbiased M q ρ c (fun i => (hin i).ne')
  refine ⟨?_, ?_⟩
  · rw [shotAverage_mean (bornLaw M q ρ) _ hnorm N hN]
    exact hmean
  · have hv := born_average_variance_le_largest M q hq.2 ρ (energyScore G M q c) N hN
    have hop := largest_score_operator_le M q hq.1 c hin
    have hU : 0 ≤ ∑ i, |c i| / Real.sqrt (inclusion M q i) :=
      Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have hsq : (∑ i, |c i| / Real.sqrt (inclusion M q i)) ^ 2
        ≤ coeffPowerSum c ^ 3 / T := by
      have h2 := pow_le_pow_left₀ hU hamp 2
      have hpow : (coeffPowerSum c ^ ((3:ℝ)/2) / Real.sqrt T) ^ 2
          = coeffPowerSum c ^ 3 / T := by
        rw [div_pow, rpow_three_halves _ hC.le, mul_pow, Real.sq_sqrt hC.le,
          Real.sq_sqrt hT.le, pow_succ (coeffPowerSum c) 2]
      rw [hpow] at h2
      exact h2
    apply hv.trans
    rw [mul_comm (N : ℝ) T, ← div_div]
    exact div_le_div_of_nonneg_right (hop.trans hsq) (Nat.cast_nonneg N)

end Qatlib.Papers.ShadowTomog26.EnergyEstimate
