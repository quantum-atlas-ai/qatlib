/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressMatching
import Qatlib.Concepts.SpinorSampling.Matching.MatchedPlanArithmetic

set_option backward.isDefEq.respectTransparency false

/-!
# Partial Address Plan

Partial Address Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained

namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators

/-- Construction for xyz Count Q in the partial address plan model. -/
def xyzCountQ (M : ℕ) (q ε δ : ℚ) : ℕ :=
  max 2 (max (ceilNatQ (32*q/(δ*ε^2))) (1+ceilSqrtQ (100*(M : ℚ)*q/(δ*ε^2))))

/-- Construction for checked XYZCount Q in the partial address plan model. -/
def checkedXYZCountQ (M : ℕ) (q ε δ : ℚ) : Option ℕ :=
  if 0 ≤ q ∧ q ≤ 1/2 ∧ 0<ε ∧ 0<δ ∧ δ<1 then some (xyzCountQ M q ε δ) else none

noncomputable section

/-- Complete original `xyz_count_two` guarantee for `PartialAddressPlan`; all source hypotheses and output obligations are retained. -/
theorem xyz_count_two (M : ℕ) (q ε δ : ℚ) : 2 ≤ xyzCountQ M q ε δ := by
  exact Nat.le_max_left _ _

/-- Complete original `xyz_count_linear_budget` guarantee for `PartialAddressPlan`; all source hypotheses and output obligations are retained. -/
theorem xyz_count_linear_budget (M : ℕ) (q ε δ : ℚ)
    (hq : 0 ≤ q) (hε : 0<ε) (hδ : 0<δ) :
    32*(q : ℝ) ≤ (xyzCountQ M q ε δ : ℝ)*((δ : ℝ)*(ε : ℝ)^2) := by
  let a : ℚ :=32*q/(δ*ε^2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc := (ceil_nat_bounds a ha).1
  have hn : ceilNatQ a ≤ xyzCountQ M q ε δ := by
    dsimp only [xyzCountQ,a]
    omega
  have hnR : (ceilNatQ a : ℝ) ≤ (xyzCountQ M q ε δ : ℝ) := by exact_mod_cast hn
  have hr : 32*(q : ℝ)/((δ : ℝ)*(ε : ℝ)^2) ≤ (xyzCountQ M q ε δ : ℝ) := by
    simpa only [a,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hc.trans hnR
  have heR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hdR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<(δ : ℝ)*(ε : ℝ)^2)).mp hr

/-- Complete original `xyz_count_collision_budget` guarantee for `PartialAddressPlan`; all source hypotheses and output obligations are retained. -/
theorem xyz_count_collision_budget (M : ℕ) (q ε δ : ℚ)
    (hq : 0 ≤ q) (hε : 0<ε) (hδ : 0<δ) :
    100*(M : ℝ)*(q : ℝ) ≤ (((xyzCountQ M q ε δ)*(xyzCountQ M q ε δ-1) : ℕ) : ℝ)*
      ((δ : ℝ)*(ε : ℝ)^2) := by
  let b : ℚ :=100*(M : ℚ)*q/(δ*ε^2)
  let n := xyzCountQ M q ε δ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs := ceil_sqrt_q_square b hb
  have hn2 : 2 ≤ n := xyz_count_two M q ε δ
  have hn : 1+ceilSqrtQ b ≤ n := by dsimp only [n,xyzCountQ,b]; omega
  have hnR : (ceilSqrtQ b : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show ceilSqrtQ b+1 ≤ n by omega)
  have hprod : (ceilSqrtQ b : ℝ)^2 ≤ ((n*(n-1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    have h1 : (ceilSqrtQ b : ℝ) ≤ (n : ℝ)-1 := by linarith
    have h2 : (ceilSqrtQ b : ℝ) ≤ (n : ℝ) := by linarith
    simpa only [pow_two] using mul_le_mul h2 h1 (Nat.cast_nonneg (ceilSqrtQ b)) (Nat.cast_nonneg n)
  have hr : 100*(M : ℝ)*(q : ℝ)/((δ : ℝ)*(ε : ℝ)^2) ≤ ((n*(n-1) : ℕ) : ℝ) := by
    simpa only [b,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using hs.trans hprod
  have heR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hdR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<(δ : ℝ)*(ε : ℝ)^2)).mp hr

namespace UniformMatching
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- Complete original `xyz_count_confidence` guarantee for `PartialAddressPlan`; all source hypotheses and output obligations are retained. -/
theorem xyz_count_confidence (u v : E → Bool → ℂ)
    (hu : ∀ e,RetainedSpin.qubitMass (u e)=1) (hv : ∀ e,RetainedSpin.qubitMass (v e)=1)
    (q ε δ : ℚ) (hq0 : 0 ≤ q) (hε : 0<ε) (hδ : 0<δ)
    (hq : average (fun e => sectorMass (u e) (v e) true) ≤ (q : ℝ)) :
    (law u v hu hv).probEvent (fun ω : Fin (xyzCountQ (2*Fintype.card E) q ε δ) → GlobalRecord E =>
      (ε : ℝ)< |orderedUStatistic globalKernel ω-average (fun e => RetainedSpin.bellProbability (u e) (v e))|) ≤
      (δ : ℝ) := by
  let n := xyzCountQ (2*Fintype.card E) q ε δ
  have hn2 : 2 ≤ n := xyz_count_two _ q ε δ
  have hlin := xyz_count_linear_budget (2*Fintype.card E) q ε δ hq0 hε hδ
  have hcol := xyz_count_collision_budget (2*Fintype.card E) q ε δ hq0 hε hδ
  have hqR : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq0
  have heR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hdR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hden : (0 : ℝ)<((n*(n-1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0<n) (by omega : 0<n-1)
  have hKq : 0 ≤ (Fintype.card E : ℝ)*(q : ℝ) := mul_nonneg (Nat.cast_nonneg _) hqR
  have hfirst : 6*(q : ℝ)/(n : ℝ) ≤ (δ : ℝ)*(ε : ℝ)^2/2 := by
    rw [div_le_iff₀ hnR]
    change 32*(q : ℝ) ≤ (n : ℝ)*((δ : ℝ)*(ε : ℝ)^2) at hlin
    nlinarith
  have hsecond : 30*(Fintype.card E : ℝ)*(q : ℝ)/(n*(n-1) : ℕ) ≤ (δ : ℝ)*(ε : ℝ)^2/2 := by
    rw [div_le_iff₀ hden]
    change 100*((2*Fintype.card E : ℕ) : ℝ)*(q : ℝ) ≤
      ((n*(n-1) : ℕ) : ℝ)*((δ : ℝ)*(ε : ℝ)^2) at hcol
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hcol ⊢
    nlinarith
  have hvar := actual_global_variance_bound u v hu hv hn2 (q : ℝ) hq
  calc
    _ ≤ (∑ ω : Fin n → GlobalRecord E,(law u v hu hv).probOf ω*
        (orderedUStatistic globalKernel ω-average (fun e => RetainedSpin.bellProbability (u e) (v e)))^2)/
        (ε : ℝ)^2 := product_chebyshev _ _ _ _ heR
    _ ≤ (6*(q : ℝ)/(n : ℝ)+30*(Fintype.card E : ℝ)*(q : ℝ)/(n*(n-1) : ℕ))/(ε : ℝ)^2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ ≤ (δ : ℝ) := by
      rw [div_le_iff₀ (sq_pos_of_pos heR)]
      linarith

/-- Complete original `checked_xyz_count_confidence` guarantee for `PartialAddressPlan`; all source hypotheses and output obligations are retained. -/
theorem checked_xyz_count_confidence (u v : E → Bool → ℂ)
    (hu : ∀ e,RetainedSpin.qubitMass (u e)=1) (hv : ∀ e,RetainedSpin.qubitMass (v e)=1)
    (q ε δ : ℚ) (n : ℕ) (hc : checkedXYZCountQ (2*Fintype.card E) q ε δ=some n)
    (hq : average (fun e => sectorMass (u e) (v e) true) ≤ (q : ℝ)) :
    (law u v hu hv).probEvent (fun ω : Fin n → GlobalRecord E =>
      (ε : ℝ)< |orderedUStatistic globalKernel ω-average (fun e => RetainedSpin.bellProbability (u e) (v e))|) ≤
      (δ : ℝ) := by
  unfold checkedXYZCountQ at hc
  split_ifs at hc with h
  · have hn := Option.some.inj hc
    subst n
    exact xyz_count_confidence u v hu hv q ε δ h.1 h.2.2.1 h.2.2.2.1 hq

#print axioms checked_xyz_count_confidence
#print axioms xyz_count_confidence
end UniformMatching
#print axioms xyz_count_two
#print axioms xyz_count_linear_budget
#print axioms xyz_count_collision_budget
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
