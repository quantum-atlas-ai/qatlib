/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail

def tailWeight {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) (x : X) : ℝ :=
  if q<L x then p.prob x else 0

def tailMass {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) : ℝ :=
    ∑ x,tailWeight p L q x

def tailLoss {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) : ℝ :=
    ∑ x,tailWeight p L q x*L x

theorem tailWeight_bounds {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) (x : X) :
    0≤tailWeight p L q x ∧ tailWeight p L q x≤p.prob x := by
  by_cases h : q<L x <;> simp [tailWeight,h,p.nonneg x]

theorem tailMass_bounds {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) :
    0≤tailMass p L q ∧ tailMass p L q≤1 := by
  refine ⟨Finset.sum_nonneg (fun x _ => (tailWeight_bounds p L q x).1),?_⟩
  calc
    _ ≤ ∑ x,p.prob x := Finset.sum_le_sum (fun x _ => (tailWeight_bounds p L q x).2)
    _ = 1 := p.sum_one

def tailLaw {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ)
    (h : 0<tailMass p L q) : FinDist X where
  prob x := tailWeight p L q x/tailMass p L q
  nonneg x := div_nonneg (tailWeight_bounds p L q x).1 h.le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self h.ne'

theorem tailLaw_outside {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ)
    (h : 0<tailMass p L q) (x : X) (hx : ¬q<L x) : (tailLaw p L q h).prob x=0 := by
  simp only [tailLaw,tailWeight,hx,↓reduceIte,zero_div]

theorem tailLaw_mean {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (L : X → ℝ) (q : ℝ)
    (h : 0<tailMass p L q) : (tailLaw p L q h).expect L=tailLoss p L q/tailMass p L q := by
  simp only [FinDist.expect,tailLaw,div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rfl

theorem tailLaw_mass_one {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ)
    (h : 0<tailMass p L q) : tailMass (tailLaw p L q h) L q=1 := by
  have hw (x : X) : tailWeight (tailLaw p L q h) L q x=(tailLaw p L q h).prob x := by
    by_cases hx : q<L x
    · simp [tailWeight,hx]
    · simp [tailWeight,hx,tailLaw_outside p L q h x hx]
  simpa only [tailMass,hw] using (tailLaw p L q h).sum_one

theorem tailLoss_bounds {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q D : ℝ)
    (hL : ∀ x,L x ∈ Set.Icc (0:ℝ) D) : 0≤tailLoss p L q ∧ tailLoss p L q≤D*tailMass p L q := by
  refine ⟨Finset.sum_nonneg (fun x _ => mul_nonneg (tailWeight_bounds p L q x).1 (hL x).1),?_⟩
  calc
    _ ≤ ∑ x,tailWeight p L q x*D := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hL x).2 (tailWeight_bounds p L q x).1)
    _ = D*tailMass p L q := by rw [← Finset.sum_mul]; unfold tailMass; ring

theorem tailLaw_mean_bounds {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (L : X → ℝ) (q D : ℝ)
    (hL : ∀ x,L x ∈ Set.Icc (0:ℝ) D) (h : 0<tailMass p L q) :
    (tailLaw p L q h).expect L ∈ Set.Icc (0:ℝ) D := by
  rw [tailLaw_mean]
  exact ⟨div_nonneg (tailLoss_bounds p L q D hL).1 h.le,(div_le_iff₀ h).2 (by nlinarith [(tailLoss_bounds p L q D hL).2])⟩

def normalizedPayoff (C q l : ℝ) : ℝ := C*l*(if q<l then 1 else 0)

theorem normalizedPayoff_bounds (C q l D : ℝ) (hC : 0≤C) (hl : l ∈ Set.Icc (0:ℝ) D) (hCD : C*D≤1) :
    normalizedPayoff C q l ∈ Set.Icc (0:ℝ) 1 := by
  by_cases h : q<l
  · simp only [normalizedPayoff,h,↓reduceIte,mul_one]
    exact ⟨mul_nonneg hC hl.1,(mul_le_mul_of_nonneg_left hl.2 hC).trans hCD⟩
  · simp [normalizedPayoff,h]

theorem normalizedPayoff_expect {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (L : X → ℝ) (C q : ℝ) :
    p.expect (fun x => normalizedPayoff C q (L x))=C*tailLoss p L q := by
  unfold FinDist.expect tailLoss
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : q<L x
  · simp only [normalizedPayoff,tailWeight,h,↓reduceIte,mul_one]
    ring
  · simp [normalizedPayoff,tailWeight,h]

theorem conditional_mean_from_payoff {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (L : X → ℝ) (C q : ℝ)
    (hC : 0<C) (hT : 0<tailMass p L q) :
    (tailLaw p L q hT).expect L=p.expect (fun x => normalizedPayoff C q (L x))/(C*tailMass p L q) := by
  rw [tailLaw_mean,normalizedPayoff_expect]
  field_simp

end Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail
