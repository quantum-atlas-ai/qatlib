/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff

theorem payoff_at_zero {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (ha : MeasureProb (preparedAAState A j) S=0) (D : ℝ) (g : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))=g 0 := by
  let z : Fin M := ⟨0,by omega⟩
  have hp (k : Fin M) : (aeLaw M A j S hA hM).prob k=if k=z then 1 else 0 := by
    rw [aeLaw_zero_mass M hM A j S hA ha]
    have h := phaseMass_grid M (by omega) z k
    simpa only [z,Nat.cast_zero,zero_div,phaseMass] using! h
  rw [Finset.sum_eq_single z]
  · simp [hp,aeEstimate,z]
  · intro k _ hk
    rw [hp,if_neg hk,zero_mul]
  · simp

theorem payoff_at_one {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (ha : MeasureProb (preparedAAState A j) S=1) (D : ℝ) (g : ℝ → ℝ) :
    (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))=g D := by
  let z : Fin M := ⟨M/2,by omega⟩
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast (show M≠0 by omega)
  have hcast : ((M/2:ℕ):ℝ)*2=(M:ℝ) := by exact_mod_cast Nat.div_mul_cancel hEven
  have hz : (z.val:ℝ)/(M:ℝ)=1/2 := by
    apply (div_eq_iff hm).mpr
    change ((M/2:ℕ):ℝ)=1/2*(M:ℝ)
    linarith
  have he : aeEstimate M z=1 := by
    rw [aeEstimate,mul_div_assoc,hz,mul_one_div,Real.sin_pi_div_two]
    norm_num
  have hp (k : Fin M) : (aeLaw M A j S hA hM).prob k=if k=z then 1 else 0 := by
    rw [aeLaw_one_mass M hM A j S hA ha]
    have h := phaseMass_grid M (by omega) z k
    rw [hz] at h
    exact h
  rw [Finset.sum_eq_single z]
  · simp [hp,he]
  · intro k _ hk
    rw [hp,if_neg hk,zero_mul]
  · simp

theorem actual_mean_smooth_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ unitaryGroup I ℂ) (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    let a := MeasureProb (preparedAAState A j) S;
    |(∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))-g (D*a)| ≤
      (|gp (D*a)| *|D|+(K:ℝ)*D^2)/(M:ℝ) := by
  (try dsimp only)
  let a := MeasureProb (preparedAAState A j) S
  change |(∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))-g (D*a)| ≤
    (|gp (D*a)| *|D|+(K:ℝ)*D^2)/(M:ℝ)
  have hgeo := (prepared_aa_good_bad_geometry A j S hA).2.2.2.2
  have ha0 : 0 ≤ a := hgeo.1
  have ha1 : a ≤ 1 := hgeo.2
  by_cases hz : a=0
  · rw [payoff_at_zero M hM A j S hA hz D g,hz,mul_zero,sub_self,abs_zero]
    positivity
  by_cases ho : a=1
  · rw [payoff_at_one M hM hEven A j S hA ho D g,ho,mul_one,sub_self,abs_zero]
    positivity
  have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hz)
  have hau : a < 1 := lt_of_le_of_ne ha1 ho
  let θ := Real.arcsin (Real.sqrt a)/Real.pi
  have hr : Real.sqrt a < 1 := by simpa only [Real.sqrt_one] using! Real.sqrt_lt_sqrt ha0 hau
  have hθ0 : 0 < θ := div_pos (Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hap)) Real.pi_pos
  have hθ1 : θ < 1/2 := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    have h := Real.arcsin_lt_pi_div_two.mpr hr
    linarith
  have ht : target θ=a := by
    have he : θ*Real.pi=Real.arcsin (Real.sqrt a) := by dsimp only [θ]; field_simp
    rw [target,he,Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hr.le,Real.sq_sqrt ha0]
  have h := actual_smooth_payoff_error M hM A j S hA θ hθ0 hθ1
    (by simpa only [target] using! ht.symm) D g gp K hg hgp
  simpa only [ht] using! h

end Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff
