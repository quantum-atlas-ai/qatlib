/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.PauliReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ShadowModels.ShadowChannel
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.RationalSelector
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.PauliReadout

def chooseQ (r s : ℚ) : Bool := decide (r ≤ s)

theorem chooseQ_error (x y : ℝ) (r s : ℚ) :
    (if chooseQ r s then x else y) ≤ min x y+|(r:ℝ)-x|+|(s:ℝ)-y| := by
  by_cases h : r ≤ s
  · have hrs : (r:ℝ) ≤ (s:ℝ) := by exact_mod_cast h
    simp only [chooseQ,h,decide_true,ite_true]
    rcases le_total x y with hxy|hyx
    · rw [min_eq_left hxy]
      linarith [abs_nonneg ((r:ℝ)-x),abs_nonneg ((s:ℝ)-y)]
    · rw [min_eq_right hyx]
      linarith [neg_le_abs ((r:ℝ)-x),le_abs_self ((s:ℝ)-y)]
  · have hrs : (s:ℝ) ≤ (r:ℝ) := by exact_mod_cast (le_of_not_ge h)
    simp only [chooseQ,h,decide_false,Bool.false_eq_true,ite_false]
    rcases le_total x y with hxy|hyx
    · rw [min_eq_left hxy]
      linarith [le_abs_self ((r:ℝ)-x),neg_le_abs ((s:ℝ)-y)]
    · rw [min_eq_right hyx]
      linarith [abs_nonneg ((r:ℝ)-x),abs_nonneg ((s:ℝ)-y)]

def meanScoreQ {n N : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℚ) (xs : Fin N → Fin n → Fin 3×Bool) : ℚ :=
  (∑ k,energyScoreQ ends w (xs k))/(N:ℚ)

theorem meanScoreQ_real {n N : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℚ) (xs : Fin N → Fin n → Fin 3×Bool) :
    (meanScoreQ ends w xs:ℝ)=FinDist.avg (fun o => (energyScoreQ ends w o:ℝ)) xs := by
  simp [meanScoreQ,FinDist.avg]

noncomputable def shotsLaw (n N : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : FinDist (Fin N → Fin n → Fin 3×Bool) :=
  independentSampleLaw (fun _ : Fin N => readoutLaw n ρ hρ htr)

theorem shots_actual_born (n N : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (xs : Fin N → Fin n → Fin 3×Bool) :
    (Matrix.trace (tensorPauliFreshProduct (fun i => tensorPauliKraus n (xs i))*
      tensorPauliFreshProduct (fun _ : Fin N => finDensity n ρ)*
      (tensorPauliFreshProduct (fun i => tensorPauliKraus n (xs i)))ᴴ)).re=
      (shotsLaw n N ρ hρ htr).prob xs :=
  tensorPauliFreshProduct_born (finDensity n ρ) (finDensity_physical n ρ hρ htr) xs

theorem variance_nonneg {X : Type} [Fintype X] [DecidableEq X] (q : FinDist X) (f : X → ℝ) :
    0 ≤ q.variance f := Finset.sum_nonneg (fun x _ => mul_nonneg (q.nonneg x) (sq_nonneg _))

theorem mean_abs_le_sqrt {X : Type} [Fintype X] [DecidableEq X] (q : FinDist X) (f : X → ℝ) :
    q.expect (fun x => |f x|) ≤ Real.sqrt (q.expect (fun x => (f x)^2)) := by
  have hv := variance_nonneg q (fun x => |f x|)
  rw [FinDist.variance_eq_expect_sq_sub] at hv
  simp only [sq_abs] at hv
  have hm : 0 ≤ q.expect (fun x => (f x)^2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (q.nonneg x) (sq_nonneg _))
  have ha : 0 ≤ q.expect (fun x => |f x|) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (q.nonneg x) (abs_nonneg _))
  nlinarith [Real.sq_sqrt hm,Real.sqrt_nonneg (q.expect (fun x => (f x)^2))]

theorem readout_mean_error {n N : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℚ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hN : 0<N) :
    (shotsLaw n N ρ hρ htr).expect (fun xs => |(meanScoreQ ends w xs:ℝ)-
      energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ|) ≤
      Real.sqrt ((readoutLaw n ρ hρ htr).variance (fun o => (energyScoreQ ends w o:ℝ))/(N:ℝ)) := by
  let q := readoutLaw n ρ hρ htr
  let f := fun o => (energyScoreQ ends w o:ℝ)
  have hmean := energyScoreQ_unbiased ends w ρ hρ htr
  have hs := FinDist.expect_avg_sub_sq q f hN
  have hm : q.expect f=energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ := hmean
  rw [hm] at hs
  have h := mean_abs_le_sqrt (shotsLaw n N ρ hρ htr)
    (fun xs => (meanScoreQ ends w xs:ℝ)-energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ)
  have he : (shotsLaw n N ρ hρ htr).expect (fun xs =>
      ((meanScoreQ ends w xs:ℝ)-energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ)^2)=q.variance f/(N:ℝ) := by
    simpa only [FinDist.expect,shotsLaw,independentSampleLaw,FinDist.probOf,meanScoreQ_real,q,f] using hs
  rw [he] at h
  exact h
end Qatlib.Papers.RydbergMaxCut26.MainResults.RationalSelector
