/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualMeanPayoff
import Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.QaeLaw.MeanPayoff
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy

namespace Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested

def bodyGood (n s d p : ℕ) : Finset (BodyReg n s d p) := Finset.univ.filter (fun v => v.2=true)

def finiteTarget {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^s)*∑ j : Reg s,g (D*termMean a c seed termCode j)

def finiteBudget {n s d p : ℕ} (M : ℕ) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (gp : ℝ → ℝ) (K : NNReal) : ℝ :=
  (1/(2:ℝ)^s)*∑ j : Reg s,(|gp (D*termMean a c seed termCode j)| *|D|+(K:ℝ)*D^2)/(M:ℝ)

def finiteMean {n s d p : ℕ} (M : ℕ) (hM : 2 ≤ M) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  nestedMean (I:=BodyReg n s d p) s M hM (innerBody a c seed termCode) (bodySeed n s d p seed)
    (fun _ => bodyGood n s d p) (innerBody_unitary a c seed termCode) D g

def finiteLaw {n s d p : ℕ} (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (g : ℝ → ℝ)
    (hrange : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) : FinDist (Fin N) :=
  nestedLaw (I:=BodyReg n s d p) s M N hM hN (innerBody a c seed termCode) (bodySeed n s d p seed)
    (fun _ => bodyGood n s d p) (innerBody_unitary a c seed termCode) D g hrange

theorem finite_inner_payoff_error {n s d p : ℕ} (hd : 0 < d)
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s)
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    |(∑ k,(aeLaw M (innerBody a c seed termCode j) (bodySeed n s d p seed) (bodyGood n s d p)
      (innerBody_unitary a c seed termCode j) hM).prob k*g (D*aeEstimate M k))-
      g (D*termMean a c seed termCode j)| ≤
      (|gp (D*termMean a c seed termCode j)| *|D|+(K:ℝ)*D^2)/(M:ℝ) := by
  have h := actual_mean_smooth_error (I:=BodyReg n s d p) M hM hEven (innerBody a c seed termCode j)
    (bodySeed n s d p seed) (bodyGood n s d p) (innerBody_unitary a c seed termCode j) D g gp K hg hgp
  (try dsimp only at h)
  rw [preparedAAState,bodyGood,innerBody_flag_born hd] at h
  exact h

theorem finite_inner_bias {n s d p : ℕ} (hd : 0 < d)
    (M : ℕ) (hM : 2 ≤ M) (hEven : 2 ∣ M) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    |finiteMean M hM a c seed termCode D g-finiteTarget a c seed termCode D g| ≤
      finiteBudget M a c seed termCode D gp K := by
  unfold finiteMean nestedMean finiteTarget finiteBudget
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (show 0≤1/(2:ℝ)^s by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact finite_inner_payoff_error hd M hM hEven a c seed termCode j D g gp K hg hgp

theorem finite_nested_total_error {n s d p : ℕ} (hd : 0 < d)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) (hEven : 2 ∣ M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-finiteTarget a c seed termCode D g| ≤
        outerWindow N (finiteMean M hM a c seed termCode D g)+finiteBudget M a c seed termCode D gp K),
      (finiteLaw M N hM hN a c seed termCode D g hrange).prob z := by
  have hinner := finite_inner_bias hd M hM hEven a c seed termCode D g gp K hg hgp
  have houter := nested_bhmt (I:=BodyReg n s d p) s M N hM hN (innerBody a c seed termCode)
    (bodySeed n s d p seed) (fun _ => bodyGood n s d p) (innerBody_unitary a c seed termCode) D g hrange
  change 8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-finiteMean M hM a c seed termCode D g| ≤ outerWindow N (finiteMean M hM a c seed termCode D g)),
      (finiteLaw M N hM hN a c seed termCode D g hrange).prob z at houter
  apply houter.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hz' := (Finset.mem_filter.mp hz).2
    have ht := abs_sub_le (aeEstimate N z) (finiteMean M hM a c seed termCode D g)
      (finiteTarget a c seed termCode D g)
    linarith
  · intro z _ _
    exact (finiteLaw M N hM hN a c seed termCode D g hrange).nonneg z

theorem source_sum_target {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    finiteTarget a c seed termCode ((2:ℝ)^d) g=
      (1/(2:ℝ)^s)*∑ j : Reg s,g (∑ i : Reg d,((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p) := by
  unfold finiteTarget
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold termMean
  have h : (2:ℝ)^d≠0 := pow_ne_zero _ (by norm_num)
  field_simp

end Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
