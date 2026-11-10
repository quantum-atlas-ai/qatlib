/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy

namespace Qatlib.Papers.MonteCarloInt20.MainResults.Allocation

theorem budget_bound {n s d p : ℕ} (M : ℕ) (hM : 0 < M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (code : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (gp : ℝ → ℝ) (K : NNReal) (L : ℝ)
    (hL : ∀ j, |gp (D*termMean a c seed code j)| ≤ L) :
    finiteBudget M a c seed code D gp K ≤ (L*|D|+(K:ℝ)*D^2)/(M:ℝ) := by
  unfold finiteBudget
  calc
    _ ≤ (1/(2:ℝ)^s)*∑ _j : Reg s, (L*|D|+(K:ℝ)*D^2)/(M:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right (hL j) (abs_nonneg D)) le_rfl) (by positivity))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      push_cast
      have hs : (2:ℝ)^s ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp

theorem finiteMean_bounds {n s d p : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (code : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (D : ℝ) (g : ℝ → ℝ)
    (hrange : ∀ k : Fin M, g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    finiteMean M hM a c seed code D g ∈ Set.Icc (0:ℝ) 1 := by
  have hb (j : Reg s) : (∑ k : Fin M,
      (aeLaw M (innerBody a c seed code j) (bodySeed n s d p seed) (bodyGood n s d p)
        (innerBody_unitary a c seed code j) hM).prob k*g (D*aeEstimate M k)) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg (fun k _ => mul_nonneg
        ((aeLaw M (innerBody a c seed code j) (bodySeed n s d p seed) (bodyGood n s d p)
          (innerBody_unitary a c seed code j) hM).nonneg k) (hrange k).1)
    · calc
        _ ≤ ∑ k : Fin M, (aeLaw M (innerBody a c seed code j) (bodySeed n s d p seed) (bodyGood n s d p)
            (innerBody_unitary a c seed code j) hM).prob k := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_of_le_one_right ((aeLaw M (innerBody a c seed code j) (bodySeed n s d p seed)
            (bodyGood n s d p) (innerBody_unitary a c seed code j) hM).nonneg k) (hrange k).2
        _ = 1 := (aeLaw M (innerBody a c seed code j) (bodySeed n s d p seed) (bodyGood n s d p)
          (innerBody_unitary a c seed code j) hM).sum_one
  unfold finiteMean nestedMean
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => (hb j).1))
  · calc
      _ ≤ (1/(2:ℝ)^s)*∑ _j : Reg s, (1:ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hb j).2)) (by positivity)
      _ = 1 := by simp [Reg]

theorem outerWindow_bound (N : ℕ) (hN : 1 ≤ N) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    outerWindow N μ ≤ (Real.pi+Real.pi^2)/(N:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have hp := Real.sqrt_nonneg (μ*(1-μ))
  have hs := Real.sq_sqrt (mul_nonneg hμ.1 (sub_nonneg.mpr hμ.2))
  have hx : Real.sqrt (μ*(1-μ)) ≤ 1/2 := by nlinarith [sq_nonneg (μ-1/2)]
  unfold outerWindow
  have hh : 2*Real.pi*Real.sqrt (μ*(1-μ)) ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hsq : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  calc
    _ ≤ Real.pi/(N:ℝ)+Real.pi^2/(N:ℝ)^2 :=
      add_le_add (div_le_div_of_nonneg_right hh (le_of_lt hn0)) le_rfl
    _ ≤ Real.pi/(N:ℝ)+Real.pi^2/(N:ℝ) := by
      gcongr
    _ = _ := by ring

theorem allocated_accuracy {n s d p : ℕ} (hd : 0 < d)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) (hEven : 2 ∣ M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (code : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x, HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M, g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1)
    (L ε : ℝ) (hε : 0 < ε) (hL : ∀ j, |gp (D*termMean a c seed code j)| ≤ L)
    (hInner : 2*(L*|D|+(K:ℝ)*D^2)/ε ≤ M)
    (hOuter : 2*(Real.pi+Real.pi^2)/ε ≤ N) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-finiteTarget a c seed code D g| ≤ ε),
      (finiteLaw M N hM hN a c seed code D g hrange).prob z := by
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi : (L*|D|+(K:ℝ)*D^2)/(M:ℝ) ≤ ε/2 := by
    have h := (div_le_iff₀ hε).mp hInner
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have ho : (Real.pi+Real.pi^2)/(N:ℝ) ≤ ε/2 := by
    have h := (div_le_iff₀ hε).mp hOuter
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hb := budget_bound M (by omega) a c seed code D gp K L hL
  have hw := outerWindow_bound N (by omega) _ (finiteMean_bounds M hM a c seed code D g hrange)
  apply (finite_nested_total_error hd M N hM hN hEven a c seed code D g gp K hg hgp hrange).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hz' := (Finset.mem_filter.mp hz).2
      linarith⟩
  · intro z _ _
    exact (finiteLaw M N hM hN a c seed code D g hrange).nonneg z

theorem allocated_relative_accuracy {n s d p : ℕ} (hd : 0 < d)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) (hEven : 2 ∣ M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (code : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x, HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M, g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1)
    (L εrel : ℝ) (hε : 0 < εrel) (hTarget : 0 < finiteTarget a c seed code D g)
    (hL : ∀ j, |gp (D*termMean a c seed code j)| ≤ L)
    (hInner : 2*(L*|D|+(K:ℝ)*D^2)/(εrel*finiteTarget a c seed code D g) ≤ M)
    (hOuter : 2*(Real.pi+Real.pi^2)/(εrel*finiteTarget a c seed code D g) ≤ N) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-finiteTarget a c seed code D g|/finiteTarget a c seed code D g ≤ εrel),
      (finiteLaw M N hM hN a c seed code D g hrange).prob z := by
  simpa only [div_le_iff₀ hTarget] using!
    allocated_accuracy hd M N hM hN hEven a c seed code D g gp K hg hgp hrange
      L (εrel*finiteTarget a c seed code D g) (mul_pos hε hTarget) hL hInner hOuter

end Qatlib.Papers.MonteCarloInt20.MainResults.Allocation
