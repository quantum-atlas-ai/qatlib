/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovHelpers
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial derivative bounds from integer nodes

This module proves a degree constraint for real polynomials bounded between `b1` and `b2` at the
integer nodes from `0` to `N`. If the absolute derivative is at least a positive `c` somewhere
in `[0, N]`, then `discrete_node_derivative_bound` gives `c * N ≤ p.natDegree ^ 2 * (c + b2 -
b1)`, the squared form of the estimate in [BealsEtAl2001].

The proof uses `discrete_node_nearest` to compare interval extrema with nearby integer nodes.
The intermediate theorem `discrete_node_derivative_of_sharp` isolates the dependence on the
sharp Markov inequality on `[-1, 1]`; the final theorem supplies the established sharp
derivative bound.

## Main statements

* `discrete_node_nearest`: every point of `[0, N]` lies within `1 / 2` of an integer node in
  that interval.
* `discrete_node_derivative_of_sharp`: derive the discrete-node estimate from the sharp Markov
  inequality.
* `discrete_node_derivative_bound`: the unconditional discrete-node degree constraint.

## References

* [Beals et al., 2001, Theorem 4.12][BealsEtAl2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Polynomial
open scoped BigOperators

/-- Every real point in `[0, N]` lies within distance `1 / 2` of a natural-number node `k ≤ N`. -/
theorem discrete_node_nearest (N : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) N) :
    ∃ k : ℕ, k ≤ N ∧ |x-(k:ℝ)| ≤ 1/2 := by
  have hdist := abs_sub_round x
  have h0 : 0 ≤ round x := by
    by_contra hn
    have hn' : round x ≤ -1 := by omega
    have hn'' : (round x : ℝ) ≤ -1 := by exact_mod_cast hn'
    have hab := (abs_le.mp hdist).2
    linarith [hx.1]
  have hN : round x ≤ (N : ℤ) := by
    by_contra hn
    have hn' : (N : ℤ)+1 ≤ round x := by omega
    have hn'' : (N : ℝ)+1 ≤ (round x : ℝ) := by exact_mod_cast hn'
    have hab := (abs_le.mp hdist).1
    linarith [hx.2]
  let k := (round x).toNat
  have hk : (k : ℤ) = round x := Int.toNat_of_nonneg h0
  refine ⟨k,?_,?_⟩
  · exact_mod_cast (hk.trans_le hN)
  · have hkr : (k:ℝ) = (round x:ℝ) := by exact_mod_cast hk
    rwa [hkr]

/-- Assuming the sharp Markov derivative inequality, a polynomial bounded between `b1` and `b2`
at all integer nodes from `0` to `N` satisfies `c * N ≤ p.natDegree ^ 2 * (c + b2 - b1)`
whenever `c > 0` and its absolute derivative is at least `c` at some point of `[0, N]`. -/
theorem discrete_node_derivative_of_sharp
    (hsharp : ∀ (d : ℕ) (p : Polynomial ℝ) (C : ℝ), p.natDegree ≤ d → 0 ≤ C →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d:ℝ)^2*C) :
  ∀ (N : ℕ) (p : Polynomial ℝ) (b1 b2 c x : ℝ), 0 < c →
    (∀ i : ℕ, i ≤ N → b1 ≤ p.eval (i:ℝ) ∧ p.eval (i:ℝ) ≤ b2) →
    x ∈ Set.Icc (0 : ℝ) (N:ℝ) → c ≤ |p.derivative.eval x| →
    c*(N:ℝ) ≤ (p.natDegree:ℝ)^2*(c+b2-b1) := by
  intro N p b1 b2 c x hc hnode hx hcx
  have hΔ : 0 ≤ b2-b1 := by have h := hnode 0 (Nat.zero_le N); linarith [h.1,h.2]
  by_cases hN0 : N = 0
  · subst N
    simp only [Nat.cast_zero,mul_zero]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hI : (Set.Icc (0 : ℝ) (N:ℝ)).Nonempty := ⟨0,⟨le_rfl,hN.le⟩⟩
  obtain ⟨uM,huM,hM⟩ := isCompact_Icc.exists_isMaxOn hI p.continuous.continuousOn
  obtain ⟨um,hum,hm⟩ := isCompact_Icc.exists_isMinOn hI p.continuous.continuousOn
  obtain ⟨uD,huD,hD⟩ := isCompact_Icc.exists_isMaxOn hI p.derivative.continuous.abs.continuousOn
  let M := p.eval uM
  let m := p.eval um
  let D := |p.derivative.eval uD|
  have hD0 : 0 ≤ D := abs_nonneg _
  have hbounds (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) (N:ℝ)) : m ≤ p.eval z ∧ p.eval z ≤ M :=
    ⟨hm hz,hM hz⟩
  have hDbound (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) (N:ℝ)) : |p.derivative.eval z| ≤ D := hD hz
  have hR : 0 ≤ M-m := sub_nonneg.mpr (hbounds uM huM).1
  let q := p.comp (Polynomial.C ((N:ℝ)/2)*Polynomial.X+Polynomial.C ((N:ℝ)/2)) -
    Polynomial.C ((M+m)/2)
  have hqdeg : q.natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (sharp_markov_affine_degree p _ _) (by simp))
  have hqb : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |q.eval z| ≤ (M-m)/2 := by
    intro z hz
    have hz' : (N:ℝ)/2*z+(N:ℝ)/2 ∈ Set.Icc (0 : ℝ) (N:ℝ) := by
      constructor <;> nlinarith [hz.1,hz.2]
    have hb := hbounds _ hz'
    simp only [q,Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    apply abs_le.mpr
    constructor <;> linarith [hb.1,hb.2]
  have harg : 2*uD/(N:ℝ)-1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have := div_nonneg (by nlinarith [huD.1] : 0 ≤ 2*uD) hN.le
      linarith
    · have := (div_le_iff₀ hN).mpr (by nlinarith [huD.2] : 2*uD ≤ 2*(N:ℝ))
      linarith
  have hs := hsharp p.natDegree q ((M-m)/2) hqdeg (by positivity) hqb _ harg
  have hmap : (N:ℝ)/2*(2*uD/(N:ℝ)-1)+(N:ℝ)/2 = uD := by
    field_simp [ne_of_gt hN]
    ring
  simp only [q,Polynomial.derivative_sub,Polynomial.derivative_C,sub_zero] at hs
  rw [sharp_markov_affine_derivative,hmap,abs_mul,abs_of_pos (by positivity : 0 < (N:ℝ)/2)] at hs
  have hND : (N:ℝ)*D ≤ (p.natDegree:ℝ)^2*(M-m) := by linarith
  have hlip (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (N:ℝ))
      (hv : v ∈ Set.Icc (0 : ℝ) (N:ℝ)) : |p.eval u-p.eval v| ≤ D*|u-v| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z _ => (p.hasDerivAt z).hasDerivWithinAt)
        (fun z hz => by simpa only [Real.norm_eq_abs] using hDbound z hz)
        (convex_Icc (0:ℝ) (N:ℝ)) hv hu
  obtain ⟨kM,hkM,hnearM⟩ := discrete_node_nearest N uM huM
  obtain ⟨km,hkm,hnearm⟩ := discrete_node_nearest N um hum
  have hkM' : (kM:ℝ) ∈ Set.Icc (0:ℝ) (N:ℝ) := ⟨Nat.cast_nonneg _,by exact_mod_cast hkM⟩
  have hkm' : (km:ℝ) ∈ Set.Icc (0:ℝ) (N:ℝ) := ⟨Nat.cast_nonneg _,by exact_mod_cast hkm⟩
  have hMclose := (hlip uM kM huM hkM').trans (mul_le_mul_of_nonneg_left hnearM hD0)
  have hmclose := (hlip um km hum hkm').trans (mul_le_mul_of_nonneg_left hnearm hD0)
  have hrange : M-m ≤ b2-b1+D := by
    have hMside := (abs_le.mp hMclose).2
    have hmside := (abs_le.mp hmclose).1
    have htop := (hnode kM hkM).2
    have hbottom := (hnode km hkm).1
    change p.eval uM-p.eval um ≤ _
    linarith
  by_cases hd : (N:ℝ) ≤ (p.natDegree:ℝ)^2
  · have hmul := mul_le_mul_of_nonneg_left hd hc.le
    have hplus := mul_nonneg (sq_nonneg (p.natDegree:ℝ)) hΔ
    nlinarith
  · have hDc : c ≤ D := hcx.trans (hDbound x hx)
    have hmul := mul_le_mul_of_nonneg_right hDc
      (show 0 ≤ (N:ℝ)-(p.natDegree:ℝ)^2 by linarith)
    have hrange' := mul_le_mul_of_nonneg_left hrange (sq_nonneg (p.natDegree:ℝ))
    nlinarith

/-- A real polynomial bounded between `b1` and `b2` at the integer nodes from `0` to `N`, with
absolute derivative at least `c > 0` somewhere in `[0, N]`, satisfies `c * N ≤ p.natDegree ^
2 * (c + b2 - b1)`. This is the squared degree constraint of [Beals et al., Theorem
4.12][BealsEtAl2001]. -/
theorem discrete_node_derivative_bound :
    ∀ (N : ℕ) (p : Polynomial ℝ) (b1 b2 c x : ℝ), 0 < c →
      (∀ i : ℕ, i ≤ N → b1 ≤ p.eval (i : ℝ) ∧ p.eval (i : ℝ) ≤ b2) →
      x ∈ Set.Icc (0 : ℝ) (N : ℝ) → c ≤ |p.derivative.eval x| →
      c * (N : ℝ) ≤ (p.natDegree : ℝ)^2 * (c + b2 - b1) :=
  discrete_node_derivative_of_sharp sharp_markov_derivative

end Qatlib.Concepts.QueryComplexity.DegreeMethod
