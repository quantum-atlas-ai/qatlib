/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.AlmostAffineGradientStat
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianOpti

/-!
# Rescaled almost-affine gradient estimation

This module proves `sourceAlmostAffineGradient`, selecting a dyadic grid from the requested
error, range, and scale. The proof transfers robust affine readout to the rescaled coordinates
and median estimator used in the gradient setting of [GilyenArunachalamWiebe2019].

## Main statements

* `sourceAlmostAffineGradient`: simultaneous gradient accuracy with the prescribed failure
  probability and explicit query, gate, and comparison counts.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

namespace SourceAlmostAffineGradientAux

/-- For positive `t`, rounding `log₂ t` upward gives a power of two at least `t`. -/
private theorem pow2_ceil_lower (t : ℝ) (ht : 0 < t) :
    t ≤ (2:ℝ)^(⌈Real.logb 2 t⌉ : ℤ) := by
  have h1 : (Real.logb 2 t : ℝ) ≤ ((⌈Real.logb 2 t⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.le_ceil _
  calc t = (2:ℝ)^((Real.logb 2 t : ℝ)) := (Real.rpow_logb (by norm_num) (by norm_num) ht).symm
    _ ≤ (2:ℝ)^(((⌈Real.logb 2 t⌉ : ℤ):ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (2:ℝ)^(⌈Real.logb 2 t⌉ : ℤ) := Real.rpow_intCast (2:ℝ) _

/-- For positive `t`, the power of two obtained by rounding `log₂ t` upward is strictly less
than `2*t`. -/
private theorem pow2_ceil_upper (t : ℝ) (ht : 0 < t) :
    (2:ℝ)^(⌈Real.logb 2 t⌉ : ℤ) < 2*t := by
  have h1 : (((⌈Real.logb 2 t⌉ : ℤ):ℝ)) < (Real.logb 2 t : ℝ) + 1 := by
    exact_mod_cast Int.ceil_lt_add_one _
  have h3 : (2:ℝ)^(((⌈Real.logb 2 t⌉ : ℤ):ℝ)) < (2:ℝ)^((Real.logb 2 t : ℝ) + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_logb (by norm_num) (by norm_num) ht,
    Real.rpow_intCast (2:ℝ) _, Real.rpow_one] at h3
  linarith

/-- If positive `t` and `u` satisfy `8 < t*u`, the sum of their ceiling binary logarithms is at
least four. -/
private theorem ceil_add_ge_four (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (h8 : 8 < t*u) :
    (4:ℤ) ≤ ⌈Real.logb 2 t⌉ + ⌈Real.logb 2 u⌉ := by
  by_contra hcon
  have h3 : ⌈Real.logb 2 t⌉ + ⌈Real.logb 2 u⌉ ≤ 3 := by omega
  have pA : 0 < (2:ℝ)^(⌈Real.logb 2 t⌉ : ℤ) := zpow_pos (by norm_num) _
  have pB : 0 < (2:ℝ)^(⌈Real.logb 2 u⌉ : ℤ) := zpow_pos (by norm_num) _
  have htule : t*u ≤ (2:ℝ)^(⌈Real.logb 2 t⌉ : ℤ)*(2:ℝ)^(⌈Real.logb 2 u⌉ : ℤ) := by
    nlinarith [pow2_ceil_lower t ht, pow2_ceil_lower u hu]
  have hmono : (2:ℝ)^(⌈Real.logb 2 t⌉ + ⌈Real.logb 2 u⌉) ≤ (2:ℝ)^(3:ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) h3
  have h8' : (2:ℝ)^(3:ℤ) = 8 := by norm_num
  rw [zpow_add₀ (by norm_num : ((2:ℝ) ≠ 0))] at hmono
  linarith

end SourceAlmostAffineGradientAux

open Qatlib.Concepts.GradientOracle.GradientAlgo.SourceAlmostAffineGradientAux

/-- Proves simultaneous accuracy of the rescaled coordinate medians with the requested failure
probability, together with grid-size and query, gate, and comparison bounds, under the
stated almost-affine hypotheses. See [GilyenArunachalamWiebe2019]. -/
theorem sourceAlmostAffineGradient : SourceAlmostAffineGradient := by
  intro d c r ε L δ g hr hε hεL hδ hδ1 hg nε nL n _NL f S hbad hgood
  have hL : 0 < L := lt_trans hε hεL
  have h4p : 0 < 4/(r*ε) := div_pos (by norm_num) (mul_pos hr hε)
  have h3p : 0 < 3*r*L := mul_pos (mul_pos (by norm_num) hr) hL
  have hloε := pow2_ceil_lower (4/(r*ε)) h4p
  have hloL := pow2_ceil_lower (3*r*L) h3p
  have hEpos : 0 < (2:ℝ)^nε := lt_of_lt_of_le h4p hloε
  have hLpos : 0 < (2:ℝ)^nL := lt_of_lt_of_le h3p hloL
  have hrε : r*ε ≠ 0 := (mul_pos hr hε).ne'
  have h8 : 8 < (4/(r*ε))*(3*r*L) := by
    have hEq : (4/(r*ε))*(3*r*L) = 12*L/ε := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hrε hε.ne']
      ring
    rw [hEq, lt_div_iff₀ hε]
    linarith
  have h4le : (4:ℤ) ≤ nε+nL := ceil_add_ge_four (4/(r*ε)) (3*r*L) h4p h3p h8
  have hnng : 0 ≤ nε+nL := by omega
  have hcast : ((nε+nL).toNat : ℤ) = nε+nL := Int.toNat_of_nonneg hnng
  have h2n : (2:ℝ)^n = (2:ℝ)^nε*(2:ℝ)^nL := by
    show (2:ℝ)^((nε+nL).toNat) = _
    rw [← zpow_natCast, hcast, zpow_add₀ (by norm_num : ((2:ℝ) ≠ 0))]
  have hhi : (2:ℝ)^nε < 8/(r*ε) := by
    have h := pow2_ceil_upper (4/(r*ε)) h4p
    rwa [show (2:ℝ)*(4/(r*ε)) = 8/(r*ε) from by rw [← mul_div_assoc]; norm_num] at h
  have hg' : ∀ j : Fin d, |r*(g j)/(2:ℝ)^nL| ≤ 1/3 := by
    intro j
    rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos hLpos, div_le_iff₀ hLpos]
    have hA : r*|g j| ≤ r*L := mul_le_mul_of_nonneg_left (hg j) (le_of_lt hr)
    linarith [hA, hloL]
  have hterm : ∀ (x : GradientGrid d (2^n)) (j : Fin d),
      g j*(r*sourceGradientGridPoint n (x j))
        = (r/(2*(2:ℝ)^n)-r/2)*(g j) + (r/(2:ℝ)^n)*(g j*((x j).val)) := by
    intro x j
    simp only [sourceGradientGridPoint]
    field_simp; ring
  have hsumfac : ∀ x : GradientGrid d (2^n),
      ∑ j, (r*(g j)/(2:ℝ)^nL)*((x j).val)
        = (r/(2:ℝ)^nL)*∑ j, g j*((x j).val) := by
    intro x
    have h₁ : ∀ j : Fin d, (r*(g j)/(2:ℝ)^nL)*((x j).val)
        = (r/(2:ℝ)^nL)*(g j*((x j).val)) := fun j => by field_simp
    rw [Finset.sum_congr rfl (fun j _ => h₁ j), ← Finset.mul_sum]
  have hexpsum : ∀ x : GradientGrid d (2^n),
      ∑ j, g j*(r*sourceGradientGridPoint n (x j))
        = (r/(2*(2:ℝ)^n)-r/2)*(∑ j, g j) + (r/(2:ℝ)^n)*∑ j, g j*((x j).val) := by
    intro x
    rw [Finset.sum_congr rfl (fun j _ => hterm x j), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have hkey : ∀ x : GradientGrid d (2^n),
      (2:ℝ)^nε*(c + ∑ j, g j*(r*sourceGradientGridPoint n (x j)))
        = (2:ℝ)^nε*(c + (r/(2*(2:ℝ)^n)-r/2)*(∑ j, g j))
          + ∑ j, (r*(g j)/(2:ℝ)^nL)*((x j).val) := by
    intro x
    rw [hexpsum x, hsumfac x, h2n]
    field_simp; ring
  have hgood' : ∀ x ∈ S, |(2:ℝ)^nε*f x
      - ((2:ℝ)^nε*(c + (r/(2*(2:ℝ)^n)-r/2)*(∑ j, g j))
        + ∑ j, (r*(g j)/(2:ℝ)^nL)*((x j).val))| ≤ 1/(42*Real.pi) := by
    intro x hx
    have hkx := hkey x
    have hxg := hgood x hx
    rw [← hkx]
    have hrew : (2:ℝ)^nε*f x - (2:ℝ)^nε*(c + ∑ j, g j*(r*sourceGradientGridPoint n (x j)))
        = (2:ℝ)^nε*(f x - (c + ∑ j, g j*(r*sourceGradientGridPoint n (x j)))) := by ring
    rw [hrew, abs_mul, abs_of_pos hEpos]
    refine le_trans (mul_le_mul_of_nonneg_left hxg (le_of_lt hEpos)) ?_
    apply le_of_lt
    calc (2:ℝ)^nε*(ε*r/(8*42*Real.pi))
        < (8/(r*ε))*(ε*r/(8*42*Real.pi)) :=
          mul_lt_mul_of_pos_right hhi (div_pos (mul_pos hε hr) (by positivity))
      _ = 1/(42*Real.pi) := by field_simp
  have hmed := almostAffineVectorMedian d n (Nat.pow_pos (by decide))
    (fun x => (2:ℝ)^nε*f x) (fun j => r*(g j)/(2:ℝ)^nL)
    ((2:ℝ)^nε*(c + (r/(2*(2:ℝ)^n)-r/2)*(∑ j, g j))) S hg' hbad hgood'
  have hA := hmed.1 (gradientMedianRepetitions d δ)
  obtain ⟨-, hmasseq, -, -, hdq, hiq, hfg, hcnt⟩ := hA
  have hmassnn : ∀ ω : Fin (2*gradientMedianRepetitions d δ+1) → GradientGrid d (2^n),
      0 ≤ gradientFreshMass d (2^n) (Nat.pow_pos (by decide))
        (fun x => (2:ℝ)^nε*f x) ω := by
    intro ω
    rw [hmasseq ω]
    exact Finset.prod_nonneg fun t _ => bornProb_nonneg _ _
  have hB := hmed.2 δ hδ hδ1
  have hbound : ((2:ℝ)^nL/r)*(4/(2:ℝ)^n) ≤ ε := by
    have hEq : ((2:ℝ)^nL/r)*(4/((2:ℝ)^nε*(2:ℝ)^nL)) = 4/(r*(2:ℝ)^nε) := by
      field_simp
    rw [h2n, hEq, div_le_iff₀ (mul_pos hr hEpos)]
    nlinarith [(div_le_iff₀ (mul_pos hr hε)).1 hloε]
  have hsub : (Finset.univ.filter (fun ω : Fin (2*gradientMedianRepetitions d δ+1)
          → GradientGrid d (2^n) =>
        ∀ j, |((gradientMedianCounted (gradientMedianRepetitions d δ) ω j).1 : ℝ)
          - r*(g j)/(2:ℝ)^nL| ≤ 4/(2:ℝ)^n))
      ⊆ (Finset.univ.filter (fun ω : Fin (2*gradientMedianRepetitions d δ+1)
          → GradientGrid d (2^n) =>
        ∀ j, |((2:ℝ)^nL/r)*((gradientMedianCounted (gradientMedianRepetitions d δ) ω j).1 : ℝ)
          - g j| ≤ ε)) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    intro j
    have hj := hω j
    have hscale : ((2:ℝ)^nL/r)*((gradientMedianCounted (gradientMedianRepetitions d δ) ω j).1 : ℝ)
        - g j = ((2:ℝ)^nL/r)*(((gradientMedianCounted (gradientMedianRepetitions d δ) ω j).1 : ℝ)
          - r*(g j)/(2:ℝ)^nL) := by
      field_simp
    rw [hscale, abs_mul, abs_of_pos (div_pos hLpos hr)]
    exact le_trans (mul_le_mul_of_nonneg_left hj (le_of_lt (div_pos hLpos hr))) hbound
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcast.symm
  · show 4 ≤ (nε+nL).toNat
    omega
  · exact le_trans hB.2 (Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hmassnn ω)
  · exact hdq
  · exact hiq
  · exact hfg
  · intro ω
    exact (hcnt ω).2

end Qatlib.Concepts.GradientOracle.GradientAlgo
