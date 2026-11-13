/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.EffectiveBesselCutoff
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBoundsGily

/-!
# Effective Bessel truncation for trigonometric polynomials

This module proves factorial bounds for parity-restricted Bessel tails and uses a rational
cutoff certificate to approximate cosine and sine uniformly on `[-1, 1]`. `cutoff_polynomials`
records parity, degree, and approximation error for the resulting compact polynomials.

`cutoff_source_budget` and `source_truncation_rate` relate the cutoff to a real radius
satisfying a scalar cost equation, with explicit degree estimates in the QSP simulation setting
of [GilyenSuLowWiebe2019].

## Main statements

* `bessel_factorial_tail`: bounds the Bessel tail by its first factorial majorant.
* `cutoff_polynomials`: certifies the trigonometric approximation at the effective cutoff.
* `cutoff_source_budget`: compares the cutoff with the source radius and bounds its degree
  budget.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.HamiltonianSim
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- For 0 ≤ a ≤ q/2, twice the sum of the parity-restricted factorial tail starting at q is at
most `(8 / 3) * (a ^ q / q.factorial)`. -/
theorem parity_factorial_tail (q : ℕ) (a : ℝ) (ha : 0 ≤ a) (haq : a ≤ (q:ℝ)/2) :
    2 * (∑' k : ℕ, a^(q+2*k)/((q+2*k).factorial:ℝ)) ≤
      (8/3:ℝ)*(a^q/(q.factorial:ℝ)) := by
  have hg : Summable (fun k : ℕ => (a^q/(q.factorial:ℝ))*(1/4:ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left _
  have ht := fun k => compact_parity_term q k a ha haq
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) ht hg
  have hsum := hs.tsum_le_tsum ht hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)] at hsum
  norm_num at hsum
  linarith

/-- When |t| ≤ q, twice the sum of absolute Bessel coefficients at orders q + 2k is at most `(8
/ 3) * ((|t| / 2) ^ q / q.factorial)`. -/
theorem bessel_factorial_tail (q : ℕ) (t : ℝ) (ht : |t| ≤ q) :
    2*(∑' k : ℕ, |besselInt (q+2*k) t|) ≤
      (8/3:ℝ)*((|t|/2)^q/(q.factorial:ℝ)) := by
  have hinj : Function.Injective (fun k : ℕ => q+2*k) := by
    intro i j h; change q+2*i=q+2*j at h; omega
  have hs := (Real.summable_pow_div_factorial (|t|/2)).comp_injective hinj
  exact (mul_le_mul_of_nonneg_left
    ((besselInt_parity_summable q t).tsum_le_tsum (fun k => besselInt_abs_bound _ t) hs)
    (by norm_num : (0:ℝ) ≤ 2)).trans
      (parity_factorial_tail q (|t|/2) (by positivity) (by linarith))

/-- For 0 ≤ a ≤ q/2, the factorial term a^(q+1)/(q+1)! is at most a^q/q!. -/
theorem next_factorial_le (q : ℕ) (a : ℝ) (ha : 0 ≤ a) (haq : a ≤ (q:ℝ)/2) :
    a^(q+1)/((q+1).factorial:ℝ) ≤ a^q/(q.factorial:ℝ) := by
  have hd : (0:ℝ) < (q:ℝ)+1 := by positivity
  have hf : (0:ℝ) < (q.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos q
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  apply (div_le_div_iff₀ (mul_pos hd hf) hf).mpr
  have h := mul_le_mul_of_nonneg_left (show a ≤ (q:ℝ)+1 by linarith)
    (mul_nonneg (pow_nonneg ha q) hf.le)
  nlinarith only [h]

/-- A rational cutoff guard implies the corresponding real inequalities for the first omitted
order and its factorial tail bound. -/
theorem guard_cast (t ε : ℚ) (R : ℕ) (h : Guard t ε R) :
    |(t:ℝ)| ≤ firstOmitted R ∧
      (8/3:ℝ)*((|(t:ℝ)|/2)^firstOmitted R/((firstOmitted R).factorial:ℝ)) ≤ ε := by
  constructor
  · exact_mod_cast h.1
  · have hc : (tailBound t R : ℝ) ≤ (ε:ℝ) := Rat.cast_le.mpr h.2
    simpa only [tailBound, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_natCast] using! hc

/-- For rational t and positive rational ε, the effective cutoff yields even cosine and odd sine
polynomials of degrees at most 2R and 2R + 1, respectively. Both approximate their
corresponding trigonometric functions within ε uniformly on [-1, 1]. -/
theorem cutoff_polynomials (t ε : ℚ) (hε : 0 < ε) :
    let R := cutoff t ε hε
    (compactCosPoly (t:ℝ) R).comp (-Polynomial.X) = compactCosPoly (t:ℝ) R ∧
    (compactSinPoly (t:ℝ) R).comp (-Polynomial.X) = -compactSinPoly (t:ℝ) R ∧
    (compactCosPoly (t:ℝ) R).natDegree ≤ 2*R ∧
    (compactSinPoly (t:ℝ) R).natDegree ≤ 2*R+1 ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.cos ((t:ℝ)*x)-(compactCosPoly (t:ℝ) R).eval x| ≤ ε) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.sin ((t:ℝ)*x)-(compactSinPoly (t:ℝ) R).eval x| ≤ ε) := by
  (try dsimp only)
  let R := cutoff t ε hε
  let q := firstOmitted R
  have hg := guard_cast t ε R (cutoff_guard t ε hε)
  have he : 2*(∑' k : ℕ, |besselInt (q+2*k) (t:ℝ)|) ≤ (ε:ℝ) :=
    (bessel_factorial_tail q (t:ℝ) hg.1).trans hg.2
  have ho : 2*(∑' k : ℕ, |besselInt ((q+1)+2*k) (t:ℝ)|) ≤ (ε:ℝ) := by
    refine (bessel_factorial_tail (q+1) (t:ℝ) ?_).trans ?_
    · exact hg.1.trans (by exact_mod_cast Nat.le_succ q)
    · exact (mul_le_mul_of_nonneg_left (next_factorial_le q (|(t:ℝ)|/2)
        (by positivity) (by linarith [hg.1])) (by norm_num : (0:ℝ) ≤ 8/3)).trans hg.2
  refine ⟨compact_cos_even _ _, compact_sin_odd _ _, compact_cos_degree _ _,
    compact_sin_degree _ _, fun x hx => (compact_cos_error _ _ hx _).trans he, ?_⟩
  intro x hx
  have hq : q+1 = 2*R+3 := rfl
  rw [hq] at ho
  exact (compact_sin_error _ _ hx _).trans ho

/-- For nonzero rational t, a radius r at least e|t|/2 satisfying `(e|t|/(2r)) ^ r = (5/4)ε`
makes `Nat.floor (r / 2)` satisfy the rational cutoff guard. -/
theorem source_radius_guard (t ε : ℚ) (ht : t ≠ 0) (r : ℝ)
    (hsr : Real.exp 1*|(t:ℝ)|/2 ≤ r)
    (he : Real.rpow ((Real.exp 1*|(t:ℝ)|/2)/r) r = (5/4)*(ε:ℝ)) :
    Guard t ε (Nat.floor (r/2)) := by
  have htR : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hs : 0 < Real.exp 1*|(t:ℝ)|/2 := by positivity
  have hr : 0 < r := hs.trans_le hsr
  let R := Nat.floor (r/2)
  let q := firstOmitted R
  have hq : r < (q:ℝ) := by
    have h := Nat.lt_floor_add_one (r/2)
    dsimp [q,firstOmitted,R]
    push_cast
    linarith
  have htq : |(t:ℝ)| ≤ q := by
    have hh := Real.add_one_le_exp 1
    nlinarith [abs_nonneg (t:ℝ)]
  have hterm :=
      compact_first_coefficient q (by dsimp [q,firstOmitted]; omega) (|(t:ℝ)|/2) (by positivity)
  have hmono := compact_scale_antitone (Real.exp 1*|(t:ℝ)|/2) r (q:ℝ) hs hsr hq.le
  have hb : (8/3:ℝ)*((|(t:ℝ)|/2)^q/(q.factorial:ℝ)) ≤ (ε:ℝ) := by
    rw [he] at hmono
    change (Real.exp 1*|(t:ℝ)|/2/(q:ℝ))^(q:ℝ) ≤ (5/4)*(ε:ℝ) at hmono
    rw [Real.rpow_natCast] at hmono
    have heq : Real.exp 1*(|(t:ℝ)|/2)/(q:ℝ) = (Real.exp 1*|(t:ℝ)|/2)/(q:ℝ) := by ring
    rw [heq] at hterm
    nlinarith
  constructor
  · exact_mod_cast htq
  · have hb' : (tailBound t R : ℝ) ≤ (ε:ℝ) := by
      simpa only [tailBound, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
        Rat.cast_abs, Rat.cast_natCast] using! hb
    exact Rat.cast_le.mp hb'

/-- For nonzero rational t and 0 < ε < 1/e, provides the unique radius r ≥ e|t|/2 satisfying the
scalar cost equation and bounds the effective cutoff by `Nat.floor (r / 2)`. It also gives
the two regime-dependent degree estimates and a degree bound for every positive auxiliary
scale. -/
theorem cutoff_source_budget (t ε : ℚ) (hε : 0 < ε) (ht : t ≠ 0)
    (hε1 : (ε:ℝ) < 1/Real.exp 1) :
    let s := Real.exp 1*|(t:ℝ)|/2
    let η := (5/4:ℝ)*(ε:ℝ)
    let L := Real.log (1/η)
    ∃ r : ℝ, s ≤ r ∧ Real.rpow (s/r) r = η ∧
      (∀ u : ℝ, s ≤ u → Real.rpow (s/u) u = η → u = r) ∧
      cutoff t ε hε ≤ Nat.floor (r/2) ∧
      (s ≤ L/Real.exp 1 → ((2*cutoff t ε hε+1 : ℕ):ℝ) ≤
        4*L/Real.log (Real.exp 1+L/s)+1) ∧
      (L/Real.exp 1 ≤ s → ((2*cutoff t ε hε+1 : ℕ):ℝ) ≤ Real.exp 1*s+1) ∧
      (∀ u : ℝ, 0 < u → ((2*cutoff t ε hε+1 : ℕ):ℝ) ≤ Real.exp u*s+L/u+1) := by
  (try dsimp only)
  have htR : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hs : 0 < Real.exp 1*|(t:ℝ)|/2 := by positivity
  have hεR : (0:ℝ) < ε := by exact_mod_cast hε
  have hη : (0:ℝ) < (5/4)*(ε:ℝ) := by positivity
  have hη1 : (5/4:ℝ)*(ε:ℝ) < 1 := by
    have h := (lt_div_iff₀ (Real.exp_pos 1)).mp hε1
    have hh := Real.add_one_le_exp 1
    nlinarith
  obtain ⟨r,hsr,he,hu⟩ := simulationCostEquation_answer _ _ hs hη hη1
  have hR := cutoff_le t ε hε _ (source_radius_guard t ε ht r hsr he)
  have hr : 0 < r := hs.trans_le hsr
  have hf := Nat.floor_le (show 0 ≤ r/2 by positivity)
  have hRn : (cutoff t ε hε : ℝ) ≤ (Nat.floor (r/2) : ℝ) := by exact_mod_cast hR
  have hcut : ((2*cutoff t ε hε+1 : ℕ):ℝ) ≤ r+1 := by push_cast; linarith
  have hb := simulationCostBounds_answer _ _ r hs hη hη1 hsr he
  refine ⟨r,hsr,he,hu,hR,?_,?_,?_⟩
  · intro hsmall
    exact hcut.trans (add_le_add (hb.1 hsmall).2 (le_refl _))
  · intro hlarge
    exact hcut.trans (add_le_add (hb.2.1 hlarge) (le_refl _))
  · intro u hu
    exact hcut.trans (add_le_add (hb.2.2 u hu) (le_refl _))

/-- For nonzero real t and 0 < ε < 1/e, constructs a radius satisfying the scalar cost equation
whose rounded truncation yields cosine and sine approximations within ε on [-1, 1]. The
result includes degree bounds in both parameter regimes and for every positive auxiliary
scale [GilyenSuLowWiebe2019]. -/
theorem source_truncation_rate (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε)
    (hε1 : ε < 1/Real.exp 1) :
    let s := Real.exp 1*|t|/2
    let η := (5/4:ℝ)*ε
    ∃ r : ℝ, s ≤ r ∧ Real.rpow (s/r) r = η ∧
      (let R := Nat.floor (r/2)
       (compactCosPoly t R).natDegree ≤ 2*R ∧
       (compactSinPoly t R).natDegree ≤ 2*R+1 ∧
       (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.cos (t*x)-(compactCosPoly t R).eval x| ≤ ε) ∧
       (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.sin (t*x)-(compactSinPoly t R).eval x| ≤ ε) ∧
       (s ≤ Real.log (1/η)/Real.exp 1 → ((2*R+1:ℕ):ℝ) ≤
         4*Real.log (1/η)/Real.log (Real.exp 1+Real.log (1/η)/s)+1) ∧
       (Real.log (1/η)/Real.exp 1 ≤ s → ((2*R+1:ℕ):ℝ) ≤ Real.exp 1*s+1) ∧
       (∀ u : ℝ, 0 < u → ((2*R+1:ℕ):ℝ) ≤ Real.exp u*s+Real.log (1/η)/u+1)) := by
  (try dsimp only)
  obtain ⟨r,hsr,he,hp⟩ := clause45 t ε ht hε hε1
  have hs : 0 < Real.exp 1*|t|/2 := by positivity
  have hr : 0 < r := hs.trans_le hsr
  have hη1 : (5/4:ℝ)*ε < 1 := by
    have h := (lt_div_iff₀ (Real.exp_pos 1)).mp hε1
    have hh := Real.add_one_le_exp 1
    nlinarith
  have hb := simulationCostBounds_answer _ _ r hs (by positivity) hη1 hsr he
  have hf := Nat.floor_le (show 0 ≤ r/2 by positivity)
  have hcut : ((2*Nat.floor (r/2)+1:ℕ):ℝ) ≤ r+1 := by push_cast; linarith
  refine ⟨r,hsr,he,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1,?_,?_,?_⟩
  · intro hsmall
    exact hcut.trans (add_le_add (hb.1 hsmall).2 (le_refl _))
  · intro hlarge
    exact hcut.trans (add_le_add (hb.2.1 hlarge) (le_refl _))
  · intro u hu
    exact hcut.trans (add_le_add (hb.2.2 u hu) (le_refl _))

/-- For nonzero rational t and 0 < ε < 1/e, packages the effective cutoff guard, cosine and sine
degree and error bounds, and a source radius bounding the cutoff. It also records the
degree-budget estimate for every positive auxiliary scale. -/
theorem frontier1 (t ε : ℚ) (hε : 0 < ε) (ht : t ≠ 0)
    (hε1 : (ε:ℝ) < 1/Real.exp 1) :
    let R := cutoff t ε hε
    Guard t ε R ∧
    (compactCosPoly (t:ℝ) R).natDegree ≤ 2*R ∧
    (compactSinPoly (t:ℝ) R).natDegree ≤ 2*R+1 ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.cos ((t:ℝ)*x)-(compactCosPoly (t:ℝ) R).eval x| ≤ ε) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.sin ((t:ℝ)*x)-(compactSinPoly (t:ℝ) R).eval x| ≤ ε) ∧
    ∃ r : ℝ, Real.exp 1*|(t:ℝ)|/2 ≤ r ∧
      Real.rpow ((Real.exp 1*|(t:ℝ)|/2)/r) r = (5/4)*(ε:ℝ) ∧
      R ≤ Nat.floor (r/2) ∧
      (∀ u : ℝ, 0 < u → ((2*R+1:ℕ):ℝ) ≤ Real.exp u*(Real.exp 1*|(t:ℝ)|/2)+
        Real.log (1/((5/4)*(ε:ℝ)))/u+1) := by
  have hp := cutoff_polynomials t ε hε
  obtain ⟨r,hsr,he,_,hR,_,_,hscale⟩ := cutoff_source_budget t ε hε ht hε1
  exact ⟨cutoff_guard t ε hε,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2,
    r,hsr,he,hR,hscale⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff
