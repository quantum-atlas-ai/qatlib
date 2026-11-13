/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder

/-!
# Reduced denominators from modular order phases

This module defines `reducedOrderDecode`, a bounded rational decoder with an endpoint adjustment
for circular phase samples. It recovers the reduced fraction associated with any good order
phase, without requiring its spectral index to be coprime to the order; this is the rational
reconstruction step in [Shor1997].

The denominator is `r / gcd(s, r)` for spectral index `s` and order `r`. These denominators can
subsequently be combined across samples to recover the full order.

## Main statements

* `reducedOrderDecode_count`: a bound on the number of rational candidates tested.
* `reduced_order_denominator_of_every_good_phase`: recovery of the reduced numerator and
  denominator from every good phase window.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery
set_option autoImplicit false

/-- Replaces the final clock label by zero and preserves every other clock value for rational
decoding. -/
def reducedOrderNumerator (M : ℕ) (y : Fin M) : ℕ :=
  if y.val+1=M then 0 else y.val

/-- Runs bounded rational decoding with denominator bound `N` on the endpoint-adjusted clock
numerator. -/
def reducedOrderDecode (N M : ℕ) (y : Fin M) : Option (ℕ×ℕ)×ℕ :=
  boundedRationalDecode N M (reducedOrderNumerator M y)

/-- The reduced-order decoder tests at most `N * (N + 1) / 2` rational candidates. -/
theorem reducedOrderDecode_count (N M : ℕ) (y : Fin M) :
    (reducedOrderDecode N M y).2 ≤ N*(N+1)/2 :=
  boundedRationalDecode_count _ _ _

/-- Every denominator returned by the reduced-order decoder is positive and at most `N`. -/
theorem reducedOrderDecode_sound (N M : ℕ) (y : Fin M) (p q : ℕ)
    (h : (reducedOrderDecode N M y).1 = some (p,q)) : 0<q ∧ q≤N := by
  have hs := boundedRationalDecode_sound N M (reducedOrderNumerator M y) p q h
  exact ⟨hs.1,hs.2.1⟩

/-- For `M > 2`, a sample within circular distance `1 / M` of phase zero has adjusted numerator
at most one. -/
private theorem reduced_zero_window (M : ℕ) (y : Fin M) (hM : 2 < M)
    (hw : phaseDistance 0 ((y.val:ℝ)/M) ≤ 1/(M:ℝ)) :
    reducedOrderNumerator M y ≤ 1 := by
  let t : ℝ := (y.val:ℝ)/M
  let n : ℤ := ⌊-t+1/2⌋
  have hMM : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have ht : 0 ≤ t := by positivity
  have ht' : t < 1 := (div_lt_one hMM).mpr (by exact_mod_cast y.isLt)
  have he : 1/(M:ℝ) < 1 := (div_lt_one hMM).mpr (by exact_mod_cast (show 1<M by omega))
  simp only [phaseDistance, zero_sub] at hw
  change |-t-(n:ℝ)| ≤ 1/(M:ℝ) at hw
  obtain ⟨hl,hu⟩ := abs_le.mp hw
  have hn0 : n ≤ 0 := by
    by_contra hh
    have hh' : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    linarith
  have hn1 : -1 ≤ n := by
    by_contra hh
    have hh' : (n:ℝ) ≤ -2 := by exact_mod_cast (show n≤ -2 by omega)
    linarith
  have hn : n=0 ∨ n= -1 := by omega
  rcases hn with hn | hn
  · have hy : (y.val:ℝ)/M ≤ 1/(M:ℝ) := by simpa [hn, t] using! hl
    have hy' : y.val ≤ 1 := by exact_mod_cast (div_le_div_iff_of_pos_right hMM).mp hy
    unfold reducedOrderNumerator
    split <;> omega
  · have hy : 1-(y.val:ℝ)/M ≤ 1/(M:ℝ) := by simpa [hn,t,add_comm] using! hu
    have hh : (M:ℝ) ≤ y.val+1 := by
      have heq : 1-(y.val:ℝ)/M = ((M:ℝ)-y.val)/M := by field_simp
      rw [heq] at hy
      have hh := (div_le_div_iff_of_pos_right hMM).mp hy
      linarith
    have hlast : y.val+1=M := by
      have hhN : M≤y.val+1 := by exact_mod_cast hh
      omega
    simp [reducedOrderNumerator, hlast]

/-- Under the nontriviality and clock-size hypotheses, a sample within circular distance `1 / M`
of `s / r` decodes to `(s / gcd(s, r), r / gcd(s, r))`, where `r = orderOf a` [Shor1997]. -/
theorem reduced_order_denominator_of_every_good_phase :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (s : Fin (orderOf a)) (y : Fin M),
      1<N → 1<orderOf a → 2*N^2<M →
      phaseDistance ((s.val:ℝ)/(orderOf a:ℝ)) ((y.val:ℝ)/M)≤1/(M:ℝ) →
      (reducedOrderDecode N M y).1=some
        (s.val/Nat.gcd s.val (orderOf a),orderOf a/Nat.gcd s.val (orderOf a)) := by
  intro N M _ a s y hN hr hsize hw
  have hrN := modular_order_le_modulus N a
  have hr0 := modular_order_pos N a
  have hM : 2<M := by nlinarith
  have hMM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hrr : (0:ℝ)<orderOf a := by exact_mod_cast hr0
  by_cases hs0 : s.val=0
  · have hy : reducedOrderNumerator M y ≤ 1 := reduced_zero_window M y hM (by simpa [hs0] using! hw)
    have hyM : reducedOrderNumerator M y < M := by omega
    have hwin : |(reducedOrderNumerator M y:ℚ)/M - (0:ℚ)/1| ≤ 1/(M:ℚ) := by
      simp only [zero_div, sub_zero,
          abs_of_nonneg (by positivity : (0:ℚ) ≤ (reducedOrderNumerator M y:ℚ)/M)]
      apply (div_le_div_iff_of_pos_right (by positivity : (0:ℚ)<M)).2
      exact_mod_cast hy
    simpa [reducedOrderDecode, hs0, Nat.div_self hr0] using!
      (bounded_rational_actual_decoder_unique_recovery N M (reducedOrderNumerator M y) 0 1
        (by omega) (by omega) (by omega) (by simp) hsize hyM hwin).1
  · have hrM : 2*orderOf a < M := by nlinarith
    have heps : 1/(M:ℝ) < 1/(orderOf a:ℝ) :=
      one_div_lt_one_div_of_lt hrr (by exact_mod_cast (show orderOf a<M by omega))
    have hs1 : (1:ℝ)≤ s.val := by exact_mod_cast (show 1≤ s.val by omega)
    have hsr : (s.val:ℝ)+1≤orderOf a := by exact_mod_cast s.isLt
    have hx : 1/(M:ℝ) < (s.val:ℝ)/(orderOf a:ℝ) :=
      heps.trans_le ((div_le_div_iff_of_pos_right hrr).mpr hs1)
    have hle : (s.val:ℝ)/(orderOf a:ℝ) ≤ 1-1/(orderOf a:ℝ) := by
      apply (div_le_iff₀ hrr).mpr
      field_simp
      linarith
    have hx' : (s.val:ℝ)/(orderOf a:ℝ) < 1-1/(M:ℝ) := by linarith
    have ho := phaseDistance_window_unwrap _ _ _ hx hx' (by positivity)
      ((div_lt_one hMM).mpr (by exact_mod_cast y.isLt)) hw
    have hlast : y.val+1 ≠ M := by
      intro hh
      have hyR : (y.val:ℝ)+1=M := by exact_mod_cast hh
      have hu := (abs_le.mp ho).2
      have hbad : 1/(orderOf a:ℝ) ≤ 2/(M:ℝ) := by
        have ht : (y.val:ℝ)/M = 1-1/(M:ℝ) := by field_simp; linarith
        rw [ht] at hu
        have heq : 2/(M:ℝ) = 1/(M:ℝ)+1/(M:ℝ) := by ring
        rw [heq]
        linarith
      have hb := (div_le_div_iff₀ hrr hMM).mp hbad
      have hrMr : (2:ℝ)*orderOf a < M := by exact_mod_cast hrM
      linarith
    let g := Nat.gcd s.val (orderOf a)
    have hg : 0<g := Nat.gcd_pos_of_pos_right _ hr0
    have hgr : g ∣ orderOf a := Nat.gcd_dvd_right _ _
    have hgs : g ∣ s.val := Nat.gcd_dvd_left _ _
    have hq : 0<orderOf a/g := Nat.div_gcd_pos_of_pos_right _ hr0
    have hp : s.val/g < orderOf a/g := by
      rw [Nat.div_lt_iff_lt_mul hg, Nat.div_mul_cancel hgr]
      exact s.isLt
    have hc : Nat.Coprime (s.val/g) (orderOf a/g) := Nat.coprime_div_gcd_div_gcd hg
    have heq : ((s.val/g:ℕ):ℝ)/((orderOf a/g:ℕ):ℝ) = (s.val:ℝ)/(orderOf a:ℝ) := by
      have hgsR : ((s.val/g:ℕ):ℝ) = (s.val:ℝ)/(g:ℝ) := Nat.cast_div hgs (by positivity)
      have hgrR : ((orderOf a/g:ℕ):ℝ) = (orderOf a:ℝ)/(g:ℝ) := Nat.cast_div hgr (by positivity)
      rw [hgsR,hgrR]
      field_simp
    have hQ : |(y.val:ℚ)/M - ((s.val/g:ℕ):ℚ)/((orderOf a/g:ℕ):ℚ)| ≤ 1/(M:ℚ) := by
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      rw [heq]
      exact ho
    exact (bounded_rational_actual_decoder_unique_recovery N M y.val (s.val/g) (orderOf a/g)
      hq ((Nat.div_le_self _ _).trans hrN) hp hc hsize y.isLt hQ).1
        |> (by simpa [reducedOrderDecode, reducedOrderNumerator, hlast] using! ·)
end Qatlib.Concepts.PeriodSampling.OrderRecovery
