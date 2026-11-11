/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max

/-!
# Finite support scalar unitarity on the integers

Defines autocorrelation and the delta autocorrelation condition `IsBandedUnitary` for finitely
supported complex weights on the integers. The theorem `noGo_lemma` shows that such weights
consist of a single coefficient of norm one, expressing the scalar obstruction of [Meyer1996].

## Main statements

* `autocorr`: defines the finite autocorrelation sum.
* `IsBandedUnitary`: requires delta autocorrelation.
* `noGo_lemma`: characterizes the weights as a phase times a singleton.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Concepts.QcaDynamics.ScalarNoGo

/-- The autocorrelation of finitely supported integer weights at displacement `d`, summing `w (m
+ d) * star (w m)` over the support. -/
def autocorr (w : ℤ →₀ ℂ) (d : ℤ) : ℂ :=
  ∑ m ∈ w.support, w (m + d) * star (w m)

/-- The condition that the autocorrelation of finitely supported integer weights is one at zero
and zero at every nonzero displacement. -/
def IsBandedUnitary (w : ℤ →₀ ℂ) : Prop :=
  ∀ d : ℤ, autocorr w d = if d = 0 then 1 else 0

/-- Finitely supported integer weights satisfying `IsBandedUnitary` equal a singleton weight
multiplied by a complex scalar of norm one; see [Meyer1996]. -/
theorem noGo_lemma (w : ℤ →₀ ℂ) (h : IsBandedUnitary w) :
    ∃ (k : ℤ) (c : ℂ), ‖c‖ = 1 ∧ w = c • Finsupp.single k 1 := by

  have hw : w ≠ 0 := by
    intro hw0
    have h0 := h 0
    rw [autocorr, hw0] at h0
    simp at h0
  have hne : w.support.Nonempty := Finsupp.support_nonempty_iff.mpr hw
  set s : Finset ℤ := w.support with hs

  set lo : ℤ := s.min' hne with hlo_def
  set hi : ℤ := s.max' hne with hhi_def
  have hlo_mem : lo ∈ s := Finset.min'_mem s hne
  have hhi_mem : hi ∈ s := Finset.max'_mem s hne
  have hlo_min : ∀ x ∈ s, lo ≤ x := fun x hx => Finset.min'_le s x hx
  have hhi_max : ∀ x ∈ s, x ≤ hi := fun x hx => Finset.le_max' s x hx

  have hwidth : hi = lo := by
    by_contra hne_width
    have hlt : lo < hi :=
      lt_of_le_of_ne (Finset.min'_le_max' s hne) (fun h => hne_width h.symm)
    have hrpos : 0 < hi - lo := sub_pos.mpr hlt
    have hrne : hi - lo ≠ 0 := ne_of_gt hrpos

    have hsingle : ∑ m ∈ s, w (m + (hi - lo)) * star (w m) =
        w (lo + (hi - lo)) * star (w lo) := by
      refine Finset.sum_eq_single_of_mem (f := fun m => w (m + (hi - lo)) * star (w m))
        lo hlo_mem ?_
      intro m hm hmlo
      have hnotmem : m + (hi - lo) ∉ s := by
        intro hmem
        have hle : m + (hi - lo) ≤ hi := hhi_max _ hmem
        have hmle : m ≤ lo := by omega
        have hminle : lo ≤ m := hlo_min m hm
        exact hmlo (le_antisymm hmle hminle)
      have hzero : w (m + (hi - lo)) = 0 :=
        by_contra (fun hne => hnotmem (Finsupp.mem_support_iff.mpr hne))
      simp only [hzero, zero_mul]
    have hterm : lo + (hi - lo) = hi := by omega
    have hsum : autocorr w (hi - lo) = w hi * star (w lo) := by
      rw [autocorr, ← hs, hsingle, hterm]
    have hr0 : autocorr w (hi - lo) = 0 := by
      have hd := h (hi - lo)
      rwa [if_neg hrne] at hd
    have hprod : w hi * star (w lo) = 0 := by
      rw [← hsum]
      exact hr0
    have hhi_ne : w hi ≠ 0 := Finsupp.mem_support_iff.mp hhi_mem
    have hlo_ne : star (w lo) ≠ 0 := by
      rw [star_ne_zero]
      exact Finsupp.mem_support_iff.mp hlo_mem
    exact mul_ne_zero hhi_ne hlo_ne hprod

  have hsupp : s ⊆ {lo} := by
    intro x hx
    rw [Finset.mem_singleton]
    have h1 : lo ≤ x := hlo_min x hx
    have h2 : x ≤ hi := hhi_max x hx
    omega
  have hw_eq : w = (w lo) • Finsupp.single lo (1 : ℂ) := by
    ext x
    by_cases hx : x = lo
    · subst hx
      simp
    · have hnotmem : x ∉ s := by
        intro hmem
        exact hx (by simpa using hsupp hmem)
      have hzero : w x = 0 := (by_contra (fun hne => hnotmem (Finsupp.mem_support_iff.mpr hne)))
      simp [hzero, hx]

  have h0 : w lo * star (w lo) = 1 := by
    have hsingle : ∑ m ∈ s, w (m + 0) * star (w m) = w (lo + 0) * star (w lo) := by
      refine Finset.sum_eq_single_of_mem (f := fun m => w (m + 0) * star (w m))
        lo hlo_mem ?_
      intro m hm hmlo
      have hnotmem : m ∉ s := by
        intro hmem
        exact hmlo (by simpa using hsupp hmem)
      have hzero : w m = 0 := (by_contra (fun hne => hnotmem (Finsupp.mem_support_iff.mpr hne)))
      simp [hzero]
    have hterm : lo + 0 = lo := by omega
    have hsum : autocorr w 0 = w lo * star (w lo) := by
      rw [autocorr, ← hs, hsingle, hterm]
    have := h 0
    rw [hsum] at this
    simpa using this
  have hnorm : ‖w lo‖ = 1 := by
    have hmc : w lo * star (w lo) = 1 := h0
    have hns : (Complex.normSq (w lo) : ℂ) = 1 := by
      rw [← Complex.mul_conj]
      exact hmc
    have hns' : Complex.normSq (w lo) = 1 := Complex.ofReal_inj.mp hns
    have hsq : ‖w lo‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, hns']
    nlinarith [norm_nonneg (w lo)]
  exact ⟨lo, w lo, hnorm, hw_eq⟩

end Qatlib.Concepts.QcaDynamics.ScalarNoGo
