/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ActualBalance

/-!
# Rigidity of relaxed parity success

For event acceptance below the parity query threshold, weak separation of the two parity classes
forces every acceptance value to equal one half. The theorem `parity_no_condition8` rules out
uniform separation by any positive bias. These results support the parity analysis of
[FarhiEtAl1998].

## Main statements

* `parity_relaxed_success_forces_half`: If `2 * QueryCount C < n` and event acceptance is at
  least one half on even inputs and at most one half on odd inputs, it equals one half on every
  input.
* `parity_no_condition8`: With `2 * QueryCount C < n`, event acceptance cannot be uniformly at
  least `1 / 2 + ε` on even inputs and at most `1 / 2 - ε` on odd inputs for positive `ε`.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

variable {n : ℕ}
variable {W : Type} [Fintype W] [DecidableEq W]

/-- If `2 * QueryCount C < n` and event acceptance is at least one half on even inputs and at
most one half on odd inputs, it equals one half on every input. -/
theorem parity_relaxed_success_forces_half
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n)
    (hplus : ∀ f, parityOddB f = false → (1 : ℝ) / 2 ≤ parityAcceptance C ψ E f)
    (hminus : ∀ f, parityOddB f = true → parityAcceptance C ψ E f ≤ (1 : ℝ) / 2) :
    ∀ f, parityAcceptance C ψ E f = (1 : ℝ) / 2 := by
  classical
  have hI : 0 < Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
  obtain ⟨i0⟩ := Fintype.card_pos_iff.mp hI
  set Pplus := Finset.univ.filter (fun f : Fin n → Bool => parityOddB f = false) with hPp
  set Pminus := Finset.univ.filter (fun f : Fin n → Bool => parityOddB f = true) with hPm
  have hmap : ∀ f ∈ Pminus, flipAt i0 f ∈ Pplus := by
    intro f hf
    simp only [hPp, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hPm, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [parityOddB_flipAt, hf]
    rfl
  have hmap' : ∀ f ∈ Pplus, flipAt i0 f ∈ Pminus := by
    intro f hf
    simp only [hPm, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hPp, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [parityOddB_flipAt, hf]
    rfl
  have himg : Pplus = Pminus.image (flipAt i0) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro f hf
      exact Finset.mem_image.mpr ⟨flipAt i0 f, hmap' f hf, flipAt_involutive i0 f⟩
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact hmap g hg
  have hbal := parity_acceptance_sum_balance C ψ E h2k
  have hreindex : ∑ f ∈ Pplus, parityAcceptance C ψ E f
      = ∑ f ∈ Pminus, parityAcceptance C ψ E (flipAt i0 f) := by
    conv_lhs => rw [himg]
    rw [Finset.sum_image (fun x _ y _ hxy => (flipAt_involutive i0).injective hxy)]
  rw [hreindex] at hbal
  have hnonneg : ∀ f ∈ Pminus,
      0 ≤ parityAcceptance C ψ E (flipAt i0 f) - parityAcceptance C ψ E f := by
    intro f hf
    have h1 : (1 : ℝ) / 2 ≤ parityAcceptance C ψ E (flipAt i0 f) :=
      hplus _ (by
        simpa only [hPp, Finset.mem_filter, Finset.mem_univ, true_and] using hmap f hf)
    have h2 : parityAcceptance C ψ E f ≤ (1 : ℝ) / 2 :=
      hminus f (by
        simpa only [hPm, Finset.mem_filter, Finset.mem_univ, true_and] using hf)
    linarith
  have hzero : ∑ f ∈ Pminus,
      (parityAcceptance C ψ E (flipAt i0 f) - parityAcceptance C ψ E f) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith [hbal]
  have hflipeq : ∀ f ∈ Pminus,
      parityAcceptance C ψ E (flipAt i0 f) = parityAcceptance C ψ E f := by
    intro f hf
    have hpt := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero f hf
    linarith
  have hterm : ∀ f ∈ Pminus, parityAcceptance C ψ E f = (1 : ℝ) / 2 := by
    intro f hf
    have h1 : (1 : ℝ) / 2 ≤ parityAcceptance C ψ E (flipAt i0 f) :=
      hplus _ (by
        simpa only [hPp, Finset.mem_filter, Finset.mem_univ, true_and] using hmap f hf)
    have h2 : parityAcceptance C ψ E f ≤ (1 : ℝ) / 2 :=
      hminus f (by
        simpa only [hPm, Finset.mem_filter, Finset.mem_univ, true_and] using hf)
    linarith [hflipeq f hf]
  intro f
  by_cases hf : parityOddB f = false
  · have hfP : f ∈ Pplus := by
      simp only [hPp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf
    rw [himg, Finset.mem_image] at hfP
    obtain ⟨g, hg, hfg⟩ := hfP
    rw [← hfg, hflipeq g hg]
    exact hterm g hg
  · have hft : parityOddB f = true := by
      cases hb : parityOddB f
      · exact absurd hb hf
      · rfl
    exact hterm f (by
      simp only [hPm, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hft)

/-- With `2 * QueryCount C < n`, event acceptance cannot be uniformly at least `1 / 2 + ε` on
even inputs and at most `1 / 2 - ε` on odd inputs for positive `ε`. -/
theorem parity_no_condition8
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n)
    (ε : ℝ) (hε : 0 < ε)
    (hplus : ∀ f, parityOddB f = false → (1 : ℝ) / 2 + ε ≤ parityAcceptance C ψ E f)
    (hminus : ∀ f, parityOddB f = true → parityAcceptance C ψ E f ≤ (1 : ℝ) / 2 - ε) :
    False := by
  have hhalf := parity_relaxed_success_forces_half C ψ E h2k
    (fun f hf => by linarith [hplus f hf])
    (fun f hf => by linarith [hminus f hf])
  have hw : parityOddB (fun _ : Fin n => false) = false := by
    simp [parityOddB, boolSupp]
  have h1 := hplus (fun _ : Fin n => false) hw
  rw [hhalf (fun _ : Fin n => false)] at h1
  linarith

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
