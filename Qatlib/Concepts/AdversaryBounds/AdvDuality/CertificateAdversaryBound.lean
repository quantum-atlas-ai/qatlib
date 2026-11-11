/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
import Qatlib.Concepts.AdversaryBounds.OptimizedAdv

/-!
# Certificate upper bound for the adversary value

`advValue_le_of_certificates` bounds the adversary value by a uniform bound on certificate
sizes. The required certificate property is that inputs with different outputs possess a
differing coordinate in the intersection of their certificate sets. For background, see
[AmbainisEtAl2009].

## Main statements

* `advValue_le_of_certificates`: If every certificate set has size at most a nonnegative `C` and
  every pair with different outputs has a differing coordinate in both certificates, then
  `advValue input g ≤ ENNReal.ofReal C`.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal
open Classical BigOperators

/-- If every certificate set has size at most a nonnegative `C` and every pair with different
outputs has a differing coordinate in both certificates, then `advValue input g ≤
ENNReal.ofReal C`. -/
theorem advValue_le_of_certificates {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (c : X → Finset κ) (C : ℝ) (hC : 0 ≤ C)
    (hcard : ∀ x, (c x).card ≤ C)
    (hc : ∀ x y, g x ≠ g y → ∃ j ∈ c x ∩ c y, input x j ≠ input y j) :
    advValue input g ≤ ENNReal.ofReal C := by
  classical
  by_cases hnc : ∃ a b, g a ≠ g b
  · obtain ⟨a, b, hab⟩ := hnc
    have hd (x : X) : ∃ y, g x ≠ g y := by
      by_cases he : g x = g a
      · exact ⟨b, fun hh => hab (he.symm.trans hh)⟩
      · exact ⟨a, he⟩
    have hcpos (x : X) : 0 < (c x).card := by
      obtain ⟨y, hxy⟩ := hd x
      obtain ⟨j, hj, _⟩ := hc x y hxy
      exact Finset.card_pos.mpr ⟨j, (Finset.mem_inter.mp hj).1⟩
    have hcposR (x : X) : 0 < ((c x).card : ℝ) := by exact_mod_cast hcpos x
    have hCpos : 0 < C := (hcposR a).trans_le (hcard a)
    obtain ⟨j₀, hj₀, _⟩ := hc a b hab
    letI : Nonempty κ := ⟨j₀⟩
    let p (x : X) (i : κ) : ℝ := if i ∈ c x then 1 / ((c x).card : ℝ) else 0
    have hp0 (x : X) (i : κ) : 0 ≤ p x i := by
      dsimp only [p]
      split_ifs <;> positivity
    have hp1 (x : X) : ∑ i, p x i = 1 := by
      simp [p, Finset.sum_ite_mem, (hcposR x).ne']
    have hk (x y : X) (hxy : g x ≠ g y) :
        1 / C ≤ advMinimaxTerm input (fun _ => 1) p x y := by
      obtain ⟨j, hj, hdiff⟩ := hc x y hxy
      have hjx := (Finset.mem_inter.mp hj).1
      have hjy := (Finset.mem_inter.mp hj).2
      have hx := one_div_le_one_div_of_le (hcposR x) (hcard x)
      have hy := one_div_le_one_div_of_le (hcposR y) (hcard y)
      have hprod : (1 / C) ^ 2 ≤ (1 / ((c x).card : ℝ)) * (1 / ((c y).card : ℝ)) := by
        simpa only [pow_two] using! mul_le_mul hx hy (by positivity : 0 ≤ 1 / C)
          (by positivity : 0 ≤ 1 / ((c x).card : ℝ))
      calc
        _ ≤ Real.sqrt ((1 / ((c x).card : ℝ)) * (1 / ((c y).card : ℝ))) :=
            Real.le_sqrt_of_sq_le hprod
        _ = (if input x j ≠ input y j then Real.sqrt (p x j * p y j) / (1 : ℝ) else 0) := by
            simp [p, hjx, hjy, hdiff]
        _ ≤ _ := by
            change (if input x j ≠ input y j then Real.sqrt (p x j * p y j) / (1 : ℝ) else 0) ≤
              ∑ i : κ, if input x i ≠ input y i then Real.sqrt (p x i * p y i) / (1 : ℝ) else 0
            exact Finset.single_le_sum (f := fun (i : κ) =>
              if input x i ≠ input y i then Real.sqrt (p x i * p y i) / (1 : ℝ) else 0)
              (fun i _ => by (try dsimp only); split_ifs <;> positivity) (Finset.mem_univ j)
    unfold advValue advAlphaR
    refine iSup_le fun Γ => ?_
    by_cases hzero : ‖Γ.val‖ = 0
    · have h0 : ∀ i : κ, ENNReal.ofReal ((fun _ => (1 : ℝ)) i) * ENNReal.ofReal ‖Γ.val‖ /
          ENNReal.ofReal ‖genAdvFilter input Γ.val i‖ = 0 := by
        intro i
        rw [hzero]
        simp
      unfold advAlphaWitnessR
      simp only [h0, iInf_const]
      exact bot_le
    · have hpos : 0 < ‖Γ.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      obtain ⟨x, y, hxy, hbound⟩ := advNonneg_witness_le_minimaxTerm input g (fun _ => 1)
        (by intro i; norm_num) Γ.val Γ.property.1 Γ.property.2.1 Γ.property.2.2.1 hpos p hp0 hp1
      let f (i : κ) := ‖advFilterR input Γ.val i‖ / ‖Γ.val‖
      obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
      have he : (⨆ i, f i) = f j := le_antisymm
        (ciSup_le (fun i => hj i (Finset.mem_univ i)))
        (le_ciSup (Set.finite_range f).bddAbove j)
      have hr : 1 / C ≤ f j := by
        have hb := (hk x y hxy).trans hbound
        simp only [mul_one] at hb
        change 1 / C ≤ (⨆ i, f i) at hb
        rw [he] at hb
        exact hb
      have hn : ‖Γ.val‖ / C ≤ ‖advFilterR input Γ.val j‖ := by
        have hh := (le_div_iff₀ hpos).mp hr
        convert! hh using 1
        ring
      have hfpos : 0 < ‖advFilterR input Γ.val j‖ := (div_pos hpos hCpos).trans_le hn
      have hjne : ENNReal.ofReal ‖advFilterR input Γ.val j‖ ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact hfpos
      have hfil : genAdvFilter input Γ.val j = advFilterR input Γ.val j := rfl
      unfold advAlphaWitnessR
      calc (⨅ i : κ, ENNReal.ofReal ((fun _ => (1 : ℝ)) i) * ENNReal.ofReal ‖Γ.val‖ /
              ENNReal.ofReal ‖genAdvFilter input Γ.val i‖)
            ≤ ENNReal.ofReal ((fun _ => (1 : ℝ)) j) * ENNReal.ofReal ‖Γ.val‖ /
                ENNReal.ofReal ‖genAdvFilter input Γ.val j‖ :=
              iInf_le (f := fun i : κ => ENNReal.ofReal ((fun _ => (1 : ℝ)) i) *
                ENNReal.ofReal ‖Γ.val‖ / ENNReal.ofReal ‖genAdvFilter input Γ.val i‖) j
          _ = ENNReal.ofReal ‖Γ.val‖ / ENNReal.ofReal ‖advFilterR input Γ.val j‖ := by
              rw [hfil]; simp
          _ ≤ ENNReal.ofReal C := by
              rw [ENNReal.div_le_iff hjne ENNReal.ofReal_ne_top]
              calc ENNReal.ofReal ‖Γ.val‖
                    = ENNReal.ofReal ((‖Γ.val‖ / C) * C) := by
                      rw [div_mul_cancel₀ _ hCpos.ne']
                _ ≤ ENNReal.ofReal (‖advFilterR input Γ.val j‖ * C) :=
                    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn hC)
                _ = ENNReal.ofReal C * ENNReal.ofReal ‖advFilterR input Γ.val j‖ :=
                    (ENNReal.ofReal_mul (norm_nonneg _)).trans (mul_comm _ _)
  · unfold advValue advAlphaR
    refine iSup_le fun Γ => ?_
    obtain ⟨x₀, y₀, hne⟩ : ∃ x y, Γ.val x y ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact Γ.property.2.2.2 (Matrix.ext fun x y => hcon x y)
    exact absurd (Γ.property.2.2.1 x₀ y₀ (by
      by_contra hcon; exact hnc ⟨x₀, y₀, hcon⟩)) hne
end Qatlib.Concepts.AdversaryBounds.AdvDuality
