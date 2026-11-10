/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.TopK
import Qatlib.Papers.EntangleTrans99.MainResults.TTransform.Basic
import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.TTransform

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Papers.EntangleTrans99.MainResults.Majorization
open scoped BigOperators

theorem tTransformSpectrum_eq_swap {D : ℕ} (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) :
    tTransformSpectrum spec θ k l
      = fun j => θ * spec j + (1 - θ) * spec (Equiv.swap k l j) := by
  funext j
  by_cases hkl : k = l
  · subst hkl
    simp [tTransformSpectrum, Equiv.swap_self]
    ring
  · unfold tTransformSpectrum
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, if_neg hkl, Equiv.swap_apply_left]
      ring
    · by_cases hjl : j = l
      · subst hjl
        rw [if_neg hjk, if_pos rfl, Equiv.swap_apply_right]
        ring
      · rw [if_neg hjk, if_neg hjl, Equiv.swap_apply_of_ne_of_ne hjk hjl]
        ring

theorem majorizes_tTransformSpectrum_general {D : ℕ} (spec : Fin D → ℝ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (k l : Fin D) :
    Majorizes spec (tTransformSpectrum spec θ k l) := by
  rw [majorizes_iff_forall_subset_sum]
  intro K hK s hcard
  have hconv : ∀ j, tTransformSpectrum spec θ k l j
      = θ * spec j + (1 - θ) * spec (Equiv.swap k l j) :=
    fun j => congrFun (tTransformSpectrum_eq_swap spec θ k l) j
  have h1 : ∑ i ∈ s, spec i ≤ prefixSum (sortedDesc spec) K :=
    finset_sum_le_prefixSum spec hK hcard
  have h2 : ∑ i ∈ s, spec (Equiv.swap k l i) ≤ prefixSum (sortedDesc spec) K := by
    rw [← Finset.sum_image (f := spec) (g := Equiv.swap k l)
      (fun x _ y _ hxy => Equiv.injective _ hxy)]
    exact finset_sum_le_prefixSum spec hK (by
      rw [Finset.card_image_of_injective s (Equiv.injective _)]
      exact hcard)
  calc ∑ i ∈ s, tTransformSpectrum spec θ k l i
      = ∑ i ∈ s, (θ * spec i + (1 - θ) * spec (Equiv.swap k l i)) :=
        Finset.sum_congr rfl (fun i _ => hconv i)
    _ = θ * (∑ i ∈ s, spec i) + (1 - θ) * (∑ i ∈ s, spec (Equiv.swap k l i)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ θ * prefixSum (sortedDesc spec) K
          + (1 - θ) * prefixSum (sortedDesc spec) K := by
        have h1' := mul_le_mul_of_nonneg_left h1 hθ0
        have h2' := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hθ1)
        linarith
    _ = prefixSum (sortedDesc spec) K := by ring

noncomputable def tTransformChain {D : ℕ} (spec : Fin D → ℝ) :
    List (ℝ × Fin D × Fin D) → (Fin D → ℝ)
  | [] => spec
  | (θ, k, l) :: rest => tTransformChain (tTransformSpectrum spec θ k l) rest

theorem majorizes_tTransformChain {D : ℕ} (spec : Fin D → ℝ)
    (steps : List (ℝ × Fin D × Fin D))
    (hθ : ∀ p ∈ steps, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    Majorizes spec (tTransformChain spec steps) := by
  induction steps generalizing spec with
  | nil => exact majorizes_refl spec
  | cons p rest ih =>
    obtain ⟨θ, k, l⟩ := p
    refine majorizes_trans (majorizes_tTransformSpectrum_general spec θ
      (hθ (θ, k, l) (by simp)).1 (hθ (θ, k, l) (by simp)).2 k l) ?_
    exact ih (tTransformSpectrum spec θ k l) (fun q hq => hθ q (by simp [hq]))

noncomputable def twoOutcomeChain {D E : ℕ} : ℕ → LoccProtocol D E
  | 0 => .halt
  | k + 1 => .stepA 2 (fun _ => 1) (fun _ => twoOutcomeChain k)

theorem loccBits_twoOutcomeChain {D E : ℕ} (k : ℕ) :
    LoccBits (twoOutcomeChain (D := D) (E := E) k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show Nat.ceil (Real.log ((2 : ℕ) : ℝ) / Real.log 2) +
      Finset.univ.sup (fun _ : Fin 2 => LoccBits (twoOutcomeChain (D := D) (E := E) k))
      = k + 1
    rw [ih, Finset.sup_const Finset.univ_nonempty]
    have h2 : Nat.ceil (Real.log ((2 : ℕ) : ℝ) / Real.log 2) = 1 := outcomeCostBits_two
    omega

theorem loccBits_twoOutcomeChain_pred {D E : ℕ} :
    LoccBits (twoOutcomeChain (D := D) (E := E) (D - 1)) = D - 1 :=
  loccBits_twoOutcomeChain (D := D) (E := E) (D - 1)

end Qatlib.Papers.EntangleTrans99.MainResults.TTransform
