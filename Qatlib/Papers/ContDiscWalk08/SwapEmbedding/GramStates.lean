/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs

/-!
# Weighted Gram states and swap compression

The structure `GramData` records a Hermitian matrix, positive weights and normalization, and
amplitude compatibility conditions. The states `gramState` form an isometric embedding whose
swap compression is the normalized Hamiltonian, implementing the Gram-state construction
described in [Childs2010].

## Main statements

* `gramIsometry_conjTranspose_mul`: the Gram-state embedding is isometric.
* `gramIsometry_gram`: its swap compression equals the normalized Hamiltonian.
* `gramWalkSetup`: the Gram data determine a walk setup.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped ComplexConjugate

namespace Qatlib.Papers.ContDiscWalk08.SwapEmbedding

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Packages a Hermitian matrix, positive weights and normalization satisfying a weighted row
identity, and amplitudes satisfying modulus and swapped cross-product conditions. -/
structure GramData (I : Type*) [Fintype I] [DecidableEq I] where

  H : Matrix I I ℂ

  isHermitian : H.IsHermitian

  d : I → ℝ

  d_pos : ∀ j, 0 < d j

  C : ℝ

  C_pos : 0 < C

  perron : ∀ j, ∑ k, ‖H j k‖ * d k = C * d j

  s : I → I → ℂ

  s_mod : ∀ j k, (starRingEnd ℂ) (s j k) * s j k = ((‖H j k‖ * d k / d j : ℝ) : ℂ)

  s_cross : ∀ j k, (starRingEnd ℂ) (s j k) * s k j = H j k

namespace GramData

variable (G : GramData I)

/-- Defines the complex normalization factor `1 / √G.C`. -/
def normFactor (G : GramData I) : ℂ := (((Real.sqrt G.C)⁻¹ : ℝ) : ℂ)

/-- The normalization factor is fixed by complex conjugation. -/
theorem normFactor_conj (G : GramData I) :
    (starRingEnd ℂ) G.normFactor = G.normFactor := by
  unfold normFactor
  simp

/-- The square of the normalization factor multiplied by `G.C` equals one. -/
theorem normFactor_sq_mul (G : GramData I) :
    G.normFactor * G.normFactor * (G.C : ℂ) = 1 := by
  have hC : (0 : ℝ) < G.C := G.C_pos
  have hsq : (Real.sqrt G.C : ℂ) * (Real.sqrt G.C : ℂ) = (G.C : ℂ) := by
    have hcast : (Real.sqrt G.C : ℂ) * (Real.sqrt G.C : ℂ)
        = (((Real.sqrt G.C) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast Real.sq_sqrt hC.le
  have hne : (Real.sqrt G.C : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hC))
  unfold normFactor
  rw [show (((Real.sqrt G.C)⁻¹ : ℝ) : ℂ) = ((Real.sqrt G.C : ℂ))⁻¹ from by push_cast; ring]
  rw [← hsq]
  rw [show ((Real.sqrt G.C : ℂ))⁻¹ * ((Real.sqrt G.C : ℂ))⁻¹
        * ((Real.sqrt G.C : ℂ) * (Real.sqrt G.C : ℂ))
      = (((Real.sqrt G.C : ℂ))⁻¹ * (Real.sqrt G.C : ℂ))
        * (((Real.sqrt G.C : ℂ))⁻¹ * (Real.sqrt G.C : ℂ)) from by ring]
  rw [inv_mul_cancel₀ hne, one_mul]

/-- The reciprocal of `G.C` equals the square of the normalization factor over the complex
numbers. -/
theorem inv_eq_normFactor_mul (G : GramData I) :
    ((G.C)⁻¹ : ℂ) = G.normFactor * G.normFactor := by
  rw [show ((G.C)⁻¹ : ℂ) = ((G.C : ℂ))⁻¹ from by push_cast; ring]
  exact inv_eq_of_mul_eq_one_left G.normFactor_sq_mul

/-- Defines the weighted state supported on pairs whose first coordinate is `j`, with amplitudes
`G.normFactor * G.s j p.2`. -/
def gramState (G : GramData I) (j : I) : QState (I × I) :=
  fun p => if p.1 = j then G.normFactor * G.s j p.2 else 0

/-- Evaluates a Gram state on a pair, giving its weighted amplitude when the first coordinate
matches and zero otherwise. -/
@[simp] theorem gramState_apply (j a b : I) :
    G.gramState j (a, b) = if a = j then G.normFactor * G.s j b else 0 := rfl

/-- The squared modulus of a Gram-state coordinate is the normalized weighted entry norm on its
support and zero elsewhere. -/
theorem gramState_mod (j a b : I) :
    (starRingEnd ℂ) (G.gramState j (a, b)) * G.gramState j (a, b)
      = if a = j then
          G.normFactor * G.normFactor * (((‖G.H j b‖ * G.d b / G.d j : ℝ)) : ℂ)
        else 0 := by
  by_cases ha : a = j
  · simp only [gramState_apply, if_pos ha, map_mul, G.normFactor_conj]
    calc G.normFactor * (starRingEnd ℂ) (G.s j b) * (G.normFactor * G.s j b)
        = (G.normFactor * G.normFactor) *
            ((starRingEnd ℂ) (G.s j b) * G.s j b) := by ring
      _ = G.normFactor * G.normFactor *
            (((‖G.H j b‖ * G.d b / G.d j : ℝ)) : ℂ) := by rw [G.s_mod j b]
  · simp [gramState_apply, if_neg ha]

/-- The Gram states have inner product one for equal labels and zero for distinct labels. -/
theorem inner_gramState_self (j k : I) :
    Inner (G.gramState j) (G.gramState k) = if j = k then 1 else 0 := by
  rw [inner_apply, ← Finset.univ_product_univ, Finset.sum_product]
  by_cases hjk : j = k
  · subst hjk
    have hrow : ∀ a : I, ∑ b : I,
        (starRingEnd ℂ) (G.gramState j (a, b)) * G.gramState j (a, b)
        = if a = j then (G.normFactor * G.normFactor * (G.C : ℂ)) else 0 := by
      intro a
      by_cases ha : a = j
      · rw [if_pos ha]
        have hb : ∀ b : I,
            (starRingEnd ℂ) (G.gramState j (a, b)) * G.gramState j (a, b)
              = (G.normFactor * G.normFactor) *
                  (((‖G.H j b‖ * G.d b / G.d j : ℝ)) : ℂ) := by
          intro b
          rw [G.gramState_mod j a b, if_pos ha]
        rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
        have hsum : ∑ b : I, (((‖G.H j b‖ * G.d b / G.d j : ℝ)) : ℂ) = (G.C : ℂ) := by
          have hsumR : ∑ b : I, (‖G.H j b‖ * G.d b / G.d j) = G.C := by
            rw [← Finset.sum_div, G.perron j]
            exact mul_div_cancel_right₀ G.C (ne_of_gt (G.d_pos j))
          rw [← Complex.ofReal_sum, hsumR]
        rw [hsum]
      · rw [if_neg ha]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [G.gramState_mod j a b, if_neg ha]
    rw [Finset.sum_congr rfl (fun a _ => hrow a), Finset.sum_eq_single j]
    · simpa using G.normFactor_sq_mul
    · intro a _ ha; rw [if_neg ha]
    · intro h; exact absurd (Finset.mem_univ j) h
  · have hrow : ∀ a : I, ∑ b : I,
        (starRingEnd ℂ) (G.gramState j (a, b)) * G.gramState k (a, b) = 0 := by
      intro a
      by_cases ha : a = j
      · refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [gramState_apply, if_pos ha]
        rw [gramState_apply, if_neg (fun e => hjk (ha.symm.trans e))]
        simp
      · refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [gramState_apply, if_neg ha]
        simp
    rw [Finset.sum_eq_zero (fun a _ => hrow a), if_neg hjk]

/-- The inner product of a Gram state with a swapped Gram state is the corresponding entry of
`G.H` divided by `G.C`. -/
theorem inner_gramState_swap (j k : I) :
    Inner (G.gramState j) (SwapGate *ᵥ G.gramState k)
      = ((G.C)⁻¹ : ℂ) * G.H j k := by
  rw [inner_apply, applyGate_swapGate, ← Finset.univ_product_univ, Finset.sum_product]
  have hrow : ∀ a : I, ∑ b : I,
      (starRingEnd ℂ) (G.gramState j (a, b))
        * (fun p : I × I => G.gramState k (Prod.swap p)) (a, b)
      = if a = j then G.normFactor * G.normFactor * G.H j k else 0 := by
    intro a
    by_cases ha : a = j
    · rw [if_pos ha]
      have hb : ∀ b : I,
          (starRingEnd ℂ) (G.gramState j (a, b))
            * (fun p : I × I => G.gramState k (Prod.swap p)) (a, b)
          = if b = k then G.normFactor * G.normFactor * G.H j k else 0 := by
        intro b
        rw [gramState_apply, if_pos ha]
        show (starRingEnd ℂ) (G.normFactor * G.s j b) * G.gramState k (b, a) = _
        rw [gramState_apply]
        by_cases hbk : b = k
        · simp only [if_pos hbk]
          rw [hbk, ha]
          calc (starRingEnd ℂ) (G.normFactor * G.s j k) * (G.normFactor * G.s k j)
              = (G.normFactor * G.normFactor) *
                  ((starRingEnd ℂ) (G.s j k) * G.s k j) := by
                rw [map_mul, G.normFactor_conj]; ring
            _ = G.normFactor * G.normFactor * G.H j k := by rw [G.s_cross]
        · simp [if_neg hbk]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro b _ hbk; rw [if_neg hbk]
      · intro h; exact absurd (Finset.mem_univ k) h
    · rw [if_neg ha]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [gramState_apply, if_neg ha]; simp
  rw [Finset.sum_congr rfl (fun a _ => hrow a), Finset.sum_eq_single j]
  · rw [if_pos rfl, G.inv_eq_normFactor_mul]
  · intro a _ ha; rw [if_neg ha]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Defines the matrix whose column indexed by `j` is the Gram state `G.gramState j`. -/
def gramIsometry (G : GramData I) : Matrix (I × I) I ℂ :=
  Matrix.of (fun p j => G.gramState j p)

/-- The Gram-state matrix has conjugate-transpose product equal to the identity. This verifies
the isometry in the construction of [Childs2010]. -/
theorem gramIsometry_conjTranspose_mul :
    (G.gramIsometry)ᴴ * G.gramIsometry = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hconv : (∑ p : I × I, (G.gramIsometry)ᴴ j p * G.gramIsometry p k)
      = Inner (G.gramState j) (G.gramState k) := by
    rw [inner_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rfl
  rw [hconv, inner_gramState_self]

/-- Compressing the swap by the Gram-state isometry gives `G.H` scaled by `1 / G.C`. See the
weighted Gram construction in [Childs2010]. -/
theorem gramIsometry_gram :
    (G.gramIsometry)ᴴ * SwapGate * G.gramIsometry = (((G.C)⁻¹ : ℝ) : ℂ) • G.H := by
  ext j k
  rw [Matrix.smul_apply, Matrix.mul_assoc, Matrix.mul_apply]
  change (∑ p : I × I, (starRingEnd ℂ) (G.gramState j p) *
      (SwapGate *ᵥ G.gramState k) p) = (((G.C)⁻¹ : ℝ) : ℂ) * G.H j k
  rw [← inner_apply, inner_gramState_swap]
  push_cast
  ring

/-- Builds a `WalkSetup` from the weighted Gram data using the Gram-state embedding and
normalization `G.C`, as in [Childs2010]. -/
def gramWalkSetup (G : GramData I) : WalkSetup I where
  H := G.H
  isHermitian := G.isHermitian
  absNorm := G.C
  absNorm_pos := G.C_pos
  T := G.gramIsometry
  isometry := G.gramIsometry_conjTranspose_mul
  gram := G.gramIsometry_gram

end GramData

end Qatlib.Papers.ContDiscWalk08.SwapEmbedding
