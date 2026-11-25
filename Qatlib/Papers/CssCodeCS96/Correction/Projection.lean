/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CssCodeCS96.Correction.CharacterBasis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Coordinate projection of a binary code

The projection lemma of the fixed source restricts a binary code to a set of coordinates `E` and
asks when a prescribed pattern `e` on `E` extends to a codeword. The printed proof argues that the
projection has full rank, because a deficiency would produce a nonzero dual word supported inside
`E`; that dual-weight hypothesis is what makes the argument work, and the source lists it only in
the body of the proof.

The module proves the statement with the hypothesis stated explicitly: if no nonzero word of the
classical dual of `C` has weight at most the weight of `E`, then every pattern supported in `E`
extends to a codeword of `C`.

## Main statements

* `projection_surjective_of_dual_weight`: the coordinate projection of `C` onto the support of `E`
  is surjective whenever the dual has no short nonzero word.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996], Lemma 1
-/

namespace Qatlib.Papers.CssCodeCS96.Correction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix
open scoped Classical

variable {n : ℕ}

/-- If no nonzero word of the classical dual of `C` has weight at most the weight of `E`, then
every pattern on the support of `E` extends to a codeword. This is Lemma 1 of the fixed source with
its missing dual-weight hypothesis made explicit; the hypothesis `_hE` records that the prescribed
pattern is supported inside `E`, which the argument does not need because only the coordinates in
the support of `E` are constrained. -/
theorem projection_surjective_of_dual_weight
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (e E : Fin n → ZMod 2)
    (_hE : ∀ i, e i ≠ 0 → E i ≠ 0)
    (hdual : ∀ w ∈ classicalDual C, w ≠ 0 → bitWeight E < bitWeight w) :
    ∃ v ∈ C, ∀ i, E i ≠ 0 → v i = e i := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => E i ≠ 0) with hS
  let π : ↥C →ₗ[ZMod 2] ({i : Fin n // i ∈ S} → ZMod 2) :=
    { toFun := fun v j => (v : Fin n → ZMod 2) j.val
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hsurj : Function.Surjective π := by
    by_contra hns
    have hlt : LinearMap.range π < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, LinearMap.range_eq_top]
      exact hns
    obtain ⟨f, hfne, hfker⟩ := (LinearMap.range π).exists_le_ker_of_lt_top hlt
    let y : {i : Fin n // i ∈ S} → ZMod 2 := fun j => f (Pi.single j 1)
    have hstep : ∀ (x : {i : Fin n // i ∈ S} → ZMod 2) (j : {i : Fin n // i ∈ S}),
        f (x j • Pi.single j (1 : ZMod 2)) = x j * y j := by
      intro x j
      rw [map_smul, smul_eq_mul]
    have hfeval : ∀ x : {i : Fin n // i ∈ S} → ZMod 2, f x = ∑ j, x j * y j := by
      intro x
      have hx : (∑ j, x j • Pi.single j (1 : ZMod 2)) = x := by
        funext k
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          have hz : (Pi.single j (1 : ZMod 2) : {i : Fin n // i ∈ S} → ZMod 2) k = 0 := by
            simp [hj]
          rw [Pi.smul_apply, smul_eq_mul, hz, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ k) h
      calc f x = f (∑ j, x j • Pi.single j (1 : ZMod 2)) := by rw [hx]
        _ = ∑ j, f (x j • Pi.single j (1 : ZMod 2)) := map_sum f _ _
        _ = ∑ j, x j * y j := Finset.sum_congr rfl fun j _ => hstep x j
    have hyne : y ≠ 0 := by
      intro hy0
      apply hfne
      refine LinearMap.ext fun x => ?_
      rw [hfeval x, hy0]
      simp
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hyne
    let w : Fin n → ZMod 2 := fun i => if h : i ∈ S then y ⟨i, h⟩ else 0
    have hwj : w (j₀ : Fin n) = y j₀ := by
      simp only [w]
      rw [dite_eq_left j₀.property]
    have hwne : w ≠ 0 := by
      intro hw0
      have hw0' : w (j₀ : Fin n) = 0 := by rw [hw0]; rfl
      exact hj₀ (by rw [← hwj]; exact hw0')
    have hsupp : Finset.univ.filter (fun i => w i ≠ 0) ⊆
        Finset.univ.filter (fun i => E i ≠ 0) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hE0
      apply hi
      simp only [w]
      rw [dite_eq_right (by rw [hS]; simp [hE0])]
    have hweight : bitWeight w ≤ bitWeight E := Finset.card_le_card hsupp
    have horth : w ∈ classicalDual C := by
      rw [mem_classicalDual]
      intro v hv
      have hsplit : (∑ i, v i * w i) = ∑ i ∈ S, v i * w i := by
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intro i _ hi
        rw [show w i = 0 from by
          simp only [w]
          rw [dite_eq_right hi], mul_zero]
      have hcoe : (∑ i ∈ S, v i * w i) = ∑ j : {i : Fin n // i ∈ S}, v j.val * y j := by
        rw [← Finset.sum_coe_sort S (fun i => v i * w i)]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hwv : w (j : Fin n) = y j := by
          simp only [w]
          rw [dite_eq_left j.property]
        rw [hwv]
      have hval : (∑ j : {i : Fin n // i ∈ S}, v j.val * y j) = f (π ⟨v, hv⟩) := by
        rw [hfeval]
        rfl
      have hmem : π ⟨v, hv⟩ ∈ LinearMap.range π := ⟨⟨v, hv⟩, rfl⟩
      have hker := hfker hmem
      rw [LinearMap.mem_ker] at hker
      simp only [bitDot, dotProduct]
      rw [hsplit, hcoe, hval, hker]
    exact absurd (hdual w horth hwne) (by omega)
  obtain ⟨v, hv⟩ := hsurj (fun j => e j.val)
  refine ⟨v, v.property, ?_⟩
  intro i hi
  have hiS : i ∈ S := by
    rw [hS]
    simp [hi]
  have h := congrFun hv ⟨i, hiS⟩
  show (v : Fin n → ZMod 2) i = e i
  exact h

end Qatlib.Papers.CssCodeCS96.Correction
