/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.CompletePartialOrder
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

open Matrix

local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι]

structure CssData (ι κX κZ : Type*) [Fintype ι] where

  hX : Matrix κX ι (ZMod 2)

  hZ : Matrix κZ ι (ZMod 2)

  hcompat : hX * hZᵀ = 0

def CssData.numQubits (_c : CssData ι κX κZ) : ℕ := Fintype.card ι

noncomputable def CssData.encodedQubits (c : CssData ι κX κZ) : ℕ :=
  Fintype.card ι - Matrix.rank c.hX - Matrix.rank c.hZ

noncomputable def CssData.rate (c : CssData ι κX κZ) : ℚ :=
  (c.encodedQubits : ℚ) / (Fintype.card ι : ℚ)

noncomputable def cssXCheckKernel (c : CssData ι κX κZ) (i : κX) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  LinearMap.ker ((cssPauliX (c.hX i) - 1).mulVecLin)

noncomputable def cssZCheckKernel (c : CssData ι κX κZ) (j : κZ) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  LinearMap.ker ((cssPauliZ (c.hZ j) - 1).mulVecLin)

noncomputable def cssXStabilized (c : CssData ι κX κZ) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  ⨅ i, cssXCheckKernel c i

noncomputable def cssZStabilized (c : CssData ι κX κZ) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  ⨅ j, cssZCheckKernel c j

noncomputable def cssCodespace (c : CssData ι κX κZ) : Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  cssXStabilized c ⊓ cssZStabilized c

noncomputable def cssDistance (c : CssData ι κX κZ) : ℕ∞ :=
  min (sInf {w : ℕ∞ | ∃ z : ι → ZMod 2, c.hX *ᵥ z = 0 ∧
      z ∉ LinearMap.range (Matrix.mulVecLin c.hZᵀ) ∧ (bitWeight z : ℕ∞) = w})
    (sInf {w : ℕ∞ | ∃ x : ι → ZMod 2, c.hZ *ᵥ x = 0 ∧
      x ∉ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧ (bitWeight x : ℕ∞) = w})

def CssData.checkWeight (c : CssData ι κX κZ) : ℕ :=
  max (Finset.univ.sup fun i => bitWeight (c.hX i))
    (Finset.univ.sup fun j => bitWeight (c.hZ j))

def CssData.qubitIncidence (c : CssData ι κX κZ) : ℕ :=
  Finset.univ.sup fun p : ι =>
    (Finset.univ.filter fun i : κX => c.hX i p ≠ 0).card +
      (Finset.univ.filter fun j : κZ => c.hZ j p ≠ 0).card

theorem cssRank_add_le (c : CssData ι κX κZ) :
    Matrix.rank c.hX + Matrix.rank c.hZ ≤ Fintype.card ι := by
  classical
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero c.hcompat
  simpa only [Matrix.rank_transpose] using h

theorem cssDistance_eq_logical (c : CssData ι κX κZ) :
    cssDistance c = sInf {w : ℕ∞ | ∃ (x z : ι → ZMod 2),
      c.hX *ᵥ z = 0 ∧ c.hZ *ᵥ x = 0 ∧
      ¬(x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
        z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) ∧ (pauliWeight x z : ℕ∞) = w} := by
  classical
  let AZ : Set ℕ∞ := {w | ∃ z : ι → ZMod 2, c.hX *ᵥ z = 0 ∧
    z ∉ LinearMap.range (Matrix.mulVecLin c.hZᵀ) ∧ (bitWeight z : ℕ∞) = w}
  let AX : Set ℕ∞ := {w | ∃ x : ι → ZMod 2, c.hZ *ᵥ x = 0 ∧
    x ∉ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧ (bitWeight x : ℕ∞) = w}
  let AL : Set ℕ∞ := {w | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = 0 ∧ c.hZ *ᵥ x = 0 ∧
    ¬(x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
      z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) ∧ (pauliWeight x z : ℕ∞) = w}
  change min (sInf AZ) (sInf AX) = sInf AL
  apply le_antisymm
  · apply le_sInf
    rintro w ⟨x, z, hz, hx, hout, hw⟩
    rw [← hw]
    rcases not_and_or.mp hout with hxout | hzout
    · have hb : sInf AX ≤ (bitWeight x : ℕ∞) := sInf_le ⟨x, hx, hxout, rfl⟩
      exact ((min_le_right _ _).trans hb).trans
        (by exact_mod_cast bitWeight_le_pauliWeight_left x z)
    · have hb : sInf AZ ≤ (bitWeight z : ℕ∞) := sInf_le ⟨z, hz, hzout, rfl⟩
      exact ((min_le_left _ _).trans hb).trans
        (by exact_mod_cast bitWeight_le_pauliWeight_right x z)
  · apply le_min
    · apply le_sInf
      rintro w ⟨z, hz, hout, hw⟩
      apply sInf_le
      refine ⟨0, z, hz, by simp, ?_, ?_⟩
      · exact fun h => hout h.2
      · simpa using hw
    · apply le_sInf
      rintro w ⟨x, hx, hout, hw⟩
      apply sInf_le
      refine ⟨x, 0, by simp, hx, ?_, ?_⟩
      · exact fun h => hout h.1
      · simpa using hw

private noncomputable abbrev cssRowX (c : CssData ι κX κZ) :=
  LinearMap.range (Matrix.mulVecLin c.hXᵀ)

private noncomputable abbrev cssRowZ (c : CssData ι κX κZ) :=
  LinearMap.range (Matrix.mulVecLin c.hZᵀ)

omit [DecidableEq ι] in

private theorem css_rows_orthogonal (c : CssData ι κX κZ) (x : cssRowX c) (z : cssRowZ c) :
    bitDot (z : ι → ZMod 2) (x : ι → ZMod 2) = 0 := by
  classical
  obtain ⟨u, hu⟩ := x.property
  obtain ⟨v, hv⟩ := z.property
  have hc : c.hZ * c.hXᵀ = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose c.hcompat
  rw [← hu, ← hv]
  change (c.hZᵀ *ᵥ v) ⬝ᵥ (c.hXᵀ *ᵥ u) = 0
  rw [dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hc]
  simp

private noncomputable def cssStabilizerRepresentation (c : CssData ι κX κZ) :
    Representation ℂ (Multiplicative (cssRowX c × cssRowZ c)) ((ι → ZMod 2) → ℂ) where
  toFun g := (cssPauliX (g.toAdd.1 : ι → ZMod 2) * cssPauliZ (g.toAdd.2 : ι → ZMod 2)).mulVecLin
  map_one' := by
    change (cssPauliX (0 : ι → ZMod 2) * cssPauliZ 0).mulVecLin = 1
    simp only [cssPauliX_zero, cssPauliZ_zero, one_mul, Matrix.mulVecLin_one]
    rfl
  map_mul' := by
    intro a b
    change (cssPauliX ((a.toAdd.1 : ι → ZMod 2) + (b.toAdd.1 : ι → ZMod 2)) *
      cssPauliZ ((a.toAdd.2 : ι → ZMod 2) + (b.toAdd.2 : ι → ZMod 2))).mulVecLin =
      (cssPauliX (a.toAdd.1 : ι → ZMod 2) * cssPauliZ (a.toAdd.2 : ι → ZMod 2)).mulVecLin.comp
        (cssPauliX (b.toAdd.1 : ι → ZMod 2) * cssPauliZ (b.toAdd.2 : ι → ZMod 2)).mulVecLin
    rw [← Matrix.mulVecLin_mul, cssPauliXZ_mul, css_rows_orthogonal c b.toAdd.1 a.toAdd.2]
    simp

private noncomputable def cssCoefficientLabels (c : CssData ι κX κZ) :
    ((κX ⊕ κZ) → ZMod 2) →+ (cssRowX c × cssRowZ c) where
  toFun a :=
    (⟨c.hXᵀ *ᵥ (fun i => a (Sum.inl i)), ⟨(fun i => a (Sum.inl i)), rfl⟩⟩,
     ⟨c.hZᵀ *ᵥ (fun j => a (Sum.inr j)), ⟨(fun j => a (Sum.inr j)), rfl⟩⟩)
  map_zero' := by
    apply Prod.ext <;> apply Subtype.ext
    · exact Matrix.mulVec_zero _
    · exact Matrix.mulVec_zero _
  map_add' := by
    intro a b
    apply Prod.ext <;> apply Subtype.ext
    · exact Matrix.mulVec_add c.hXᵀ (fun i => a (Sum.inl i)) (fun i => b (Sum.inl i))
    · exact Matrix.mulVec_add c.hZᵀ (fun j => a (Sum.inr j)) (fun j => b (Sum.inr j))

omit [DecidableEq ι] in

private theorem cssCoefficientLabels_surjective (c : CssData ι κX κZ) :
    Function.Surjective (cssCoefficientLabels c) := by
  rintro ⟨x, z⟩
  obtain ⟨u, hu⟩ := x.property
  obtain ⟨v, hv⟩ := z.property
  refine ⟨Sum.elim u v, ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact hu
  · exact hv

private noncomputable def cssCoefficientRepresentation (c : CssData ι κX κZ) :
    Representation ℂ (Multiplicative (((κX ⊕ κZ) → ZMod 2))) ((ι → ZMod 2) → ℂ) :=
  (cssStabilizerRepresentation c).comp (cssCoefficientLabels c).toMultiplicative

private theorem cssCoefficientRepresentation_basis [DecidableEq κX] [DecidableEq κZ]
    (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    cssCoefficientRepresentation c (Multiplicative.ofAdd (Pi.single k 1)) =
      (Sum.elim (fun i => cssPauliX (c.hX i)) (fun j => cssPauliZ (c.hZ j)) k).mulVecLin := by
  let a : (κX ⊕ κZ) → ZMod 2 := Pi.single k 1
  change cssCoefficientRepresentation c (Multiplicative.ofAdd a) = _
  classical
  cases k with
  | inl i =>
    have hx : c.hXᵀ *ᵥ (fun j => a (Sum.inl j)) = c.hX i := by
      ext q
      simp [a, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    have hz : c.hZᵀ *ᵥ (fun j => a (Sum.inr j)) = 0 := by
      ext q
      simp [a, Matrix.mulVec, dotProduct]
    change (cssPauliX (c.hXᵀ *ᵥ (fun j => a (Sum.inl j))) *
      cssPauliZ (c.hZᵀ *ᵥ (fun j => a (Sum.inr j)))).mulVecLin = _
    rw [hx, hz, cssPauliZ_zero, mul_one]
    rfl
  | inr j =>
    have hx : c.hXᵀ *ᵥ (fun i => a (Sum.inl i)) = 0 := by
      ext q
      simp [a, Matrix.mulVec, dotProduct]
    have hz : c.hZᵀ *ᵥ (fun i => a (Sum.inr i)) = c.hZ j := by
      ext q
      simp [a, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    change (cssPauliX (c.hXᵀ *ᵥ (fun i => a (Sum.inl i))) *
      cssPauliZ (c.hZᵀ *ᵥ (fun i => a (Sum.inr i)))).mulVecLin = _
    rw [hx, hz, cssPauliX_zero, one_mul]
    rfl

omit [Fintype ι] [DecidableEq ι] in

private theorem binary_rep_fixed_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ (Multiplicative (κ → ZMod 2)) ((ι → ZMod 2) → ℂ))
    (v : (ι → ZMod 2) → ℂ) :
    (∀ a : κ → ZMod 2, ρ (Multiplicative.ofAdd a) v = v) ↔
      (∀ i : κ, ρ (Multiplicative.ofAdd (Pi.single i 1)) v = v) := by
  constructor
  · intro h i
    exact h _
  · intro h
    have h0 : ρ (Multiplicative.ofAdd (0 : κ → ZMod 2)) v = v := by
      change ρ 1 v = v
      rw [ρ.map_one]
      rfl
    have hs : ∀ s : Finset κ, ∀ a : κ → ZMod 2,
        ρ (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (a i))) v = v := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro a; exact h0
      | @insert i s hi ih =>
        intro a
        rw [Finset.sum_insert hi]
        change ρ (Multiplicative.ofAdd (Pi.single i (a i)) *
          Multiplicative.ofAdd (∑ j ∈ s, Pi.single j (a j))) v = v
        rw [ρ.map_mul]
        change ρ (Multiplicative.ofAdd (Pi.single i (a i)))
          (ρ (Multiplicative.ofAdd (∑ j ∈ s, Pi.single j (a j))) v) = v
        rw [ih a]
        rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (a i) with hz | ho
        · rw [hz]
          simpa only [Pi.single_zero] using h0
        · simpa [ho] using h i
    intro a
    have ha : (∑ i : κ, Pi.single i (a i)) = a := by
      ext j
      simp [Pi.single_apply]
    simpa only [ha] using hs Finset.univ a

private theorem mem_cssCodespace_iff (c : CssData ι κX κZ) (v : (ι → ZMod 2) → ℂ) :
    v ∈ cssCodespace c ↔
      (∀ i : κX, cssPauliX (c.hX i) *ᵥ v = v) ∧
      (∀ j : κZ, cssPauliZ (c.hZ j) *ᵥ v = v) := by
  classical
  simp [cssCodespace, cssXStabilized, cssZStabilized, cssXCheckKernel, cssZCheckKernel,
    sub_eq_zero]

private theorem cssCoefficient_invariants (c : CssData ι κX κZ) :
    (cssCoefficientRepresentation c).invariants = cssCodespace c := by
  classical
  ext v
  rw [Representation.mem_invariants, mem_cssCodespace_iff]
  change (∀ a : (κX ⊕ κZ) → ZMod 2,
    cssCoefficientRepresentation c (Multiplicative.ofAdd a) v = v) ↔ _
  rw [binary_rep_fixed_iff]
  simp only [cssCoefficientRepresentation_basis, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Matrix.mulVecLin_apply]

private theorem cssStabilizer_invariants (c : CssData ι κX κZ) :
    (cssStabilizerRepresentation c).invariants = cssCodespace c := by
  classical
  rw [← cssCoefficient_invariants c]
  ext v
  simp only [Representation.mem_invariants]
  constructor
  · intro h a
    exact h ((cssCoefficientLabels c).toMultiplicative a)
  · intro h g
    obtain ⟨a, ha⟩ := cssCoefficientLabels_surjective c g.toAdd
    have hh := h (Multiplicative.ofAdd a)
    change cssStabilizerRepresentation c
        (Multiplicative.ofAdd (cssCoefficientLabels c a)) v = v at hh
    rw [ha] at hh
    exact hh

private theorem cssStabilizer_character (c : CssData ι κX κZ)
    (g : Multiplicative (cssRowX c × cssRowZ c)) :
    (cssStabilizerRepresentation c).character g =
      if g = 1 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  classical
  unfold Representation.character
  change LinearMap.trace ℂ ((ι → ZMod 2) → ℂ)
    (cssPauliX (g.toAdd.1 : ι → ZMod 2) * cssPauliZ (g.toAdd.2 : ι → ZMod 2)).mulVecLin = _
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq, cssPauliXZ_trace]
  have he : g = 1 ↔ (g.toAdd.1 : ι → ZMod 2) = 0 ∧ (g.toAdd.2 : ι → ZMod 2) = 0 := by
    constructor
    · intro h
      subst g
      exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hz⟩
      change g.toAdd = (0, 0)
      apply Prod.ext <;> apply Subtype.ext
      · exact hx
      · exact hz
  simp only [he]

omit [DecidableEq ι] in

private theorem css_row_card {κ : Type*} [Fintype κ] (A : Matrix κ ι (ZMod 2))
    [Fintype ↥(LinearMap.range (Matrix.mulVecLin Aᵀ))] :
    Fintype.card ↥(LinearMap.range (Matrix.mulVecLin Aᵀ)) = 2 ^ Matrix.rank A := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  change 2 ^ Matrix.rank Aᵀ = 2 ^ Matrix.rank A
  rw [Matrix.rank_transpose]

theorem cssCodespace_finrank (c : CssData ι κX κZ) :
    Module.finrank ℂ ↥(cssCodespace c) = 2 ^ c.encodedQubits := by
  classical
  rw [← cssStabilizer_invariants c]
  let G := Multiplicative (cssRowX c × cssRowZ c)
  letI : Fintype (cssRowX c) := Fintype.ofFinite _
  letI : Fintype (cssRowZ c) := Fintype.ofFinite _
  letI : Fintype G := inferInstance
  have hgn : (Nat.card G : ℂ) ≠ 0 := by
    rw [← Fintype.card_eq_nat_card]
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card G))
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hgn
  have ha := (cssStabilizerRepresentation c).card_inv_mul_sum_char_eq_finrank
  simp only [cssStabilizer_character, Finset.sum_ite_eq', Finset.mem_univ, if_true] at ha
  have hgc : Nat.card G = 2 ^ (Matrix.rank c.hX + Matrix.rank c.hZ) := by
    rw [← Fintype.card_eq_nat_card]
    change Fintype.card (Multiplicative (cssRowX c × cssRowZ c)) = _
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod,
      css_row_card c.hX, css_row_card c.hZ, ← pow_add]
  have hbc : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by simp
  rw [hgc, hbc] at ha
  push_cast at ha
  have hr := cssRank_add_le c
  have hp : (2 : ℂ) ^ Fintype.card ι =
      2 ^ (Matrix.rank c.hX + Matrix.rank c.hZ) * 2 ^ c.encodedQubits := by
    rw [← pow_add]
    congr 1
    unfold CssData.encodedQubits
    omega
  rw [hp, inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))] at ha
  exact_mod_cast ha.symm

end Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
