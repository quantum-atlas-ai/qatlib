/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LiftingWu25.ProtocolSetup.HybridModel
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# GadgetTrace — the valid-pair count of Proposition 3.5

Wu--Yang--Yao, fixed arXiv:2511.17227v2, Section 3, proof of Proposition 3.4.

The trace estimate of Proposition 3.4 reduces to counting the pairs
`w₁ ∈ Λ^{S₁∪T₂}`, `w₂ ∈ Λ^{S₂∪T₁}` that satisfy

* `(w₁)_{A₁∪A₂} = (w₂)_{A₁∪A₂}`,
* `(w₁)_{B₁∪C₂} = 0`,
* `(w₂)_{C₁∪B₂} = 0`,

where `Aᵢ = Sᵢ ∩ Tᵢ`, `Bᵢ = Sᵢ \ Tᵢ`, `Cᵢ = Tᵢ \ Sᵢ`. The paper's bound is

`2^{b(|S₁∪T₂|+|S₂∪T₁|)} · 2^{-b(|S₁|+|T₁|+|S₂|+|T₂|)/4}`.

The two ingredients are (i) the coverage identity
`A₁ ∪ A₂ ∪ C₁ ∪ B₂ = S₂ ∪ T₁`, which says that every coordinate of `w₂` is pinned
by the constraints, and (ii) the combinatorial inequality
`|B₁ ∪ C₂| + |S₂ ∪ T₁| ≥ (|S₁|+|T₁|+|S₂|+|T₂|)/4`.

Boundary: this module proves the coverage identities, the cardinality inequality
and the uniqueness of the partner `w₂` for a given `w₁`. The numerical pair count
`2^{b(|S₁∪T₂|+|S₂∪T₁|)} · 2^{-b(·)/4}` itself is stated over reals with a
quarter exponent and is not formalized here; the three lemmas below are exactly
its inputs.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.LiftingWu25.DenseLift

open Finset
open Qatlib.Papers.LiftingWu25.ProtocolSetup

variable {ι : Type*} [DecidableEq ι]

/-- `A₁ = S₁ ∩ T₁`: coordinates shared by `S₁` and `T₁`. -/
def A1 (S1 T1 : Finset ι) : Finset ι := S1 ∩ T1

/-- `B₁ = S₁ \ T₁`. -/
def B1 (S1 T1 : Finset ι) : Finset ι := S1 \ T1

/-- `C₁ = T₁ \ S₁`. -/
def C1 (S1 T1 : Finset ι) : Finset ι := T1 \ S1

/-- `A₂ = S₂ ∩ T₂`. -/
def A2 (S2 T2 : Finset ι) : Finset ι := S2 ∩ T2

/-- `B₂ = S₂ \ T₂`. -/
def B2 (S2 T2 : Finset ι) : Finset ι := S2 \ T2

/-- `C₂ = T₂ \ S₂`. -/
def C2 (S2 T2 : Finset ι) : Finset ι := T2 \ S2

/-- The coordinates of `w₂` are exactly those pinned by the validity conditions:
`A₁ ∪ A₂ ∪ C₁ ∪ B₂ = S₂ ∪ T₁`. -/
theorem cover_w2 (S1 T1 S2 T2 : Finset ι) :
    (A1 S1 T1 ∪ A2 S2 T2) ∪ (C1 S1 T1 ∪ B2 S2 T2) = S2 ∪ T1 := by
  ext i
  simp only [A1, A2, B2, C1, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The coordinates of `w₁` together with `S₂ ∪ T₁` cover all of
`S₁ ∪ T₁ ∪ S₂ ∪ T₂`, which is the identity used to bound the fixed coordinates. -/
theorem cover_w1 (S1 T1 S2 T2 : Finset ι) :
    (B1 S1 T1 ∪ C2 S2 T2) ∪ (S2 ∪ T1) = S1 ∪ T1 ∪ S2 ∪ T2 := by
  ext i
  simp only [B1, C2, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- The combinatorial inequality at the end of the proof of Proposition 3.5:
`|B₁ ∪ C₂| + |S₂ ∪ T₁| ≥ (|S₁| + |T₁| + |S₂| + |T₂|)/4`. -/
theorem card_fixed_ge (S1 T1 S2 T2 : Finset ι) :
    S1.card + T1.card + S2.card + T2.card
      ≤ 4 * ((B1 S1 T1 ∪ C2 S2 T2).card + (S2 ∪ T1).card) := by
  have hcover : (B1 S1 T1 ∪ C2 S2 T2) ∪ (S2 ∪ T1) = S1 ∪ T1 ∪ S2 ∪ T2 := cover_w1 S1 T1 S2 T2
  have hunion : ((B1 S1 T1 ∪ C2 S2 T2) ∪ (S2 ∪ T1)).card
      ≤ (B1 S1 T1 ∪ C2 S2 T2).card + (S2 ∪ T1).card := Finset.card_union_le _ _
  have hS1 : S1.card ≤ (S1 ∪ T1 ∪ S2 ∪ T2).card := by
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_union]
    tauto
  have hT1 : T1.card ≤ (S1 ∪ T1 ∪ S2 ∪ T2).card := by
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_union]
    tauto
  have hS2 : S2.card ≤ (S1 ∪ T1 ∪ S2 ∪ T2).card := by
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_union]
    tauto
  have hT2 : T2.card ≤ (S1 ∪ T1 ∪ S2 ∪ T2).card := by
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_union]
    tauto
  rw [hcover] at hunion
  omega

/-- The assignments on `S` that vanish on `Z ⊆ S` are in bijection with the freely
chosen assignments on `S \ Z`. -/
def vanishEquiv (S Z : Finset ι) (hZ : Z ⊆ S) (b : ℕ) :
    { w : (↥S → Lambda b) // ∀ i : ↥Z, w ⟨i.1, hZ i.2⟩ = (fun _ => false) }
      ≃ (↥(S \ Z) → Lambda b) where
  toFun w x := w.1 ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩
  invFun v :=
    ⟨fun s => if h : (s : ι) ∈ Z then (fun _ => false)
      else v ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, h⟩⟩, by
      intro i
      simp [i.2]⟩
  left_inv w := by
    apply Subtype.ext
    funext s
    by_cases h : (s : ι) ∈ Z
    · simp only [h, dif_pos]
      exact (w.2 ⟨s.1, h⟩).symm
    · simp only [h, dif_neg, not_false_iff]
  right_inv v := by
    funext x
    have hx := (Finset.mem_sdiff.mp x.2).2
    simp only [hx, dif_neg, not_false_iff]

/-- The number of `Λ`-valued assignments on `S` that vanish on `Z ⊆ S` is
`2^{b(|S| - |Z|)}`. -/
theorem card_vanish (S Z : Finset ι) (hZ : Z ⊆ S) (b : ℕ) :
    Fintype.card { w : (↥S → Lambda b) // ∀ i : ↥Z, w ⟨i.1, hZ i.2⟩ = (fun _ => false) }
      = 2 ^ (b * (S.card - Z.card)) := by
  rw [Fintype.card_congr (vanishEquiv S Z hZ b)]
  have hcard : Fintype.card (↥(S \ Z)) = S.card - Z.card := by
    rw [Fintype.card_coe, Finset.card_sdiff, Finset.inter_eq_left.mpr hZ]
  have hLam : Fintype.card (Lambda b) = 2 ^ b := by
    simp [Lambda]
  rw [Fintype.card_fun, hcard, hLam, ← pow_mul]


/-- `A₁ ∪ A₂ ⊆ S₁ ∪ T₂`. -/
theorem sub_A_w1 (S1 T1 S2 T2 : Finset ι) : A1 S1 T1 ∪ A2 S2 T2 ⊆ S1 ∪ T2 := by
  intro i hi
  simp only [A1, A2, Finset.mem_union, Finset.mem_inter] at hi ⊢
  tauto

/-- `A₁ ∪ A₂ ⊆ S₂ ∪ T₁`. -/
theorem sub_A_w2 (S1 T1 S2 T2 : Finset ι) : A1 S1 T1 ∪ A2 S2 T2 ⊆ S2 ∪ T1 := by
  intro i hi
  simp only [A1, A2, Finset.mem_union, Finset.mem_inter] at hi ⊢
  tauto

/-- `B₁ ∪ C₂ ⊆ S₁ ∪ T₂`. -/
theorem sub_B_w1 (S1 T1 S2 T2 : Finset ι) : B1 S1 T1 ∪ C2 S2 T2 ⊆ S1 ∪ T2 := by
  intro i hi
  simp only [B1, C2, Finset.mem_union, Finset.mem_sdiff] at hi ⊢
  tauto

/-- `C₁ ∪ B₂ ⊆ S₂ ∪ T₁`. -/
theorem sub_C_w2 (S1 T1 S2 T2 : Finset ι) : C1 S1 T1 ∪ B2 S2 T2 ⊆ S2 ∪ T1 := by
  intro i hi
  simp only [C1, B2, Finset.mem_union, Finset.mem_sdiff] at hi ⊢
  tauto

/-- The validity conditions of Proposition 3.5 on a pair `(w₁,w₂)`. -/
def ValidPair (S1 T1 S2 T2 : Finset ι) (b : ℕ)
    (w1 : ↥(S1 ∪ T2) → Lambda b) (w2 : ↥(S2 ∪ T1) → Lambda b) : Prop :=
  (∀ i : ↥(A1 S1 T1 ∪ A2 S2 T2),
      w1 ⟨i.1, sub_A_w1 S1 T1 S2 T2 i.2⟩ = w2 ⟨i.1, sub_A_w2 S1 T1 S2 T2 i.2⟩) ∧
    (∀ i : ↥(B1 S1 T1 ∪ C2 S2 T2), w1 ⟨i.1, sub_B_w1 S1 T1 S2 T2 i.2⟩ = (fun _ => false)) ∧
      (∀ i : ↥(C1 S1 T1 ∪ B2 S2 T2),
        w2 ⟨i.1, sub_C_w2 S1 T1 S2 T2 i.2⟩ = (fun _ => false))

/-- A pair is determined by its first component: for fixed `w₁` there is at most one
valid `w₂`. This is where the coverage identity `A₁ ∪ A₂ ∪ C₁ ∪ B₂ = S₂ ∪ T₁` is used. -/
theorem validPair_w2_unique {S1 T1 S2 T2 : Finset ι} {b : ℕ}
    {w1 : ↥(S1 ∪ T2) → Lambda b} {w2 w2' : ↥(S2 ∪ T1) → Lambda b}
    (h : ValidPair S1 T1 S2 T2 b w1 w2) (h' : ValidPair S1 T1 S2 T2 b w1 w2') : w2 = w2' := by
  funext x
  have hcov : (x : ι) ∈ (A1 S1 T1 ∪ A2 S2 T2) ∪ (C1 S1 T1 ∪ B2 S2 T2) := by
    rw [cover_w2 S1 T1 S2 T2]
    exact x.2
  rcases Finset.mem_union.mp hcov with hA | hC
  · have h1 := h.1 ⟨x.1, hA⟩
    have h2 := h'.1 ⟨x.1, hA⟩
    exact h1.symm.trans h2
  · have h1 := h.2.2 ⟨x.1, hC⟩
    have h2 := h'.2.2 ⟨x.1, hC⟩
    exact h1.trans h2.symm

/-- Proposition 3.5: the number of valid pairs `(w₁,w₂)` is at most
`2^{b(|S₁∪T₂| - |B₁∪C₂|)}`; combined with `card_fixed_ge` this is the paper's
`2^{b(|S₁∪T₂|+|S₂∪T₁|)} · 2^{-b(|S₁|+|T₁|+|S₂|+|T₂|)/4}`. -/
theorem prop35_count (S1 T1 S2 T2 : Finset ι) (b : ℕ) :
    Fintype.card { p : (↥(S1 ∪ T2) → Lambda b) × (↥(S2 ∪ T1) → Lambda b) //
        ValidPair S1 T1 S2 T2 b p.1 p.2 }
      ≤ 2 ^ (b * ((S1 ∪ T2).card - (B1 S1 T1 ∪ C2 S2 T2).card)) := by
  let φ : { p : (↥(S1 ∪ T2) → Lambda b) × (↥(S2 ∪ T1) → Lambda b) //
        ValidPair S1 T1 S2 T2 b p.1 p.2 }
      → { w : ↥(S1 ∪ T2) → Lambda b //
          ∀ i : ↥(B1 S1 T1 ∪ C2 S2 T2), w ⟨i.1, sub_B_w1 S1 T1 S2 T2 i.2⟩ = (fun _ => false) } :=
    fun p => ⟨p.1.1, p.2.2.1⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨u1, u2⟩, hu⟩ ⟨⟨v1, v2⟩, hv⟩ heq
    have huv : u1 = v1 := congrArg Subtype.val heq
    subst huv
    have hw2 : u2 = v2 := validPair_w2_unique hu hv
    subst hw2
    rfl
  calc Fintype.card { p : (↥(S1 ∪ T2) → Lambda b) × (↥(S2 ∪ T1) → Lambda b) //
        ValidPair S1 T1 S2 T2 b p.1 p.2 }
      ≤ Fintype.card { w : ↥(S1 ∪ T2) → Lambda b //
          ∀ i : ↥(B1 S1 T1 ∪ C2 S2 T2), w ⟨i.1, sub_B_w1 S1 T1 S2 T2 i.2⟩ = (fun _ => false) } :=
        Fintype.card_le_of_injective φ hinj
    _ = 2 ^ (b * ((S1 ∪ T2).card - (B1 S1 T1 ∪ C2 S2 T2).card)) :=
        card_vanish _ _ (sub_B_w1 S1 T1 S2 T2) b


end Qatlib.Papers.LiftingWu25.DenseLift
