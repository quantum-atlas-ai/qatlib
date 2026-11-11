/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy

/-!
# Dimension-one states and Bell-state examples

This module proves boundary cases for bipartite pure-state entanglement and explicit properties
of the four Bell states. A normalized state with either subsystem of dimension one is a product
state with Schmidt rank one. The Bell family provides the complementary two-qubit examples from
standard quantum information theory [Wilde2017].

`bell_inner` proves orthonormality, and `frontier1` combines these results with Bell-state
normalization, entanglement, a maximally mixed first marginal, and entropy `Real.log 2`.

## Main statements

* `boundary_dim_one`: product structure and Schmidt rank one at dimension-one boundaries.
* `bell_inner`: orthonormality of the Bell family.
* `bell_two_le_schmidtRank`: a lower bound of two on Bell-state Schmidt rank.
* `frontier1`: the combined boundary and Bell-state properties.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability.EntanglementBoundaryConsumers

open Qatlib
open Qatlib.Concepts.Entanglement.Separability
open Qatlib
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- Every bipartite state with left dimension one factors as the constant unit left vector
tensored with its right-coordinate slice. -/
theorem eq_tensorState_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E)) :
    ψ = TensorState (fun _ => (1 : ℂ)) (fun j => ψ (0, j)) := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [Subsingleton.elim i 0]
  simp

/-- Every bipartite state with right dimension one factors as its left-coordinate slice tensored
with the constant unit right vector. -/
theorem eq_tensorState_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1)) :
    ψ = TensorState (fun i => ψ (i, 0)) (fun _ => (1 : ℂ)) := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [Subsingleton.elim j 0]
  simp

/-- Every bipartite state with left dimension one is a product state. -/
theorem isProductState_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E)) :
    IsProductState ψ :=
  ⟨fun _ => (1 : ℂ), fun j => ψ (0, j), eq_tensorState_left_one E ψ⟩

/-- Every bipartite state with right dimension one is a product state. -/
theorem isProductState_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1)) :
    IsProductState ψ :=
  ⟨fun i => ψ (i, 0), fun _ => (1 : ℂ), eq_tensorState_right_one D ψ⟩

/-- For a normalized state with left dimension one, the right-coordinate slice is normalized. -/
theorem normalized_right_factor_of_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E))
    (hψ : Normalized ψ) : Normalized (fun j => ψ (0, j)) := by
  have hψ' : ∑ i : Fin 1 × Fin E, ‖ψ i‖ ^ 2 = 1 := hψ
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at hψ'
  exact hψ'

/-- For a normalized state with right dimension one, the left-coordinate slice is normalized. -/
theorem normalized_left_factor_of_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1))
    (hψ : Normalized ψ) : Normalized (fun i => ψ (i, 0)) := by
  have hψ' : ∑ i : Fin D × Fin 1, ‖ψ i‖ ^ 2 = 1 := hψ
  rw [Fintype.sum_prod_type] at hψ'
  simp only [Fin.sum_univ_one] at hψ'
  exact hψ'

/-- A normalized bipartite pure state has positive Schmidt rank. -/
theorem schmidtRank_pos_of_normalized (D E : ℕ) (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : 0 < schmidtRank ψ := by
  obtain ⟨r, c, u, v, -, -, -, -, hmass, -, hrank⟩ := exists_schmidtData ψ
  have hψ' : ∑ i, ‖ψ i‖ ^ 2 = 1 := hψ
  have hex : ∃ i : Fin r, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero fun i _ => by simp [hcon], hψ'] at hmass
    exact zero_ne_one hmass
  rw [hrank]
  exact (Set.ncard_pos).mpr ⟨hex.choose, hex.choose_spec⟩

/-- A normalized bipartite state is a product state of Schmidt rank one whenever either
subsystem has dimension one. -/
theorem boundary_dim_one (D E : ℕ) (hdim : D = 1 ∨ E = 1)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    IsProductState ψ ∧ schmidtRank ψ = 1 := by
  have hprod : IsProductState ψ := by
    rcases hdim with hd | he
    · subst hd; exact isProductState_left_one E ψ
    · subst he; exact isProductState_right_one D ψ
  refine ⟨hprod, ?_⟩
  have hle : schmidtRank ψ ≤ 1 :=
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.1 D E ψ).mp hprod
  have hpos := schmidtRank_pos_of_normalized D E ψ hψ
  omega

/-- The pure-state inner product is additive in its first argument. -/
private theorem inner_add_left {I : Type*} [Fintype I] [DecidableEq I]
    (φ₁ φ₂ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (φ₁ + φ₂) ψ = Qatlib.Foundations.PureStateMath.Inner φ₁ ψ + Qatlib.Foundations.PureStateMath.Inner φ₂ ψ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.add_apply, map_add, add_mul]
  rw [← Finset.sum_add_distrib]

/-- The pure-state inner product is additive in its second argument. -/
private theorem inner_add_right {I : Type*} [Fintype I] [DecidableEq I]
    (φ ψ₁ ψ₂ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ (ψ₁ + ψ₂) = Qatlib.Foundations.PureStateMath.Inner φ ψ₁ + Qatlib.Foundations.PureStateMath.Inner φ ψ₂ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

/-- Scaling the first argument of the pure-state inner product multiplies it by the conjugate
scalar. -/
private theorem inner_smul_left {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (φ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (c • φ) ψ = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply,
      Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  rw [← Finset.mul_sum]

/-- Complex conjugation fixes negative one. -/
private theorem star_neg_one : (starRingEnd ℂ) (-1 : ℂ) = -1 := by
  simp [map_neg]

/-- A Bell state is the indicated normalized superposition of two computational basis kets, with
parity and sign selected by its Boolean labels. -/
private theorem bell_eq (s : Bool × Bool) :
    bell s = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
      (Qatlib.Foundations.PureStateMath.Ket ((⟨0, by omega⟩ : Fin 2), if s.1 then (1 : Fin 2) else 0) +
        (if s.2 then (-1 : ℂ) else 1) •
          Qatlib.Foundations.PureStateMath.Ket ((⟨1, by omega⟩ : Fin 2), if !s.1 then (1 : Fin 2) else 0)) := rfl

/-- Expand the inner product of two scaled two-ket superpositions into four basis-index equality
terms. -/
private theorem inner_two_kets {I : Type*} [Fintype I] [DecidableEq I]
    (c d c' d' : ℂ) (p q p' q' : I) :
    Qatlib.Foundations.PureStateMath.Inner (c • (Qatlib.Foundations.PureStateMath.Ket p + d • Qatlib.Foundations.PureStateMath.Ket q)) (c' • (Qatlib.Foundations.PureStateMath.Ket p' + d' • Qatlib.Foundations.PureStateMath.Ket q')) =
      (starRingEnd ℂ) c * c' *
        ((if p = p' then 1 else 0) + d' * (if p = q' then 1 else 0) +
          (starRingEnd ℂ) d * ((if q = p' then 1 else 0) + d' * (if q = q' then 1 else 0))) := by
  simp only [inner_smul_left, Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_smul_right,
    inner_add_left, inner_add_right, Qatlib.Foundations.PureStateMath.inner_ket_ket]
  ring

/-- The Boolean-indexed Bell states form an orthonormal family. -/
theorem bell_inner (s t : Bool × Bool) :
    Qatlib.Foundations.PureStateMath.Inner (bell s) (bell t) = if s = t then (1 : ℂ) else 0 := by
  by_cases h : s = t
  · subst h
    rw [if_pos rfl]
    exact (normalized_iff_inner_self (bell s)).mp (bell_normalized s)
  · rw [if_neg h, bell_eq s, bell_eq t, inner_two_kets]
    fin_cases s <;> fin_cases t
    all_goals
      simp only [ite_true, ite_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, map_one, star_neg_one]
    all_goals try simp
    all_goals exact absurd rfl h

/-- Distinct Boolean label pairs determine distinct Bell state vectors. -/
theorem bell_injective : Function.Injective bell := by
  intro s t hst
  by_contra hne
  have h0 : Qatlib.Foundations.PureStateMath.Inner (bell s) (bell t) = 0 := by
    rw [bell_inner, if_neg hne]
  have h1 : Qatlib.Foundations.PureStateMath.Inner (bell t) (bell t) = 1 :=
    (normalized_iff_inner_self (bell t)).mp (bell_normalized t)
  rw [hst] at h0
  exact zero_ne_one (h0.symm.trans h1)

/-- Every Bell state has Schmidt rank at least two. -/
theorem bell_two_le_schmidtRank (s : Bool × Bool) : 2 ≤ schmidtRank (bell s) := by
  obtain ⟨-, hent, hm⟩ := Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.2.1 s
  have hiff : schmidtRank (bell s) ≤ 1 → IsProductState (bell s) :=
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.1 _ _ _).mpr
  by_contra hle
  push Not at hle
  have hle' : schmidtRank (bell s) ≤ 1 := by omega
  exact hent.2 (hiff hle')

/-- Dimension-one bipartite states have Schmidt rank one, and the Bell family is orthonormal,
normalized, and entangled, with maximally mixed first marginal and entropy `Real.log 2`. -/
theorem frontier1 :
    (∀ (D E : ℕ), D = 1 ∨ E = 1 → ∀ ψ : QState (Fin D × Fin E), Normalized ψ →
      IsProductState ψ ∧ schmidtRank ψ = 1) ∧
    (∀ s t : Bool × Bool, Qatlib.Foundations.PureStateMath.Inner (bell s) (bell t) = if s = t then (1 : ℂ) else 0) ∧
    (∀ s : Bool × Bool,
      Normalized (bell s) ∧ IsEntangled (bell s) ∧ 2 ≤ schmidtRank (bell s) ∧
        PartialTrace (outerProduct (bell s)) = (1 / 2 : ℂ) • (1 : Operator 2) ∧
        entropy (bell s) (bell_normalized s) = Real.log 2) := by
  refine ⟨fun D E hdim ψ hψ => boundary_dim_one D E hdim ψ hψ,
    fun s t => bell_inner s t, ?_⟩
  intro s
  obtain ⟨hn, hent, hm⟩ := Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.2.1 s
  exact ⟨hn, hent, bell_two_le_schmidtRank s, hm, entropy_bell s⟩

end Qatlib.Concepts.Entanglement.Separability.EntanglementBoundaryConsumers

end
