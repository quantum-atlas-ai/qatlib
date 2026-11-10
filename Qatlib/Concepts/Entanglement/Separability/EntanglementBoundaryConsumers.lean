/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy
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

theorem eq_tensorState_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E)) :
    ψ = TensorState (fun _ => (1 : ℂ)) (fun j => ψ (0, j)) := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [Subsingleton.elim i 0]
  simp

theorem eq_tensorState_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1)) :
    ψ = TensorState (fun i => ψ (i, 0)) (fun _ => (1 : ℂ)) := by
  funext p
  obtain ⟨i, j⟩ := p
  rw [Subsingleton.elim j 0]
  simp

theorem isProductState_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E)) :
    IsProductState ψ :=
  ⟨fun _ => (1 : ℂ), fun j => ψ (0, j), eq_tensorState_left_one E ψ⟩

theorem isProductState_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1)) :
    IsProductState ψ :=
  ⟨fun i => ψ (i, 0), fun _ => (1 : ℂ), eq_tensorState_right_one D ψ⟩

theorem normalized_right_factor_of_left_one (E : ℕ) (ψ : QState (Fin 1 × Fin E))
    (hψ : Normalized ψ) : Normalized (fun j => ψ (0, j)) := by
  have hψ' : ∑ i : Fin 1 × Fin E, ‖ψ i‖ ^ 2 = 1 := hψ
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at hψ'
  exact hψ'

theorem normalized_left_factor_of_right_one (D : ℕ) (ψ : QState (Fin D × Fin 1))
    (hψ : Normalized ψ) : Normalized (fun i => ψ (i, 0)) := by
  have hψ' : ∑ i : Fin D × Fin 1, ‖ψ i‖ ^ 2 = 1 := hψ
  rw [Fintype.sum_prod_type] at hψ'
  simp only [Fin.sum_univ_one] at hψ'
  exact hψ'

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

private theorem inner_add_left {I : Type*} [Fintype I] [DecidableEq I]
    (φ₁ φ₂ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (φ₁ + φ₂) ψ = Qatlib.Foundations.PureStateMath.Inner φ₁ ψ + Qatlib.Foundations.PureStateMath.Inner φ₂ ψ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.add_apply, map_add, add_mul]
  rw [← Finset.sum_add_distrib]

private theorem inner_add_right {I : Type*} [Fintype I] [DecidableEq I]
    (φ ψ₁ ψ₂ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner φ (ψ₁ + ψ₂) = Qatlib.Foundations.PureStateMath.Inner φ ψ₁ + Qatlib.Foundations.PureStateMath.Inner φ ψ₂ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply,
    Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

private theorem inner_smul_left {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (φ ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (c • φ) ψ = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  rw [Qatlib.Foundations.PureStateMath.inner_apply,
      Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  rw [← Finset.mul_sum]

private theorem star_neg_one : (starRingEnd ℂ) (-1 : ℂ) = -1 := by
  simp [map_neg]

private theorem bell_eq (s : Bool × Bool) :
    bell s = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
      (Qatlib.Foundations.PureStateMath.Ket ((⟨0, by omega⟩ : Fin 2), if s.1 then (1 : Fin 2) else 0) +
        (if s.2 then (-1 : ℂ) else 1) •
          Qatlib.Foundations.PureStateMath.Ket ((⟨1, by omega⟩ : Fin 2), if !s.1 then (1 : Fin 2) else 0)) := rfl

private theorem inner_two_kets {I : Type*} [Fintype I] [DecidableEq I]
    (c d c' d' : ℂ) (p q p' q' : I) :
    Qatlib.Foundations.PureStateMath.Inner (c • (Qatlib.Foundations.PureStateMath.Ket p + d • Qatlib.Foundations.PureStateMath.Ket q)) (c' • (Qatlib.Foundations.PureStateMath.Ket p' + d' • Qatlib.Foundations.PureStateMath.Ket q')) =
      (starRingEnd ℂ) c * c' *
        ((if p = p' then 1 else 0) + d' * (if p = q' then 1 else 0) +
          (starRingEnd ℂ) d * ((if q = p' then 1 else 0) + d' * (if q = q' then 1 else 0))) := by
  simp only [inner_smul_left, Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_smul_right,
    inner_add_left, inner_add_right, Qatlib.Foundations.PureStateMath.inner_ket_ket]
  ring

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

theorem bell_injective : Function.Injective bell := by
  intro s t hst
  by_contra hne
  have h0 : Qatlib.Foundations.PureStateMath.Inner (bell s) (bell t) = 0 := by
    rw [bell_inner, if_neg hne]
  have h1 : Qatlib.Foundations.PureStateMath.Inner (bell t) (bell t) = 1 :=
    (normalized_iff_inner_self (bell t)).mp (bell_normalized t)
  rw [hst] at h0
  exact zero_ne_one (h0.symm.trans h1)

theorem bell_two_le_schmidtRank (s : Bool × Bool) : 2 ≤ schmidtRank (bell s) := by
  obtain ⟨-, hent, hm⟩ := Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.2.1 s
  have hiff : schmidtRank (bell s) ≤ 1 → IsProductState (bell s) :=
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.g1.2.1 _ _ _).mpr
  by_contra hle
  push Not at hle
  have hle' : schmidtRank (bell s) ≤ 1 := by omega
  exact hent.2 (hiff hle')

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
