/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.EttingerHSP04.MainResults

open Qatlib.Foundations.PureStateMath
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]

def IsHPeriodic (f : G → β) (H : Subgroup G) : Prop :=
  ∀ g h : G, h ∈ H → f (g * h) = f g

def IsStrictlyHPeriodic (f : G → β) (H : Subgroup G) : Prop :=
  IsHPeriodic f H ∧ ∀ g h : G, f (g * h) = f g → h ∈ H

theorem IsHPeriodic.mono {f : G → β} {H K : Subgroup G} (hKH : K ≤ H)
    (hf : IsHPeriodic f H) : IsHPeriodic f K := by
  intro g k hk
  exact hf g k (hKH hk)

theorem isHPeriodic_bot (f : G → β) : IsHPeriodic f (⊥ : Subgroup G) := by
  intro g h hh
  have h1 : h = 1 := by simpa using hh
  subst h1
  simp

theorem IsStrictlyHPeriodic.periodic_iff {f : G → β} {H : Subgroup G}
    (hf : IsStrictlyHPeriodic f H) (g h : G) : f (g * h) = f g ↔ h ∈ H :=
  ⟨hf.2 g h, hf.1 g h⟩

noncomputable def cosetAvg (K : Subgroup G) (ψ : QState G) : QState G :=
  fun g => ((Fintype.card ↥K : ℂ))⁻¹ * ∑ k : ↥K, ψ (g * (k : G))

def RightKInvariant (K : Subgroup G) (ψ : QState G) : Prop :=
  ∀ g k : G, k ∈ K → ψ (g * k) = ψ g

theorem cosetAvg_eq_self_of_invariant {K : Subgroup G} {ψ : QState G}
    (hψ : RightKInvariant K ψ) : cosetAvg K ψ = ψ := by
  funext g
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hcard : ((Fintype.card ↥K : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ↥K)).ne'
  have hsum : (∑ k : ↥K, ψ (g * (k : G))) = (Fintype.card ↥K : ℂ) * ψ g := by
    rw [Finset.sum_congr rfl (fun (k : ↥K) _ => hψ g (k : G) k.property),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [cosetAvg, hsum]
  field_simp

theorem cosetAvg_invariant (K : Subgroup G) (ψ : QState G) {g k : G} (hk : k ∈ K) :
    cosetAvg K ψ (g * k) = cosetAvg K ψ g := by
  simp only [cosetAvg]
  congr 1

  have h := Equiv.sum_comp (Equiv.mulLeft (⟨k, hk⟩ : ↥K))
    (fun k' : ↥K => ψ (g * (k' : G)))
  calc
    (∑ k' : ↥K, ψ ((g * k) * (k' : G)))
        = ∑ k' : ↥K, ψ (g * (((⟨k, hk⟩ : ↥K) * k' : ↥K) : G)) := by
          apply Finset.sum_congr rfl
          intro k' _
          rw [Subgroup.coe_mul, mul_assoc]
    _ = ∑ k' : ↥K, ψ (g * (k' : G)) := h

theorem cosetAvg_idem (K : Subgroup G) (ψ : QState G) :
    cosetAvg K (cosetAvg K ψ) = cosetAvg K ψ := by
  funext g
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hcard : ((Fintype.card ↥K : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ↥K)).ne'
  have hinner : ∀ k : ↥K,
      (∑ k' : ↥K, ψ ((g * (k : G)) * (k' : G))) = ∑ k' : ↥K, ψ (g * (k' : G)) := by
    intro k
    have h := Equiv.sum_comp (Equiv.mulLeft k) (fun k' : ↥K => ψ (g * (k' : G)))
    calc
      (∑ k' : ↥K, ψ ((g * (k : G)) * (k' : G)))
          = ∑ k' : ↥K, ψ (g * ((k * k' : ↥K) : G)) := by
            apply Finset.sum_congr rfl
            intro k' _
            rw [Subgroup.coe_mul, mul_assoc]
      _ = ∑ k' : ↥K, ψ (g * (k' : G)) := h
  simp only [cosetAvg]
  rw [show (∑ k : ↥K, ((Fintype.card ↥K : ℂ))⁻¹ * ∑ k' : ↥K,
        ψ ((g * (k : G)) * (k' : G)))
      = ((Fintype.card ↥K : ℂ))⁻¹ * ∑ k : ↥K, ∑ k' : ↥K,
        ψ ((g * (k : G)) * (k' : G)) by
        rw [Finset.mul_sum]]
  simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem cosetAvg_add (K : Subgroup G) (ψ φ : QState G) :
    cosetAvg K (ψ + φ) = cosetAvg K ψ + cosetAvg K φ := by
  funext g
  simp only [cosetAvg, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem cosetAvg_smul (K : Subgroup G) (a : ℂ) (ψ : QState G) :
    cosetAvg K (a • ψ) = a • cosetAvg K ψ := by
  funext g
  simp only [cosetAvg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem cosetAvg_contract {K : Subgroup G} (ψ : QState G) :
    (∑ g, ‖cosetAvg K ψ g‖ ^ 2) ≤ ∑ g, ‖ψ g‖ ^ 2 := by
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hcard : 0 < Fintype.card ↥K := Fintype.card_pos
  have hcardne : ((Fintype.card ↥K : ℂ)) ≠ 0 := by exact_mod_cast hcard.ne'
  have hcardR : (0:ℝ) < (Fintype.card ↥K : ℝ) := by exact_mod_cast hcard

  have hpoint : ∀ g : G, ‖cosetAvg K ψ g‖ ^ 2 ≤
      ((Fintype.card ↥K : ℝ))⁻¹ * ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2 := by
    intro g
    have hnorm : ‖cosetAvg K ψ g‖ =
        ((Fintype.card ↥K : ℝ))⁻¹ * ‖∑ k : ↥K, ψ (g * (k : G))‖ := by
      simp only [cosetAvg, norm_mul]
      have : ‖((Fintype.card ↥K : ℂ))⁻¹‖ = ((Fintype.card ↥K : ℝ))⁻¹ := by
        rw [norm_inv, RCLike.norm_natCast]
      rw [this]
    rw [hnorm]
    have hcs : ‖∑ k : ↥K, ψ (g * (k : G))‖ ^ 2 ≤
        (Fintype.card ↥K : ℝ) * ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ↥K)
        (fun _ => (1 : ℝ)) (fun k => ‖ψ (g * (k : G))‖)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
      have hnn : 0 ≤ ∑ k : ↥K, ‖ψ (g * (k : G))‖ :=
        Finset.sum_nonneg (fun k _ => norm_nonneg _)
      have hnormsum : ‖∑ k : ↥K, ψ (g * (k : G))‖ ≤ ∑ k : ↥K, ‖ψ (g * (k : G))‖ :=
        norm_sum_le (Finset.univ : Finset ↥K) (fun k : ↥K => ψ (g * (k : G)))
      nlinarith [norm_nonneg (∑ k : ↥K, ψ (g * (k : G))), hnn]
    have hinv : (0:ℝ) ≤ ((Fintype.card ↥K : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hcardR)
    calc
      (((Fintype.card ↥K : ℝ))⁻¹ * ‖∑ k : ↥K, ψ (g * (k : G))‖) ^ 2
          = ((Fintype.card ↥K : ℝ))⁻¹ ^ 2 * ‖∑ k : ↥K, ψ (g * (k : G))‖ ^ 2 := by ring
      _ ≤ ((Fintype.card ↥K : ℝ))⁻¹ ^ 2 *
            ((Fintype.card ↥K : ℝ) * ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = ((Fintype.card ↥K : ℝ))⁻¹ * ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2 := by
          field_simp

  calc
    (∑ g, ‖cosetAvg K ψ g‖ ^ 2)
        ≤ ∑ g, ((Fintype.card ↥K : ℝ))⁻¹ * ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2 :=
          Finset.sum_le_sum (fun g _ => hpoint g)
    _ = ((Fintype.card ↥K : ℝ))⁻¹ * ∑ g, ∑ k : ↥K, ‖ψ (g * (k : G))‖ ^ 2 := by
          rw [Finset.mul_sum]
    _ = ((Fintype.card ↥K : ℝ))⁻¹ * ∑ k : ↥K, ∑ g, ‖ψ (g * (k : G))‖ ^ 2 := by
          rw [Finset.sum_comm]
    _ = ((Fintype.card ↥K : ℝ))⁻¹ * ∑ _k : ↥K, ∑ g, ‖ψ g‖ ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          have h := Equiv.sum_comp (Equiv.mulRight (k : G)) (fun g => ‖ψ g‖ ^ 2)
          simpa using h
    _ = ∑ g, ‖ψ g‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

noncomputable def initialCouplet (f : G → β) : QState (G × β) :=
  fun p => if p.2 = f p.1 then ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ else 0

theorem initialCouplet_normalized (f : G → β) : Normalized (initialCouplet f) := by
  have hNpos : 0 < Fintype.card G := Fintype.card_pos
  have hNposR : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hsqrt : (0:ℝ) < Real.sqrt (Fintype.card G : ℝ) := Real.sqrt_pos_of_pos hNposR
  have hnorm : ‖((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹‖ =
      (Real.sqrt (Fintype.card G : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
  have hterm : ∀ g : G, (∑ b : β, ‖initialCouplet f (g, b)‖ ^ 2) =
      (Real.sqrt (Fintype.card G : ℝ))⁻¹ ^ 2 := by
    intro g
    rw [Finset.sum_eq_single (f g)]
    · simp only [initialCouplet, ↓reduceIte, hnorm]
    · intro b _ hb
      simp only [initialCouplet, if_neg hb, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
    · intro h
      exact absurd (Finset.mem_univ (f g)) h
  unfold Normalized
  rw [Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hs : (Real.sqrt (Fintype.card G : ℝ))⁻¹ ^ 2 = ((Fintype.card G : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hNposR.le]
  rw [hs]
  exact mul_inv_cancel₀ hNposR.ne'

noncomputable def coupletAvg (K : Subgroup G) (ψ : QState (G × β)) : QState (G × β) :=
  fun p => ((Fintype.card ↥K : ℂ))⁻¹ * ∑ k : ↥K, ψ (p.1 * (k : G), p.2)

theorem coupletAvg_eq_self_of_periodic {K : Subgroup G} {f : G → β}
    (hf : IsHPeriodic f K) : coupletAvg K (initialCouplet f) = initialCouplet f := by
  funext p
  obtain ⟨g, b⟩ := p
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hcard : ((Fintype.card ↥K : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ↥K)).ne'
  have hterm : ∀ k : ↥K, initialCouplet f (g * (k : G), b) = initialCouplet f (g, b) := by
    intro k
    simp only [initialCouplet]
    rw [hf g (k : G) k.property]
  simp only [coupletAvg]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

theorem coupletAvg_add (K : Subgroup G) (ψ φ : QState (G × β)) :
    coupletAvg K (ψ + φ) = coupletAvg K ψ + coupletAvg K φ := by
  funext p
  simp only [coupletAvg, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem coupletAvg_smul (K : Subgroup G) (a : ℂ) (ψ : QState (G × β)) :
    coupletAvg K (a • ψ) = a • coupletAvg K ψ := by
  funext p
  simp only [coupletAvg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

noncomputable def coupletAvgLM (K : Subgroup G) :
    QState (G × β) →ₗ[ℂ] QState (G × β) where
  toFun := coupletAvg K
  map_add' := coupletAvg_add K
  map_smul' := coupletAvg_smul K

theorem coupletAvg_contract (K : Subgroup G) (ψ : QState (G × β)) :
    (∑ p : G × β, ‖coupletAvg K ψ p‖ ^ 2) ≤ ∑ p : G × β, ‖ψ p‖ ^ 2 := by

  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

  have hslice' : ∀ (g : G) (b : β), coupletAvg K ψ (g, b) =
      cosetAvg K (fun x => ψ (x, b)) g := by
    intro g b
    simp [coupletAvg, cosetAvg]
  simp only [hslice']
  have hswapL : (∑ g : G, ∑ b : β, ‖cosetAvg K (fun x => ψ (x, b)) g‖ ^ 2)
      = ∑ b : β, ∑ g : G, ‖cosetAvg K (fun x => ψ (x, b)) g‖ ^ 2 :=
    Finset.sum_comm
  have hswapR : (∑ g : G, ∑ b : β, ‖ψ (g, b)‖ ^ 2) =
      ∑ b : β, ∑ g : G, ‖ψ (g, b)‖ ^ 2 := Finset.sum_comm
  rw [hswapL, hswapR]
  apply Finset.sum_le_sum
  intro b _
  exact cosetAvg_contract (fun x => ψ (x, b))

noncomputable def multisetState (ψ : QState (G × β)) (s : ℕ) :
    QState (Fin s → G × β) :=
  fun p => ∏ i, ψ (p i)

noncomputable def projS (K : Subgroup G) (s : ℕ)
    (φ : QState (Fin s → G × β)) : QState (Fin s → G × β) :=
  fun p => ((Fintype.card ↥K : ℂ) ^ s)⁻¹ *
    ∑ kvec : (Fin s → ↥K), φ (fun i => ((p i).1 * (kvec i : G), (p i).2))

theorem projS_multisetState (K : Subgroup G) (ψ : QState (G × β)) (s : ℕ) :
    projS K s (multisetState ψ s) = multisetState (coupletAvg K ψ) s := by
  funext p
  simp only [projS, multisetState, coupletAvg]
  have hfac : (∑ kvec : (Fin s → ↥K),
        ∏ i, ψ ((p i).1 * ((kvec i : ↥K) : G), (p i).2))
      = ∏ i : Fin s, ∑ k : ↥K, ψ ((p i).1 * (k : G), (p i).2) := by
    rw [← Finset.sum_prod_piFinset]
    simp
  rw [hfac, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [inv_pow]

theorem projS_add (K : Subgroup G) (s : ℕ) (φ ψ : QState (Fin s → G × β)) :
    projS K s (φ + ψ) = projS K s φ + projS K s ψ := by
  funext p
  simp only [projS, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem projS_smul (K : Subgroup G) (s : ℕ) (a : ℂ)
    (φ : QState (Fin s → G × β)) :
    projS K s (a • φ) = a • projS K s φ := by
  funext p
  simp only [projS, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

noncomputable def projSLM (K : Subgroup G) (s : ℕ) :
    QState (Fin s → G × β) →ₗ[ℂ] QState (Fin s → G × β) where
  toFun := projS K s
  map_add' := projS_add K s
  map_smul' := projS_smul K s

theorem projS_fixes_multisetState_of_periodic {K : Subgroup G} {f : G → β}
    (hf : IsHPeriodic f K) (s : ℕ) :
    projS K s (multisetState (initialCouplet f) s) =
      multisetState (initialCouplet f) s := by
  rw [projS_multisetState, coupletAvg_eq_self_of_periodic hf]

theorem multisetState_normSq (ψ : QState (G × β)) (s : ℕ) :
    (∑ p : Fin s → G × β, ‖multisetState ψ s p‖ ^ 2) =
      (∑ q : G × β, ‖ψ q‖ ^ 2) ^ s := by
  simp only [multisetState]
  have hpt : ∀ p : (Fin s → G × β), ‖∏ i, ψ (p i)‖ ^ 2 = ∏ i, ‖ψ (p i)‖ ^ 2 := by
    intro p
    rw [norm_prod, Finset.prod_pow]
  calc
    (∑ p : Fin s → G × β, ‖∏ i, ψ (p i)‖ ^ 2)
        = ∑ p : Fin s → G × β, ∏ i, ‖ψ (p i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro p _
          exact hpt p
    _ = ∏ _i : Fin s, ∑ q : G × β, ‖ψ q‖ ^ 2 := by
          rw [← Finset.sum_prod_piFinset]
          simp
    _ = (∑ q : G × β, ‖ψ q‖ ^ 2) ^ s := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem projS_normSq_le (K : Subgroup G) (ψ : QState (G × β)) (s : ℕ)
    (h : ∑ q : G × β, ‖coupletAvg K ψ q‖ ^ 2 ≤ (1/2 : ℝ)) :
    ∑ p : Fin s → G × β, ‖projS K s (multisetState ψ s) p‖ ^ 2 ≤ (1/2 : ℝ) ^ s := by
  rw [projS_multisetState, multisetState_normSq]
  exact pow_le_pow_left₀ (by positivity) h s

variable {I : Type*} [Fintype I]

noncomputable def stateNorm (ψ : QState I) : ℝ :=
  ‖(EuclideanSpace.equiv I ℂ).symm ψ‖

theorem stateNorm_sq (ψ : QState I) :
    stateNorm ψ ^ 2 = ∑ i, ‖ψ i‖ ^ 2 := by
  rw [stateNorm, EuclideanSpace.norm_sq_eq]
  simp

theorem stateNorm_add_le (u v : QState I) :
    stateNorm (u + v) ≤ stateNorm u + stateNorm v := by
  rw [stateNorm]
  have h : (EuclideanSpace.equiv I ℂ).symm (u + v) =
      (EuclideanSpace.equiv I ℂ).symm u + (EuclideanSpace.equiv I ℂ).symm v :=
    (EuclideanSpace.equiv I ℂ).symm.map_add u v
  rw [h]
  exact norm_add_le _ _

theorem stateNorm_sub_le (u v : QState I) :
    stateNorm u ≤ stateNorm v + stateNorm (u - v) := by
  have h := stateNorm_add_le v (u - v)
  rwa [add_sub_cancel] at h

section Tensor

variable {σ Ω : Type*}

noncomputable def prodState (q : QState σ) (φ : QState Ω) : QState (σ × Ω) :=
  fun p => q p.1 * φ p.2

@[simp] theorem prodState_zero_right (q : QState σ) :
    prodState q (0 : QState Ω) = 0 := by
  funext p
  obtain ⟨a, x⟩ := p
  simp [prodState]

theorem prodState_normSq [Fintype σ] [Fintype Ω] (q : QState σ) (φ : QState Ω) :
    (∑ p : σ × Ω, ‖prodState q φ p‖ ^ 2) =
      (∑ a, ‖q a‖ ^ 2) * (∑ x, ‖φ x‖ ^ 2) := by
  rw [Fintype.sum_prod_type]
  have hterm : ∀ a : σ, (∑ x : Ω, ‖prodState q φ (a, x)‖ ^ 2) =
      ‖q a‖ ^ 2 * ∑ x : Ω, ‖φ x‖ ^ 2 := by
    intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [prodState, norm_mul, mul_pow]
  simp only [hterm]
  rw [Finset.sum_mul]

theorem stateNorm_eq_sqrt [Fintype I] (ψ : QState I) :
    stateNorm ψ = Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := by
  rw [← stateNorm_sq ψ, Real.sqrt_sq (show (0:ℝ) ≤ stateNorm ψ from norm_nonneg _)]

theorem stateNorm_prodState [Fintype σ] [Fintype Ω] (q : QState σ) (φ : QState Ω) :
    stateNorm (prodState q φ) = stateNorm q * stateNorm φ := by
  rw [stateNorm_eq_sqrt, prodState_normSq, stateNorm_eq_sqrt, stateNorm_eq_sqrt,
    Real.sqrt_mul (by positivity)]

noncomputable def tensorPair (A : QState σ →ₗ[ℂ] QState σ) (B : QState Ω →ₗ[ℂ] QState Ω)
    (ξ : QState (σ × Ω)) : QState (σ × Ω) :=
  fun p => A (fun a => B (fun x => ξ (a, x)) p.2) p.1

theorem tensorPair_prodState (A : QState σ →ₗ[ℂ] QState σ) (B : QState Ω →ₗ[ℂ] QState Ω)
    (q : QState σ) (φ : QState Ω) :
    tensorPair A B (prodState q φ) = prodState (A q) (B φ) := by
  funext p
  obtain ⟨a, x⟩ := p
  simp only [tensorPair, prodState]
  have hB : ∀ a' : σ, B (fun x' => q a' * φ x') = q a' • B φ := by
    intro a'
    have h : (fun x' => q a' * φ x') = q a' • φ := rfl
    rw [h, B.map_smul]
  simp only [hB]
  have hA : (fun a' : σ => (q a' • B φ) x) = ((B φ) x) • q := by
    funext a'
    simp [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hA, A.map_smul]
  simp [Pi.smul_apply, smul_eq_mul, mul_comm]

noncomputable def testFun (Q : QState σ →ₗ[ℂ] QState σ) (P : QState Ω →ₗ[ℂ] QState Ω)
    (ξ : QState (σ × Ω)) : QState (σ × Ω) :=
  tensorPair Q P ξ +
    tensorPair (LinearMap.id : QState σ →ₗ[ℂ] QState σ)
      ((LinearMap.id : QState Ω →ₗ[ℂ] QState Ω) - P) ξ

theorem testFun_prodState_of_fixed (Q : QState σ →ₗ[ℂ] QState σ)
    (P : QState Ω →ₗ[ℂ] QState Ω) (q : QState σ) (φ : QState Ω) (hP : P φ = φ) :
    testFun Q P (prodState q φ) = prodState (Q q) φ := by
  rw [testFun, tensorPair_prodState, tensorPair_prodState]
  have hzero : ((LinearMap.id : QState Ω →ₗ[ℂ] QState Ω) - P) φ = 0 := by
    rw [LinearMap.sub_apply, LinearMap.id_apply, hP]
    simp
  rw [hzero, prodState_zero_right, hP]
  simp

theorem testFun_sub_prodState (Q : QState σ →ₗ[ℂ] QState σ)
    (P : QState Ω →ₗ[ℂ] QState Ω) (q : QState σ) (φ : QState Ω) :
    testFun Q P (prodState q φ) - prodState q φ = prodState (Q q - q) (P φ) := by
  rw [testFun, tensorPair_prodState, tensorPair_prodState]
  funext p
  obtain ⟨a, x⟩ := p
  simp only [prodState, Pi.add_apply, Pi.sub_apply, LinearMap.sub_apply, LinearMap.id_apply]
  ring

end Tensor

noncomputable def fiberCard (f : G → β) (K : Subgroup G) (g : G) (b : β) : ℕ :=
  (Finset.univ.filter (fun k : ↥K => f (g * (k : G)) = b)).card

theorem fiberCard_eq_of_strict {H : Subgroup G} {f : G → β}
    (hf : IsStrictlyHPeriodic f H) (K : Subgroup G) {g : G} {k₀ : ↥K} {b : β}
    (hk₀ : f (g * (k₀ : G)) = b) :
    fiberCard f K g b = Fintype.card ↥(K ⊓ H) := by
  unfold fiberCard
  symm
  refine Finset.card_bij (s := (Finset.univ : Finset ↥(K ⊓ H)))
    (t := Finset.univ.filter (fun k : ↥K => f (g * (k : G)) = b))
    (fun (h : ↥(K ⊓ H)) (_ : h ∈ (Finset.univ : Finset ↥(K ⊓ H))) =>
      (⟨k₀ * (h : G), K.mul_mem k₀.property h.property.1⟩ : ↥K)) ?_ ?_ ?_
  · intro h _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← mul_assoc, hf.1 (g * (k₀ : G)) (h : G) h.property.2, hk₀]
  · intro h₁ _ h₂ _ heq
    have hval : (k₀ : G) * (h₁ : G) = (k₀ : G) * (h₂ : G) := by
      simpa using congrArg (Subtype.val) heq
    exact Subtype.ext (mul_left_cancel hval)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hmemK : k₀⁻¹ * (k : G) ∈ K := K.mul_mem (K.inv_mem k₀.property) k.property
    have hmemH : k₀⁻¹ * (k : G) ∈ H := by
      refine hf.2 (g * (k₀ : G)) (k₀⁻¹ * (k : G)) ?_
      calc f ((g * (k₀ : G)) * (k₀⁻¹ * (k : G))) = f (g * (k : G)) := by
            rw [show (g * (k₀ : G)) * (k₀⁻¹ * (k : G)) = g * (k : G) by
              simp only [Subgroup.coe_inv]; group]
        _ = b := hk
        _ = f (g * (k₀ : G)) := hk₀.symm
    refine ⟨⟨k₀⁻¹ * (k : G), ⟨hmemK, hmemH⟩⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_inv]
    group

theorem sum_fiberCard (f : G → β) (K : Subgroup G) (g : G) :
    (∑ b : β, fiberCard f K g b) = Fintype.card ↥K := by
  unfold fiberCard
  have h : ∀ b : β,
      (Finset.univ.filter (fun k : ↥K => f (g * (k : G)) = b)).card =
        ∑ k : ↥K, if f (g * (k : G)) = b then 1 else 0 := by
    intro b
    simp
  simp only [h]
  rw [Finset.sum_comm]
  simp

theorem sum_sq_fiberCard {H : Subgroup G} {f : G → β} (hf : IsStrictlyHPeriodic f H)
    (K : Subgroup G) (g : G) :
    (∑ b : β, (fiberCard f K g b : ℝ) ^ 2) =
      (Fintype.card ↥(K ⊓ H) : ℝ) * (Fintype.card ↥K : ℝ) := by
  have hsq : ∀ b : β, (fiberCard f K g b : ℝ) ^ 2 =
      (Fintype.card ↥(K ⊓ H) : ℝ) * (fiberCard f K g b : ℝ) := by
    intro b
    by_cases hb : ∃ k : ↥K, f (g * (k : G)) = b
    · obtain ⟨k₀, hk₀⟩ := hb
      rw [fiberCard_eq_of_strict hf K hk₀]
      ring
    · have hzero : fiberCard f K g b = 0 := by
        unfold fiberCard
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _ hk
        exact hb ⟨k, hk⟩
      rw [hzero]
      simp
  calc (∑ b : β, (fiberCard f K g b : ℝ) ^ 2)
      = ∑ b : β, (Fintype.card ↥(K ⊓ H) : ℝ) * (fiberCard f K g b : ℝ) :=
        Finset.sum_congr rfl (fun b _ => hsq b)
    _ = (Fintype.card ↥(K ⊓ H) : ℝ) * ∑ b : β, (fiberCard f K g b : ℝ) := by
        rw [Finset.mul_sum]
    _ = (Fintype.card ↥(K ⊓ H) : ℝ) * (Fintype.card ↥K : ℝ) := by
        have hsumR : (∑ b : β, (fiberCard f K g b : ℝ)) = (Fintype.card ↥K : ℝ) := by
          rw [← Nat.cast_sum, sum_fiberCard]
        rw [hsumR]

theorem sum_initialCouplet_eq_card {f : G → β} (K : Subgroup G) (g : G) (b : β) :
    (∑ k : ↥K, initialCouplet f (g * (k : G), b)) =
      ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ * (fiberCard f K g b : ℂ) := by
  have hterm : ∀ k : ↥K, initialCouplet f (g * (k : G), b) =
      if f (g * (k : G)) = b then ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ else 0 := by
    intro k
    by_cases h : f (g * (k : G)) = b
    · have h' : b = f (g * (k : G)) := h.symm
      simp only [initialCouplet, if_pos h', if_pos h]
    · have h' : b ≠ f (g * (k : G)) := fun hh => h hh.symm
      simp only [initialCouplet, if_neg h', if_neg h]
  simp only [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  simp only [fiberCard]
  rw [mul_comm]

theorem norm_sq_couplet_eq {f : G → β} (K : Subgroup G) (g : G) (b : β) :
    ‖coupletAvg K (initialCouplet f) (g, b)‖ ^ 2 =
      (((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 * (Fintype.card ↥K : ℝ)⁻¹ ^ 2) *
        (fiberCard f K g b : ℝ) ^ 2 := by
  rw [coupletAvg, sum_initialCouplet_eq_card]
  have hG : ‖(((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹)‖ =
      ((Real.sqrt (Fintype.card G : ℝ))⁻¹) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hK : ‖((Fintype.card ↥K : ℂ))⁻¹‖ = ((Fintype.card ↥K : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hn : ‖((fiberCard f K g b : ℂ))‖ = (fiberCard f K g b : ℝ) :=
    Complex.norm_natCast _
  rw [norm_mul, norm_mul, hK, hG, hn, mul_pow, mul_pow]
  ring

theorem coupletAvg_initialCouplet_normSq {H : Subgroup G} {f : G → β}
    (hf : IsStrictlyHPeriodic f H) (K : Subgroup G) :
    (∑ p : G × β, ‖coupletAvg K (initialCouplet f) p‖ ^ 2) =
      (Fintype.card ↥(K ⊓ H) : ℝ) / (Fintype.card ↥K : ℝ) := by
  have hGpos : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hKpos : (0:ℝ) < (Fintype.card ↥K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : ((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 = ((Fintype.card G : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hGpos.le]
  have htermB : ∀ g : G, (∑ b : β, ‖coupletAvg K (initialCouplet f) (g, b)‖ ^ 2) =
      (((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 * (Fintype.card ↥K : ℝ)⁻¹ ^ 2) *
        ((Fintype.card ↥(K ⊓ H) : ℝ) * (Fintype.card ↥K : ℝ)) := by
    intro g
    have h1 : (∑ b : β, ‖coupletAvg K (initialCouplet f) (g, b)‖ ^ 2) =
        (((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 * (Fintype.card ↥K : ℝ)⁻¹ ^ 2) *
          ∑ b : β, (fiberCard f K g b : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [norm_sq_couplet_eq]
    rw [h1, sum_sq_fiberCard hf K g]
  rw [Fintype.sum_prod_type]
  calc (∑ g : G, ∑ b : β, ‖coupletAvg K (initialCouplet f) (g, b)‖ ^ 2)
      = ∑ g : G, (((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 * (Fintype.card ↥K : ℝ)⁻¹ ^ 2) *
          ((Fintype.card ↥(K ⊓ H) : ℝ) * (Fintype.card ↥K : ℝ)) :=
        Finset.sum_congr rfl (fun g _ => htermB g)
    _ = (Fintype.card G : ℝ) *
          (((Real.sqrt (Fintype.card G : ℝ))⁻¹) ^ 2 * (Fintype.card ↥K : ℝ)⁻¹ ^ 2) *
          ((Fintype.card ↥(K ⊓ H) : ℝ) * (Fintype.card ↥K : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Fintype.card ↥(K ⊓ H) : ℝ) / (Fintype.card ↥K : ℝ) := by
        rw [hc]
        field_simp

noncomputable def subgroupOfInfEquiv (K H : Subgroup G) :
    ↥((K ⊓ H).subgroupOf K) ≃ ↥(K ⊓ H) where
  toFun x := ⟨(x.1 : G), x.2⟩
  invFun y := ⟨⟨(y.1 : G), y.2.1⟩, y.2⟩
  left_inv x := by cases x with | mk _ _ => rfl
  right_inv y := by cases y with | mk _ _ => rfl

theorem coupletAvg_initialCouplet_le_half {H : Subgroup G} {f : G → β}
    (hf : IsStrictlyHPeriodic f H) {K : Subgroup G} (hK : ¬ IsHPeriodic f K) :
    (∑ p : G × β, ‖coupletAvg K (initialCouplet f) p‖ ^ 2) ≤ (1/2 : ℝ) := by
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  haveI : Nonempty ↥(K ⊓ H) := ⟨⟨1, K.one_mem, H.one_mem⟩⟩
  have hKH : ¬ K ≤ H := fun hle => hK (hf.1.mono hle)
  have htop : (K ⊓ H).subgroupOf K ≠ ⊤ := by
    intro h
    apply hKH
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥K) ∈ (K ⊓ H).subgroupOf K := by
      rw [h]
      exact Subgroup.mem_top _
    have hmem2 : x ∈ K ⊓ H := hmem
    exact hmem2.2
  have hidx : 1 < ((K ⊓ H).subgroupOf K).index := Subgroup.one_lt_index_of_ne_top htop
  have hmul := Subgroup.card_mul_index ((K ⊓ H).subgroupOf K)
  have hcard : Nat.card ↥((K ⊓ H).subgroupOf K) = Nat.card ↥(K ⊓ H) :=
    Nat.card_congr (subgroupOfInfEquiv K H)
  have hle : 2 * Fintype.card ↥(K ⊓ H) ≤ Fintype.card ↥K := by
    have h2 : 2 ≤ ((K ⊓ H).subgroupOf K).index := hidx
    have hstep : 2 * Nat.card ↥((K ⊓ H).subgroupOf K) ≤
        Nat.card ↥((K ⊓ H).subgroupOf K) * ((K ⊓ H).subgroupOf K).index := by
      calc 2 * Nat.card ↥((K ⊓ H).subgroupOf K)
          = Nat.card ↥((K ⊓ H).subgroupOf K) * 2 := by ring
        _ ≤ Nat.card ↥((K ⊓ H).subgroupOf K) * ((K ⊓ H).subgroupOf K).index :=
            Nat.mul_le_mul_left _ h2
    rw [hmul] at hstep
    rw [hcard] at hstep
    simpa [Nat.card_eq_fintype_card] using hstep
  have hKpos : (0:ℝ) < (Fintype.card ↥K : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [coupletAvg_initialCouplet_normSq hf K]
  rw [div_le_iff₀ hKpos]
  have hleR : 2 * (Fintype.card ↥(K ⊓ H) : ℝ) ≤ (Fintype.card ↥K : ℝ) := by
    exact_mod_cast hle
  linarith

theorem sqrt_inv_two_pow (s : ℕ) :
    Real.sqrt ((1/2 : ℝ) ^ s) = (1/2 : ℝ) ^ ((s : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [show ((s : ℝ) / 2) = (s : ℝ) * (1/2) by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [Real.rpow_natCast]

theorem lemma3_test_transport
    {σ : Type*} (Q : QState σ →ₗ[ℂ] QState σ) {K : Subgroup G} {f : G → β}
    (hf : IsHPeriodic f K) (s : ℕ) (q q' : QState σ) (hQ : Q q = q') :
    testFun Q (projSLM K s) (prodState q (multisetState (initialCouplet f) s)) =
      prodState q' (multisetState (initialCouplet f) s) := by
  have hP : projSLM K s (multisetState (initialCouplet f) s) =
      multisetState (initialCouplet f) s :=
    projS_fixes_multisetState_of_periodic hf s
  rw [testFun_prodState_of_fixed Q (projSLM K s) q _ hP, hQ]

theorem lemma4_distance_bound {σ : Type*} [Fintype σ]
    {H : Subgroup G} {f : G → β} (hf : IsStrictlyHPeriodic f H)
    {K : Subgroup G} (hK : ¬ IsHPeriodic f K) (s : ℕ)
    (Q : QState σ →ₗ[ℂ] QState σ) (q : QState σ)
    (hQ : ∀ ψ : QState σ, (∑ a : σ, ‖Q ψ a‖ ^ 2) = ∑ a : σ, ‖ψ a‖ ^ 2)
    (hq : (∑ a : σ, ‖q a‖ ^ 2) = 1) :
    stateNorm (testFun Q (projSLM K s) (prodState q (multisetState (initialCouplet f) s))
      - prodState q (multisetState (initialCouplet f) s)) ≤ 2 * (1/2 : ℝ) ^ ((s : ℝ) / 2) := by
  rw [testFun_sub_prodState, stateNorm_prodState]
  have hPsum : (∑ p : Fin s → G × β,
      ‖projS K s (multisetState (initialCouplet f) s) p‖ ^ 2) ≤ (1/2 : ℝ) ^ s :=
    projS_normSq_le K (initialCouplet f) s (coupletAvg_initialCouplet_le_half hf hK)
  have hPnorm : stateNorm (projS K s (multisetState (initialCouplet f) s)) ≤
      (1/2 : ℝ) ^ ((s : ℝ) / 2) := by
    calc stateNorm (projS K s (multisetState (initialCouplet f) s))
        = Real.sqrt (∑ p : Fin s → G × β,
            ‖projS K s (multisetState (initialCouplet f) s) p‖ ^ 2) := stateNorm_eq_sqrt _
      _ ≤ Real.sqrt ((1/2 : ℝ) ^ s) := Real.sqrt_le_sqrt hPsum
      _ = (1/2 : ℝ) ^ ((s : ℝ) / 2) := sqrt_inv_two_pow s
  have hQnorm : stateNorm (Q q - q) ≤ 2 := by
    have hsq : (∑ a : σ, ‖(Q q - q) a‖ ^ 2) ≤ 4 := by
      have h1 : ∀ a : σ, ‖(Q q - q) a‖ ^ 2 ≤ 2 * (‖Q q a‖ ^ 2 + ‖q a‖ ^ 2) := by
        intro a
        have htri : ‖Q q a - q a‖ ≤ ‖Q q a‖ + ‖q a‖ := norm_sub_le _ _
        calc ‖(Q q - q) a‖ ^ 2 = ‖Q q a - q a‖ ^ 2 := by simp
          _ ≤ (‖Q q a‖ + ‖q a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ ≤ 2 * (‖Q q a‖ ^ 2 + ‖q a‖ ^ 2) := add_sq_le
      calc (∑ a : σ, ‖(Q q - q) a‖ ^ 2)
          ≤ ∑ a : σ, 2 * (‖Q q a‖ ^ 2 + ‖q a‖ ^ 2) :=
            Finset.sum_le_sum (fun a _ => h1 a)
        _ = 2 * ((∑ a : σ, ‖Q q a‖ ^ 2) + (∑ a : σ, ‖q a‖ ^ 2)) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [← Finset.sum_add_distrib]
        _ = 4 := by rw [hQ q, hq]; norm_num
    calc stateNorm (Q q - q) = Real.sqrt (∑ a : σ, ‖(Q q - q) a‖ ^ 2) := stateNorm_eq_sqrt _
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hsq
      _ = 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  calc stateNorm (Q q - q) * stateNorm (projS K s (multisetState (initialCouplet f) s))
      ≤ 2 * (1/2 : ℝ) ^ ((s : ℝ) / 2) :=
        mul_le_mul hQnorm hPnorm (by rw [stateNorm]; exact norm_nonneg _) (by norm_num)

def iteratedState {Ω : Type*} (T : ℕ → QState Ω → QState Ω) (init : QState Ω) :
    ℕ → QState Ω
  | 0 => init
  | (j+1) => T j (iteratedState T init j)

theorem lemma5_iterated_distance {Ω : Type*} [Fintype Ω]
    (T : ℕ → QState Ω → QState Ω) (init : QState Ω) (s j : ℕ)
    (hstep : ∀ i < j, stateNorm (iteratedState T init (i+1) - iteratedState T init i) ≤
      2 * (1/2 : ℝ) ^ ((s : ℝ) / 2)) :
    stateNorm (iteratedState T init j - init) ≤ (2 * (j : ℝ)) * (1/2 : ℝ) ^ ((s : ℝ) / 2) := by
  revert hstep
  induction j with
  | zero =>
      intro _
      simp [iteratedState, stateNorm]
  | succ j ih =>
      intro hstep
      have hprev : ∀ i < j, stateNorm (iteratedState T init (i+1) - iteratedState T init i) ≤
          2 * (1/2 : ℝ) ^ ((s : ℝ) / 2) :=
        fun i hi => hstep i (Nat.lt_succ_of_lt hi)
      have ih' := ih hprev
      have hlast : stateNorm (iteratedState T init (j+1) - iteratedState T init j) ≤
          2 * (1/2 : ℝ) ^ ((s : ℝ) / 2) := hstep j (Nat.lt_succ_self j)
      have hdecomp : iteratedState T init (j+1) - init =
          (iteratedState T init (j+1) - iteratedState T init j) +
            (iteratedState T init j - init) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      calc stateNorm (iteratedState T init (j+1) - init)
          = stateNorm ((iteratedState T init (j+1) - iteratedState T init j) +
              (iteratedState T init j - init)) := by rw [hdecomp]
        _ ≤ stateNorm (iteratedState T init (j+1) - iteratedState T init j) +
              stateNorm (iteratedState T init j - init) := stateNorm_add_le _ _
        _ ≤ 2 * (1/2 : ℝ) ^ ((s : ℝ) / 2) +
              (2 * (j : ℝ)) * (1/2 : ℝ) ^ ((s : ℝ) / 2) := add_le_add hlast ih'
        _ = (2 * ((j : ℝ) + 1)) * (1/2 : ℝ) ^ ((s : ℝ) / 2) := by ring
        _ = 2 * (((j + 1 : ℕ) : ℝ)) * (1/2 : ℝ) ^ ((s : ℝ) / 2) := by push_cast; ring

theorem lemma6_ancilla_projection {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ)
    (x y : Fin r → ℝ) (hMx : M.mulVec x = y)
    (hy : ∀ ν, y ν = 1/4 ∨ y ν = 3/4) (ν : Fin r) :
    (∑ μ, M ν μ * x μ) = 1/4 ∨ (∑ μ, M ν μ * x μ) = 3/4 := by
  have h : (∑ μ, M ν μ * x μ) = y ν := by
    rw [← congrFun hMx ν]
    rfl
  rw [h]
  exact hy ν

theorem delta_pow_entry_bound {r : ℕ} (hr : 0 < r) (Δ : Matrix (Fin r) (Fin r) ℝ)
    (hΔ : ∀ i j, |Δ i j| ≤ ((r : ℝ)⁻¹) ^ 2) :
    ∀ k : ℕ, ∀ i j : Fin r, |(Δ ^ (k + 1)) i j| ≤ ((r : ℝ)⁻¹) ^ (k + 2) := by
  intro k
  induction k with
  | zero =>
      intro i j
      simpa using hΔ i j
  | succ k ih =>
      intro i j
      have hpow : Δ ^ (k + 1 + 1) = Δ ^ (k + 1) * Δ := pow_succ _ _
      rw [hpow, Matrix.mul_apply]
      calc |∑ l, (Δ ^ (k + 1)) i l * Δ l j|
          ≤ ∑ l, |(Δ ^ (k + 1)) i l * Δ l j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin r, ((r : ℝ)⁻¹) ^ (k + 2) * ((r : ℝ)⁻¹) ^ 2 := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            exact mul_le_mul (ih i l) (hΔ l j) (abs_nonneg _) (by positivity)
        _ = (r : ℝ) * (((r : ℝ)⁻¹) ^ (k + 2) * ((r : ℝ)⁻¹) ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ((r : ℝ)⁻¹) ^ (k + 3) := by
            have hsq : (r : ℝ) * ((r : ℝ)⁻¹) ^ 2 = (r : ℝ)⁻¹ := by
              have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
              field_simp
            calc (r : ℝ) * (((r : ℝ)⁻¹) ^ (k + 2) * ((r : ℝ)⁻¹) ^ 2)
                = ((r : ℝ)⁻¹) ^ (k + 2) * ((r : ℝ) * ((r : ℝ)⁻¹) ^ 2) := by ring
              _ = ((r : ℝ)⁻¹) ^ (k + 2) * (r : ℝ)⁻¹ := by rw [hsq]
              _ = ((r : ℝ)⁻¹) ^ (k + 3) := by
                  rw [show k + 3 = (k + 2) + 1 by ring]
                  exact (pow_succ _ _).symm

theorem delta_neumann_telescope {r : ℕ} (Δ : Matrix (Fin r) (Fin r) ℝ) (N : ℕ) :
    (1 - Δ) * (∑ k ∈ Finset.range N, Δ ^ k) = 1 - Δ ^ N := by
  simpa using mul_neg_geom_sum Δ N

theorem lemma6_neumann_core {r : ℕ} (hr : 0 < r) (Δ : Matrix (Fin r) (Fin r) ℝ)
    (hΔ : ∀ i j, |Δ i j| ≤ ((r : ℝ)⁻¹) ^ 2) (N : ℕ) :
    (1 - Δ) * (∑ k ∈ Finset.range N, Δ ^ k) = 1 - Δ ^ N ∧
      ∀ k : ℕ, ∀ i j : Fin r, |(Δ ^ (k + 1)) i j| ≤ ((r : ℝ)⁻¹) ^ (k + 2) :=
  ⟨delta_neumann_telescope Δ N, delta_pow_entry_bound hr Δ hΔ⟩

section MeasurementBound

variable {Ω : Type*} [Fintype Ω]

noncomputable def outcomeProb {r : ℕ} (ψ : QState (Fin r × Ω)) (ν : Fin r) : ℝ :=
  ∑ p : Fin r × Ω, if p.1 = ν then ‖ψ p‖ ^ 2 else 0

theorem outcomeProb_of_supported {r : ℕ} {ψ : QState (Fin r × Ω)} (ν : Fin r)
    (hnorm : (∑ p, ‖ψ p‖ ^ 2) = 1) (h : ∀ p, p.1 ≠ ν → ψ p = 0) :
    outcomeProb ψ ν = 1 := by
  unfold outcomeProb
  rw [← hnorm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 = ν
  · simp [hp]
  · simp [hp, h p hp]

theorem outcomeProb_eq_sum_filter {r : ℕ} (ψ : QState (Fin r × Ω)) (ν : Fin r) :
    outcomeProb ψ ν =
      ∑ p ∈ (Finset.univ.filter (fun p : Fin r × Ω => p.1 = ν)), ‖ψ p‖ ^ 2 := by
  unfold outcomeProb
  rw [Finset.sum_filter]

theorem outcomeProb_close {r : ℕ} {ψ φ : QState (Fin r × Ω)} (ν : Fin r)
    (hψ : (∑ p, ‖ψ p‖ ^ 2) = 1) (hφ : (∑ p, ‖φ p‖ ^ 2) = 1) :
    |outcomeProb ψ ν - outcomeProb φ ν| ≤ 2 * stateNorm (ψ - φ) := by
  set A : Finset (Fin r × Ω) :=
    Finset.univ.filter (fun p : Fin r × Ω => p.1 = ν) with hA

  have hpoint : ∀ p ∈ A, |‖ψ p‖ ^ 2 - ‖φ p‖ ^ 2| ≤
      ‖ψ p - φ p‖ * (‖ψ p‖ + ‖φ p‖) := by
    intro p _
    have habs : |‖ψ p‖ - ‖φ p‖| ≤ ‖ψ p - φ p‖ := abs_norm_sub_norm_le (ψ p) (φ p)
    have hnn : 0 ≤ ‖ψ p‖ + ‖φ p‖ := by positivity
    have hsq : ‖ψ p‖ ^ 2 - ‖φ p‖ ^ 2 =
        (‖ψ p‖ - ‖φ p‖) * (‖ψ p‖ + ‖φ p‖) := by ring
    rw [hsq, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right habs hnn

  have hsum_abs : |outcomeProb ψ ν - outcomeProb φ ν| ≤
      ∑ p ∈ A, ‖ψ p - φ p‖ * (‖ψ p‖ + ‖φ p‖) := by
    rw [outcomeProb_eq_sum_filter ψ ν, outcomeProb_eq_sum_filter φ ν, ← hA,
      ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpoint)

  have hcs := Real.sum_mul_le_sqrt_mul_sqrt A
    (fun p => ‖ψ p - φ p‖) (fun p => ‖ψ p‖ + ‖φ p‖)

  have hA_sub : (∑ p ∈ A, ‖ψ p - φ p‖ ^ 2) ≤
      ∑ p : Fin r × Ω, ‖(ψ - φ) p‖ ^ 2 := by
    rw [hA, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : p.1 = ν
    · simp [hp]
    · simp only [hp, if_false]
      exact pow_nonneg (norm_nonneg _) 2
  have hsqrt1 : Real.sqrt (∑ p ∈ A, ‖ψ p - φ p‖ ^ 2) ≤ stateNorm (ψ - φ) := by
    calc Real.sqrt (∑ p ∈ A, ‖ψ p - φ p‖ ^ 2)
        ≤ Real.sqrt (∑ p : Fin r × Ω, ‖(ψ - φ) p‖ ^ 2) := Real.sqrt_le_sqrt hA_sub
      _ = stateNorm (ψ - φ) := (stateNorm_eq_sqrt (ψ - φ)).symm

  have hA_v : (∑ p ∈ A, (‖ψ p‖ + ‖φ p‖) ^ 2) ≤ 4 := by
    have hsub : (∑ p ∈ A, (‖ψ p‖ + ‖φ p‖) ^ 2) ≤
        ∑ p : Fin r × Ω, (‖ψ p‖ + ‖φ p‖) ^ 2 := by
      rw [hA, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.1 = ν
      · simp [hp]
      · simp only [hp, if_false]
        positivity
    have hpt : ∀ p : Fin r × Ω, (‖ψ p‖ + ‖φ p‖) ^ 2 ≤
        2 * (‖ψ p‖ ^ 2 + ‖φ p‖ ^ 2) := by
      intro p
      exact add_sq_le
    have htot : (∑ p : Fin r × Ω, (‖ψ p‖ + ‖φ p‖) ^ 2) ≤ 4 := by
      have h1 : (∑ p : Fin r × Ω, (‖ψ p‖ + ‖φ p‖) ^ 2) ≤
          ∑ p : Fin r × Ω, 2 * (‖ψ p‖ ^ 2 + ‖φ p‖ ^ 2) :=
        Finset.sum_le_sum (fun p _ => hpt p)
      have h2 : (∑ p : Fin r × Ω, 2 * (‖ψ p‖ ^ 2 + ‖φ p‖ ^ 2)) = 4 := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hψ, hφ]
        norm_num
      linarith
    linarith
  have hsqrt2 : Real.sqrt (∑ p ∈ A, (‖ψ p‖ + ‖φ p‖) ^ 2) ≤ 2 := by
    calc Real.sqrt (∑ p ∈ A, (‖ψ p‖ + ‖φ p‖) ^ 2)
        ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hA_v
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

  calc |outcomeProb ψ ν - outcomeProb φ ν|
      ≤ ∑ p ∈ A, ‖ψ p - φ p‖ * (‖ψ p‖ + ‖φ p‖) := hsum_abs
    _ ≤ Real.sqrt (∑ p ∈ A, ‖ψ p - φ p‖ ^ 2) *
          Real.sqrt (∑ p ∈ A, (‖ψ p‖ + ‖φ p‖) ^ 2) := hcs
    _ ≤ stateNorm (ψ - φ) * 2 :=
        mul_le_mul hsqrt1 hsqrt2 (Real.sqrt_nonneg _)
          (by rw [stateNorm]; exact norm_nonneg _)
    _ = 2 * stateNorm (ψ - φ) := by ring

theorem theorem2_success_probability {r s : ℕ}
    (Ψ Φ : QState (Fin r × (Fin s → G × β))) (ν : Fin r)
    (hΨ : (∑ p, ‖Ψ p‖ ^ 2) = 1) (hΦ : (∑ p, ‖Φ p‖ ^ 2) = 1)
    (hΦ0 : ∀ p, p.1 ≠ ν → Φ p = 0)
    (hdist : stateNorm (Ψ - Φ) ≤ 2 * (r : ℝ) * (1/2 : ℝ) ^ ((s : ℝ) / 2)) :
    1 - 4 * (r : ℝ) * (1/2 : ℝ) ^ ((s : ℝ) / 2) ≤ outcomeProb Ψ ν := by
  have h1 : outcomeProb Φ ν = 1 := outcomeProb_of_supported ν hΦ hΦ0
  have hclose := outcomeProb_close (Ω := Fin s → G × β) ν hΨ hΦ
  have hle := (abs_le.mp hclose).1
  have hdist2 : 2 * stateNorm (Ψ - Φ) ≤ 4 * (r : ℝ) * (1/2 : ℝ) ^ ((s : ℝ) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hdist (by norm_num : (0:ℝ) ≤ 2)
    nlinarith
  rw [h1] at hle
  linarith

end MeasurementBound

section QueryAlgorithm

theorem exists_test_count (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, 4 * (r : ℝ) * (1/2 : ℝ) ^ ((s : ℝ) / 2) ≤ ε := by
  have hrR : (0 : ℝ) < 4 * (r : ℝ) := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hrR) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨2 * n, ?_⟩
  have hs : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by
    push_cast
    ring
  rw [hs, Real.rpow_natCast]
  have h := mul_lt_mul_of_pos_left hn hrR
  rw [mul_div_cancel₀ _ (ne_of_gt hrR)] at h
  exact le_of_lt h

theorem theorem1_reduction {r : ℕ} (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, ∀ (Ψ Φ : QState (Fin r × (Fin s → G × β))) (ν : Fin r),
      (∑ p, ‖Ψ p‖ ^ 2) = 1 → (∑ p, ‖Φ p‖ ^ 2) = 1 →
      (∀ p, p.1 ≠ ν → Φ p = 0) →
      stateNorm (Ψ - Φ) ≤ 2 * (r : ℝ) * (1/2 : ℝ) ^ ((s : ℝ) / 2) →
      1 - ε ≤ outcomeProb Ψ ν := by
  obtain ⟨s, hs⟩ := exists_test_count r hr ε hε
  refine ⟨s, ?_⟩
  intro Ψ Φ ν hΨ hΦ hΦ0 hdist
  have hmain := theorem2_success_probability Ψ Φ ν hΨ hΦ hΦ0 hdist
  linarith

end QueryAlgorithm

end Qatlib.Papers.EttingerHSP04.MainResults
