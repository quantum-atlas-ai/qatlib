/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AffineHSP02.MainResults

open scoped BigOperators

structure QHedral (p q : ℕ) (G : Type) [Group G] where

  trans : Subgroup G
  trans_normal : trans.Normal

  trans_card : Nat.card trans = p

  group_card : Nat.card G = p * q

def conjugateSubgroup {G : Type} [Group G] (H : Subgroup G) (b : G) : Subgroup G :=
  H.map (MulAut.conj b).toMonoidHom

structure FinLaw (Ω : Type) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1

noncomputable def totalVariation {Ω : Type} [Fintype Ω] (P Q : FinLaw Ω) : ℝ :=
  (1 / 2) * ∑ x, |P.prob x - Q.prob x|

structure SubgroupLaw (G Ω : Type) [Group G] [Fintype Ω] where
  law : Subgroup G → FinLaw Ω

def MeasurementReconstructible (G : Type) [Group G] : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω), ∃ M : SubgroupLaw G Ω, Function.Injective M.law

def FullyReconstructible (G : Type) [Group G] : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω), ∃ M : SubgroupLaw G Ω, ∃ dec : Ω → Subgroup G,
    ∀ s : Subgroup G, ∃ F : Finset Ω,
      (∀ ω ∈ F, dec ω = s) ∧ (1 / 2 : ℝ) ≤ ∑ ω ∈ F, (M.law s).prob ω

def HiddenConjugatesMeasurementReconstructible (G : Type) [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (δ : ℝ) (law : G → FinLaw Ω),
    (1 / 4 ≤ δ) ∧ (δ ≤ 1) ∧
    ∀ b b' : G, conjugateSubgroup H b ≠ conjugateSubgroup H b' →
      δ ≤ totalVariation (law b) (law b')

def HiddenConjugatesFullyReconstructible (G : Type) [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (law : G → FinLaw Ω) (dec : Ω → G),
    ∀ b : G, ∃ F : Finset Ω,
      (∀ ω ∈ F, dec ω = b) ∧ (1 / 2 : ℝ) ≤ ∑ ω ∈ F, (law b).prob ω

def IndexPolylog (p q : ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ p - 1 ≤ C * q * (Nat.log 2 p + 1) ^ k

def IndexPolylogSub {G : Type} [Group G] (H : Subgroup G) (n : ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ n ≤ C * Nat.card H * (Nat.log 2 n + 1) ^ k

noncomputable def qroot (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem qroot_pow_eq (p t : ℕ) :
    qroot p ^ t = Complex.exp (((2 * Real.pi * t / p : ℝ) : ℂ) * Complex.I) := by
  unfold qroot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem re_qroot_pow (p t : ℕ) : (qroot p ^ t).re = Real.cos (2 * Real.pi * t / p) := by
  rw [qroot_pow_eq, Complex.exp_ofReal_mul_I_re]

theorem norm_qroot_pow (p t : ℕ) : ‖qroot p ^ t‖ = 1 := by
  rw [qroot_pow_eq, Complex.norm_exp_ofReal_mul_I]

theorem re_qroot_pow_ge_neg_one (p t : ℕ) : -1 ≤ (qroot p ^ t).re := by
  have h1 : |(qroot p ^ t).re| ≤ ‖qroot p ^ t‖ := Complex.abs_re_le_norm _
  rw [norm_qroot_pow] at h1
  have h2 : -1 ≤ (qroot p ^ t).re := by
    have := (abs_le.1 h1).1
    linarith
  exact h2

theorem cos_ge_half_of_low (p x : ℕ) (hp : 0 < p) (hx : (x : ℝ) ≤ p / 6) :
    (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * x / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hle : 2 * Real.pi * x / p ≤ Real.pi / 3 := by
    rw [div_le_iff₀ hpR]
    nlinarith [Real.pi_pos, hpx, hx, hpR]
  have hnonneg : 0 ≤ 2 * Real.pi * x / p := by positivity
  have h := Real.cos_le_cos_of_nonneg_of_le_pi hnonneg
    (le_of_lt (by linarith [Real.pi_pos] : Real.pi / 3 < Real.pi)) hle
  rw [Real.cos_pi_div_three] at h
  linarith

theorem cos_ge_half_of_high (p x : ℕ) (hp : 0 < p) (hx : 5 * (p : ℝ) / 6 ≤ x)
    (hxp : (x : ℝ) < p) :
    (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * x / p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set θ : ℝ := 2 * Real.pi * x / p with hθ
  have hshift : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
    rw [Real.cos_two_pi_sub]
  rw [hshift]
  have hlo : 0 ≤ 2 * Real.pi - θ := by
    rw [hθ]
    have : 2 * Real.pi * x / p < 2 * Real.pi := by
      rw [div_lt_iff₀ hpR]
      nlinarith [Real.pi_pos, hpR, hxp]
    linarith
  have hhi : 2 * Real.pi - θ ≤ Real.pi / 3 := by
    rw [hθ]
    have hx5 : 5 * Real.pi / 3 ≤ 2 * Real.pi * x / p := by
      rw [le_div_iff₀ hpR]
      nlinarith [Real.pi_pos, hpR, hx]
    linarith
  have h := Real.cos_le_cos_of_nonneg_of_le_pi hlo
    (le_of_lt (by linarith [Real.pi_pos] : Real.pi / 3 < Real.pi)) hhi
  rw [Real.cos_pi_div_three] at h
  linarith

theorem counting_of_gauss_bound
    (p q : ℕ) (hp : 0 < p) (f : ℕ → ℕ) (hf : ∀ t, f t < p)
    (ε B : ℝ) (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hGauss : ‖∑ t ∈ Finset.range q, qroot p ^ (f t)‖ ≤ B)
    (hBq : B ≤ (3 / 2) * ε * q) :
    (1 / 3 - ε) * (q : ℝ) ≤
      (((Finset.range q).filter
        (fun t => p / 6 < (f t : ℝ) ∧ (f t : ℝ) < 5 * (p : ℝ) / 6)).card : ℝ) := by
  set S : Finset ℕ := (Finset.range q).filter
      (fun t => p / 6 < (f t : ℝ) ∧ (f t : ℝ) < 5 * (p : ℝ) / 6) with hSdef
  have hSmem : ∀ t ∈ Finset.range q,
      (t ∈ S ↔ (p / 6 < (f t : ℝ) ∧ (f t : ℝ) < 5 * (p : ℝ) / 6)) := by
    intro t ht
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
  have hterm : ∀ t ∈ Finset.range q,
      ((1 / 2 : ℝ) - (3 / 2) * (if t ∈ S then 1 else 0)) ≤ (qroot p ^ (f t)).re := by
    intro t ht
    by_cases hb : t ∈ S
    · rw [if_pos hb]
      have := re_qroot_pow_ge_neg_one p (f t)
      push_cast
      linarith
    · rw [if_neg hb]
      have hnb : ¬ (p / 6 < (f t : ℝ) ∧ (f t : ℝ) < 5 * (p : ℝ) / 6) :=
        fun hP => hb ((hSmem t ht).2 hP)
      have hgood : (f t : ℝ) ≤ p / 6 ∨ 5 * (p : ℝ) / 6 ≤ f t := by
        by_contra h
        push_neg at h
        exact hnb h
      rw [re_qroot_pow]
      rcases hgood with hlow | hhigh
      · have := cos_ge_half_of_low p (f t) hp hlow
        linarith
      · have := cos_ge_half_of_high p (f t) hp hhigh (by exact_mod_cast hf t)
        linarith
  have hlb : (∑ t ∈ Finset.range q,
        ((1 / 2 : ℝ) - (3 / 2) * (if t ∈ S then 1 else 0)))
      ≤ ∑ t ∈ Finset.range q, (qroot p ^ (f t)).re :=
    Finset.sum_le_sum hterm
  have hre : (∑ t ∈ Finset.range q, (qroot p ^ (f t)).re)
      = (∑ t ∈ Finset.range q, qroot p ^ (f t)).re :=
    (Complex.re_sum (s := Finset.range q)
      (f := fun t => qroot p ^ (f t))).symm
  have hrele : (∑ t ∈ Finset.range q, (qroot p ^ (f t)).re) ≤ B := by
    rw [hre]
    exact le_trans (Complex.re_le_norm _) hGauss
  have hind : (∑ t ∈ Finset.range q, (if t ∈ S then (1 : ℝ) else 0))
      = (S.card : ℝ) := by
    rw [← Finset.sum_filter]
    have hEq : (Finset.range q).filter (fun t => t ∈ S) = S := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, htS⟩; exact htS
      · intro htS
        refine ⟨?_, htS⟩
        rw [hSdef] at htS
        exact (Finset.mem_filter.1 htS).1
    rw [hEq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (∑ t ∈ Finset.range q, (1 / 2 : ℝ)) = (q : ℝ) / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h2 : (∑ t ∈ Finset.range q, (3 / 2 : ℝ) * (if t ∈ S then 1 else 0))
      = (3 / 2) * (S.card : ℝ) := by
    rw [← Finset.mul_sum, hind]
  have hval : (∑ t ∈ Finset.range q,
        ((1 / 2 : ℝ) - (3 / 2) * (if t ∈ S then 1 else 0)))
      = (q : ℝ) / 2 - (3 / 2) * (S.card : ℝ) := by
    rw [Finset.sum_sub_distrib, h1, h2]
  rw [hval] at hlb
  have hsplit : (q : ℝ) / 2 - (3 / 2) * (S.card : ℝ) ≤ B := le_trans hlb hrele
  have hfin : (1 / 3 - ε) * (q : ℝ) ≤ (S.card : ℝ) := by
    nlinarith [hsplit, hBq, hε, hB0]
  exact hfin

def orbitResidue (p : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) (t : ℕ) : ℕ :=
  (((a : ZMod p) ^ t) * k).val

noncomputable def gaussSum (p : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) (q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range q, qroot p ^ (orbitResidue p a k t)

theorem orbitResidue_lt (p : ℕ) (hp : 0 < p) (a : (ZMod p)ˣ) (k : ZMod p)
    (t : ℕ) : orbitResidue p a k t < p := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  unfold orbitResidue
  exact ZMod.val_lt _

theorem source_lemma1_of_gaussBound
    (p q : ℕ) (hp : 0 < p) (a : (ZMod p)ˣ) (k : ZMod p)
    (ε B : ℝ) (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hGauss : ‖gaussSum p a k q‖ ≤ B)
    (hBq : B ≤ (3 / 2) * ε * q) :
    (1 / 3 - ε) * (q : ℝ) ≤
      (((Finset.range q).filter
        (fun t => p / 6 < (orbitResidue p a k t : ℝ) ∧
          (orbitResidue p a k t : ℝ) < 5 * (p : ℝ) / 6)).card : ℝ) := by
  exact counting_of_gauss_bound p q hp (orbitResidue p a k)
    (orbitResidue_lt p hp a k) ε B hε hB0 hGauss hBq

theorem counting_of_sqrt_gauss_bound
    (p q : ℕ) (hp : 0 < p) (f : ℕ → ℕ) (hf : ∀ t, f t < p)
    (C : ℝ) (hC : 0 < C) (hq : 1 ≤ q)
    (hGauss : ‖∑ t ∈ Finset.range q, qroot p ^ (f t)‖ ≤ C * Real.sqrt p) :
    (1 / 3 - (2 * C * Real.sqrt p) / (3 * (q : ℝ))) * (q : ℝ) ≤
      ((((Finset.range q).filter
        (fun t => p / 6 < (f t : ℝ) ∧ (f t : ℝ) < 5 * (p : ℝ) / 6)).card : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsp : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hε : 0 < (2 * C * Real.sqrt p) / (3 * (q : ℝ)) := by positivity
  have hB0 : 0 ≤ C * Real.sqrt p := by positivity
  have hBq : C * Real.sqrt p ≤
      (3 / 2) * ((2 * C * Real.sqrt p) / (3 * (q : ℝ))) * (q : ℝ) := by
    field_simp
    ring_nf
    norm_num
  exact counting_of_gauss_bound p q hp f hf
    ((2 * C * Real.sqrt p) / (3 * (q : ℝ))) (C * Real.sqrt p)
    hε hB0 hGauss hBq

end Qatlib.Papers.AffineHSP02.MainResults
