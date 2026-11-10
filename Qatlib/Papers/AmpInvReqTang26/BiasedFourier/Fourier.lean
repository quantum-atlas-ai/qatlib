/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.BiasedFourier

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel
set_option warningAsError false

def isRightHalf (q : ℕ) (g : Fin q) : Prop :=
  (g : ℕ) ≤ q / 4 ∨ q - q / 4 ≤ (g : ℕ)

instance (q : ℕ) (g : Fin q) : Decidable (isRightHalf q g) := by
  unfold isRightHalf
  infer_instance

def muEpsWeight (ε : ℝ) (q : ℕ) (g : Fin q) : ℝ :=
  (1 - ε) * (q : ℝ)⁻¹ +
    if isRightHalf q g then ε * (halfCount q : ℝ)⁻¹ else 0

def fourierUnitVec (ε : ℝ) (q : ℕ) (k : Fin q) : Fin q → ℂ :=
  fun g => (Real.sqrt (muEpsWeight ε q g) : ℂ) * phase q g ^ (k : ℕ)

def Ftilde (ε : ℝ) (q : ℕ) (g k : Fin q) : ℂ :=
  (Real.sqrt (muEpsWeight ε q g) : ℂ) * phase q g ^ (k : ℕ)

theorem muEpsWeight_bounds (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε0 : 0 ≤ ε)
    (g : Fin q) :
    (1 - ε) / (q : ℝ) ≤ muEpsWeight ε q g ∧
      muEpsWeight ε q g ≤ (1 + 2 * ε) / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqhc : q ≤ 3 * halfCount q := by
    unfold halfCount; omega
  have hhc0 : (0 : ℝ) < (halfCount q : ℝ) := by
    have : 0 < halfCount q := by unfold halfCount; omega
    exact_mod_cast this
  have hz : 0 ≤ if isRightHalf q g then ε * (halfCount q : ℝ)⁻¹ else 0 := by
    split_ifs <;> positivity
  have h3 : (halfCount q : ℝ)⁻¹ ≤ 3 * (q : ℝ)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hhc0 hq0, one_mul]
    exact_mod_cast hqhc
  constructor
  · rw [div_eq_mul_inv]
    exact le_add_of_nonneg_right hz
  · by_cases h : isRightHalf q g
    · rw [div_eq_mul_inv]
      unfold muEpsWeight
      rw [if_pos h]
      calc (1 - ε) * (q : ℝ)⁻¹ + ε * (halfCount q : ℝ)⁻¹
          ≤ (1 - ε) * (q : ℝ)⁻¹ + ε * (3 * (q : ℝ)⁻¹) :=
            add_le_add_right (mul_le_mul_of_nonneg_left h3 hε0) _
        _ = (1 + 2 * ε) * (q : ℝ)⁻¹ := by ring
    · rw [div_eq_mul_inv]
      unfold muEpsWeight
      rw [if_neg h, add_zero]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hq0.le)

theorem muEpsWeight_nonneg (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (g : Fin q) : 0 ≤ muEpsWeight ε q g := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h1 := (muEpsWeight_bounds q hq ε hε0 g).1
  have h2 : 0 ≤ (1 - ε) / (q : ℝ) := div_nonneg (by linarith) hq0.le
  linarith

theorem card_rightHalf (q : ℕ) (hq : 0 < q) :
    ∑ g : Fin q, (if isRightHalf q g then (1 : ℝ) else 0)
      = ((halfCount q : ℕ) : ℝ) := by
  have hq4 : q / 4 < q := by omega
  have hsplit : ∀ g : Fin q, (if isRightHalf q g then (1 : ℝ) else 0)
      = (if (g : ℕ) ≤ q / 4 then (1 : ℝ) else 0)
        + (if q - q / 4 ≤ (g : ℕ) then (1 : ℝ) else 0) := by
    intro g
    rcases Decidable.em ((g : ℕ) ≤ q / 4) with h1 | h1 <;>
      rcases Decidable.em (q - q / 4 ≤ (g : ℕ)) with h2 | h2
    · exfalso; omega
    · rw [if_pos (show isRightHalf q g by exact Or.inl h1), if_pos h1, if_neg h2]
      ring
    · rw [if_pos (show isRightHalf q g by exact Or.inr h2), if_neg h1, if_pos h2]
      ring
    · rw [if_neg (show ¬ isRightHalf q g by
            unfold isRightHalf
            rintro (hc | hc)
            · exact h1 hc
            · exact h2 hc), if_neg h1, if_neg h2]
      ring
  rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib,
    Finset.sum_boole, Finset.sum_boole]
  have hA : (Finset.univ.filter (fun g : Fin q => (g : ℕ) ≤ q / 4)).card
      = q / 4 + 1 := by
    have hset : (Finset.univ.filter (fun g : Fin q => (g : ℕ) ≤ q / 4))
        = Finset.Iic (⟨q / 4, hq4⟩ : Fin q) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
        Fin.le_def]
    rw [hset, Fin.card_Iic]
  have hB : (Finset.univ.filter (fun g : Fin q => q - q / 4 ≤ (g : ℕ))).card
      = q / 4 := by
    rcases Nat.lt_or_ge (q - q / 4) q with hcq | hcq
    · have hset : (Finset.univ.filter (fun g : Fin q => q - q / 4 ≤ (g : ℕ)))
          = Finset.Ici (⟨q - q / 4, hcq⟩ : Fin q) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici,
          Fin.le_def]
      rw [hset, Fin.card_Ici]
      show q - (q - q / 4) = q / 4
      omega
    · have hempty : (Finset.univ.filter (fun g : Fin q => q - q / 4 ≤ (g : ℕ)))
          = ∅ := by
        ext g
        simp
        have hg := g.isLt
        omega
      rw [hempty, Finset.card_empty]
      omega
  rw [hA, hB]
  unfold halfCount
  push_cast
  ring

theorem sum_muEpsWeight (q : ℕ) (hq : 0 < q) (ε : ℝ) (_hε0 : 0 ≤ ε) (_hε1 : ε ≤ 1) :
    ∑ g : Fin q, muEpsWeight ε q g = 1 := by
  have hhc : (0 : ℝ) < ((halfCount q : ℕ) : ℝ) := by
    have : 0 < halfCount q := by unfold halfCount; omega
    exact_mod_cast this
  have hsum0 : ∑ g : Fin q, (1 - ε) * ((q : ℕ) : ℝ)⁻¹ = 1 - ε := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hqne : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  have hsumc : ∑ g : Fin q, (if isRightHalf q g then ε * ((halfCount q : ℕ) : ℝ)⁻¹ else 0)
      = ε * ((halfCount q : ℕ) : ℝ)⁻¹ * ((halfCount q : ℕ) : ℝ) := by
    have hscale : ∑ g : Fin q, (if isRightHalf q g then ε * ((halfCount q : ℕ) : ℝ)⁻¹ else 0)
        = ε * ((halfCount q : ℕ) : ℝ)⁻¹
          * ∑ g : Fin q, (if isRightHalf q g then (1 : ℝ) else 0) := by
      have hpt : ∀ g : Fin q,
          (if isRightHalf q g then ε * ((halfCount q : ℕ) : ℝ)⁻¹ else 0)
          = ε * ((halfCount q : ℕ) : ℝ)⁻¹
              * (if isRightHalf q g then (1 : ℝ) else 0) := by
        intro g
        by_cases h : isRightHalf q g <;> simp [h]
      exact (Finset.sum_congr rfl fun g _ => hpt g).trans (Finset.mul_sum _ _ _).symm
    rw [hscale, card_rightHalf q hq]
  calc ∑ g : Fin q, muEpsWeight ε q g
      = ∑ g : Fin q, (1 - ε) * ((q : ℕ) : ℝ)⁻¹
        + ∑ g : Fin q, (if isRightHalf q g then ε * ((halfCount q : ℕ) : ℝ)⁻¹ else 0) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun g _ => rfl
    _ = 1 := by
          rw [hsum0, hsumc, mul_assoc, inv_mul_cancel₀ hhc.ne', mul_one]
          linarith

private theorem omega_prim (q : ℕ) (hq : 0 < q) : IsPrimitiveRoot (omega q) q := by
  have hom : omega q = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) := by
    rw [omega]
    congr 1
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    push_cast
    field_simp
  rw [hom]
  exact Complex.isPrimitiveRoot_exp q hq.ne'

private theorem omega_pow_q (q : ℕ) (hq : 0 < q) : omega q ^ q = 1 :=
  (omega_prim q hq).pow_eq_one

private theorem omega_pow_eq_one_iff (q : ℕ) (hq : 0 < q) (i : ℕ) :
    omega q ^ i = 1 ↔ q ∣ i :=
  (omega_prim q hq).pow_eq_one_iff_dvd i

private theorem charSum (q : ℕ) (hq : 0 < q) (i : ℕ) :
    ∑ g : Fin q, omega q ^ ((g : ℕ) * i) = if q ∣ i then (q : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun g => omega q ^ (g * i)) q]
  by_cases hd : q ∣ i
  · rw [if_pos hd]
    have hone : omega q ^ i = 1 := (omega_pow_eq_one_iff q hq i).mpr hd
    have hconv : ∀ g ∈ Finset.range q, omega q ^ (g * i) = (1 : ℂ) ^ g := by
      intro g _
      rw [Nat.mul_comm, pow_mul, hone]
    rw [Finset.sum_congr rfl hconv]
    simp
  · rw [if_neg hd]
    have hr1 : omega q ^ i ≠ 1 := fun h => hd ((omega_pow_eq_one_iff q hq i).mp h)
    have hconv : ∀ g ∈ Finset.range q, omega q ^ (g * i) = (omega q ^ i) ^ g := by
      intro g _
      rw [Nat.mul_comm, pow_mul]
    rw [Finset.sum_congr rfl hconv]
    have hxpq : (omega q ^ i) ^ q = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, omega_pow_q q hq, one_pow]
    have hgeom := geom_sum_mul (omega q ^ i) q
    rw [hxpq, sub_self] at hgeom
    rcases mul_eq_zero.mp hgeom with h0 | h1
    · exact h0
    · exact absurd (sub_eq_zero.mp h1) hr1

private theorem star_omega (q : ℕ) (hq : 0 < q) (g l : Fin q) :
    star (omega q ^ ((g : ℕ) * (l : ℕ))) = omega q ^ ((g : ℕ) * (q - (l : ℕ))) := by
  have hzw : omega q ^ ((g : ℕ) * (l : ℕ)) * omega q ^ ((g : ℕ) * (q - (l : ℕ))) = 1 := by
    have hl := l.isLt
    have hsum : (l : ℕ) + (q - (l : ℕ)) = q := by omega
    rw [← pow_add, ← Nat.mul_add, hsum, Nat.mul_comm, pow_mul, omega_pow_q q hq, one_pow]
  have hst : star (omega q ^ ((g : ℕ) * (l : ℕ))) * omega q ^ ((g : ℕ) * (l : ℕ)) = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      norm_pow, norm_omega q, one_pow]
    norm_num
  calc star (omega q ^ ((g : ℕ) * (l : ℕ)))
      = star (omega q ^ ((g : ℕ) * (l : ℕ))) * 1 := by ring
    _ = star (omega q ^ ((g : ℕ) * (l : ℕ))) *
          (omega q ^ ((g : ℕ) * (l : ℕ)) * omega q ^ ((g : ℕ) * (q - (l : ℕ)))) := by rw [hzw]
    _ = (star (omega q ^ ((g : ℕ) * (l : ℕ))) * omega q ^ ((g : ℕ) * (l : ℕ))) *
          omega q ^ ((g : ℕ) * (q - (l : ℕ))) := by ring
    _ = 1 * omega q ^ ((g : ℕ) * (q - (l : ℕ))) := by rw [hst]
    _ = omega q ^ ((g : ℕ) * (q - (l : ℕ))) := by ring

private theorem dft_tight (q : ℕ) (hq : 0 < q) (v : Fin q → ℂ) :
    ∑ g : Fin q, ‖∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k‖ ^ 2
      = q * ∑ k : Fin q, ‖v k‖ ^ 2 := by
  have hcast : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
    intro w
    rw [Complex.star_def]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]
  have hL : ((∑ g : Fin q, ‖∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k‖ ^ 2 : ℝ) : ℂ)
      = ∑ g : Fin q, (∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k) *
          star (∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun g _ => hcast _
  have hR : ((q * ∑ k : Fin q, ‖v k‖ ^ 2 : ℝ) : ℂ)
      = (q : ℂ) * ∑ k : Fin q, (v k * star (v k)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hcast (v k)
  have hterm : ∀ (g k l : Fin q),
      (omega q ^ ((g : ℕ) * (k : ℕ)) * v k) * star (omega q ^ ((g : ℕ) * (l : ℕ)) * v l)
        = (v k * star (v l)) * omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) := by
    intro g k l
    rw [star_mul, star_omega q hq g l]
    have hcomb : omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ))))
        = omega q ^ ((g : ℕ) * (k : ℕ)) * omega q ^ ((g : ℕ) * (q - (l : ℕ))) := by
      rw [Nat.mul_add, pow_add]
    calc (omega q ^ ((g : ℕ) * (k : ℕ)) * v k) *
          (star (v l) * omega q ^ ((g : ℕ) * (q - (l : ℕ))))
        = (omega q ^ ((g : ℕ) * (k : ℕ)) * omega q ^ ((g : ℕ) * (q - (l : ℕ))))
            * (v k * star (v l)) := by ring
      _ = omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) * (v k * star (v l)) := by
          rw [← hcomb]
      _ = (v k * star (v l)) * omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) := by ring
  have hiff : ∀ (k l : Fin q),
      q ∣ ((k : ℕ) + (q - (l : ℕ))) ↔ (l : ℕ) = (k : ℕ) := by
    intro k l
    have hk := k.isLt
    have hl := l.isLt
    constructor
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      have hm2 : m < 2 := by
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · exact hm2
        · exfalso
          have h3 : (k : ℕ) + (q - (l : ℕ)) < 2 * q := by omega
          rw [hm] at h3
          have h4 : 2 * q ≤ m * q := Nat.mul_le_mul hm2 (Nat.le_refl q)
          simp only [Nat.mul_comm] at h3 h4
          omega
      rcases (show m = 0 ∨ m = 1 by omega) with hm0 | hm0
      · rw [hm0] at hm
        omega
      · rw [hm0] at hm
        omega
    · intro he
      exact ⟨1, by omega⟩
  refine (Complex.ofReal_inj).mp ?_
  rw [hL]
  calc ∑ g : Fin q, (∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k) *
          star (∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k)
      = ∑ g : Fin q, ∑ k : Fin q, ∑ l : Fin q,
          (v k * star (v l)) * omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm g k l
    _ = ∑ k : Fin q, ∑ l : Fin q, ∑ g : Fin q,
          (v k * star (v l)) * omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin q, ∑ l : Fin q,
          (v k * star (v l)) * ∑ g : Fin q, omega q ^ ((g : ℕ) * ((k : ℕ) + (q - (l : ℕ)))) := by
        exact Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k : Fin q, ∑ l : Fin q,
          (v k * star (v l)) * (if (l : ℕ) = (k : ℕ) then (q : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [charSum q hq ((k : ℕ) + (q - (l : ℕ)))]
        simp only [hiff k l]
    _ = ∑ k : Fin q, (q : ℂ) * (v k * star (v k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hcond : ∀ l : Fin q,
            (if (l : ℕ) = (k : ℕ) then (q : ℂ) else 0) = (if l = k then (q : ℂ) else 0) := by
          intro l
          by_cases h : l = k
          · rw [if_pos (by rw [h]), if_pos h]
          · rw [if_neg (by
              intro hc
              exact h (Fin.val_inj.mp hc)), if_neg h]
        have hrew : ∑ l : Fin q, (v k * star (v l)) * (if (l : ℕ) = (k : ℕ) then (q : ℂ) else 0)
            = ∑ l : Fin q, (v k * star (v l)) * (if l = k then (q : ℂ) else 0) :=
          Finset.sum_congr rfl fun l _ => by rw [hcond l]
        rw [hrew]
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ k)]
        ring
    _ = (q : ℂ) * ∑ k : Fin q, (v k * star (v k)) := (Finset.mul_sum _ _ _).symm
    _ = ((q * ∑ k : Fin q, ‖v k‖ ^ 2 : ℝ) : ℂ) := hR.symm

theorem actual_dft_tight (q : ℕ) (hq : 0 < q) (v : Fin q → ℂ) :
    ∑ g : Fin q, ‖∑ k : Fin q, omega q ^ ((g : ℕ) * (k : ℕ)) * v k‖ ^ 2
      = q * ∑ k : Fin q, ‖v k‖ ^ 2 := dft_tight q hq v

private theorem sum_fin_lt {q : ℕ} (k : ℕ) (hk : k ≤ q) (f : Fin q → ℝ) :
    ∑ i : Fin k, f (Fin.castLE hk i)
      = ∑ i : Fin q, (if (i : ℕ) < k then f i else 0) := by
  have himg : (Finset.univ.image (fun i : Fin k => Fin.castLE hk i))
      = Finset.univ.filter (fun i : Fin q => (i : ℕ) < k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, -, rfl⟩
      simp only [Fin.val_castLE]
      exact i.isLt
    · intro hj
      refine ⟨⟨(j : ℕ), hj⟩, ?_⟩
      exact Fin.eq_of_val_eq (by simp)
  have hinj : Set.InjOn (fun i : Fin k => Fin.castLE hk i)
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a _ b _ hab
    exact Fin.eq_of_val_eq (by simpa using! congrArg Fin.val hab)
  calc ∑ i : Fin k, f (Fin.castLE hk i)
      = ∑ j ∈ Finset.image (fun i : Fin k => Fin.castLE hk i) Finset.univ, f j :=
        (Finset.sum_image hinj).symm
    _ = ∑ j ∈ Finset.univ.filter (fun i : Fin q => (i : ℕ) < k), f j := by
        rw [himg]
    _ = ∑ i : Fin q, (if (i : ℕ) < k then f i else 0) := by
        rw [← Finset.sum_filter (fun i : Fin q => (i : ℕ) < k) f]

theorem lemma36_singular_values (q : ℕ) (hq : 1 < q) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ v : Fin q → ℂ,
      (1 - ε) * ∑ i : Fin q, ‖v i‖ ^ 2 ≤
          ∑ i : Fin q, ‖∑ j : Fin q, Ftilde ε q i j * v j‖ ^ 2 ∧
        ∑ i : Fin q, ‖∑ j : Fin q, Ftilde ε q i j * v j‖ ^ 2 ≤
          (1 + 2 * ε) * ∑ i : Fin q, ‖v i‖ ^ 2 := by
  intro v
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < q)
  have hqne : ((q : ℝ)) ≠ 0 := hq0.ne'
  have hmu : ∀ i : Fin q, (1 - ε) / (q : ℝ) ≤ muEpsWeight ε q i
      ∧ muEpsWeight ε q i ≤ (1 + 2 * ε) / (q : ℝ) := muEpsWeight_bounds q hq ε hε0.le
  have hmu0 : ∀ i : Fin q, 0 ≤ muEpsWeight ε q i :=
    muEpsWeight_nonneg q hq ε hε0.le (by linarith)
  have hdft := dft_tight q (by omega) v
  have hrow : ∀ i : Fin q, ∑ j : Fin q, Ftilde ε q i j * v j
      = ((Real.sqrt (muEpsWeight ε q i) : ℝ) : ℂ) *
        ∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j := by
    intro i
    unfold Ftilde
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      unfold phase
      rw [← pow_mul]
      ring
  have hnormsq : ∀ i : Fin q, ‖∑ j : Fin q, Ftilde ε q i j * v j‖ ^ 2
      = muEpsWeight ε q i
          * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 := by
    intro i
    rw [hrow i, Complex.norm_mul, mul_pow,
      Complex.norm_of_nonneg (Real.sqrt_nonneg (muEpsWeight ε q i)),
      Real.sq_sqrt (hmu0 i)]
  constructor
  · calc (1 - ε) * ∑ i : Fin q, ‖v i‖ ^ 2
        = ((1 - ε) / (q : ℝ)) * (q * ∑ i : Fin q, ‖v i‖ ^ 2) := by
          field_simp
      _ = ((1 - ε) / (q : ℝ))
          * ∑ i : Fin q, ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 := by
          rw [hdft]
      _ ≤ ∑ i : Fin q, muEpsWeight ε q i
          * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 := by
          calc ((1 - ε) / (q : ℝ))
                * ∑ i : Fin q, ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2
              = ∑ i : Fin q, ((1 - ε) / (q : ℝ))
                  * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 :=
                Finset.mul_sum _ _ _
            _ ≤ ∑ i : Fin q, muEpsWeight ε q i
                  * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_right ((hmu i).1) (by positivity)
      _ = ∑ i : Fin q, ‖∑ j : Fin q, Ftilde ε q i j * v j‖ ^ 2 := by
          exact Finset.sum_congr rfl fun i _ => (hnormsq i).symm
  · calc ∑ i : Fin q, ‖∑ j : Fin q, Ftilde ε q i j * v j‖ ^ 2
        = ∑ i : Fin q, muEpsWeight ε q i
          * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 := by
          exact Finset.sum_congr rfl fun i _ => hnormsq i
      _ ≤ ((1 + 2 * ε) / (q : ℝ))
          * ∑ i : Fin q, ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 := by
          calc ∑ i : Fin q, muEpsWeight ε q i
                * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2
              ≤ ∑ i : Fin q, ((1 + 2 * ε) / (q : ℝ))
                  * ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_right ((hmu i).2) (by positivity)
            _ = ((1 + 2 * ε) / (q : ℝ))
                  * ∑ i : Fin q, ‖∑ j : Fin q, omega q ^ ((i : ℕ) * (j : ℕ)) * v j‖ ^ 2 :=
                (Finset.mul_sum _ _ _).symm
      _ = ((1 + 2 * ε) / (q : ℝ)) * (q * ∑ i : Fin q, ‖v i‖ ^ 2) := by rw [hdft]
      _ = (1 + 2 * ε) * ∑ i : Fin q, ‖v i‖ ^ 2 := by field_simp

theorem lemma37_projection_bound {q k : ℕ} (_hk : 0 < k) (ε : ℝ)
    (_hε0 : 0 < ε) (hε1 : ε < 1)
    (F : Fin k → Fin q → ℂ) (u : Fin k → Fin q → ℂ)
    (horth : ∀ i j : Fin k, ∑ x : Fin q, star (u i x) * u j x =
      if i = j then 1 else 0)
    (hspan : ∀ (j : Fin k) (x : Fin q),
      F j x = ∑ i : Fin k, (∑ y : Fin q, star (u i y) * F j y) * u i x)
    (hframe : ∀ (e : Fin k → ℂ) (w : Fin q → ℂ),
      (∀ x : Fin q, w x = ∑ i : Fin k, e i * u i x) →
      (1 - ε) * ∑ i : Fin k, ‖e i‖ ^ 2 ≤
        ∑ j : Fin k, ‖∑ x : Fin q, star (F j x) * w x‖ ^ 2)
    (v : Fin q → ℂ) :
    ∑ i : Fin k, ‖∑ x : Fin q, star (u i x) * v x‖ ^ 2 ≤
      (1 - ε)⁻¹ * ∑ j : Fin k, ‖∑ x : Fin q, star (F j x) * v x‖ ^ 2 := by
  have hεpos : (0 : ℝ) < 1 - ε := by linarith
  have hεne : ((1 : ℝ) - ε) ≠ 0 := hεpos.ne'

  have hres : ∀ m : Fin k,
      ∑ x : Fin q, star (u m x)
        * (v x - ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x) = 0 := by
    intro m
    have hexp : ∀ x : Fin q,
        star (u m x) * (v x - ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
        = star (u m x) * v x
          - star (u m x) * ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x := by
      intro x
      rw [mul_sub]
    simp only [hexp, Finset.sum_sub_distrib]
    have h2 : ∑ x : Fin q, star (u m x)
        * (∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
        = ∑ y : Fin q, star (u m y) * v y := by
      calc ∑ x : Fin q, star (u m x)
            * (∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
          = ∑ x : Fin q, ∑ i : Fin k, star (u m x)
              * ((∑ y : Fin q, star (u i y) * v y) * u i x) :=
              Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
        _ = ∑ i : Fin k, ∑ x : Fin q, star (u m x)
              * ((∑ y : Fin q, star (u i y) * v y) * u i x) := Finset.sum_comm
        _ = ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y)
              * (∑ x : Fin q, star (u m x) * u i x) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by ring
        _ = ∑ i : Fin k, (if m = i then (∑ y : Fin q, star (u i y) * v y) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [horth m i]
            by_cases h : m = i <;> simp [h]
        _ = ∑ y : Fin q, star (u m y) * v y := by simp
    rw [h2, sub_self]

  have hPv : ∀ j : Fin k, (∑ x : Fin q, star (F j x) * v x)
      = ∑ x : Fin q, star (F j x)
          * (∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x) := by
    intro j
    have hstarF : ∀ x : Fin q, star (F j x)
        = ∑ i : Fin k, star (∑ y : Fin q, star (u i y) * F j y) * star (u i x) := by
      intro x
      rw [hspan j x, star_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [star_mul, mul_comm]
    have hdiff : (∑ x : Fin q, star (F j x) * v x)
        - ∑ x : Fin q, star (F j x)
            * (∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
        = ∑ x : Fin q, star (F j x)
            * (v x - ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => (mul_sub _ _ _).symm
    have hzero : ∑ x : Fin q, star (F j x)
        * (v x - ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x) = 0 := by
      simp only [hstarF]
      have hstep : ∀ x : Fin q,
          (∑ i : Fin k, star (∑ y : Fin q, star (u i y) * F j y) * star (u i x))
            * (v x - ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
          = ∑ i : Fin k, star (∑ y : Fin q, star (u i y) * F j y)
              * (star (u i x)
                  * (v x - ∑ i' : Fin k, (∑ y : Fin q, star (u i' y) * v y) * u i' x)) := by
        intro x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hres i, mul_zero]
    exact eq_of_sub_eq_zero (by rw [hdiff, hzero])
  have hfr := hframe (fun i => ∑ y : Fin q, star (u i y) * v y)
    (fun x => ∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)
    (fun _ => rfl)
  have hfr' : (1 - ε) * ∑ i : Fin k, ‖∑ y : Fin q, star (u i y) * v y‖ ^ 2
      ≤ ∑ j : Fin k, ‖∑ x : Fin q, star (F j x) * v x‖ ^ 2 := by
    have hsw : ∑ j : Fin k, ‖∑ x : Fin q, star (F j x)
          * (∑ i : Fin k, (∑ y : Fin q, star (u i y) * v y) * u i x)‖ ^ 2
        = ∑ j : Fin k, ‖∑ x : Fin q, star (F j x) * v x‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [hPv j]
    rw [← hsw]
    exact hfr
  calc ∑ i : Fin k, ‖∑ x : Fin q, star (u i x) * v x‖ ^ 2
      = (1 - ε)⁻¹ * ((1 - ε) * ∑ i : Fin k, ‖∑ x : Fin q, star (u i x) * v x‖ ^ 2) := by
        field_simp
    _ ≤ (1 - ε)⁻¹ * ∑ j : Fin k, ‖∑ x : Fin q, star (F j x) * v x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hfr' (inv_nonneg.mpr hεpos.le)

theorem lemma38_projection_diagonal {q k : ℕ} (hk : 0 < k) (hkq : k < q)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (F : Fin q → Fin q → ℂ) (u : Fin k → Fin q → ℂ)
    (horth : ∀ i j : Fin k, ∑ x : Fin q, star (u i x) * u j x =
      if i = j then 1 else 0)
    (hspan : ∀ (j : Fin k) (x : Fin q),
      F (Fin.castLE (Nat.le_of_lt hkq) j) x =
        ∑ i : Fin k,
          (∑ y : Fin q, star (u i y) * F (Fin.castLE (Nat.le_of_lt hkq) j) y) * u i x)
    (hframe : ∀ (e : Fin k → ℂ) (w : Fin q → ℂ),
      (∀ x : Fin q, w x = ∑ i : Fin k, e i * u i x) →
      (1 - ε) * ∑ i : Fin k, ‖e i‖ ^ 2 ≤
        ∑ j : Fin k,
          ‖∑ x : Fin q, star (F (Fin.castLE (Nat.le_of_lt hkq) j) x) * w x‖ ^ 2)
    (hoff : ∑ j : Fin q,
        (if j = ⟨k, hkq⟩ then (0 : ℝ)
          else ‖∑ x : Fin q, star (F j x) * F ⟨k, hkq⟩ x‖ ^ 2) ≤ 2 * ε ^ 2) :
    ∑ i : Fin k, ‖∑ x : Fin q, star (u i x) * F ⟨k, hkq⟩ x‖ ^ 2 ≤
      2 * ε ^ 2 / (1 - ε) := by
  have hεpos : (0 : ℝ) < 1 - ε := by linarith
  have h37 := lemma37_projection_bound hk ε hε0 hε1
    (fun j : Fin k => F (Fin.castLE (Nat.le_of_lt hkq) j)) u horth hspan hframe
    (F ⟨k, hkq⟩)
  have hpart : ∑ j : Fin k,
        ‖∑ x : Fin q, star (F (Fin.castLE (Nat.le_of_lt hkq) j) x) * F ⟨k, hkq⟩ x‖ ^ 2
      ≤ ∑ j : Fin q,
          (if j = ⟨k, hkq⟩ then (0 : ℝ)
            else ‖∑ x : Fin q, star (F j x) * F ⟨k, hkq⟩ x‖ ^ 2) := by
    have hsw := sum_fin_lt k (Nat.le_of_lt hkq)
      (fun j => ‖∑ x : Fin q, star (F j x) * F ⟨k, hkq⟩ x‖ ^ 2)
    rw [hsw]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h1 : (j : ℕ) < k
    · have hne : j ≠ ⟨k, hkq⟩ := by
        intro hcon
        have : (j : ℕ) = k := by
          have h2 : (j : Fin q) = ⟨k, hkq⟩ := hcon
          apply_fun (fun z => (z : ℕ)) at h2
          simpa using! h2
        omega
      rw [if_pos h1, if_neg hne]
    · rw [if_neg h1]
      positivity
  calc ∑ i : Fin k, ‖∑ x : Fin q, star (u i x) * F ⟨k, hkq⟩ x‖ ^ 2
      ≤ (1 - ε)⁻¹ * ∑ j : Fin k,
          ‖∑ x : Fin q, star (F (Fin.castLE (Nat.le_of_lt hkq) j) x) * F ⟨k, hkq⟩ x‖ ^ 2 :=
          h37
    _ ≤ (1 - ε)⁻¹ * ∑ j : Fin q,
          (if j = ⟨k, hkq⟩ then (0 : ℝ)
            else ‖∑ x : Fin q, star (F j x) * F ⟨k, hkq⟩ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hpart (inv_nonneg.mpr hεpos.le)
    _ ≤ (1 - ε)⁻¹ * (2 * ε ^ 2) :=
          mul_le_mul_of_nonneg_left hoff (inv_nonneg.mpr hεpos.le)
    _ = 2 * ε ^ 2 / (1 - ε) := by field_simp

theorem lemma33_biased_fourier_unitary (q : ℕ) (hq : 1 < q) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (u : Fin q → Fin q → ℂ)
    (horth : ∀ i j : Fin q, ∑ x : Fin q, star (u i x) * u j x =
      if i = j then 1 else 0)
    (hspan : ∀ (k : Fin q) (x : Fin q),
      fourierUnitVec ε q k x
        = ∑ i : Fin q, (∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y) * u i x)
    (hsupp : ∀ (k i : Fin q), (k : ℕ) < (i : ℕ) →
      ∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y = 0)
    (hoff : ∀ k : Fin q, ∑ i : Fin q,
        (if (i : ℕ) < (k : ℕ)
          then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
          else 0) ≤ 2 * ε ^ 2 / (1 - ε)) :
    ∃ F : Matrix (Fin q) (Fin q) ℂ, Fᴴ * F = 1 ∧
      ∀ k : Fin q, ∃ α : Fin q → ℂ,
        (∀ ℓ : Fin q, k < (ℓ : ℕ) → α ℓ = 0) ∧
        (∑ ℓ : Fin q, ‖α ℓ‖ ^ 2 = 1) ∧
        (1 - 4 * ε ^ 2 ≤ ‖α k‖ ^ 2) ∧
        (∀ g : Fin q, (F *ᵥ fourierUnitVec ε q k) g = α g) := by
  have hεpos : (0 : ℝ) < 1 - ε := by linarith
  have hεne : ((1 : ℝ) - ε) ≠ 0 := hεpos.ne'
  have hmu0 : ∀ g : Fin q, 0 ≤ muEpsWeight ε q g :=
    muEpsWeight_nonneg q hq ε hε0.le (by linarith)

  have hnorm1 : ∀ k : Fin q, ∑ g : Fin q, ‖fourierUnitVec ε q k g‖ ^ 2 = 1 := by
    intro k
    have hterm : ∀ g : Fin q, ‖fourierUnitVec ε q k g‖ ^ 2 = muEpsWeight ε q g := by
      intro g
      have hph : ‖phase q g ^ (k : ℕ)‖ = 1 := by
        rw [norm_pow, norm_phase q g, one_pow]
      have hsq : ‖((Real.sqrt (muEpsWeight ε q g) : ℝ) : ℂ)‖ ^ 2
          = muEpsWeight ε q g := by
        rw [Complex.norm_of_nonneg (Real.sqrt_nonneg (muEpsWeight ε q g)),
          Real.sq_sqrt (hmu0 g)]
      unfold fourierUnitVec
      rw [Complex.norm_mul, mul_pow, hsq, hph]
      ring
    rw [Finset.sum_congr rfl (fun g _ => hterm g), sum_muEpsWeight q (by omega) ε hε0.le
      (by linarith)]

  have hcast : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      Complex.star_def, mul_comm]

  have hgen : ∀ (w : Fin q → ℂ),
      (∀ x : Fin q, w x = ∑ i : Fin q, (∑ y : Fin q, star (u i y) * w y) * u i x) →
      ∑ x : Fin q, star (w x) * w x
        = ∑ i : Fin q, star (∑ y : Fin q, star (u i y) * w y)
            * (∑ y : Fin q, star (u i y) * w y) := by
    intro w hw
    have h1 : ∀ x : Fin q, star (w x)
        = ∑ i : Fin q, star (∑ y : Fin q, star (u i y) * w y) * star (u i x) := by
      intro x
      rw [hw x, star_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [star_mul, mul_comm]
    calc ∑ x : Fin q, star (w x) * w x
        = ∑ x : Fin q, (∑ i : Fin q, star (∑ y : Fin q, star (u i y) * w y) * star (u i x))
            * ∑ i : Fin q, (∑ y : Fin q, star (u i y) * w y) * u i x := by
          exact Finset.sum_congr rfl fun x _ => by rw [h1 x, hw x]
      _ = ∑ x : Fin q, ∑ i : Fin q, ∑ i' : Fin q,
          (star (∑ y : Fin q, star (u i y) * w y) * star (u i x))
            * ((∑ y : Fin q, star (u i' y) * w y) * u i' x) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_mul_sum _ _ _ _
      _ = ∑ i : Fin q, ∑ i' : Fin q, ∑ x : Fin q,
          (star (∑ y : Fin q, star (u i y) * w y) * star (u i x))
            * ((∑ y : Fin q, star (u i' y) * w y) * u i' x) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin q, ∑ i' : Fin q,
          (star (∑ y : Fin q, star (u i y) * w y) * (∑ y : Fin q, star (u i' y) * w y))
            * (∑ x : Fin q, star (u i x) * u i' x) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          have hre : ∀ x : Fin q,
              (star (∑ y : Fin q, star (u i y) * w y) * star (u i x))
                * ((∑ y : Fin q, star (u i' y) * w y) * u i' x)
              = (star (∑ y : Fin q, star (u i y) * w y)
                  * (∑ y : Fin q, star (u i' y) * w y))
                * (star (u i x) * u i' x) := fun x => by ring
          rw [Finset.sum_congr rfl fun x _ => hre x, ← Finset.mul_sum]
      _ = ∑ i : Fin q, star (∑ y : Fin q, star (u i y) * w y)
          * (∑ y : Fin q, star (u i y) * w y) := by
          have horth' : ∀ (i i' : Fin q),
              (star (∑ y : Fin q, star (u i y) * w y)
                  * (∑ y : Fin q, star (u i' y) * w y))
                * (∑ x : Fin q, star (u i x) * u i' x)
              = if i = i' then star (∑ y : Fin q, star (u i y) * w y)
                    * (∑ y : Fin q, star (u i' y) * w y) else 0 := by
            intro i i'
            rw [horth i i']
            by_cases h : i = i' <;> simp [h]
          rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => horth' i i']
          simp

  have hL : ∀ k : Fin q,
      ∑ i : Fin q, ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2 = 1 := by
    intro k
    have h1 : ((∑ g : Fin q, ‖fourierUnitVec ε q k g‖ ^ 2 : ℝ) : ℂ)
        = ∑ x : Fin q, star (fourierUnitVec ε q k x) * fourierUnitVec ε q k x := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun x _ => hcast _
    have h2 : ((1 : ℝ) : ℂ)
        = ((∑ i : Fin q, ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hnorm1 k, h1, hgen (fourierUnitVec ε q k) (hspan k)]
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (hcast _).symm
    exact Complex.ofReal_inj.mp h2.symm
  refine ⟨Matrix.of (fun i x => star (u i x)), ?_, ?_⟩
  · have hFF : Matrix.of (fun i x => star (u i x))
        * (Matrix.of (fun i x => star (u i x)))ᴴ = 1 := by
      ext a c
      simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply,
        star_star, Matrix.one_apply]
      exact horth a c
    exact (Matrix.mul_eq_one_comm_of_card_eq (m := Fin q) (n := Fin q) (R := ℂ)
      rfl).mp hFF
  · intro k
    refine ⟨fun i => ∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y,
      hsupp k, hL k, ?_, ?_⟩
    · have hdecomp : ∑ i : Fin q,
          ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
          = ‖∑ y : Fin q, star (u k y) * fourierUnitVec ε q k y‖ ^ 2
            + ∑ i : Fin q, (if (i : ℕ) < (k : ℕ)
                then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
                else 0) := by
        have hpoint : ∀ i : Fin q,
            ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
            = (if i = k then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2 else 0)
              + (if (i : ℕ) < (k : ℕ)
                then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
                else 0) := by
          intro i
          rcases Nat.lt_trichotomy (i : ℕ) (k : ℕ) with h | h | h
          · have hne : i ≠ k := by
              intro hc
              have hval : (i : ℕ) = (k : ℕ) := by rw [hc]
              omega
            rw [if_neg hne, if_pos h]
            ring
          · rw [if_pos (Fin.val_inj.mp h), if_neg (by omega)]
            ring
          · have hne : i ≠ k := by
              intro hc
              have hval : (i : ℕ) = (k : ℕ) := by rw [hc]
              omega
            have h0 : ∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y = 0 :=
              hsupp k i h
            rw [if_neg hne, if_neg (by omega), h0]
            simp
        calc ∑ i : Fin q, ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
            = ∑ i : Fin q, ((if i = k
                  then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
                  else 0)
                + (if (i : ℕ) < (k : ℕ)
                  then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
                  else 0)) :=
              Finset.sum_congr rfl fun i _ => hpoint i
          _ = ‖∑ y : Fin q, star (u k y) * fourierUnitVec ε q k y‖ ^ 2
                + ∑ i : Fin q, (if (i : ℕ) < (k : ℕ)
                    then ‖∑ y : Fin q, star (u i y) * fourierUnitVec ε q k y‖ ^ 2
                    else 0) := by
              rw [Finset.sum_add_distrib]
              congr 1
              simp
      have hoffk := hoff k
      have hge : (1 : ℝ) - 2 * ε ^ 2 / (1 - ε)
          ≤ ‖∑ y : Fin q, star (u k y) * fourierUnitVec ε q k y‖ ^ 2 := by
        have := hL k
        have := hdecomp
        have := hoffk
        linarith
      have hε2 : 2 * ε ^ 2 / (1 - ε) ≤ 4 * ε ^ 2 := by
        have hd : (0 : ℝ) < 1 - ε := by linarith
        rw [div_le_iff₀ hd]
        nlinarith [sq_nonneg ε, mul_nonneg (show (0 : ℝ) ≤ 2 * ε by positivity)
          (show (0 : ℝ) ≤ 1 - 2 * ε by linarith)]
      linarith
    · intro g
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]

end Qatlib.Papers.AmpInvReqTang26.BiasedFourier
