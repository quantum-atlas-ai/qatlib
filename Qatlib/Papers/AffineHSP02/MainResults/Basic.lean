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

/-!
# Reconstruction predicates and orbit counting

Introduces finite probability laws, abstract reconstruction predicates, and the cardinality data
`QHedral` for a group with a normal translation subgroup. These predicates specify finite laws
and decoders without encoding computational running times.

The analytic part defines roots of unity and orbit sums, then converts a bound on their norm
into a lower bound on the number of orbit residues in the middle interval `(p/6, 5p/6)`. See
[MooreEtAl2002].

## Main statements

* `MeasurementReconstructible`: finite laws distinguish subgroups injectively.
* `counting_of_gauss_bound`: a character-sum bound forces many residues into the middle
  interval.
* `source_lemma1_of_gaussBound`: the counting result specialized to multiplicative orbits.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AffineHSP02.MainResults

open scoped BigOperators

/-- Cardinality data for a group of size `p * q` with a normal subgroup of size `p`, designated
as the translation subgroup. -/
structure QHedral (p q : ℕ) (G : Type) [Group G] where

  trans : Subgroup G
  trans_normal : trans.Normal

  trans_card : Nat.card trans = p

  group_card : Nat.card G = p * q

/-- The conjugate of `H` by `b`, obtained as its image under conjugation. -/
def conjugateSubgroup {G : Type} [Group G] (H : Subgroup G) (b : G) : Subgroup G :=
  H.map (MulAut.conj b).toMonoidHom

/-- A finite probability law with nonnegative real weights summing to one. -/
structure FinLaw (Ω : Type) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1

/-- Half the sum of the absolute differences between the weights of two finite probability laws. -/
noncomputable def totalVariation {Ω : Type} [Fintype Ω] (P Q : FinLaw Ω) : ℝ :=
  (1 / 2) * ∑ x, |P.prob x - Q.prob x|

/-- An assignment of a finite probability law to each subgroup of `G`. -/
structure SubgroupLaw (G Ω : Type) [Group G] [Fintype Ω] where
  law : Subgroup G → FinLaw Ω

/-- The existence of finite probability laws whose assignment to subgroups is injective. -/
def MeasurementReconstructible (G : Type) [Group G] : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω), ∃ M : SubgroupLaw G Ω, Function.Injective M.law

/-- The existence of finite subgroup-dependent laws and a decoder that identifies every subgroup
on an event of probability at least one half. -/
def FullyReconstructible (G : Type) [Group G] : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω), ∃ M : SubgroupLaw G Ω, ∃ dec : Ω → Subgroup G,
    ∀ s : Subgroup G, ∃ F : Finset Ω,
      (∀ ω ∈ F, dec ω = s) ∧ (1 / 2 : ℝ) ≤ ∑ ω ∈ F, (M.law s).prob ω

/-- The existence of finite laws for conjugate parameters with total variation at least a common
`δ ∈ [1/4, 1]` whenever the conjugate subgroups differ. -/
def HiddenConjugatesMeasurementReconstructible (G : Type) [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (δ : ℝ) (law : G → FinLaw Ω),
    (1 / 4 ≤ δ) ∧ (δ ≤ 1) ∧
    ∀ b b' : G, conjugateSubgroup H b ≠ conjugateSubgroup H b' →
      δ ≤ totalVariation (law b) (law b')

/-- The existence of finite laws and a decoder that recovers each conjugating parameter on an
event of probability at least one half. -/
def HiddenConjugatesFullyReconstructible (G : Type) [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (law : G → FinLaw Ω) (dec : Ω → G),
    ∀ b : G, ∃ F : Finset Ω,
      (∀ ω ∈ F, dec ω = b) ∧ (1 / 2 : ℝ) ≤ ∑ ω ∈ F, (law b).prob ω

/-- The existence of positive natural `C` and natural `k` with `p - 1 ≤ C * q * (Nat.log 2 p +
1)^k`. -/
def IndexPolylog (p q : ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ p - 1 ≤ C * q * (Nat.log 2 p + 1) ^ k

/-- The existence of positive natural `C` and natural `k` with `n ≤ C * Nat.card H * (Nat.log 2
n + 1)^k`. -/
def IndexPolylogSub {G : Type} [Group G] (H : Subgroup G) (n : ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ n ≤ C * Nat.card H * (Nat.log 2 n + 1) ^ k

/-- The complex exponential `exp(2πi / p)` used for the orbit sums. -/
noncomputable def qroot (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

/-- The `t`th power of `qroot p` equals the complex exponential of `i * (2π * t / p)`. -/
theorem qroot_pow_eq (p t : ℕ) :
    qroot p ^ t = Complex.exp (((2 * Real.pi * t / p : ℝ) : ℂ) * Complex.I) := by
  unfold qroot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The real part of `qroot p ^ t` is `cos(2π * t / p)`. -/
theorem re_qroot_pow (p t : ℕ) : (qroot p ^ t).re = Real.cos (2 * Real.pi * t / p) := by
  rw [qroot_pow_eq, Complex.exp_ofReal_mul_I_re]

/-- The complex norm of every natural power of `qroot p` is one. -/
theorem norm_qroot_pow (p t : ℕ) : ‖qroot p ^ t‖ = 1 := by
  rw [qroot_pow_eq, Complex.norm_exp_ofReal_mul_I]

/-- The real part of every natural power of `qroot p` is at least −1. -/
theorem re_qroot_pow_ge_neg_one (p t : ℕ) : -1 ≤ (qroot p ^ t).re := by
  have h1 : |(qroot p ^ t).re| ≤ ‖qroot p ^ t‖ := Complex.abs_re_le_norm _
  rw [norm_qroot_pow] at h1
  have h2 : -1 ≤ (qroot p ^ t).re := by
    have := (abs_le.1 h1).1
    linarith
  exact h2

/-- If `p > 0` and `x ≤ p/6`, then `cos(2π * x / p) ≥ 1/2`. -/
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

/-- If `p > 0` and `5p/6 ≤ x < p`, then `cos(2π * x / p) ≥ 1/2`. -/
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

/-- If a sum of `q` root-of-unity phases has norm at most `B ≤ (3/2) * ε * q`, at least `(1/3 -
ε) * q` of the associated residues lie strictly between `p/6` and `5p/6`. -/
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

/-- The natural representative of the residue `a^t * k` modulo `p`. -/
def orbitResidue (p : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) (t : ℕ) : ℕ :=
  (((a : ZMod p) ^ t) * k).val

/-- The sum of `qroot p` raised to the orbit residues for `0 ≤ t < q`. -/
noncomputable def gaussSum (p : ℕ) (a : (ZMod p)ˣ) (k : ZMod p) (q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range q, qroot p ^ (orbitResidue p a k t)

/-- For positive `p`, every orbit residue is strictly smaller than `p`. -/
theorem orbitResidue_lt (p : ℕ) (hp : 0 < p) (a : (ZMod p)ˣ) (k : ZMod p)
    (t : ℕ) : orbitResidue p a k t < p := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  unfold orbitResidue
  exact ZMod.val_lt _

/-- A bound `B ≤ (3/2) * ε * q` on the orbit Gauss-sum norm forces at least `(1/3 - ε) * q`
orbit indices into `(p/6, 5p/6)` [Moore et al., Lemma 1][MooreEtAl2002]. -/
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

/-- A norm bound `C * sqrt(p)` gives at least `(1/3 - 2 * C * sqrt(p) / (3 * q)) * q` indices
with residues in `(p/6, 5p/6)`. -/
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
