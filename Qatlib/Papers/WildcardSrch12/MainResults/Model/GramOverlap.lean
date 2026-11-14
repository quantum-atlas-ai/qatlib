/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Papers.WildcardSrch12.MainResults.Model.SourceModel
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# WildcardSrch12 — the Gram matrix of `|ψ_x^k⟩`

Ambainis–Montanaro, arXiv:1210.1148v4, §3 ("The pretty good measurement"):

> "the Gram matrix of the states `|ψ_x^k⟩` is given by
>  `G_xy = C(n - d(x,y), k) / C(n,k)`"    (paper, §3, formula (1))

Here `G` is realized as the library's `ensembleGram` of the actual column
family, so this file proves that the *actual* Gram matrix has the paper's
entries — an honest computation of a finite sum, not a definitional shortcut.
This is the starting point of Lemmas 7–9 of the paper.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open ComplexConjugate
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults

/-- Complex conjugation is the star operation. -/
theorem star_eq_conj (z : ℂ) : star z = conj z := congrFun Complex.star_def z

/-- The amplitude of `|ψ_x^k⟩` at a basis vector with the correct subset size and
the correct restriction equals the uniform normalization `C(n,k)^{-1/2}`. -/
theorem psiAmp_eq_of_pos {n k : ℕ} (x : BitStr n) (p : StateIdx n)
    (h : p.1.card = k ∧ p.2 = embedOn x p.1) :
    psiAmp k x p = ((Real.sqrt ((Nat.choose n k : ℝ)⁻¹) : ℝ) : ℂ) := by
  simp [psiAmp, ite_eq_left h]

/-- Off the support of `|ψ_x^k⟩` the amplitude vanishes. -/
theorem psiAmp_eq_zero_of_neg {n k : ℕ} (x : BitStr n) (p : StateIdx n)
    (h : ¬ (p.1.card = k ∧ p.2 = embedOn x p.1)) : psiAmp k x p = 0 := by
  simp [psiAmp, ite_eq_right h]

/-- The squared module of a single normalized amplitude: the constant
`C(n,k)^{-1}`. -/
theorem conj_amp_mul_self (n k : ℕ) :
    conj (((Real.sqrt ((Nat.choose n k : ℝ)⁻¹)) : ℝ) : ℂ)
        * (((Real.sqrt ((Nat.choose n k : ℝ)⁻¹)) : ℝ) : ℂ)
      = ((Nat.choose n k : ℝ)⁻¹ : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The amplitude product `conj(ψ_x^k(p)) · ψ_y^k(p)` is the constant
`C(n,k)^{-1}` exactly on the basis vectors `(S, x|_S)` where `S` has cardinality
`k` and the two restrictions `x|_S`, `y|_S` coincide, and `0` elsewhere. -/
theorem conj_psiAmp_mul {n k : ℕ} (x y : BitStr n) (p : StateIdx n) :
    conj (psiAmp k y p) * psiAmp k x p =
      if p.1.card = k ∧ p.2 = embedOn x p.1 ∧ p.2 = embedOn y p.1
      then ((Nat.choose n k : ℝ)⁻¹ : ℂ) else 0 := by
  by_cases hx : p.1.card = k ∧ p.2 = embedOn x p.1
  · by_cases hy : p.1.card = k ∧ p.2 = embedOn y p.1
    · rw [psiAmp_eq_of_pos y p hy, psiAmp_eq_of_pos x p hx, conj_amp_mul_self,
        ite_eq_left ⟨hx.1, hx.2, hy.2⟩]
    · rw [psiAmp_eq_zero_of_neg y p hy, psiAmp_eq_of_pos x p hx, map_zero, zero_mul,
        ite_eq_right (fun h => hy ⟨h.1, h.2.2⟩)]
  · rw [psiAmp_eq_zero_of_neg x p hx, mul_zero,
      ite_eq_right (fun h => hx ⟨h.1, h.2.1⟩)]

/-- Inner sum over the value register: for a fixed subset `S` at most one value
of the `|x_S⟩` register carries amplitude, so the fibre sum is a single term. -/
theorem sum_fibre_psiAmp {n k : ℕ} (x y : BitStr n) (S : Finset (Fin n)) :
    (∑ b : BitStr n, conj (psiAmp k y (S, b)) * psiAmp k x (S, b))
      = if S.card = k ∧ S ⊆ agreeSet x y then ((Nat.choose n k : ℝ)⁻¹ : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun b _ => conj_psiAmp_mul x y (S, b))]
  by_cases hk : S.card = k
  · by_cases hsub : S ⊆ agreeSet x y
    · have he : embedOn x S = embedOn y S := (embedOn_eq_iff x y S).mpr hsub
      rw [ite_eq_left ⟨hk, hsub⟩, Finset.sum_eq_single (embedOn x S)]
      · rw [ite_eq_left ⟨hk, rfl, he⟩]
      · intro b _ hb
        rw [ite_eq_right (fun h => hb h.2.1)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have he : embedOn x S ≠ embedOn y S := fun h => hsub ((embedOn_eq_iff x y S).mp h)
      rw [ite_eq_right (fun h => hsub h.2)]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [ite_eq_right]
      rintro ⟨_, h1, h2⟩
      exact he (h1.symm.trans h2)
  · rw [ite_eq_right (fun h => hk h.1)]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [ite_eq_right]
    rintro ⟨h, _, _⟩
    exact hk h

/-- The inner product `⟨ψ_x^k|ψ_y^k⟩` is the number of `k`-subsets of the
agreement set, times `C(n,k)^{-1}`. -/
theorem sum_conj_psiAmp_mul {n k : ℕ} (x y : BitStr n) :
    (∑ p : StateIdx n, conj (psiAmp k y p) * psiAmp k x p)
      = ((((Finset.univ.filter (fun S : Finset (Fin n) => S.card = k ∧ S ⊆ agreeSet x y)).card : ℝ) : ℂ))
          * ((Nat.choose n k : ℝ)⁻¹ : ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_fibre_psiAmp]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, ← Complex.ofReal_natCast]

/-- The number of `k`-element subsets of `[n]` that are contained in `T` is
`C(|T|, k)`. -/
theorem card_filter_powersetCard_subset {n k : ℕ} (T : Finset (Fin n)) :
    ((Finset.univ.powersetCard k).filter (fun S => S ⊆ T)).card = Nat.choose T.card k := by
  have h : (Finset.univ.powersetCard k).filter (fun S => S ⊆ T) = T.powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hsub⟩
      exact ⟨hsub, hc⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨⟨Finset.subset_univ S, hc⟩, hsub⟩
  rw [h, Finset.card_powersetCard]

/-- Cardinality of the `k`-subsets of `T`, in the `filter` presentation produced
by the fibre-sum computation. -/
theorem card_filter_card_eq_subset {n k : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k ∧ S ⊆ T)).card
      = Nat.choose T.card k := by
  have h : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k ∧ S ⊆ T))
      = (Finset.univ.powersetCard k).filter (fun S => S ⊆ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, hc, hsub⟩
      exact ⟨⟨Finset.subset_univ S, hc⟩, hsub⟩
    · rintro ⟨⟨-, hc⟩, hsub⟩
      exact ⟨Finset.mem_univ S, hc, hsub⟩
  rw [h, card_filter_powersetCard_subset]

/-- The `(y,x)` entry of the actual Gram matrix of the states `|ψ_x^k⟩` is the
paper's `G_xy = C(n - d(x,y), k)/C(n,k)` (§3, formula (1)). -/
theorem gramMat_mat {n k : ℕ} (x y : BitStr n) :
    (gramMat n k).mat y x = ((gramEntry n k (hammingDist x y) : ℝ) : ℂ) := by
  have hmat : (gramMat n k).mat y x
      = ∑ d : Fin (stateDim n), star (psiEnsemble n k d y) * psiEnsemble n k d x := by
    simp only [gramMat, ensembleGram, HermitianMat.mat_mk]
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
  rw [hmat]
  trans ∑ p : StateIdx n, conj (psiAmp k y p) * psiAmp k x p
  · rw [← Equiv.sum_comp (Fintype.equivFin (StateIdx n))]
    apply Finset.sum_congr rfl
    intro p _
    simp only [psiEnsemble, stateColumn, Equiv.symm_apply_apply]
    rfl
  · rw [sum_conj_psiAmp_mul, card_filter_card_eq_subset, card_agreeSet]
    have hcast : ((Nat.choose (n - hammingDist x y) k : ℝ) : ℂ)
          * ((Nat.choose n k : ℝ)⁻¹ : ℂ)
        = ((gramEntry n k (hammingDist x y) : ℝ) : ℂ) := by
      rw [gramEntry, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    exact hcast

end Qatlib.Papers.WildcardSrch12.MainResults
