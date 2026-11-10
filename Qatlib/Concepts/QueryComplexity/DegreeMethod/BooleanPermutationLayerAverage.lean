/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.PermutationLayerAverage
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalBeal
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanPermutationLayerAverage

open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

def permInput (σ : Equiv.Perm I) (x : I → Bool) : I → Bool := fun i => x (σ i)

omit [Fintype I] [DecidableEq I] in

theorem permInput_permInput (τ σ : Equiv.Perm I) (x : I → Bool) :
    permInput σ (permInput τ x) = permInput (τ * σ) x := by
  funext i
  simp [permInput, Equiv.Perm.mul_apply]

omit [DecidableEq I] in

theorem boolWeight_eq_card_subtype (x : I → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x = Fintype.card {i : I // x i = true} := by
  show (Finset.univ.filter fun i : I => x i = true).card = _
  rw [Fintype.card_subtype]

omit [DecidableEq I] in

theorem boolWeight_permInput (σ : Equiv.Perm I) (x : I → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (permInput σ x) = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x := by
  have h : {i : I // x (σ i) = true} ≃ {i : I // x i = true} :=
    σ.subtypeEquiv fun _ => Iff.rfl
  rw [boolWeight_eq_card_subtype (permInput σ x), boolWeight_eq_card_subtype x]
  exact Fintype.card_congr h

omit [DecidableEq I] in

theorem boolWeight_le_card (x : I → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x ≤ Fintype.card I :=
  calc Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x = (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolSupp x).card := rfl
    _ ≤ Finset.card (Finset.univ : Finset I) := Finset.card_le_univ _
    _ = Fintype.card I := Finset.card_univ

noncomputable def permAverage (p : MvPolynomial I ℝ) (x : I → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm I, p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ x))

def layerPermEquiv (σ : Equiv.Perm I) (k : ℕ) :
    {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k} ≃
      {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k} where
  toFun f := ⟨permInput σ f.1, by rw [boolWeight_permInput, f.2]⟩
  invFun f := ⟨permInput σ.symm f.1, by rw [boolWeight_permInput, f.2]⟩
  left_inv f := Subtype.ext (by funext i; simp [permInput])
  right_inv f := Subtype.ext (by funext i; simp [permInput])

omit [DecidableEq I] in

theorem exists_perm_of_eq_weight (x y : I → Bool)
    (h : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight y) :
    ∃ σ : Equiv.Perm I, permInput σ x = y := by
  have hc : Fintype.card {i : I // y i = true} = Fintype.card {i : I // x i = true} := by
    rw [← boolWeight_eq_card_subtype y, ← boolWeight_eq_card_subtype x, h]
  set e0 : {i : I // y i = true} ≃ {i : I // x i = true} := Fintype.equivOfCardEq hc
  refine ⟨e0.extendSubtype, ?_⟩
  show permInput e0.extendSubtype x = y
  funext i
  by_cases hi : y i = true
  · show x (e0.extendSubtype i) = y i
    rw [hi]
    exact e0.extendSubtype_mem i hi
  · have hne : x (e0.extendSubtype i) ≠ true := e0.extendSubtype_not_mem i hi
    show x (e0.extendSubtype i) = y i
    cases hx : x (e0.extendSubtype i) <;> cases hy : y i <;> simp_all

theorem permAverage_permInput (p : MvPolynomial I ℝ) (τ : Equiv.Perm I) (x : I → Bool) :
    permAverage p (permInput τ x) = permAverage p x := by
  unfold permAverage
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft τ)
    (fun σ : Equiv.Perm I => p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ x)))
  simpa only [permInput_permInput, Equiv.coe_mulLeft] using he

theorem permAverage_const_on_layer (p : MvPolynomial I ℝ) (x y : I → Bool)
    (h : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight y) :
    permAverage p y = permAverage p x := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_eq_weight x y h
  rw [← hσ]
  exact permAverage_permInput p σ x

theorem sum_permAverage_eq_layerSum (p : MvPolynomial I ℝ) (k : ℕ) :
    (∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k}, permAverage p y.1)
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerSum p k := by
  have hswap : (∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
        ∑ σ : Equiv.Perm I, p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1)))
      = ∑ σ : Equiv.Perm I,
          ∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
            p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1)) :=
    Finset.sum_comm
  have hinner : ∀ σ : Equiv.Perm I,
      (∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
          p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1)))
        = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerSum p k := by
    intro σ
    exact Equiv.sum_comp (layerPermEquiv σ k)
      (fun z : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k} =>
        p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint z.1))
  calc (∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k}, permAverage p y.1)
      = (∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
          (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm I, p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1))) := rfl
    _ = (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ *
          ∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
            ∑ σ : Equiv.Perm I, p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1)) := by
              exact (Finset.mul_sum (R := ℝ) _ _ _).symm
    _ = (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm I,
            ∑ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f = k},
              p.eval (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ y.1)) := by
                rw [hswap]
    _ = (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm I, Qatlib.Concepts.QueryComplexity.DegreeMethod.layerSum p k := by
                simp only [hinner]
    _ = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerSum p k := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
                inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem permAverage_eq_layerAverage (p : MvPolynomial I ℝ) (x : I → Bool) :
    permAverage p x
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x) := by
  have hkle : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x ≤ Fintype.card I :=
      boolWeight_le_card x
  have hC : (Nat.choose (Fintype.card I) (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x) : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Nat.choose (Fintype.card I) (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x) : ℝ) := by
      exact_mod_cast Nat.choose_pos hkle
    exact ne_of_gt hpos
  have hsum :=
      sum_permAverage_eq_layerSum p (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x)
  have hconst : ∀ y : {f : I → Bool // Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight f
        = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x},
      permAverage p y.1 = permAverage p x := fun y =>
        permAverage_const_on_layer p x y.1 y.2.symm
  have hsum' : Qatlib.Concepts.QueryComplexity.DegreeMethod.layerSum p (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x)
      = (Nat.choose (Fintype.card I) (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x) : ℝ)
          * permAverage p x := by
    rw [← hsum, Finset.sum_congr rfl fun y _ => hconst y, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Qatlib.Concepts.QueryComplexity.DegreeMethod.card_level_real]
  rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage, hsum']
  field_simp [hC]

theorem frontier1 :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ),
      (∀ x : I → Bool,
        permAverage p x
          = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x)) ∧
      ∃ q : Polynomial ℝ,
        Polynomial.natDegree q ≤ MvPolynomial.totalDegree p ∧
          ∀ x : I → Bool,
            permAverage p x
              = Polynomial.eval ((Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x : ℕ) : ℝ) q := by
  intro I _ _ p
  refine ⟨fun x => permAverage_eq_layerAverage p x, ?_⟩
  obtain ⟨q, hq, hdeg⟩ :=
    Qatlib.Concepts.QueryComplexity.DegreeMethod.symmetrizationAverageSubgoal I p
  exact ⟨q, hdeg, fun x => by
    rw [permAverage_eq_layerAverage p x,
      hq (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x) (boolWeight_le_card x)]⟩

theorem permAverage_eq_avgPoly (p : MvPolynomial I ℝ) (x : I → Bool) :
    permAverage p x = Polynomial.eval ((Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x : ℕ) : ℝ)
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.avgPoly p) := by
  rw [permAverage_eq_layerAverage]
  exact Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage_eq_avgPoly p _
      (boolWeight_le_card x)

theorem permAverage_zero_cube (p : MvPolynomial (Fin 0) ℝ) :
    permAverage p (fun _ => false) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 0 := by
  have hw : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun _ : Fin 0 => false) = 0 :=
      by decide
  have h := permAverage_eq_layerAverage p (fun _ => false)
  rwa [hw] at h

theorem permAverage_constant_inputs (p : MvPolynomial (Fin 3) ℝ) :
    permAverage p (fun _ => false) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 0 ∧
      permAverage p (fun _ => true) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 3 := by
  have hw0 :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun _ : Fin 3 => false) = 0 := by
        decide
  have hw3 : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun _ : Fin 3 => true) = 3 :=
      by decide
  have h0 := permAverage_eq_layerAverage p (fun _ => false)
  have h3 := permAverage_eq_layerAverage p (fun _ => true)
  rw [hw0] at h0
  rw [hw3] at h3
  exact ⟨h0, h3⟩

theorem permAverage_all_layers (p : MvPolynomial (Fin 3) ℝ) :
    permAverage p (fun _ => false) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 0 ∧
      permAverage p (fun i => i.val = 0) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 1 ∧
        permAverage p (fun i => i.val < 2) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 2 ∧
          permAverage p (fun _ => true) = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 3 := by
  have hw0 :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun _ : Fin 3 => false) = 0 := by
        decide
  have hw1 :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun i : Fin 3 => i.val = 0) = 1 := by
        decide
  have hw2 :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun i : Fin 3 => i.val < 2) = 2 := by
        decide
  have hw3 : Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (fun _ : Fin 3 => true) = 3 :=
      by decide
  have h0 := permAverage_eq_layerAverage p (fun _ => false)
  have h1 := permAverage_eq_layerAverage p (fun i => i.val = 0)
  have h2 := permAverage_eq_layerAverage p (fun i => i.val < 2)
  have h3 := permAverage_eq_layerAverage p (fun _ => true)
  rw [hw0] at h0
  rw [hw1] at h1
  rw [hw2] at h2
  rw [hw3] at h3
  exact ⟨h0, h1, h2, h3⟩

def permSymmEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by simp
  right_inv σ := by simp

def ltPoint (n k : ℕ) : Fin n → Bool := fun i => i.val < k

def ltPointEquiv (n k : ℕ) (hk : k ≤ n) : {i : Fin n // ltPoint n k i = true} ≃ Fin k where
  toFun i := ⟨i.1, of_decide_eq_true i.2⟩
  invFun j := ⟨⟨j.1, lt_of_lt_of_le j.2 hk⟩, decide_eq_true j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

theorem boolWeight_lt_point (n k : ℕ) (hk : k ≤ n) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight (ltPoint n k) = k := by
  rw [boolWeight_eq_card_subtype]
  exact (Fintype.card_congr (ltPointEquiv n k hk)).trans (Fintype.card_fin k)

theorem permLayerAverage_eq_permAverage_standard_point (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p k
      = permAverage p (ltPoint n k) := by
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage permAverage
  congr 1
  have hre : (∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.eval (fun i => if (σ.symm i).val < k then (1 : ℝ) else 0) p)
      = ∑ σ : Equiv.Perm (Fin n),
          MvPolynomial.eval (fun i => if (σ i).val < k then (1 : ℝ) else 0) p :=
    Equiv.sum_comp (permSymmEquiv n)
      (fun τ : Equiv.Perm (Fin n) =>
        MvPolynomial.eval (fun i => if (τ i).val < k then (1 : ℝ) else 0) p)
  rw [hre]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hfun : (fun i => if (σ i).val < k then (1 : ℝ) else 0)
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint (permInput σ (ltPoint n k)) := by
    funext i
    by_cases h : (σ i).val < k <;>
      simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.boolPoint, permInput, ltPoint, h]
  rw [hfun]

theorem permLayerAverage_eq_layerAverage (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (hk : k ≤ n) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p k
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k := by
  rw [permLayerAverage_eq_permAverage_standard_point, permAverage_eq_layerAverage,
    boolWeight_lt_point n k hk]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanPermutationLayerAverage
