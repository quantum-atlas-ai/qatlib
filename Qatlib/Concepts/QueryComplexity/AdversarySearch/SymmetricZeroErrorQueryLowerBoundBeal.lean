/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.SymmetricZeroErrorQueryLowerBoundStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Classical

private theorem weight_le_card {I : Type} [Fintype I] [DecidableEq I] (x : I → Bool) :
    boolWeight x ≤ Fintype.card I := by
  simpa [boolWeight, boolSupp] using
    Finset.card_le_card (Finset.filter_subset (fun i => x i = true) Finset.univ)

private theorem average_zero {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (k : ℕ)
    (h : ∀ x : I → Bool, boolWeight x = k → p.eval (boolPoint x) = 0) :
    layerAverage p k = 0 := by
  unfold layerAverage layerSum
  have hz : (∑ x : {x : I → Bool // boolWeight x = k}, p.eval (boolPoint x.1)) = 0 :=
    Finset.sum_eq_zero (fun x _ => h x.1 x.2)
  rw [hz,zero_mul]

private theorem average_lower {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I) (c : ℝ)
    (h : ∀ x : I → Bool, boolWeight x = k → c ≤ p.eval (boolPoint x)) :
    c ≤ layerAverage p k := by
  have hn : (Nat.choose (Fintype.card I) k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hs : (Nat.choose (Fintype.card I) k : ℝ)*c ≤ layerSum p k := by
    calc
      _ = ∑ _x : {x : I → Bool // boolWeight x = k}, c := by
        simp [card_level_real, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => h x.1 x.2)
  have he :=
      mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (Nat.cast_nonneg ((Fintype.card I).choose k)))
  simpa [layerAverage, mul_assoc, mul_comm, mul_left_comm, hn] using he

private theorem average_nonzero {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (x : I → Bool)
    (h : ∀ y : I → Bool, boolWeight y = boolWeight x → (1/2 : ℝ) ≤ p.eval (boolPoint y)) :
    avgPoly p ≠ 0 := by
  intro hz
  have hl := average_lower p (boolWeight x) (weight_le_card x) (1/2) h
  rw [layerAverage_eq_avgPoly p _ (weight_le_card x), hz, Polynomial.eval_zero] at hl
  norm_num at hl

theorem symmetricZeroErrorQueryLowerBound : SymmetricZeroErrorQueryLowerBound := by
  intro I W _ _ _ _ C ψ E0 E1 f hsym hnon hno1 hno0 hans
  let P0 := booleanAcceptancePolynomial C ψ E0
  let P1 := booleanAcceptancePolynomial C ψ E1
  have hd0 := (acceptance_boolean_multilinearization_preserves_run C ψ E0).1
  have hd1 := (acceptance_boolean_multilinearization_preserves_run C ψ E1).1
  have he0 (x : I → Bool) : P0.eval (boolPoint x) =
      MeasureProb (Run (TensorGate (BitOracleOn x) 1) C ψ) E0 :=
    (acceptance_boolean_multilinearization_preserves_run C ψ E0).2.2 x
  have he1 (x : I → Bool) : P1.eval (boolPoint x) =
      MeasureProb (Run (TensorGate (BitOracleOn x) 1) C ψ) E1 :=
    (acceptance_boolean_multilinearization_preserves_run C ψ E1).2.2 x
  obtain ⟨x0,hx0,x1,hx1⟩ : ∃ x0 : I → Bool, f x0 = false ∧ ∃ x1 : I → Bool, f x1 = true := by
    obtain ⟨x,y,hxy⟩ := hnon
    cases hx : f x <;> cases hy : f y
    · exact False.elim (hxy (hx.trans hy.symm))
    · exact ⟨x,hx,y,hy⟩
    · exact ⟨y,hy,x,hx⟩
    · exact False.elim (hxy (hx.trans hy.symm))
  have hp0 : avgPoly P0 ≠ 0 := average_nonzero P0 x0 (by
    intro y hy
    have hf : f y = false := (hsym y x0 hy).trans hx0
    have hs := hans y
    rw [hno1 y hf, add_zero] at hs
    rwa [he0 y])
  have hp1 : avgPoly P1 ≠ 0 := average_nonzero P1 x1 (by
    intro y hy
    have hf : f y = true := (hsym y x1 hy).trans hx1
    have hs := hans y
    rw [hno0 y hf, zero_add] at hs
    rwa [he1 y])
  have hroot (k : ℕ) (hk : k ≤ Fintype.card I) :
      Polynomial.eval (k : ℝ) (avgPoly P0 * avgPoly P1) = 0 := by
    have hn : Nonempty {x : I → Bool // boolWeight x = k} :=
      Fintype.card_pos_iff.mp (by
        rw [card_weight_eq_choose (Fintype.card I) rfl]
        exact Nat.choose_pos hk)
    obtain ⟨⟨x,hx⟩⟩ := hn
    rw [Polynomial.eval_mul]
    cases hf : f x
    · have hz : layerAverage P1 k = 0 := average_zero P1 k (by
        intro y hy
        have hg : f y = false := (hsym y x (hy.trans hx.symm)).trans hf
        rw [he1 y]
        exact hno1 y hg)
      rw [layerAverage_eq_avgPoly P1 k hk] at hz
      rw [hz,mul_zero]
    · have hz : layerAverage P0 k = 0 := average_zero P0 k (by
        intro y hy
        have hg : f y = true := (hsym y x (hy.trans hx.symm)).trans hf
        rw [he0 y]
        exact hno0 y hg)
      rw [layerAverage_eq_avgPoly P0 k hk] at hz
      rw [hz,zero_mul]
  have himg : ((Finset.range (Fintype.card I + 1)).image (fun k : ℕ => (k : ℝ))) ⊆
      (avgPoly P0 * avgPoly P1).roots.toFinset := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (mul_ne_zero hp0 hp1)).mpr
      (hroot k (by have := Finset.mem_range.mp hk; omega)))
  have hcard : Fintype.card I + 1 ≤ (avgPoly P0 * avgPoly P1).natDegree := by
    calc
      _ = ((Finset.range (Fintype.card I + 1)).image (fun k : ℕ => (k : ℝ))).card := by
        rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      _ ≤ (avgPoly P0 * avgPoly P1).roots.toFinset.card := Finset.card_le_card himg
      _ ≤ (avgPoly P0 * avgPoly P1).roots.card := Multiset.toFinset_card_le _
      _ ≤ _ := Polynomial.card_roots' _
  have hd : (avgPoly P0 * avgPoly P1).natDegree ≤ 4*QueryCount C := by
    have ha := avgPoly_natDegree_le P0
    have hb := avgPoly_natDegree_le P1
    have hc := Polynomial.natDegree_mul_le (p := avgPoly P0) (q := avgPoly P1)
    change P0.totalDegree ≤ 2*QueryCount C at hd0
    change P1.totalDegree ≤ 2*QueryCount C at hd1
    omega
  exact hcard.trans hd

end Qatlib.Concepts.QueryComplexity.AdversarySearch
