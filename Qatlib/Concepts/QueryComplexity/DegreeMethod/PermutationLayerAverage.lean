/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

/-!
# Permutation averages and Hamming-layer averages

This module relates `permLayerAverage`, obtained by permuting a canonical Boolean point, to the
uniform Hamming-layer average. Permutations preserve Hamming weight and act transitively on each
layer, so the two averages agree.

The resulting average is represented by a univariate polynomial of degree at most the original
total degree, supplying the symmetrization step of [BealsEtAl2001].

## Main statements

* `stageB_query_comparison_clause64`: Identifies the two averages and supplies a univariate
  polynomial with the required degree bound.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators

/-- The mean of a polynomial over all coordinate permutations of the point whose first `k`
coordinates are one. -/
noncomputable def permLayerAverage (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin n),
    MvPolynomial.eval (fun i => if (σ.symm i).val < k then (1 : ℝ) else 0) p

/-- The Boolean point whose coordinate is true exactly when its index is less than `k`. -/
def layerPoint (n k : ℕ) : Fin n → Bool := fun i => i.val < k
end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryCore

open scoped Classical BigOperators

/-- Evaluates a real multivariate polynomial on the real embedding of a Boolean input. -/
private noncomputable def clause20_pEval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : (Fin n → Bool) → ℝ :=
  fun x => p.eval (boolPoint x)

/-- The type of Boolean inputs on `Fin n` with Hamming weight `k`. -/
private abbrev clause20_layer (n k : ℕ) : Type := {f : Fin n → Bool // boolWeight f = k}

/-- Permutes a Boolean input by precomposing it with the coordinate permutation. -/
private def clause20_perm {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => x (e i)

/-- The equivalence on permutations given by taking inverses. -/
private def clause20_symmEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by simp
  right_inv σ := by simp

/-- Hamming weight equals the cardinality of the subtype of true coordinates. -/
private theorem clause20_card_boolWeight {n : ℕ} (x : Fin n → Bool) :
    boolWeight x = Fintype.card {i : Fin n // x i = true} := by
  show (Finset.univ.filter fun i : Fin n => x i = true).card = _
  rw [Fintype.card_subtype]

/-- Permuting coordinates preserves the Hamming weight of a Boolean input. -/
private theorem clause20_permWeight {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    boolWeight (clause20_perm e x) = boolWeight x := by
  have h : {i : Fin n // x (e i) = true} ≃ {i : Fin n // x i = true} :=
    e.subtypeEquiv fun _ => Iff.rfl
  rw [clause20_card_boolWeight (clause20_perm e x), clause20_card_boolWeight x]
  exact Fintype.card_congr h

/-- Boolean inputs with equal Hamming weight are related by a coordinate permutation. -/
private theorem clause20_exists_perm_eq {n : ℕ} (x y : Fin n → Bool)
    (h : boolWeight x = boolWeight y) : ∃ e : Equiv.Perm (Fin n), clause20_perm e x = y := by
  have hc : Fintype.card {i : Fin n // y i = true}
      = Fintype.card {i : Fin n // x i = true} := by
    rw [← clause20_card_boolWeight y, ← clause20_card_boolWeight x, h]
  set e0 : {i : Fin n // y i = true} ≃ {i : Fin n // x i = true} := Fintype.equivOfCardEq hc
  refine ⟨e0.extendSubtype, ?_⟩
  show clause20_perm e0.extendSubtype x = y
  funext i
  by_cases hi : y i = true
  · show x (e0.extendSubtype i) = y i
    rw [hi]
    exact e0.extendSubtype_mem i hi
  · have hne : x (e0.extendSubtype i) ≠ true := e0.extendSubtype_not_mem i hi
    show x (e0.extendSubtype i) = y i
    cases hx : x (e0.extendSubtype i) <;> cases hy : y i <;> simp_all

/-- A coordinate permutation induces an equivalence of each fixed-weight Boolean layer. -/
private def clause20_permLayerEquiv {n k : ℕ} (e : Equiv.Perm (Fin n)) : clause20_layer n k ≃ clause20_layer n k where
  toFun f := ⟨clause20_perm e f.1, by rw [clause20_permWeight, f.2]⟩
  invFun f := ⟨clause20_perm e.symm f.1, by rw [clause20_permWeight, f.2]⟩
  left_inv f := Subtype.ext (by funext i; simp [clause20_perm])
  right_inv f := Subtype.ext (by funext i; simp [clause20_perm])

/-- The uniform mean of a real function over all coordinate permutations of a Boolean input. -/
private noncomputable def clause20_permMean {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin n), F (clause20_perm e x)

/-- The permutation mean is invariant under permuting the input coordinates. -/
private theorem clause20_permMean_invariant {n : ℕ} (F : (Fin n → Bool) → ℝ) (e : Equiv.Perm (Fin n))
    (x : Fin n → Bool) : clause20_permMean F (clause20_perm e x) = clause20_permMean F x := by
  unfold clause20_permMean
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft e) (fun r : Equiv.Perm (Fin n) => F (clause20_perm r x))
  simpa only [clause20_perm, Equiv.coe_mulLeft, Equiv.Perm.mul_apply] using! he

/-- The permutation mean takes the same value on any two inputs of the same Hamming layer. -/
private theorem clause20_permMean_const_on_layer {n k : ℕ} (F : (Fin n → Bool) → ℝ)
    (x y : Fin n → Bool) (hx : boolWeight x = k) (hy : boolWeight y = k) :
    clause20_permMean F y = clause20_permMean F x := by
  obtain ⟨e, he⟩ := clause20_exists_perm_eq x y (hx.trans hy.symm)
  rw [← he]
  exact clause20_permMean_invariant F e x

/-- Identifies the indices of `Fin n` below `k` with `Fin k`, assuming `k ≤ n`. -/
private def clause20_ltEquiv {n k : ℕ} (hk : k ≤ n) : {i : Fin n // i.val < k} ≃ Fin k where
  toFun i := ⟨i.1, i.2⟩
  invFun j := ⟨⟨j.1, lt_of_lt_of_le j.2 hk⟩, j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

/-- The canonical layer point has weight `k` when `k ≤ n`. -/
private theorem clause20_layerPoint_weight {n k : ℕ} (hk : k ≤ n) :
    boolWeight (layerPoint n k) = k := by
  have h : {i : Fin n // layerPoint n k i = true} ≃ {i : Fin n // i.val < k} :=
    Equiv.subtypeEquiv (Equiv.refl (Fin n)) fun i => by simp [layerPoint]
  rw [clause20_card_boolWeight]
  refine (Fintype.card_congr h).trans ?_
  exact (Fintype.card_congr (clause20_ltEquiv hk)).trans (Fintype.card_fin k)

/-- Summing permutation means over a Hamming layer equals the sum of the polynomial's
evaluations on that layer. -/
private theorem clause20_permMean_layerSum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    (∑ y : clause20_layer n k, clause20_permMean (clause20_pEval p) y.1) = layerSum p k := by
  have hswap : (∑ y : clause20_layer n k, ∑ e : Equiv.Perm (Fin n), clause20_pEval p (clause20_perm e y.1))
      = ∑ e : Equiv.Perm (Fin n), ∑ y : clause20_layer n k, clause20_pEval p (clause20_perm e y.1) :=
    Finset.sum_comm
  have hinner : ∀ e : Equiv.Perm (Fin n),
      (∑ y : clause20_layer n k, clause20_pEval p (clause20_perm e y.1)) = layerSum p k := by
    intro e
    exact Equiv.sum_comp (clause20_permLayerEquiv e)
        (fun z : clause20_layer n k => clause20_pEval p z.1)
  calc (∑ y : clause20_layer n k, clause20_permMean (clause20_pEval p) y.1)
      = (∑ y : clause20_layer n k,
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin n),
            clause20_pEval p (clause20_perm e y.1)) := rfl
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
          ∑ y : clause20_layer n k, ∑ e : Equiv.Perm (Fin n), clause20_pEval p (clause20_perm e y.1) := by
        exact (Finset.mul_sum (R := ℝ) _ _ _).symm
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
          ∑ e : Equiv.Perm (Fin n), ∑ y : clause20_layer n k, clause20_pEval p (clause20_perm e y.1) := by
        rw [hswap]
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
          ∑ e : Equiv.Perm (Fin n), layerSum p k := by
        simp only [hinner]
    _ = layerSum p k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- The canonical permutation average is the permutation mean of the polynomial evaluated at the
canonical layer point. -/
private theorem clause20_permLayerAverage_eq_permMean {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    permLayerAverage n p k = clause20_permMean (clause20_pEval p) (layerPoint n k) := by
  unfold permLayerAverage clause20_permMean
  congr 1
  have hpt : ∀ e : Equiv.Perm (Fin n),
      MvPolynomial.eval (fun i => if (e i).val < k then (1 : ℝ) else 0) p
        = clause20_pEval p (clause20_perm e (layerPoint n k)) := by
    intro e
    have hfun : (fun i => if (e i).val < k then (1 : ℝ) else 0)
        = boolPoint (clause20_perm e (layerPoint n k)) := by
      funext i
      by_cases h : (e i).val < k <;> simp [clause20_perm, boolPoint, layerPoint, h]
    exact congrArg (fun x : Fin n → ℝ => MvPolynomial.eval x p) hfun
  have hre : (∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.eval (fun i => if (σ.symm i).val < k then (1 : ℝ) else 0) p)
      = ∑ e : Equiv.Perm (Fin n),
          MvPolynomial.eval (fun i => if (e i).val < k then (1 : ℝ) else 0) p :=
    Equiv.sum_comp (clause20_symmEquiv n) (fun τ : Equiv.Perm (Fin n) =>
      MvPolynomial.eval (fun i => if (τ i).val < k then (1 : ℝ) else 0) p)
  rw [hre]
  exact Finset.sum_congr rfl fun e _ => hpt e

/-- Permutation and Hamming-layer averages agree at every valid weight, and these layer averages
are represented by a univariate polynomial of no greater degree [BealsEtAl2001]. -/
theorem stageB_query_comparison_clause64 :
  ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
    (∀ k : ℕ, k ≤ n → permLayerAverage n p k = layerAverage p k) ∧
    ∃ q : Polynomial ℝ,
      Polynomial.natDegree q ≤ MvPolynomial.totalDegree p ∧
        ∀ k : ℕ, k ≤ n → layerAverage p k = Polynomial.eval (k : ℝ) q := by
  intro n p
  refine ⟨?_, ?_⟩
  · intro k hk
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    have hkle : k ≤ Fintype.card (Fin n) := by rw [hcard]; exact hk
    have hC : (Nat.choose (Fintype.card (Fin n)) k : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (Nat.choose (Fintype.card (Fin n)) k : ℝ) := by
        exact_mod_cast Nat.choose_pos hkle
      exact ne_of_gt hpos
    have hsum : (∑ y : clause20_layer n k, clause20_permMean (clause20_pEval p) y.1) = layerSum p k :=
      clause20_permMean_layerSum p k
    have hconst : ∀ y : clause20_layer n k,
        clause20_permMean (clause20_pEval p) y.1 = clause20_permMean (clause20_pEval p) (layerPoint n k) := by
      intro y
      exact clause20_permMean_const_on_layer (clause20_pEval p) (layerPoint n k) y.1
        (clause20_layerPoint_weight hk) y.2
    have hsum' : layerSum p k
        = (Nat.choose (Fintype.card (Fin n)) k : ℝ)
            * clause20_permMean (clause20_pEval p) (layerPoint n k) := by
      rw [← hsum, Finset.sum_congr rfl fun y _ => hconst y, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, card_level_real]
    rw [clause20_permLayerAverage_eq_permMean, layerAverage, hsum']
    field_simp [hC]
  · refine ⟨avgPoly p, avgPoly_natDegree_le p, ?_⟩
    intro k hk
    exact layerAverage_eq_avgPoly p k (by rw [Fintype.card_fin]; exact hk)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryCore
