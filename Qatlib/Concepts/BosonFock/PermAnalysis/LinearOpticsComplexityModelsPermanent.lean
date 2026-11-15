/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
public import Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStabilityThec
public import Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBoundThec
public import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationThec
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
open Qatlib.Concepts.BosonFock.PermAnalysis

set_option autoImplicit false

open Qatlib

open scoped BigOperators Nat ComplexConjugate Matrix

open Module MeasureTheory

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib.Foundations.ComplexGeometry.PhaseRecovery Qatlib.Foundations.ProbabilityCore.Concentration

/-- Reindexing by a permutation moves its inverse from the second index to the first in a finite
product. -/
private theorem clause17_permProd_symm {n : ℕ} {R : Type*} [CommMonoid R]
    (f : Fin n → Fin n → R) (σ : Equiv.Perm (Fin n)) :
    ∏ i, f i (σ.symm i) = ∏ i, f (σ i) i := by
  calc ∏ i, f i (σ.symm i)
      = ∏ i, (fun j => f j (σ.symm j)) i := rfl
    _ = ∏ i, (fun j => f j (σ.symm j)) (σ i) :=
        (Equiv.prod_comp σ (fun j => f j (σ.symm j))).symm
    _ = ∏ i, f (σ i) i :=
        Finset.prod_congr rfl fun i _ => by simp only [Equiv.symm_apply_apply]

/-- The sum of entry products indexed by permutations equals the matrix permanent. -/
theorem clause17_permSum_permanent {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i) = Matrix.permanent M := by
  rw [Matrix.permanent]
  refine Fintype.sum_equiv
    (⟨fun σ => σ.symm, fun σ => σ.symm, fun σ => Equiv.symm_symm σ,
      fun σ => Equiv.symm_symm σ⟩ : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n)) _ _ ?_
  intro σ
  exact clause17_permProd_symm (fun a b => M a b) (Equiv.symm σ)

/-- Clears the denominator of a rational number using any natural multiple of that denominator. -/
private theorem clause17_clearDen (q : ℚ) {D : ℕ} (hdvd : q.den ∣ D) :
    ((((D / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = ((D : ℕ) : ℚ) * q := by
  have hval : ((q.den : ℕ) : ℚ) * q = ((q.num : ℤ) : ℚ) :=
    (mul_comm _ q).trans (Rat.mul_den_eq_num q)
  have hD : ((D : ℕ) : ℚ) = ((D / q.den : ℕ) : ℚ) * ((q.den : ℕ) : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have hcast : ∀ (k : ℕ), ((((k : ℤ) * q.num : ℤ) : ℚ)) = ((k : ℕ) : ℚ) * ((q.num : ℤ) : ℚ) :=
    fun _k => by push_cast; ring
  rw [hcast (D / q.den), hD, mul_assoc, hval]

/-- Each entry denominator divides the product of all denominators of the rational matrix. -/
private theorem clause17_den_dvd_prod {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (X i j).den ∣ ∏ k, ∏ l, (X k l).den :=
  dvd_trans (Finset.dvd_prod_of_mem (fun l => (X i l).den) (Finset.mem_univ j))
    (Finset.dvd_prod_of_mem (fun k => ∏ l, (X k l).den) (Finset.mem_univ i))

/-- Clears the real and imaginary entry denominators and represents the scaled squared permanent
as a sum over pairs of permutations. -/
theorem clause17_clause7b : ∀ (n : ℕ) (Xr Xi : Matrix (Fin n) (Fin n) ℚ),
    ∃ (D : ℕ) (Yr Yi : Matrix (Fin n) (Fin n) ℤ), 0 < D
      ∧ (∀ i j, (Yr i j : ℚ) = D * Xr i j ∧ (Yi i j : ℚ) = D * Xi i j)
      ∧ (∑ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n),
            ∏ i, (((Yr i (p.1 i) : ℂ) + Complex.I * (Yi i (p.1 i) : ℂ))
              * conj ((Yr i (p.2 i) : ℂ) + Complex.I * (Yi i (p.2 i) : ℂ))))
          = ((D : ℂ) ^ 2) ^ n
            * Complex.normSq (Matrix.permanent
                (Matrix.of fun i j => (Xr i j : ℂ) + Complex.I * (Xi i j : ℂ))) := by
  intro n Xr Xi
  set D : ℕ := ∏ k, ∏ l, ((Xr k l).den * (Xi k l).den) with hDdef
  set Yr : Matrix (Fin n) (Fin n) ℤ := Matrix.of
    fun i j => ((D / (Xr i j).den : ℕ) : ℤ) * (Xr i j).num with hYrdef
  set Yi : Matrix (Fin n) (Fin n) ℤ := Matrix.of
    fun i j => ((D / (Xi i j).den : ℕ) : ℤ) * (Xi i j).num with hYidef
  have hDpos : 0 < D :=
    Finset.prod_pos fun k _ =>
      Finset.prod_pos fun l _ => mul_pos (Xr k l).pos (Xi k l).pos
  have hdvdR : ∀ i j, (Xr i j).den ∣ D := fun i j =>
    dvd_trans (dvd_mul_right _ _)
      (dvd_trans (Finset.dvd_prod_of_mem (fun l => (Xr i l).den * (Xi i l).den)
        (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem (fun k => ∏ l, (Xr k l).den * (Xi k l).den)
          (Finset.mem_univ i)))
  have hdvdI : ∀ i j, (Xi i j).den ∣ D := fun i j =>
    dvd_trans (dvd_mul_left _ _)
      (dvd_trans (Finset.dvd_prod_of_mem (fun l => (Xr i l).den * (Xi i l).den)
        (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem (fun k => ∏ l, (Xr k l).den * (Xi k l).den)
          (Finset.mem_univ i)))
  refine ⟨D, Yr, Yi, hDpos, ?_, ?_⟩
  · intro i j
    exact ⟨clause17_clearDen (Xr i j) (hdvdR i j), clause17_clearDen (Xi i j) (hdvdI i j)⟩
  · set x : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      fun i j => (Xr i j : ℂ) + Complex.I * (Xi i j : ℂ) with hxdef
    have hzc : ∀ z : ℤ, ((z : ℚ) : ℂ) = ((z : ℤ) : ℂ) := fun z => by
      push_cast
      ring
    have hz : ∀ i j, ((Yr i j : ℂ) + Complex.I * (Yi i j : ℂ)) = (D : ℂ) * x i j := by
      intro i j
      have hr : ((Yr i j : ℤ) : ℂ) = ((D : ℕ) : ℂ) * ((Xr i j : ℚ) : ℂ) := by
        rw [hYrdef, Matrix.of_apply]
        rw [← hzc (((D / (Xr i j).den : ℕ) : ℤ) * (Xr i j).num)]
        rw [clause17_clearDen (Xr i j) (hdvdR i j)]
        push_cast
        ring
      have hi : ((Yi i j : ℤ) : ℂ) = ((D : ℕ) : ℂ) * ((Xi i j : ℚ) : ℂ) := by
        rw [hYidef, Matrix.of_apply]
        rw [← hzc (((D / (Xi i j).den : ℕ) : ℤ) * (Xi i j).num)]
        rw [clause17_clearDen (Xi i j) (hdvdI i j)]
        push_cast
        ring
      rw [hr, hi, hxdef, Matrix.of_apply]
      ring
    have hconjD : conj ((D : ℂ)) = (D : ℂ) := by
      simp
    have hprod : ∀ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n),
        (∏ i, (((Yr i (p.1 i) : ℂ) + Complex.I * (Yi i (p.1 i) : ℂ))
          * conj ((Yr i (p.2 i) : ℂ) + Complex.I * (Yi i (p.2 i) : ℂ))))
        = (((D : ℂ) * conj ((D : ℂ))) ^ n * ∏ i, x i (p.1 i)) * conj (∏ i, x i (p.2 i)) := by
      intro p
      have hf : ∀ i, (((Yr i (p.1 i) : ℂ) + Complex.I * (Yi i (p.1 i) : ℂ))
          * conj ((Yr i (p.2 i) : ℂ) + Complex.I * (Yi i (p.2 i) : ℂ)))
          = (((D : ℂ) * conj ((D : ℂ))) * (x i (p.1 i) * conj (x i (p.2 i)))) := by
        intro i
        rw [hz i (p.1 i), hz i (p.2 i), map_mul]
        ring
      rw [Finset.prod_congr rfl fun i _ => hf i]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, map_prod]
      ring
    have hsum : (∑ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n),
          ∏ i, (((Yr i (p.1 i) : ℂ) + Complex.I * (Yi i (p.1 i) : ℂ))
            * conj ((Yr i (p.2 i) : ℂ) + Complex.I * (Yi i (p.2 i) : ℂ))))
        = (((D : ℂ) * conj ((D : ℂ))) ^ n * Matrix.permanent x)
          * conj (Matrix.permanent x) := by
      rw [Finset.sum_congr rfl fun p _ => hprod p, Fintype.sum_prod_type]
      have hcp : conj (Matrix.permanent x)
          = ∑ τ : Equiv.Perm (Fin n), conj (∏ i, x i (τ i)) := by
        rw [← clause17_permSum_permanent x, map_sum]
      have hf1 : ∀ σ : Equiv.Perm (Fin n),
          (∑ τ : Equiv.Perm (Fin n), (((D : ℂ) * conj ((D : ℂ))) ^ n * ∏ i, x i (σ i))
              * conj (∏ i, x i (τ i)))
          = (((D : ℂ) * conj ((D : ℂ))) ^ n * ∏ i, x i (σ i))
              * conj (Matrix.permanent x) := by
        intro σ
        rw [hcp, Finset.mul_sum]
      have hf0 : (∑ σ : Equiv.Perm (Fin n),
            (((D : ℂ) * conj ((D : ℂ))) ^ n * ∏ i, x i (σ i))
              * conj (Matrix.permanent x))
          = (((D : ℂ) * conj ((D : ℂ))) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ i, x i (σ i))
              * conj (Matrix.permanent x) := by
        calc (∑ σ : Equiv.Perm (Fin n),
              (((D : ℂ) * conj ((D : ℂ))) ^ n * ∏ i, x i (σ i))
                * conj (Matrix.permanent x))
            = (((D : ℂ) * conj ((D : ℂ))) ^ n) * ∑ σ : Equiv.Perm (Fin n),
                (∏ i, x i (σ i)) * conj (Matrix.permanent x) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun σ _ => by ring
          _ = (((D : ℂ) * conj ((D : ℂ))) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ i, x i (σ i))
              * conj (Matrix.permanent x) := by rw [← Finset.sum_mul]; ring
      rw [Finset.sum_congr rfl fun σ _ => hf1 σ, hf0, clause17_permSum_permanent]
    rw [hsum, hconjD, Complex.normSq_eq_conj_mul_self]
    ring

/-- If `c` is at most `B`, the sum over `Fin` of size one more than `B` of the indicator for
values below `c` equals `c`. -/
private theorem clause17_sum_lt (c B : ℕ) (hc : c ≤ B) :
    (∑ v : Fin (B + 1), if ((v : Fin (B + 1)) : ℕ) < c then (1 : ℕ) else 0) = c := by
  rw [Fin.sum_univ_eq_sum_range (f := fun k => if k < c then (1 : ℕ) else 0) (B + 1)]
  have hsub : (Finset.range c) ⊆ (Finset.range (B + 1)) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.sum_subset hsub
    (fun k _ hk => by
      have hk' : ¬(k < c) := by
        simpa only [Finset.mem_range] using hk
      rw [ite_eq_right hk'])]
  rw [Finset.sum_congr rfl
      (fun k hk => ite_eq_left (Finset.mem_range.mp hk)), Finset.sum_const, Finset.card_range]
  norm_num

/-- Encodes a nonnegative rational permanent as a scaled cardinality using a common denominator
and bounded natural matrix entries. -/
theorem clause17_clause7a : ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℚ), (∀ i j, 0 ≤ X i j) →
    ∃ (D : ℕ) (Y : Matrix (Fin n) (Fin n) ℕ) (B : ℕ), 0 < D
      ∧ (∀ i j, (Y i j : ℚ) = D * X i j)
      ∧ (∀ i j, Y i j ≤ B)
      ∧ ((Finset.univ.filter
            (fun p : Equiv.Perm (Fin n) × (Fin n → Fin (B + 1)) =>
              ∀ i, ((p.2 i : Fin (B + 1)) : ℕ) < Y i (p.1 i))).card : ℚ)
          = (D : ℚ) ^ n * Matrix.permanent X := by
  intro n X hX
  set D : ℕ := ∏ k, ∏ l, (X k l).den with hDdef
  have hDpos : 0 < D :=
    Finset.prod_pos fun k _ => Finset.prod_pos fun l _ => (X k l).pos
  have hnum : ∀ i j, 0 ≤ (X i j).num := by
    intro i j
    by_contra hc
    have hneg : (X i j).num < 0 := lt_of_not_ge hc
    have h1 : ((X i j).num : ℚ) / ((X i j).den : ℕ) < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hneg) (by positivity)
    rw [Rat.num_div_den] at h1
    exact absurd h1 (not_lt.2 (hX i j))
  set Y : Matrix (Fin n) (Fin n) ℕ := Matrix.of
    fun i j => (((D / (X i j).den : ℕ) : ℤ) * (X i j).num).toNat with hYdef
  have hYval : ∀ i j, (Y i j : ℚ) = D * X i j := by
    intro i j
    have hz : 0 ≤ ((D / (X i j).den : ℕ) : ℤ) * (X i j).num :=
      mul_nonneg (Int.natCast_nonneg _) (hnum i j)
    have hcast : ((((((D / (X i j).den : ℕ) : ℤ) * (X i j).num).toNat : ℕ) : ℚ))
        = ((((D / (X i j).den : ℕ) : ℤ) * (X i j).num : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hz
    rw [hYdef, Matrix.of_apply, hcast]
    exact clause17_clearDen (X i j) (clause17_den_dvd_prod X i j)
  set B : ℕ := ∑ k, ∑ l, Y k l with hBdef
  have hYle : ∀ i j, Y i j ≤ B := by
    intro i j
    rw [hBdef]
    exact Nat.le_trans
      (Finset.single_le_sum (f := fun l => Y i l) (fun l _ => Nat.zero_le _)
        (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun k => ∑ l, Y k l) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ i))
  refine ⟨D, Y, B, hDpos, hYval, hYle, ?_⟩

  have hcardnat : ((Finset.univ.filter
        (fun p : Equiv.Perm (Fin n) × (Fin n → Fin (B + 1)) =>
          ∀ i, ((p.2 i : Fin (B + 1)) : ℕ) < Y i (p.1 i))).card)
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, Y i (σ i) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsplit : ∀ w : Fin n → Fin (B + 1),
        ((if (∀ i, ((w i : Fin (B + 1)) : ℕ) < Y i (σ i)) then (1 : ℕ) else 0))
        = ∏ i, (if ((w i : Fin (B + 1)) : ℕ) < Y i (σ i) then (1 : ℕ) else 0) := by
      intro w
      by_cases hall : ∀ i, ((w i : Fin (B + 1)) : ℕ) < Y i (σ i)
      · rw [ite_eq_left hall]
        exact (Finset.prod_eq_one fun i (_ : i ∈ Finset.univ) => ite_eq_left (hall i)).symm
      · rw [ite_eq_right hall]
        have hex : ∃ i₀, ¬(((w i₀ : Fin (B + 1)) : ℕ) < Y i₀ (σ i₀)) := by
          by_contra hcon
          exact hall fun i => by_contra fun hi => hcon ⟨i, hi⟩
        obtain ⟨i₀, hi₀⟩ := hex
        exact (Finset.prod_eq_zero (Finset.mem_univ i₀)
          (ite_eq_right hi₀ : (if ((w i₀ : Fin (B + 1)) : ℕ) < Y i₀ (σ i₀)
            then (1 : ℕ) else 0) = 0)).symm
    rw [Finset.sum_congr rfl fun w _ => hsplit w]
    have hpi := Finset.prod_univ_sum
      (t := fun _ : Fin n => (Finset.univ : Finset (Fin (B + 1))))
      (f := fun (i : Fin n) (v : Fin (B + 1)) =>
        (if ((v : Fin (B + 1)) : ℕ) < Y i (σ i) then (1 : ℕ) else 0))
    rw [Fintype.piFinset_univ] at hpi
    rw [← hpi]
    exact Finset.prod_congr rfl fun i _ => clause17_sum_lt (Y i (σ i)) B (hYle i (σ i))

  rw [hcardnat, Nat.cast_sum]
  refine (Finset.sum_congr
    (f := fun σ : Equiv.Perm (Fin n) => ((∏ i, Y i (σ i) : ℕ) : ℚ))
    (g := fun σ : Equiv.Perm (Fin n) => ∏ i, ((Y i (σ i) : ℕ) : ℚ))
    rfl (fun σ _ => Nat.cast_prod (fun i => Y i (σ i)) Finset.univ)).trans ?_
  have hf : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, ((Y i (σ i) : ℕ) : ℚ)) = ((D : ℚ)) ^ n * ∏ i, (X i (σ i)) := by
    intro σ
    simp only [hYval]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun σ _ => hf σ, ← Finset.mul_sum, clause17_permSum_permanent]
end Qatlib.Concepts.BosonFock.PermAnalysis
