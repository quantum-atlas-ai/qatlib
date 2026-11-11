/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra.PauliOperators

set_option backward.isDefEq.respectTransparency false

/-!
# ElecStructure10.MainResults.NumberNumber — Eq. (17): Pauli decomposition of
two-electron number–number operators

Source: Whitfield, Biamonte, Aspuru-Guzik, fixed arXiv:1001.3855v3, Eq. (17)
(p. 13, `assets/1001.3855.txt` lines 780–810).  The paper observes that after
the Jordan–Wigner transform the commutating two-local number–number operators
obey

```
∑_{p<q} (h_pqqp − h_pqpq δ_{σp σq}) a†_p a†_q a_q a_p
  = (1/4 ∑_{p<q} (h_pqqp − h_pqpq δ_{σp σq})) 1
  − (1/4) ∑_q (∑_{p≠q} (h_pqqp − h_pqpq δ_{σp σq})) σ^z_q
  + ∑_{p<q} (h_pqqp − h_pqpq δ_{σp σq})/4 σ^z_p σ^z_q .
```

We formalize this on the paper's computational register `Reg n = Fin n → Bool`
using the frozen fermion package's `numberOp` (= `a†_p a_p`, Eq. (c) of `g1`) and
the per-site `zOp` from `PauliAlgebra.PauliOperators`.  The two-electron
operator `a†_p a†_q a_q a_p` equals `numberOp p * numberOp q` (CAR, `g1`); the
fermionic coefficient is packaged as an arbitrary symmetric scalar family
`c p q = c q p` (the paper's `h_pqqp − h_pqpq δ`, symmetric because
`h_pqrs = h_qpsr`).  The core algebraic step is `n_p n_q = ¼(1 − z_p − z_q + z_p z_q)`
and the symmetric reindexing `∑_{p<q} c_pq (z_p + z_q) = ∑_q (∑_{p≠q} c_pq) z_q`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra
open scoped BigOperators

namespace Qatlib.Papers.ElecStructure10.MainResults.NumberNumber

variable {n : ℕ}

/-! ## Generic additive bookkeeping lemmas -/

/-- Auxiliary linear-algebra identity for Eq. (17) (p. 13): distribute a scalar
over `A − B − C + D`, collecting the two subtraction terms. -/
lemma smul_collapse {β : Type*} [AddCommGroup β] [Module ℂ β] (c : ℂ) (A B C D : β) :
    c • (A - B - C + D) = c • A - c • (B + C) + c • D := by
  simp only [smul_add, smul_sub]
  abel

/-- Auxiliary summation identity for Eq. (17) (p. 13):
`∑_i (if h i then (a i − b i + c i) else 0) = ∑_{h} a − ∑_{h} b + ∑_{h} c`. -/
lemma sum_ite_sub_add {ι : Type*} [Fintype ι] {β : Type*} [AddCommGroup β]
    (a b c : ι → β) (h : ι → Prop) [DecidablePred h] :
    (∑ i, if h i then (a i - b i + c i) else 0)
      = (∑ i, if h i then a i else 0) - (∑ i, if h i then b i else 0)
        + (∑ i, if h i then c i else 0) := by
  have hpt : ∀ i, (if h i then (a i - b i + c i) else 0)
      = (if h i then a i else 0) - (if h i then b i else 0) + (if h i then c i else 0) := by
    intro i; by_cases hi : h i <;> simp [hi]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Symmetric reindexing used below Eq. (17): for symmetric `c`,
`∑_{p<q} c_pq • (Z_p + Z_q) = ∑_q (∑_{p≠q} c_pq) • Z_q`. -/
lemma pairSum_expand {β : Type*} [AddCommGroup β] [Module ℂ β]
    (c : Fin n → Fin n → ℂ) (hsym : ∀ p q, c p q = c q p) (Z : Fin n → β) :
    (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (Z p + Z q) else 0)
      = ∑ q : Fin n, (∑ p : Fin n, if p ≠ q then c p q else 0) • Z q := by
  have hS1 : (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • Z p else 0)
      = ∑ q : Fin n, (∑ r : Fin n, if q < r then c q r else 0) • Z q := by
    have hinner : ∀ p : Fin n, (∑ q : Fin n, if p < q then c p q • Z p else 0)
        = (∑ q : Fin n, if p < q then c p q else 0) • Z p := by
      intro p
      have hpt : ∀ q : Fin n, (if p < q then c p q • Z p else 0)
          = (if p < q then c p q else 0) • Z p := by
        intro q; by_cases h : p < q <;> simp [h]
      simp_rw [hpt, ← Finset.sum_smul]
    calc (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • Z p else 0)
        = ∑ p : Fin n, (∑ q : Fin n, if p < q then c p q else 0) • Z p :=
          Finset.sum_congr rfl (fun p _ => hinner p)
      _ = ∑ q : Fin n, (∑ r : Fin n, if q < r then c q r else 0) • Z q := rfl
  have hS2 : (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • Z q else 0)
      = ∑ q : Fin n, (∑ p : Fin n, if p < q then c p q else 0) • Z q := by
    rw [Finset.sum_comm]
    have hinner : ∀ q : Fin n, (∑ p : Fin n, if p < q then c p q • Z q else 0)
        = (∑ p : Fin n, if p < q then c p q else 0) • Z q := by
      intro q
      have hpt : ∀ p : Fin n, (if p < q then c p q • Z q else 0)
          = (if p < q then c p q else 0) • Z q := by
        intro p; by_cases h : p < q <;> simp [h]
      simp_rw [hpt, ← Finset.sum_smul]
    exact Finset.sum_congr rfl (fun q _ => hinner q)
  have hAB : ∀ q : Fin n,
      (∑ r : Fin n, if q < r then c q r else 0) + (∑ p : Fin n, if p < q then c p q else 0)
        = ∑ p : Fin n, if p ≠ q then c p q else 0 := by
    intro q
    have hrename : (∑ r : Fin n, if q < r then c q r else 0)
        = ∑ p : Fin n, if q < p then c p q else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : q < p <;> simp [h, hsym q p]
    rw [hrename, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rcases lt_trichotomy p q with h | h | h
    · have hpq : p ≠ q := ne_of_lt h
      have hqp : ¬ q < p := not_lt.mpr (le_of_lt h)
      simp [h, hpq, hqp]
    · subst h; simp
    · have hpq : p ≠ q := ne_of_gt h
      have hpq' : ¬ p < q := not_lt.mpr (le_of_lt h)
      simp [h, hpq, hpq']
  calc (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (Z p + Z q) else 0)
      = ∑ p : Fin n, ∑ q : Fin n,
          ((if p < q then c p q • Z p else 0) + (if p < q then c p q • Z q else 0)) := by
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro q _
        by_cases h : p < q <;> simp [h, smul_add]
    _ = (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • Z p else 0)
          + (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • Z q else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.sum_add_distrib]
    _ = ∑ q : Fin n, (∑ p : Fin n, if p ≠ q then c p q else 0) • Z q := by
        rw [hS1, hS2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro q _
        simp_rw [← add_smul]
        rw [hAB q]

/-! ## The number operator as a diagonal Pauli operator -/

/-- `n_i = (1 − σ^z_i)/2`: the frozen `numberOp` equals the paper's `(1 − σ^z)/2`. -/
lemma numberOp_eq_half_z (i : Fin n) :
    numberOp i = (1 / 2 : ℂ) • ((1 : Matrix (Reg n) (Reg n) ℂ) - zOp i) := by
  ext y x
  by_cases hxy : x = y
  · subst hxy
    by_cases hxi : x i
    · simp [numberOp, zOp_apply, hxi]
      norm_num
    · simp [numberOp, zOp_apply, hxi]
  · have hyx : y ≠ x := fun h => hxy h.symm
    simp [numberOp, zOp_apply, hxy, hyx]

/-- Per-pair expansion of Eq. (17): `n_p n_q = ¼(1 − z_p − z_q + z_p z_q)`. -/
lemma numberOp_mul_eq_quarter (p q : Fin n) :
    numberOp p * numberOp q
      = (1 / 4 : ℂ) •
          ((1 : Matrix (Reg n) (Reg n) ℂ) - zOp p - zOp q + zOp p * zOp q) := by
  rw [numberOp_eq_half_z p, numberOp_eq_half_z q]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num]
  congr 1
  -- `(1 − z_p)(1 − z_q) = 1 − z_p − z_q + z_p z_q` in any ring
  noncomm_ring

/-! ## Eq. (17) -/

/-- **Eq. (17)** (fixed arXiv:1001.3855v3, p. 13): the two-electron
number–number operator `∑_{p<q} c_pq a†_p a†_q a_q a_p` (with symmetric
`c_pq = h_pqqp − h_pqpq δ`) equals, after Jordan–Wigner, the constant /
single-`σ^z` / `σ^zσ^z` decomposition with coefficients `1/4` and the
symmetric single-`σ^z` summation `∑_{p≠q}`. -/
theorem eq17_numberNumber_pauli_decomposition (c : Fin n → Fin n → ℂ)
    (hsym : ∀ p q, c p q = c q p) :
    (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (numberOp p * numberOp q) else 0)
      = (1 / 4 : ℂ) •
          ((∑ p : Fin n, ∑ q : Fin n, if p < q then c p q else 0) •
            (1 : Matrix (Reg n) (Reg n) ℂ))
        - (1 / 4 : ℂ) •
          (∑ q : Fin n, (∑ p : Fin n, if p ≠ q then c p q else 0) • zOp q)
        + (1 / 4 : ℂ) •
          (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (zOp p * zOp q) else 0) := by
  -- (i) replace every pair by `¼ c (1 − z_p − z_q + z_p z_q)`
  have hterm : ∀ p q : Fin n,
      (if p < q then c p q • (numberOp p * numberOp q) else 0)
        = (1 / 4 : ℂ) •
            (if p < q then c p q •
              ((1 : Matrix (Reg n) (Reg n) ℂ) - zOp p - zOp q + zOp p * zOp q) else 0) := by
    intro p q
    by_cases h : p < q
    · rw [if_pos h, if_pos h, numberOp_mul_eq_quarter p q]
      rw [smul_smul, smul_smul, mul_comm (c p q) (1 / 4)]
    · rw [if_neg h, if_neg h, smul_zero]
  simp_rw [hterm]
  simp_rw [← Finset.smul_sum]
  -- (ii) split the summand into constant / single-`z` / `zz`
  have hsplit : ∀ p q : Fin n,
      (if p < q then c p q •
          ((1 : Matrix (Reg n) (Reg n) ℂ) - zOp p - zOp q + zOp p * zOp q) else 0)
        = (if p < q then c p q • (1 : Matrix (Reg n) (Reg n) ℂ) else 0)
          - (if p < q then c p q • (zOp p + zOp q) else 0)
          + (if p < q then c p q • (zOp p * zOp q) else 0) := by
    intro p q
    by_cases h : p < q
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]
      exact smul_collapse (c p q) 1 (zOp p) (zOp q) (zOp p * zOp q)
    · simp [h]
  simp_rw [hsplit]
  -- (iii) distribute the double sums over `−` and `+`
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- (iv) identify the constant and single-`z` sums
  have hA : (∑ p : Fin n, ∑ q : Fin n,
        (if p < q then c p q • (1 : Matrix (Reg n) (Reg n) ℂ) else 0))
      = (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q else 0) •
          (1 : Matrix (Reg n) (Reg n) ℂ) := by
    have h1 : ∀ p q : Fin n,
        (if p < q then c p q • (1 : Matrix (Reg n) (Reg n) ℂ) else 0)
          = (if p < q then c p q else 0) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
      intro p q; by_cases h : p < q <;> simp [h]
    simp_rw [h1]
    simp_rw [← Finset.sum_smul]
  have hB : (∑ p : Fin n, ∑ q : Fin n,
        (if p < q then c p q • (zOp p + zOp q) else 0))
      = ∑ q : Fin n, (∑ p : Fin n, if p ≠ q then c p q else 0) • zOp q :=
    pairSum_expand c hsym zOp
  rw [hA, hB]
  rw [smul_add, smul_sub]

end Qatlib.Papers.ElecStructure10.MainResults.NumberNumber
