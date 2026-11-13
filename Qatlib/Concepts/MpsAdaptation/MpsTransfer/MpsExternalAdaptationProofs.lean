/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs

/-!
# Expansion of ordered mixed-transfer products

This module expands `transferWord` into a sum over physical words of conjugated left products
tensored with right products. The supporting finite-product lemmas preserve matrix order while
distributing sums, Kronecker products, and entrywise conjugation.

The zero-length and empty-physical-index cases are included explicitly in
`ordered_mixed_transfer`. These identities underlie transfer-matrix contractions for the matrix
product states described in [PerezGarciaEtAl2007].

## Main statements

* `T_kronecker`: Each local transfer matrix is a sum of conjugated Kronecker products.
* `transferWord_sum`: The ordered transfer product expands over all physical words.
* `ordered_mixed_transfer`: The expansion and its empty cases are collected for positive bond
  dimension.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

open Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open scoped Kronecker

/-- An ordered finite monoid product splits into its first factor and the ordered product of the
remaining factors. -/
theorem peel {M : Type*} [Monoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    (List.ofFn f).prod = f 0 * (List.ofFn fun i => f i.succ).prod := by
  rw [List.ofFn_succ, List.prod_cons]

/-- An ordered product of finite matrix sums equals the sum over physical words of the
corresponding ordered products. -/
private theorem ofFn_prod_sum {m : Type*} [Fintype m] [DecidableEq m] {d : ℕ} :
    ∀ (n : ℕ) (F : Fin n → Fin d → Matrix m m ℂ),
    (List.ofFn fun i : Fin n => ∑ s : Fin d, F i s).prod
      = ∑ x : Fin n → Fin d, (List.ofFn fun i : Fin n => F i (x i)).prod := by
  intro n
  induction n with
  | zero =>
      intro F
      rw [List.ofFn_zero, List.prod_nil, Finset.sum_eq_single (Fin.elim0 (α := Fin d))]
      · rw [List.ofFn_zero, List.prod_nil]
      · intro b _ hb
        exact absurd (funext fun i => i.elim0 : b = Fin.elim0) hb
      · intro h
        exact absurd (Finset.mem_univ Fin.elim0) h
  | succ n ih =>
      intro F
      rw [peel (fun i : Fin (n + 1) => ∑ s : Fin d, F i s), Finset.sum_mul,
        ih (fun i => F i.succ)]
      simp only [Finset.mul_sum]
      rw [← (Fintype.sum_prod_type (fun p : Fin d × (Fin n → Fin d) =>
        F 0 p.1 * (List.ofFn fun i : Fin n => F i.succ (p.2 i)).prod))]
      refine Fintype.sum_equiv (Fin.consEquiv fun _ => Fin d)
        (fun p => F 0 p.1 * (List.ofFn fun i : Fin n => F i.succ (p.2 i)).prod)
        (fun x => (List.ofFn fun i : Fin (n + 1) => F i (x i)).prod) ?_
      intro p
      show F 0 p.1 * (List.ofFn fun i : Fin n => F i.succ (p.2 i)).prod
        = (List.ofFn fun i : Fin (n + 1) =>
            F i ((Fin.cons (α := fun _ => Fin d) p.1 p.2 : Fin (n + 1) → Fin d) i)).prod
      rw [peel (fun i : Fin (n + 1) =>
          F i ((Fin.cons (α := fun _ => Fin d) p.1 p.2 : Fin (n + 1) → Fin d) i))]
      simp only [Fin.cons_zero, Fin.cons_succ]

/-- The Kronecker product of two equally long ordered matrix products equals the ordered product
of their pairwise Kronecker products. -/
private theorem ofFn_prod_kronecker {D : ℕ} :
    ∀ (n : ℕ) (M N : Fin n → Matrix (Fin D) (Fin D) ℂ),
    (List.ofFn M).prod ⊗ₖ (List.ofFn N).prod = (List.ofFn fun i => M i ⊗ₖ N i).prod := by
  intro n
  induction n with
  | zero =>
      intro M N
      simp only [List.ofFn_zero, List.prod_nil]
      exact Matrix.one_kronecker_one
  | succ n ih =>
      intro M N
      rw [peel M, peel N, peel (fun i => M i ⊗ₖ N i), Matrix.mul_kronecker_mul,
        ih (fun i => M i.succ) (fun i => N i.succ)]

/-- Entrywise complex conjugation commutes with an ordered finite matrix product. -/
private theorem ofFn_map_prod {D : ℕ} :
    ∀ (n : ℕ) (M : Fin n → Matrix (Fin D) (Fin D) ℂ),
    (List.ofFn M).prod.map (starRingEnd ℂ)
      = (List.ofFn fun i => (M i).map (starRingEnd ℂ)).prod := by
  intro n
  induction n with
  | zero =>
      intro M
      simp only [List.ofFn_zero, List.prod_nil]
      exact Matrix.map_one _ (map_zero (starRingEnd ℂ)) (map_one (starRingEnd ℂ))
  | succ n ih =>
      intro M
      rw [peel M, Matrix.map_mul, peel (fun i => (M i).map (starRingEnd ℂ)),
        ih (fun i => M i.succ)]

/-- The local mixed-transfer matrix equals the sum of entrywise-conjugated left tensors
Kronecker-multiplied by right tensors. -/
theorem T_kronecker {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    T A B i = ∑ s : Fin d, (A i s).map (starRingEnd ℂ) ⊗ₖ B i s := by
  ext p q
  obtain ⟨l, l'⟩ := p
  obtain ⟨r, r'⟩ := q
  simp only [T, Matrix.of_apply, Matrix.sum_apply, Matrix.kronecker_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- The ordered mixed-transfer product is the sum over physical words of conjugated left word
matrices Kronecker-multiplied by right word matrices. -/
theorem transferWord_sum {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    transferWord A B
      = ∑ x : Fin n → Fin d, (word A x).map (starRingEnd ℂ) ⊗ₖ word B x := by
  have h1 : transferWord A B
      = (List.ofFn fun i : Fin n => ∑ s : Fin d, (A i s).map (starRingEnd ℂ) ⊗ₖ B i s).prod := by
    show (List.ofFn fun i : Fin n => T A B i).prod = _
    rw [funext fun i => T_kronecker A B i]
  rw [h1, ofFn_prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← ofFn_prod_kronecker, ← ofFn_map_prod]
  rfl

/-- For zero sites, both the mixed-transfer product and every physical-word matrix product equal
the identity. -/
theorem transferWord_zero_length {d D : ℕ} (A B : Fin 0 → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    transferWord A B = 1 ∧ ∀ x : Fin 0 → Fin d, word A x = 1 := by
  refine ⟨?_, fun x => ?_⟩
  · show (List.ofFn fun i : Fin 0 => T A B i).prod = 1
    rw [List.ofFn_zero]
    rfl
  · show (List.ofFn fun i : Fin 0 => A i (x i)).prod = 1
    rw [List.ofFn_zero]
    rfl

/-- For positive length and no physical symbols, both the mixed-transfer product and its
physical-word expansion vanish. -/
theorem transferWord_empty_phys {n D : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin 0 → Matrix (Fin D) (Fin D) ℂ) :
    transferWord A B = 0
      ∧ (∑ x : Fin n → Fin 0, (word A x).map (starRingEnd ℂ) ⊗ₖ word B x) = 0 := by
  have hT : ∀ i : Fin n, T A B i = 0 := fun i => by
    ext p q; simp [T]
  refine ⟨?_, Finset.sum_eq_zero fun x _ => (x ⟨0, hn⟩).elim0⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  show (List.ofFn fun i : Fin (n' + 1) => T A B i).prod = 0
  rw [List.ofFn_succ, List.prod_cons, hT 0, zero_mul]

/-- The local Kronecker formula and ordered physical-word expansion hold for positive bond
dimension, together with the zero-length and empty-physical-index cases. -/
theorem ordered_mixed_transfer :
    (∀ (n d D : ℕ), 0 < D →
      ∀ (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (∀ i : Fin n, T A B i = ∑ s : Fin d, (A i s).map (starRingEnd ℂ) ⊗ₖ B i s)
      ∧ (transferWord A B
          = ∑ x : Fin n → Fin d, (word A x).map (starRingEnd ℂ) ⊗ₖ word B x))
    ∧ (∀ (d D : ℕ), 0 < D → ∀ (A B : Fin 0 → Fin d → Matrix (Fin D) (Fin D) ℂ),
      transferWord A B = 1 ∧ ∀ x : Fin 0 → Fin d, word A x = 1)
    ∧ (∀ (n D : ℕ), 0 < n → 0 < D →
      ∀ (A B : Fin n → Fin 0 → Matrix (Fin D) (Fin D) ℂ),
      transferWord A B = 0
        ∧ (∑ x : Fin n → Fin 0, (word A x).map (starRingEnd ℂ) ⊗ₖ word B x) = 0) := by
  refine ⟨fun _ _ _ _ A B => ⟨T_kronecker A B, transferWord_sum A B⟩,
    fun _ _ _ A B => transferWord_zero_length A B,
    fun _ _ hn _ A B => transferWord_empty_phys hn A B⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
