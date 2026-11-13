/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SignedWtEnum99.MainResults.QSEN

/-!
# Factorization of two-constraint signed weight enumerators

`qsen2` sums signed Hamming-weight terms over the intersection of two binary matrix kernels. The
module shows how a factorization `C = X * Yᵀ` with independent columns replaces the constraints
from `C` and `Cᵀ` by those from `Yᵀ` and `Xᵀ`. See [KnillLaflamme1999] for the source
development.

## Main statements

* `mulVec_eq_zero_iff_of_indep_cols`: gives the trivial-kernel criterion for independent
  columns.
* `qsen2_eq_of_factorization`: preserves the enumerator under the factored kernel constraints.

## References

* [Knill and Laflamme, 1999][KnillLaflamme1999]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

/-- The integer signed weight enumerator over binary vectors annihilated by both `A1` and `A2`,
with quadratic sign determined by `B`. -/
def qsen2 {m n : ℕ} (A1 A2 : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : ℤ) : ℤ :=
  ∑ b : Fin n → ZMod 2,
    if A1.mulVec b = 0 ∧ A2.mulVec b = 0 then
      sgnZ (quadForm B b) * x ^ bitWeight b * y ^ (n - bitWeight b)
    else 0

/-- The two-constraint enumerator is unchanged when both kernel predicates agree pointwise and
the quadratic-form matrices are equal. -/
lemma qsen2_congr {m m' n : ℕ} {A1 A2 : Matrix (Fin m) (Fin n) (ZMod 2)}
    {A1' A2' : Matrix (Fin m') (Fin n) (ZMod 2)}
    {B1 B2 : Matrix (Fin n) (Fin n) (ZMod 2)} (x y : ℤ)
    (hA1 : ∀ b : Fin n → ZMod 2, A1.mulVec b = 0 ↔ A1'.mulVec b = 0)
    (hA2 : ∀ b : Fin n → ZMod 2, A2.mulVec b = 0 ↔ A2'.mulVec b = 0)
    (hB : B1 = B2) : qsen2 A1 A2 B1 x y = qsen2 A1' A2' B2 x y := by
  subst hB
  classical
  unfold qsen2
  apply Finset.sum_congr rfl
  intro b _
  by_cases h1 : A1.mulVec b = 0
  · by_cases h2 : A2.mulVec b = 0
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨(hA1 b).mp h1, (hA2 b).mp h2⟩]
    · have h2' : ¬ A2'.mulVec b = 0 := fun hh => h2 ((hA2 b).mpr hh)
      rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => h2' hh.2)]
  · have h1' : ¬ A1'.mulVec b = 0 := fun hh => h1 ((hA1 b).mpr hh)
    rw [if_neg (fun hh => h1 hh.1), if_neg (fun hh => h1' hh.1)]

/-- A binary matrix-vector product is the linear combination of its columns with the entries of
the vector as coefficients. -/
lemma mulVec_eq_sum_cols {N k : ℕ} (X : Matrix (Fin N) (Fin k) (ZMod 2))
    (v : Fin k → ZMod 2) :
    X *ᵥ v = ∑ j : Fin k, v j • (fun i : Fin N => X i j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- A binary matrix with linearly independent columns annihilates a vector exactly when that
vector is zero. -/
lemma mulVec_eq_zero_iff_of_indep_cols {N k : ℕ} (X : Matrix (Fin N) (Fin k) (ZMod 2))
    (h : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j))
    (v : Fin k → ZMod 2) : X *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hsum : ∑ j : Fin k, v j • (fun i : Fin N => X i j) = 0 := by
      rw [← mulVec_eq_sum_cols]
      exact hv
    have hz := (Fintype.linearIndependent_iff.mp h) v hsum
    funext j
    exact hz j
  · intro hv
    rw [hv]
    exact Matrix.mulVec_zero _

/-- If `C = X * Yᵀ` and both factors have independent columns, the enumerator constrained by `C,
Cᵀ` equals the one constrained by `Yᵀ, Xᵀ`, with phase matrix `lwtr C`. See
[KnillLaflamme1999]. -/
theorem qsen2_eq_of_factorization {N k : ℕ} (C : Matrix (Fin N) (Fin N) (ZMod 2))
    (X Y : Matrix (Fin N) (Fin k) (ZMod 2)) (hC : C = X * Yᵀ)
    (hX : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => X i j))
    (hY : LinearIndependent (ZMod 2) (fun j : Fin k => fun i : Fin N => Y i j))
    (x y : ℤ) :
    qsen2 C Cᵀ (lwtr C) x y = qsen2 Yᵀ Xᵀ (lwtr C) x y := by
  apply qsen2_congr x y
  · intro b
    rw [hC, ← Matrix.mulVec_mulVec]
    exact mulVec_eq_zero_iff_of_indep_cols X hX (Yᵀ *ᵥ b)
  · intro b
    have hCt : Cᵀ = Y * Xᵀ := by
      rw [hC, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hCt, ← Matrix.mulVec_mulVec]
    exact mulVec_eq_zero_iff_of_indep_cols Y hY (Xᵀ *ᵥ b)
  · rfl

end Qatlib.Papers.SignedWtEnum99.MainResults
