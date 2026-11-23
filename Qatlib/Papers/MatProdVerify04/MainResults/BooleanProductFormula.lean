/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Boolean matrix product verification formula

[BuhrmanSpalek2006], Theorem 13, tests each proposed output entry against
the OR of its Boolean inner-product terms and conjoins the resulting tests.
The square root of the number of product terms is the size factor used in
the paper's algorithm analysis.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- The indices of the product terms in the Boolean verification formula. -/
abbrev BooleanProductTerm (n m : ℕ) := Fin n × Fin n × Fin m

/-- The conjunction at a given product-term index. -/
def booleanProductTerm {n m : ℕ} (A : Matrix (Fin n) (Fin m) Bool)
    (B : Matrix (Fin m) (Fin n) Bool) (t : BooleanProductTerm n m) : Bool :=
  A t.1 t.2.2 && B t.2.2 t.2.1

/-- The AND of all output-entry equality checks, each using an OR of product terms. -/
def booleanProductFormula {n m : ℕ} (A : Matrix (Fin n) (Fin m) Bool)
    (B : Matrix (Fin m) (Fin n) Bool) (C : Matrix (Fin n) (Fin n) Bool) : Bool :=
  Finset.univ.inf fun ij : Fin n × Fin n =>
    C ij.1 ij.2 == Finset.univ.sup fun l : Fin m => booleanProductTerm A B (ij.1, ij.2, l)

/-- The formula accepts exactly when the candidate equals the Boolean matrix product entrywise. -/
theorem boolean_product_formula_eq_true_iff {n m : ℕ} (A : Matrix (Fin n) (Fin m) Bool)
    (B : Matrix (Fin m) (Fin n) Bool) (C : Matrix (Fin n) (Fin n) Bool) :
    booleanProductFormula A B C = true ↔
      ∀ i j, C i j = true ↔ ∃ l, A i l = true ∧ B l j = true := by
  have hentry (i j : Fin n) :
      (Finset.univ.sup fun l : Fin m => booleanProductTerm A B (i, j, l)) = true ↔
        ∃ l, A i l = true ∧ B l j = true := by
    simpa [booleanProductTerm, Bool.and_eq_true] using
      (Finset.sup_eq_top_iff (α := Bool) (s := (Finset.univ : Finset (Fin m)))
        (f := fun l => booleanProductTerm A B (i, j, l)))
  change (Finset.univ.inf _ = (⊤ : Bool)) ↔ _
  rw [Finset.inf_eq_top_iff]
  simp only [Finset.mem_univ, true_implies, Prod.forall]
  exact forall_congr' fun i => forall_congr' fun j => by
    rw [← hentry i j]
    cases C i j <;> cases (Finset.univ.sup fun l : Fin m =>
      booleanProductTerm A B (i, j, l)) <;> simp

/-- A verification formula has `n² m` product-term occurrences. -/
theorem boolean_product_term_count (n m : ℕ) :
    Fintype.card (BooleanProductTerm n m) = n * n * m := by
  simp [BooleanProductTerm, Nat.mul_assoc]

/-- The square-root size factor is at most a uniform multiple of `n√m` on positive dimensions. -/
theorem boolean_product_sqrt_size_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 0 < n → 0 < m →
      Real.sqrt (Fintype.card (BooleanProductTerm n m) : ℝ) ≤
        K * (n : ℝ) * Real.sqrt (m : ℝ) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro n m _ _
  rw [boolean_product_term_count, Nat.cast_mul, Nat.cast_mul,
    Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)),
    Real.sqrt_mul_self (Nat.cast_nonneg n), one_mul]

end Qatlib.Papers.MatProdVerify04.MainResults
