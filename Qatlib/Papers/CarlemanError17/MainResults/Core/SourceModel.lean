/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# CarlemanError17 — source model: supremum norm, logarithmic norm, Kronecker powers

Forets–Pouly, *Explicit Error Bounds for Carleman Linearization*,
fixed arXiv:1711.02552v1 (7 November 2017).

This file sets up the paper's matrix vocabulary:
* (3) the induced supremum norm (maximum absolute row sum) `matSup`;
* §2.3 the logarithmic norm `logNorm` (written μ∞ in the paper);
* (5)/(8) Kronecker powers and the transfer matrices `A^i_{i+j}`.

The index type `TP n i` is the paper's `n^i`-dimensional index set, represented as
`Fin i → Fin n` (a length-`i` tuple of `Fin n` coordinates).  Consequently
`TP n (i + j)` is canonically the product `TP n i × TP n j`, and Kronecker products
are reindexed through `Fin.appendEquiv`.

Boundary: this file contains only the paper's own constructions; it does not import or
claim any frozen result (the bound concept targets `CarlemanODE.*` currently have no
Lean implementation).
-/

set_option autoImplicit false
noncomputable section

open Finset Matrix
open scoped BigOperators

namespace Qatlib.Papers.CarlemanError17.MainResults.Core

/-- Paper (3): the supremum (maximum absolute row-sum) norm of a real matrix.
For an empty row type the value is `0` by convention; every paper matrix has `n ≥ 1`. -/
noncomputable def matSup {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  @dite ℝ (Nonempty m) (Classical.propDecidable _)
    (fun h => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h) fun i => ∑ j, |A i j|)
    (fun _ => 0)

/-- Paper §2.3: the logarithmic norm μ∞ of a real matrix,
`μ(A) = max_i (A_ii + ∑_{j ≠ i} |A_ij|)`. -/
noncomputable def logNorm {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) : ℝ :=
  @dite ℝ (Nonempty m) (Classical.propDecidable _)
    (fun h => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h)
      fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j|)
    (fun _ => 0)

/-- The supremum norm of a real vector, `‖v‖ = max_i |v_i|` (paper §2.1). -/
noncomputable def vecSup {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  @dite ℝ (Nonempty ι) (Classical.propDecidable _)
    (fun h => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h) fun i => |v i|)
    (fun _ => 0)

/-- The `matSup_def` result for the CarlemanError17 paper model. -/
lemma matSup_def {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (h : Nonempty m) :
    matSup A = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h) fun i => ∑ j, |A i j| := by
  classical
  unfold matSup
  rw [dif_pos h]

/-- The `matSup_nonneg` result for the CarlemanError17 paper model. -/
lemma matSup_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    0 ≤ matSup A := by
  by_cases h : Nonempty m
  · rw [matSup_def A h]
    obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.mpr h) (fun i => ∑ j, |A i j|)
    rw [hi0]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  · classical
    unfold matSup
    rw [dif_neg h]

/-- The `logNorm_def` result for the CarlemanError17 paper model. -/
lemma logNorm_def {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) (h : Nonempty m) :
    logNorm A = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h)
      fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j| := by
  classical
  unfold logNorm
  rw [dif_pos h]

/-- Suprema over a product indexed by a function of the first coordinate only. -/
lemma sup'_univ_prod_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) :
    (Finset.univ : Finset (α × β)).sup' Finset.univ_nonempty (fun p => f p.1)
      = (Finset.univ : Finset α).sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro p _
    exact Finset.le_sup' f (Finset.mem_univ p.1)
  · rw [Finset.sup'_le_iff]
    intro i _
    exact Finset.le_sup' (fun p : α × β => f p.1)
      (Finset.mem_univ (i, Classical.choice (inferInstance : Nonempty β)))

/-- Supremum of a product of two nonnegative families over a product index type. -/
lemma sup'_univ_mul {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) (g : β → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) :
    (Finset.univ : Finset (α × β)).sup' Finset.univ_nonempty (fun p => f p.1 * g p.2)
      = (Finset.univ : Finset α).sup' Finset.univ_nonempty f
        * (Finset.univ : Finset β).sup' Finset.univ_nonempty g := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro p _
    exact mul_le_mul (Finset.le_sup' f (Finset.mem_univ p.1))
      (Finset.le_sup' g (Finset.mem_univ p.2)) (hg p.2)
      (le_trans (hf p.1) (Finset.le_sup' f (Finset.mem_univ p.1)))
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty g
    calc (Finset.univ : Finset α).sup' Finset.univ_nonempty f
          * (Finset.univ : Finset β).sup' Finset.univ_nonempty g
        = f i0 * g j0 := by rw [hi0, hj0]
      _ ≤ (Finset.univ : Finset (α × β)).sup' Finset.univ_nonempty (fun p => f p.1 * g p.2) :=
          Finset.le_sup' (fun p : α × β => f p.1 * g p.2) (Finset.mem_univ (i0, j0))

/-- Reindexing a matrix along bijections does not change its supremum norm. -/
lemma matSup_submatrix_equiv {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] (e : m' ≃ m) (f : n' ≃ n) (A : Matrix m n ℝ) :
    matSup (A.submatrix e f) = matSup A := by
  by_cases hm' : Nonempty m'
  · have hm : Nonempty m := hm'.elim fun x => ⟨e x⟩
    rw [matSup_def _ hm', matSup_def _ hm]
    have hrow : ∀ i' : m', (∑ j' : n', |A.submatrix e f i' j'|)
        = ∑ j : n, |A (e i') j| := by
      intro i'
      exact Fintype.sum_equiv f (fun j' => |A (e i') (f j')|) (fun j => |A (e i') j|)
        (fun j' => rfl)
    have hsup : (Finset.univ : Finset m').sup'
          (Finset.univ_nonempty_iff.mpr hm') (fun i' => ∑ j' : n', |A.submatrix e f i' j'|)
        = (Finset.univ : Finset m).sup'
          (Finset.univ_nonempty_iff.mpr hm) (fun i => ∑ j : n, |A i j|) := by
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        intro i' _
        rw [hrow i']
        exact Finset.le_sup' (fun i => ∑ j : n, |A i j|) (Finset.mem_univ (e i'))
      · rw [Finset.sup'_le_iff]
        intro i _
        obtain ⟨i', rfl⟩ := e.surjective i
        rw [← hrow i']
        exact Finset.le_sup' (fun i' => ∑ j' : n', |A.submatrix e f i' j'|)
          (Finset.mem_univ i')
    exact hsup
  · have hm : ¬ Nonempty m := fun h => hm' (h.elim fun x => ⟨e.symm x⟩)
    simp [matSup, dif_neg hm', dif_neg hm]

/-- Lemma 2.1 (p.4): the supremum norm is a crossnorm, `‖A ⊗ B‖ = ‖A‖ ‖B‖`. -/
theorem matSup_kronMap {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a c ℝ) (B : Matrix b d ℝ) :
    matSup (Matrix.kroneckerMap (· * ·) A B) = matSup A * matSup B := by
  by_cases ha : Nonempty a
  · by_cases hb : Nonempty b
    · have hab : Nonempty (a × b) := ⟨(Classical.choice ha, Classical.choice hb)⟩
      rw [matSup_def _ hab, matSup_def A ha, matSup_def B hb]
      have hrow : ∀ p : a × b,
          (∑ j : c × d, |Matrix.kroneckerMap (· * ·) A B p j|)
            = (∑ j1 : c, |A p.1 j1|) * (∑ j2 : d, |B p.2 j2|) := by
        intro p
        rw [← Finset.univ_product_univ, Finset.sum_product]
        simp only [Matrix.kroneckerMap_apply, abs_mul]
        rw [← Finset.sum_mul_sum]
      have hfun : (fun p : a × b => ∑ j : c × d,
            |Matrix.kroneckerMap (· * ·) A B p j|)
          = fun p : a × b => (∑ j1 : c, |A p.1 j1|) * (∑ j2 : d, |B p.2 j2|) :=
        funext hrow
      rw [hfun]
      exact sup'_univ_mul (fun i => ∑ j : c, |A i j|) (fun j => ∑ i : d, |B j i|)
        (fun i => Finset.sum_nonneg fun j _ => abs_nonneg _)
        (fun j => Finset.sum_nonneg fun i _ => abs_nonneg _)
    · have hab : ¬ Nonempty (a × b) := fun h => hb (h.elim fun p => ⟨p.2⟩)
      simp [matSup, dif_neg hab, dif_neg hb]
  · have hab : ¬ Nonempty (a × b) := fun h => ha (h.elim fun p => ⟨p.1⟩)
    simp [matSup, dif_neg hab, dif_neg ha]

/-- The identity matrix has supremum norm `1` (paper: `‖I_{n×n}‖ = 1`). -/
theorem matSup_one {α : Type*} [Fintype α] [DecidableEq α] (h : Nonempty α) :
    matSup (1 : Matrix α α ℝ) = 1 := by
  rw [matSup_def _ h]
  have hrow : ∀ i : α, (∑ j, |(1 : Matrix α α ℝ) i j|) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Matrix.one_apply]
      simp [show i ≠ j from fun h' => hj h'.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [hrow]
  exact Finset.sup'_const (s := Finset.univ) (H := Finset.univ_nonempty_iff.mpr h) 1

/-- Triangle inequality for the supremum norm. -/
lemma matSup_add_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) :
    matSup (A + B) ≤ matSup A + matSup B := by
  by_cases h : Nonempty m
  · rw [matSup_def _ h, matSup_def A h, matSup_def B h]
    rw [Finset.sup'_le_iff]
    intro i _
    calc (∑ j, |(A + B) i j|) = ∑ j, |A i j + B i j| := rfl
      _ ≤ ∑ j, (|A i j| + |B i j|) := Finset.sum_le_sum fun j _ => abs_add_le _ _
      _ = (∑ j, |A i j|) + ∑ j, |B i j| := Finset.sum_add_distrib
      _ ≤ (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h) fun i => ∑ j, |A i j|)
            + (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr h) fun i => ∑ j, |B i j|) :=
          add_le_add (by simpa using Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i))
            (by simpa using Finset.le_sup' (fun i => ∑ j, |B i j|) (Finset.mem_univ i))
  · simp [matSup, dif_neg h]

/-! ### Kronecker powers and transfer matrices (paper (5) and (8)) -/

/-- The paper's `n^i`-dimensional index type, as length-`i` tuples over `Fin n`. -/
abbrev TP (n i : ℕ) : Type := Fin i → Fin n

/-- Cast tensor-power indices along an equality of exponents. -/
def tpCast {n a b : ℕ} (h : a = b) : TP n a ≃ TP n b :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin n))

/-- Reindex a transfer matrix along exponent equalities. -/
def reindexTP {n a b c d : ℕ} (hab : a = b) (hcd : c = d)
    (A : Matrix (TP n a) (TP n c) ℝ) : Matrix (TP n b) (TP n d) ℝ :=
  A.submatrix (tpCast hab).symm (tpCast hcd).symm

/-- The `matSup_reindexTP` result for the CarlemanError17 paper model. -/
lemma matSup_reindexTP {n a b c d : ℕ} (hab : a = b) (hcd : c = d)
    (A : Matrix (TP n a) (TP n c) ℝ) :
    matSup (reindexTP hab hcd A) = matSup A := by
  subst hab
  subst hcd
  simpa [reindexTP, tpCast] using
    matSup_submatrix_equiv (Equiv.refl (TP n a)) (Equiv.refl (TP n c)) A

/-- Kronecker product of transfer matrices, with the canonical identification
`TP n (i+j) ≃ TP n i × TP n j`. -/
def kronTP {n i j a b : ℕ} (A : Matrix (TP n i) (TP n a) ℝ)
    (B : Matrix (TP n j) (TP n b) ℝ) : Matrix (TP n (i + j)) (TP n (a + b)) ℝ :=
  (Matrix.kroneckerMap (· * ·) A B).submatrix (Fin.appendEquiv i j).symm
    (Fin.appendEquiv a b).symm

/-- The `matSup_kronTP` result for the CarlemanError17 paper model. -/
lemma matSup_kronTP {n i j a b : ℕ} (A : Matrix (TP n i) (TP n a) ℝ)
    (B : Matrix (TP n j) (TP n b) ℝ) :
    matSup (kronTP A B) = matSup A * matSup B := by
  unfold kronTP
  rw [matSup_submatrix_equiv]
  exact matSup_kronMap A B

/-- Paper (8): the transfer matrix `A^i_{i+j}` from block `i` to block `i+j`.
`F j` is the paper's `F_j : R^{n × n^j}` (represented on `TP n 1 × TP n j`).
The recursion is exactly the one used in the proof of Proposition 3.3. -/
def transfer {n : ℕ} (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) :
    (i : ℕ) → (j : ℕ) → Matrix (TP n i) (TP n (i + j)) ℝ
  | 0, _ => 0
  | 1, j => reindexTP rfl (by omega) (F (j + 1))
  | (i + 2), j =>
      reindexTP (by omega) (by omega)
        (kronTP (transfer F (i + 1) j) (1 : Matrix (TP n 1) (TP n 1) ℝ))
      + reindexTP (by omega) (by omega)
        (kronTP (1 : Matrix (TP n (i + 1)) (TP n (i + 1)) ℝ) (F (j + 1)))

/-- Proposition 3.3 (p.7): for all `i ≥ 1`, `0 ≤ j ≤ k−1`, the transfer matrices
satisfy `‖A^i_{i+j}‖ ≤ i ‖F_{j+1}‖`.  Proof follows the paper: the recursive identity
`A^i = A^{i-1} ⊗ I + I^{[i-1]} ⊗ F`, the crossnorm property (Lemma 2.1), the triangle
inequality, and induction on `i`. -/
theorem prop_three_three {n : ℕ} (hn : 0 < n)
    (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) :
    ∀ (i : ℕ), 1 ≤ i → ∀ (j : ℕ),
      matSup (transfer F i j) ≤ (i : ℝ) * matSup (F (j + 1))
  | 0, hi, _ => by omega
  | 1, _, j => by
      simp only [transfer]
      rw [matSup_reindexTP]
      simp
  | (i + 2), _, j => by
      simp only [transfer]
      set X : Matrix (TP n (i + 2)) (TP n (i + 2 + j)) ℝ :=
        reindexTP (by omega) (by omega)
          (kronTP (transfer F (i + 1) j) (1 : Matrix (TP n 1) (TP n 1) ℝ)) with hXdef
      set Y : Matrix (TP n (i + 2)) (TP n (i + 2 + j)) ℝ :=
        reindexTP (by omega) (by omega)
          (kronTP (1 : Matrix (TP n (i + 1)) (TP n (i + 1)) ℝ) (F (j + 1))) with hYdef
      have hX : matSup X = matSup (transfer F (i + 1) j) := by
        rw [hXdef, matSup_reindexTP, matSup_kronTP]
        rw [matSup_one (by exact ⟨fun _ => ⟨0, hn⟩⟩), mul_one]
      have hY : matSup Y = matSup (F (j + 1)) := by
        rw [hYdef, matSup_reindexTP, matSup_kronTP]
        rw [matSup_one (by exact ⟨fun _ => ⟨0, hn⟩⟩), one_mul]
      calc matSup (X + Y) ≤ matSup X + matSup Y := matSup_add_le X Y
        _ = matSup (transfer F (i + 1) j) + matSup (F (j + 1)) := by rw [hX, hY]
        _ ≤ ((i : ℝ) + 1) * matSup (F (j + 1)) + matSup (F (j + 1)) := by
              gcongr
              have hrec := prop_three_three hn F (i + 1) (by omega) j
              push_cast at hrec
              exact hrec
        _ = ((i + 2 : ℕ) : ℝ) * matSup (F (j + 1)) := by push_cast; ring

/-- Lemma 2.2 (p.5): `μ(A ⊗ I_m) = μ(A)`.  The proof computes the row expression of
`A ⊗ I_m` at `(i,v)`: the diagonal entry is `A i i`, every off-diagonal contribution is
`|A i s|` for `s ≠ i` (the identity factor contributes only at `w = v`), and hence the
row expression equals the `i`-th logarithmic-norm summand of `A`, independently of `v`. -/
theorem logNorm_kron_identity {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] [Nonempty n] [Nonempty m]
    (A : Matrix n n ℝ) :
    logNorm (Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ)) = logNorm A := by
  rw [logNorm_def _
      (inferInstanceAs (Nonempty (n × m))), logNorm_def A (inferInstanceAs (Nonempty n))]
  have hrow : ∀ p : n × m,
      Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p p
        + ∑ j ∈ Finset.univ.erase p,
            |Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p j|
      = A p.1 p.1 + ∑ j ∈ Finset.univ.erase p.1, |A p.1 j| := by
    intro p
    have hdiag : Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p p = A p.1 p.1 := by
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply]
    have hsum : (∑ j : n × m,
          |Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p j|)
        = ∑ s : n, |A p.1 s| := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      simp only [Matrix.kroneckerMap_apply, abs_mul, Matrix.one_apply]
      have hone : (∑ y : m, |if p.2 = y then (1 : ℝ) else 0|) = 1 := by
        rw [Finset.sum_eq_single p.2]
        · simp
        · intro y _ hy
          simp [show p.2 ≠ y from fun h' => hy h'.symm]
        · intro hv
          exact absurd (Finset.mem_univ p.2) hv
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum, hone, mul_one]
    have herase : (∑ j ∈ Finset.univ.erase p,
          |Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p j|)
        = (∑ s : n, |A p.1 s|) - |A p.1 p.1| := by
      have h := Finset.add_sum_erase (Finset.univ : Finset (n × m))
        (fun j => |Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p j|)
        (Finset.mem_univ p)
      simp only [hsum, hdiag] at h
      linarith
    have hinner := Finset.add_sum_erase (Finset.univ : Finset n)
      (fun s => |A p.1 s|) (Finset.mem_univ p.1)
    rw [hdiag, herase]
    linarith
  have hfun : (fun p : n × m =>
        Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p p
          + ∑ j ∈ Finset.univ.erase p,
              |Matrix.kroneckerMap (· * ·) A (1 : Matrix m m ℝ) p j|)
      = fun p : n × m => A p.1 p.1 + ∑ j ∈ Finset.univ.erase p.1, |A p.1 j| :=
    funext hrow
  rw [hfun]
  exact sup'_univ_prod_fst (fun i : n => A i i + ∑ j ∈ Finset.univ.erase i, |A i j|)

end Qatlib.Papers.CarlemanError17.MainResults.Core
