/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SparseAccessConstructionDefs

/-!
# Block encoding from sparse matrix access

`leftPrep` and `rightPrep` prepare row-address and column-value superpositions on a padded
workspace. For legal sparse-access data with positive row and column slot counts, their relative
unitary compresses to the matrix divided by `sqrt sr * sqrt sc`.

The module constructs the workspace frames, proves unitarity and the compression formula, and
packages an exact block encoding with normalization `sparseAlpha sr sc`. See
[GilyenSuLowWiebe2019].

## Main statements

* `sparse_corner`: compute the selected matrix entry of the preparation product.
* `sparseProjectedUnitaryEncoding`: encode the normalized sparse matrix.
* `sparseBlockEncoding`: construct the exact block encoding.
* `sparseBlockEncoding_norm_le`: bound the matrix norm by the normalization.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {sr sc : ℕ}

/-- A finite complex sum supported at a single index equals the value at that index. -/
private theorem sum_indicator {A : Type*} [Fintype A] [DecidableEq A] (f : A → ℂ) (a : A) :
    (∑ x : A, if a = x then f x else 0) = f a := by
  classical
  rw [Fintype.sum_eq_single a]
  · simp
  · intro x hx
    rw [if_neg (fun h => hx h.symm)]

/-- A condition independent of the summation index can be moved outside a finite sum. -/
private theorem sum_block_inner {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (f : B → ℂ) (x a : A) :
    (∑ b : B, if x = a then f b else 0) = if x = a then ∑ b, f b else 0 := by
  classical
  by_cases h : x = a
  · simp [h]
  · have hz : ∀ b, (if x = a then f b else 0) = 0 := by
      intro b
      rw [if_neg h]
    rw [Finset.sum_congr rfl fun b _ => hz b]
    rw [if_neg h]
    simp

/-- A double finite sum supported at one outer index reduces to the inner sum at that index. -/
private theorem sum_block_outer {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (f : A → B → ℂ) (a : A) :
    (∑ x' : A, ∑ b : B, (if a = x' then f x' b else 0)) = ∑ b, f a b := by
  classical
  have h1 : (∑ x' : A, ∑ b : B, (if a = x' then f x' b else 0))
      = ∑ x' : A, (if a = x' then ∑ b, f x' b else 0) :=
    Fintype.sum_congr _ _ (fun x' => sum_block_inner (f x') a x')
  rw [h1]
  rw [sum_indicator (fun x' => ∑ b, f x' b) a]

/-- The block diagonal matrix acting on the second coordinate, with a block selected by the
first coordinate. -/
noncomputable def blockDiagFirst {A B : Type*} (blk : A → Matrix B B ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (blk p.1) p.2 q.2 else 0

/-- The matrix applying the block indexed by the middle coordinate to the first coordinate and
preserving the remaining coordinates. -/
noncomputable def blockDiagCross {A B C : Type*} (blk : A → Matrix B B ℂ) :
    Matrix (B × (A × C)) (B × (A × C)) ℂ :=
  Matrix.of fun p q =>
    if p.2.1 = q.2.1 then (if p.2.2 = q.2.2 then (blk p.2.1) p.1 q.1 else 0) else 0

/-- A block diagonal matrix is unitary when each of its blocks is unitary. -/
theorem blockDiagFirst_unitary {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (blk : A → Matrix B B ℂ) (hblk : ∀ a, blk a ∈ Matrix.unitaryGroup B ℂ) :
    blockDiagFirst blk ∈ Matrix.unitaryGroup (A × B) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  simp only [blockDiagFirst, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  by_cases h : p.1 = q.1
  · have hrw : ∀ (a : A) (b : B),
        (if p.1 = a then (blk p.1) p.2 b else 0) * star (if q.1 = a then (blk q.1) q.2 b else 0)
          = (if p.1 = a then ((blk p.1) p.2 b) * star ((blk p.1) q.2 b) else 0) := by
      intro a b
      by_cases ha : p.1 = a
      · have ha' : q.1 = a := by rw [← h]; exact ha
        simp [ha, ha']
      · have ha' : q.1 ≠ a := by
          intro e
          exact ha (h ▸ e)
        simp [ha, ha']
    simp only [hrw]
    have hout : (∑ a : A, ∑ b : B,
          (if p.1 = a then ((blk p.1) p.2 b) * star ((blk p.1) q.2 b) else 0))
        = ∑ b : B, ((blk p.1) p.2 b) * star ((blk p.1) q.2 b) :=
      sum_block_outer (fun _ b => ((blk p.1) p.2 b) * star ((blk p.1) q.2 b)) p.1
    rw [hout]
    have hone : (∑ b : B, ((blk p.1) p.2 b) * star ((blk p.1) q.2 b))
        = (blk p.1 * star (blk p.1)) p.2 q.2 := by
      rw [Matrix.mul_apply, Matrix.star_eq_conjTranspose]
      simp only [Matrix.conjTranspose_apply]
    rw [hone, Matrix.mem_unitaryGroup_iff.mp (hblk p.1)]
    by_cases h2 : p.2 = q.2
    · have hpq : p = q := Prod.ext h h2
      simp [hpq, Matrix.one_apply]
    · have hpq : p ≠ q := by
        intro e
        exact h2 (congrArg Prod.snd e)
      simp [hpq, h2]
  · have hzero : ∀ (a : A) (b : B),
        (if p.1 = a then (blk p.1) p.2 b else 0) * star (if q.1 = a then (blk q.1) q.2 b else 0) = 0 := by
      intro a b
      by_cases ha : p.1 = a
      · have ha' : q.1 ≠ a := by
          intro e
          exact h (ha.trans e.symm)
        simp [ha, ha']
      · simp [ha]
    simp only [hzero]
    have hpq : p ≠ q := fun e => h (congrArg Prod.fst e)
    simp [hpq]

/-- The sum of a block row times a conjugated block row is the corresponding entry of the block
times its conjugate transpose. -/
private theorem block_inner_sum {A B : Type*} [Fintype B] [DecidableEq B]
    (blk : A → Matrix B B ℂ) (a : A) (b b' : B) :
    (∑ bz : B, ((blk a) b bz) * star ((blk a) b' bz)) = ((blk a) * (blk a)ᴴ) b b' := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- For equal middle and final coordinates, the row product of `blockDiagCross` reduces to the
corresponding block row product supported on those coordinates. -/
private theorem cross_term_eq_block {A B C : Type*} [DecidableEq A] [DecidableEq C]
    (blk : A → Matrix B B ℂ) (b b' : B) (a : A) (c : C) :
    ∀ z : B × (A × C),
      blockDiagCross blk (b, (a, c)) z * star (blockDiagCross blk (b', (a, c)) z)
        = if z.2 = (a, c) then ((blk a) b z.1) * star ((blk a) b' z.1) else 0 := by
  intro z
  rcases z with ⟨bz, ⟨az, cz⟩⟩
  simp only [blockDiagCross, Matrix.of_apply]
  by_cases h1 : az = a
  · by_cases h2 : cz = c
    · simp [h1, h2]
    · have h2' : ¬(c = cz) := fun e => h2 e.symm
      simp [h1, h2, h2']
  · have h1' : ¬(a = az) := fun e => h1 e.symm
    simp [h1, h1']

/-- Rows of `blockDiagCross` with different middle or final coordinates have zero pointwise
products after conjugating the second row. -/
private theorem cross_term_eq_zero {A B C : Type*} [DecidableEq A] [DecidableEq C]
    (blk : A → Matrix B B ℂ) (b b' : B) (a a' : A) (c c' : C)
    (hne : (a = a' ∧ c = c') → False) :
    ∀ z : B × (A × C),
      blockDiagCross blk (b, (a, c)) z * star (blockDiagCross blk (b', (a', c')) z) = 0 := by
  intro z
  rcases z with ⟨bz, ⟨az, cz⟩⟩
  simp only [blockDiagCross, Matrix.of_apply]
  by_cases h1 : az = a
  · by_cases h2 : cz = c
    · by_cases h3 : az = a'
      · by_cases h4 : cz = c'
        · exact absurd ⟨h1.symm.trans h3, h2.symm.trans h4⟩ hne
        · have h4' : ¬(c' = cz) := fun e => h4 e.symm
          simp [h4']
      · have h3' : ¬(a' = az) := fun e => h3 e.symm
        simp [h3']
    · have h2' : ¬(c = cz) := fun e => h2 e.symm
      simp [h2']
  · have h1' : ¬(a = az) := fun e => h1 e.symm
    simp [h1']

/-- The crossed block diagonal matrix is unitary when each block is unitary. -/
theorem blockDiagCross_unitary {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (blk : A → Matrix B B ℂ)
    (hblk : ∀ a, blk a ∈ Matrix.unitaryGroup B ℂ) :
    blockDiagCross blk ∈ Matrix.unitaryGroup (B × (A × C)) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  rcases p with ⟨b, ⟨a, c⟩⟩
  rcases q with ⟨b', ⟨a', c'⟩⟩
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  by_cases haa : a = a'
  · by_cases hcc : c = c'
    · rw [haa, hcc]
      have hrw : ∀ z : B × (A × C),
          blockDiagCross blk (b, (a', c')) z * star (blockDiagCross blk (b', (a', c')) z)
            = if z.2 = (a', c') then ((blk a') b z.1) * star ((blk a') b' z.1) else 0 :=
        cross_term_eq_block blk b b' a' c'
      have hrw' : (∑ z : B × (A × C),
            blockDiagCross blk (b, (a', c')) z * star (blockDiagCross blk (b', (a', c')) z))
          = ∑ z : B × (A × C),
            (if z.2 = (a', c') then ((blk a') b z.1) * star ((blk a') b' z.1) else 0) := by
        classical
        exact Fintype.sum_congr _ _ (fun z => hrw z)
      rw [hrw']
      have hswap : (∑ x : B, ∑ y : A × C,
            (if (x, y).2 = (a', c') then ((blk a') b (x, y).1) * star ((blk a') b' (x, y).1) else 0))
          = ∑ x : B, ((blk a') b x) * star ((blk a') b' x) := by
        classical
        refine Fintype.sum_congr _ _ (fun x => ?_)
        rw [Fintype.sum_eq_single (a', c')]
        · simp
        · intro y hy
          simp [hy]
      rw [Fintype.sum_prod_type]
      rw [hswap]
      rw [block_inner_sum]
      have hmul : (blk a') * (blk a')ᴴ = (1 : Matrix B B ℂ) :=
        Matrix.mem_unitaryGroup_iff.mp (hblk a')
      rw [hmul]
      simp [Matrix.one_apply]
    · have hzero : ∀ z : B × (A × C),
          blockDiagCross blk (b, (a, c)) z * star (blockDiagCross blk (b', (a', c')) z) = 0 :=
        cross_term_eq_zero blk b b' a a' c c' (fun h => hcc h.2)
      simp only [hzero]
      have hpq : (b, (a, c)) ≠ (b', (a', c')) := by
        intro e
        exact hcc (congrArg (fun x => x.2.2) e)
      simp [hpq]
  · have hzero : ∀ z : B × (A × C),
        blockDiagCross blk (b, (a, c)) z * star (blockDiagCross blk (b', (a', c')) z) = 0 :=
      cross_term_eq_zero blk b b' a a' c c' (fun h => haa h.1)
    simp only [hzero]
    have hpq : (b, (a, c)) ≠ (b', (a', c')) := by
      intro e
      exact haa (congrArg (fun x => x.2.1) e)
    simp [hpq]

/-- The first padded column address, available when the row slot count is positive. -/
def colScratch (O : Type*) (sr : ℕ) (hsr : 0 < sr) : ColAddr O sr := .inr ⟨0, hsr⟩

/-- The first padded row address, available when the column slot count is positive. -/
def rowScratch (I : Type*) (sc : ℕ) (hsc : 0 < sc) : RowAddr I sc := .inr ⟨0, hsc⟩

/-- The designated column of `complexPrepare v zero` is the vector `v`. -/
private theorem complexPrepare_column {J : Type*} [Fintype J] [DecidableEq J] (v : J → ℂ)
    (zero : J) (j : J) : complexPrepare v zero j zero = v j := by
  have h := congrFun (complexPrepare_mulVec_ket v zero) j
  simpa [Matrix.mulVec, dotProduct, Ket, Matrix.mul_apply] using h

/-- The complex norm of a nonnegative real scalar is that scalar. -/
private theorem realComplex_norm (n : ℝ) (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]

/-- The complex norm of a real square root is the same real square root. -/
private theorem sqrtComplex_norm (n : ℝ) : ‖(Real.sqrt n : ℂ)‖ = Real.sqrt n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n)]

/-- For legal sparse-access data and a positive row slot count, every row-address vector is
normalized. -/
theorem rowAddressVector_normalized (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (hsr : 0 < sr) : Qatlib.Foundations.PureStateMath.Normalized (rowAddressVector D i) := by
  have hsqrt : (Real.sqrt sr : ℝ) ^ 2 = (sr : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hfactor : ‖(Real.sqrt sr : ℂ)⁻¹‖ = (Real.sqrt sr : ℝ)⁻¹ := by
    rw [norm_inv, sqrtComplex_norm]
  have hsq : ∀ c : ColAddr O sr, ‖rowAddressVector D i c‖ ^ 2
      = ((rowSlotCount D i c : ℝ) ^ 2) / sr := by
    intro c
    rw [rowAddressVector, Complex.norm_mul, hfactor,
      realComplex_norm (rowSlotCount D i c) (Nat.cast_nonneg _)]
    rw [mul_pow, inv_pow, hsqrt]
    ring
  have hsq2 : ∀ c : ColAddr O sr, ((rowSlotCount D i c : ℝ) ^ 2)
      = (rowSlotCount D i c : ℝ) := by
    intro c
    have hcases : rowSlotCount D i c = 0 ∨ rowSlotCount D i c = 1 := by
      have hle := rowSlotCount_le_one D hD i c
      omega
    rcases hcases with h0 | h1
    · simp [h0]
    · simp [h1]
  unfold Qatlib.Foundations.PureStateMath.Normalized
  simp only [hsq, hsq2]
  rw [← Finset.sum_div]
  have hcast : (∑ c : ColAddr O sr, (rowSlotCount D i c : ℝ)) = (sr : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_rowSlotCount D i)
    simpa [Nat.cast_sum] using h
  rw [hcast]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsr))

/-- For legal sparse-access data, the squared norms of the two Boolean amplitudes at each column
address sum to one. -/
private theorem colAmp_norm (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (r : RowAddr I sc) :
    ‖colAmp D j r false‖ ^ 2 + ‖colAmp D j r true‖ ^ 2 = 1 := by
  cases r with
  | inl i =>
    have hb := hD.entryBound i j
    have hsq : ‖D.entry i j‖ ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ ‖D.entry i j‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖D.entry i j‖)]
    have hpos : 0 ≤ 1 - ‖D.entry i j‖ ^ 2 := by linarith
    have h1 : colAmp D j (.inl i) false = D.entry i j := by simp [colAmp]
    have h2 : colAmp D j (.inl i) true = (Real.sqrt (1 - ‖D.entry i j‖ ^ 2) : ℂ) := by
      simp [colAmp]
    rw [h1, h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hpos]
    ring
  | inr c =>
    have h1 : colAmp D j (.inr c) false = 0 := by simp [colAmp]
    have h2 : colAmp D j (.inr c) true = 1 := by simp [colAmp]
    rw [h1, h2]
    simp

/-- The real weight given by the square of the column slot multiplicity times the squared norm
of the selected Boolean amplitude. -/
noncomputable def colValueWeight (D : SparseAccess I O sr sc) (j : O)
    (r : RowAddr I sc) (f : Bool) : ℝ :=
  ((colSlotCount D j r : ℝ) ^ 2) * ‖colAmp D j r f‖ ^ 2

/-- For legal sparse-access data and a positive column slot count, every column-value
superposition is normalized. -/
theorem colValueSuperposition_normalized (D : SparseAccess I O sr sc)
    (hD : SparseAccessLegal D) (j : O) (hsc : 0 < sc) :
    Qatlib.Foundations.PureStateMath.Normalized (colValueSuperposition D j) := by
  have hsqrt : (Real.sqrt sc : ℝ) ^ 2 = (sc : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hfactor : ‖(Real.sqrt sc : ℂ)⁻¹‖ = (Real.sqrt sc : ℝ)⁻¹ := by
    rw [norm_inv, sqrtComplex_norm]
  have hsq : ∀ (r : RowAddr I sc) (f : Bool), ‖colValueSuperposition D j (r, f)‖ ^ 2
      = colValueWeight D j r f / sc := by
    intro r f
    rw [colValueSuperposition, Complex.norm_mul, Complex.norm_mul, hfactor,
      realComplex_norm (colSlotCount D j r) (Nat.cast_nonneg _)]
    rw [mul_pow, mul_pow, inv_pow, hsqrt]
    simp only [colValueWeight]
    ring
  have hper : ∀ r : RowAddr I sc, (∑ f : Bool, ‖colAmp D j r f‖ ^ 2) = 1 := by
    intro r
    rw [Fintype.sum_bool, add_comm, colAmp_norm D hD j r]
  have hper' : ∀ r : RowAddr I sc,
      ‖colAmp D j r true‖ ^ 2 + ‖colAmp D j r false‖ ^ 2 = 1 := by
    intro r
    rw [← add_comm, colAmp_norm D hD j r]
  have hinner : ∀ r : RowAddr I sc,
      (∑ f : Bool, colValueWeight D j r f) = (colSlotCount D j r : ℝ) ^ 2 := by
    intro r
    have hbool : (∑ f : Bool, colValueWeight D j r f)
        = colValueWeight D j r true + colValueWeight D j r false := Fintype.sum_bool _
    rw [hbool]
    simp only [colValueWeight]
    calc (↑(colSlotCount D j r) : ℝ) ^ 2 * ‖colAmp D j r true‖ ^ 2
        + (↑(colSlotCount D j r) : ℝ) ^ 2 * ‖colAmp D j r false‖ ^ 2
        = (↑(colSlotCount D j r) : ℝ) ^ 2
            * (‖colAmp D j r true‖ ^ 2 + ‖colAmp D j r false‖ ^ 2) := by ring
      _ = (↑(colSlotCount D j r) : ℝ) ^ 2 := by rw [hper' r]; ring
  have hsum : (∑ r : RowAddr I sc, ∑ f : Bool, colValueWeight D j r f)
      = ∑ r : RowAddr I sc, (colSlotCount D j r : ℝ) ^ 2 := by
    refine Fintype.sum_congr _ _ (fun r => ?_)
    exact hinner r
  have hsq2 : ∀ r : RowAddr I sc, ((colSlotCount D j r : ℝ) ^ 2)
      = (colSlotCount D j r : ℝ) := by
    intro r
    have hcases : colSlotCount D j r = 0 ∨ colSlotCount D j r = 1 := by
      have hle := colSlotCount_le_one D hD j r
      omega
    rcases hcases with h0 | h1
    · simp [h0]
    · simp [h1]
  unfold Qatlib.Foundations.PureStateMath.Normalized
  rw [Fintype.sum_prod_type]
  simp only [hsq]
  simp only [← Finset.sum_div]
  rw [hsum]
  simp only [hsq2]
  have hcast : (∑ r : RowAddr I sc, (colSlotCount D j r : ℝ)) = (sc : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_colSlotCount D j)
    simpa [Nat.cast_sum] using h
  rw [hcast]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsc))

/-- The matrix preparing the row-address vector from the designated column scratch address. -/
noncomputable def leftBlock (D : SparseAccess I O sr sc) (i : I) (scratch : ColAddr O sr) :
    Matrix (ColAddr O sr) (ColAddr O sr) ℂ :=
  complexPrepare (rowAddressVector D i) scratch

/-- The matrix preparing the column-value superposition from the designated row scratch address
with Boolean flag false. -/
noncomputable def rightBlock (D : SparseAccess I O sr sc) (j : O) (scratch : RowAddr I sc) :
    Matrix (RowAddr I sc × Bool) (RowAddr I sc × Bool) ℂ :=
  complexPrepare (colValueSuperposition D j) (scratch, false)

/-- The workspace matrix applying `leftBlock` on legal row addresses and the identity on padded
row addresses. -/
noncomputable def leftPrep (D : SparseAccess I O sr sc) (scratch : ColAddr O sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun r => match r with
    | .inl i => leftBlock D i scratch
    | .inr _ => 1)

/-- The workspace matrix applying `rightBlock` on legal column addresses and the identity on
padded column addresses. -/
noncomputable def rightPrep (D : SparseAccess I O sr sc) (scratch : RowAddr I sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => rightBlock D j scratch
    | .inr _ => 1)

/-- The left preparation matrix is unitary for legal sparse-access data with a positive row slot
count. -/
theorem leftPrep_unitary (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratch : ColAddr O sr) (hsr : 0 < sr) :
    leftPrep D scratch ∈ Matrix.unitaryGroup (SparseWorkspace I O sr sc) ℂ := by
  refine blockDiagCross_unitary _ ?_
  intro r
  cases r with
  | inl i => exact complexPrepare_unitary _ _ (rowAddressVector_normalized D hD i hsr)
  | inr c => exact (Matrix.unitaryGroup _ ℂ).one_mem

/-- The right preparation matrix is unitary for legal sparse-access data with a positive column
slot count. -/
theorem rightPrep_unitary (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratch : RowAddr I sc) (hsc : 0 < sc) :
    rightPrep D scratch ∈ Matrix.unitaryGroup (SparseWorkspace I O sr sc) ℂ := by
  refine blockDiagFirst_unitary _ ?_
  intro c
  cases c with
  | inl j => exact complexPrepare_unitary _ _ (colValueSuperposition_normalized D hD j hsc)
  | inr k => exact (Matrix.unitaryGroup _ ℂ).one_mem

/-- The matrix whose columns are basis vectors selected by an injective map is an isometry. -/
private theorem deltaFrame_isIsometry {H A : Type*} [Fintype H] [DecidableEq H] [Fintype A]
    [DecidableEq A] (f : A → H) (hne : Function.Injective f) :
    IsIsometry (Matrix.of fun x a => if x = f a then 1 else 0) := by
  unfold IsIsometry
  ext a a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases h : a = a'
  · subst a'
    rw [Fintype.sum_eq_single (f a)]
    · simp
    · intro x hx
      simp [hx]
  · have hsum0 : (∑ x : H, star (if x = f a then (1 : ℂ) else 0)
        * (if x = f a' then (1 : ℂ) else 0)) = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      by_cases hx1 : x = f a
      · have hx2 : f a ≠ f a' := by
          intro e
          exact h (hne e)
        simp [hx1, hx2]
      · simp [hx1]
    calc (∑ x : H, star (if x = f a then (1 : ℂ) else 0)
        * (if x = f a' then (1 : ℂ) else 0)) = 0 := hsum0
      _ = if a = a' then (1 : ℂ) else 0 := by simp [h]

/-- The basis-vector frame embedding row indices with the designated column scratch address and
Boolean flag false. -/
noncomputable def leftFrame (scratch : ColAddr O sr) :
    Matrix (SparseWorkspace I O sr sc) I ℂ :=
  Matrix.of fun x i => if x = (scratch, (.inl i, false)) then 1 else 0

/-- The basis-vector frame embedding column indices with the designated row scratch address and
Boolean flag false. -/
noncomputable def rightFrame (scratch : RowAddr I sc) :
    Matrix (SparseWorkspace I O sr sc) O ℂ :=
  Matrix.of fun x j => if x = (.inl j, (scratch, false)) then 1 else 0

/-- The row-index frame `leftFrame` is an isometry. -/
theorem leftFrame_isIsometry (scratch : ColAddr O sr) :
    IsIsometry (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratch) := by
  refine deltaFrame_isIsometry _ ?_
  intro i i' h
  have h1 : ((.inl i : RowAddr I sc), false) = ((.inl i' : RowAddr I sc), false) :=
    congrArg Prod.snd h
  have h2 : i = i' := by
    injection congrArg Prod.fst h1
  exact h2

/-- The column-index frame `rightFrame` is an isometry. -/
theorem rightFrame_isIsometry (scratch : RowAddr I sc) :
    IsIsometry (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratch) := by
  refine deltaFrame_isIsometry _ ?_
  intro j j' h
  have h1 : ((.inl j : ColAddr O sr)) = ((.inl j' : ColAddr O sr)) := congrArg Prod.fst h
  have h2 : j = j' := by
    injection h1
  exact h2

/-- The designated column of `leftPrep` equals the row-address vector on the matching row
address and false flag, and vanishes elsewhere. -/
theorem leftPrep_entry (D : SparseAccess I O sr sc) (scratch : ColAddr O sr) (i : I)
    (c : ColAddr O sr) (r : RowAddr I sc) (f : Bool) :
    leftPrep D scratch (c, (r, f)) (scratch, (.inl i, false))
      = if r = .inl i then (if f = false then rowAddressVector D i c else 0) else 0 := by
  cases r with
  | inl i' =>
    by_cases hi : i' = i
    · subst hi
      simp [leftPrep, blockDiagCross, leftBlock, complexPrepare_column]
    · simp [leftPrep, blockDiagCross, leftBlock, hi]
  | inr c' =>
    simp [leftPrep, blockDiagCross]

/-- The designated column of `rightPrep` equals the column-value superposition on the matching
column address and vanishes elsewhere. -/
theorem rightPrep_entry (D : SparseAccess I O sr sc) (scratch : RowAddr I sc) (j : O)
    (c : ColAddr O sr) (r : RowAddr I sc) (f : Bool) :
    rightPrep D scratch (c, (r, f)) (.inl j, (scratch, false))
      = if c = .inl j then colValueSuperposition D j (r, f) else 0 := by
  cases c with
  | inl o =>
    by_cases hj : o = j
    · subst hj
      simp [rightPrep, blockDiagFirst, rightBlock, complexPrepare_column]
    · simp [rightPrep, blockDiagFirst, rightBlock, hj]
  | inr k =>
    simp [rightPrep, blockDiagFirst]

/-- For legal sparse-access data with positive slot counts, the selected corner of the
left-adjoint/right preparation product is `D.entry i j / (sqrt sr * sqrt sc)`. -/
theorem sparse_corner (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc)
    (i : I) (j : O) (hsr : 0 < sr) (hsc : 0 < sc) :
    ((leftPrep D scratchCol)ᴴ * (rightPrep D scratchRow))
      (scratchCol, (.inl i, false)) (.inl j, (scratchRow, false))
      = D.entry i j / ((Real.sqrt sr : ℂ) * (Real.sqrt sc : ℂ)) := by
  have hrow : rowSlotCount D i (.inl j) = if D.entry i j = 0 then 0 else 1 := by
    have h := rowLegalCount_eq D hD i j
    simpa [rowSlotCount, rowLegalCount] using h
  have hcol : colSlotCount D j (.inl i) = if D.entry i j = 0 then 0 else 1 := by
    have h := colLegalCount_eq D hD j i
    simpa [colSlotCount, colLegalCount] using h
  have hamp : colAmp D j (.inl i) false = D.entry i j := by
    simp [colAmp]
  have hpoint : ∀ x : SparseWorkspace I O sr sc,
      star (leftPrep D scratchCol x (scratchCol, (.inl i, false)))
          * (rightPrep D scratchRow x (.inl j, (scratchRow, false)))
        = if x.2 = (.inl i, false) ∧ x.1 = .inl j then
            star (rowAddressVector D i x.1) * (colValueSuperposition D j x.2) else 0 := by
    intro x
    rcases x with ⟨c, r, f⟩
    by_cases hr : r = .inl i
    · by_cases hf : f = false
      · by_cases hc : c = .inl j
        · simp [leftPrep_entry, rightPrep_entry, hr, hf, hc]
        · simp [leftPrep_entry, rightPrep_entry, hr, hf, hc]
      · simp [leftPrep_entry, rightPrep_entry, hr, hf]
    · simp [leftPrep_entry, rightPrep_entry, hr]
  have hsum : (∑ x : SparseWorkspace I O sr sc,
        star (leftPrep D scratchCol x (scratchCol, (.inl i, false)))
          * (rightPrep D scratchRow x (.inl j, (scratchRow, false))))
      = ∑ x : SparseWorkspace I O sr sc,
        (if x.2 = (.inl i, false) ∧ x.1 = .inl j then
          star (rowAddressVector D i x.1) * (colValueSuperposition D j x.2) else 0) := by
    exact Fintype.sum_congr _ _ (fun x => hpoint x)
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [hsum]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ c : ColAddr O sr,
      (∑ x : RowAddr I sc × Bool,
        (if x = (.inl i, false) ∧ c = .inl j then
          star (rowAddressVector D i c) * (colValueSuperposition D j x) else 0))
        = (if c = .inl j then
            star (rowAddressVector D i c) * (colValueSuperposition D j (.inl i, false)) else 0) := by
    intro c
    rw [Fintype.sum_eq_single (.inl i, false)]
    · simp
    · intro x hx
      simp [hx]
  have houter : (∑ c : ColAddr O sr,
        (∑ x : RowAddr I sc × Bool,
          (if x = (.inl i, false) ∧ c = .inl j then
            star (rowAddressVector D i c) * (colValueSuperposition D j x) else 0)))
      = (∑ c : ColAddr O sr,
        (if c = .inl j then
          star (rowAddressVector D i c) * (colValueSuperposition D j (.inl i, false)) else 0)) := by
    refine Fintype.sum_congr _ _ (fun c => ?_)
    rw [hinner c]
  have houter2 : (∑ c : ColAddr O sr,
        (if c = .inl j then
          star (rowAddressVector D i c) * (colValueSuperposition D j (.inl i, false)) else 0))
      = star (rowAddressVector D i (.inl j)) * (colValueSuperposition D j (.inl i, false)) := by
    rw [Fintype.sum_eq_single (.inl j)]
    · simp
    · intro c hc
      simp [hc]
  rw [houter, houter2]
  have hsrne : (Real.sqrt sr : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (Nat.cast_pos.2 hsr)).ne'
  have hscne : (Real.sqrt sc : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (Nat.cast_pos.2 hsc)).ne'
  rw [rowAddressVector, colValueSuperposition, hamp]
  by_cases hz : D.entry i j = 0
  · rw [hrow, hcol]
    simp [hz]
  · rw [hrow, hcol]
    simp [hz]
    field_simp [hsrne, hscne]

/-- The two-dimensional amplitude matrix with first column `(a, sqrt (1 - ‖a‖²))` and second
column `(-sqrt (1 - ‖a‖²), star a)`. -/
noncomputable def ampGate (a : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j =>
    if i = false then
      (if j = false then a else -((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ))
    else
      (if j = false then ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) else (starRingEnd ℂ) a)

/-- The workspace operator `(leftPrep D scratchCol)ᴴ * rightPrep D scratchRow`. -/
noncomputable def sparseOperator (D : SparseAccess I O sr sc) (scratchCol : ColAddr O sr)
    (scratchRow : RowAddr I sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  (leftPrep D scratchCol)ᴴ * (rightPrep D scratchRow)

/-- The sparse normalization `sparseAlpha sr sc` is positive when both slot counts are positive. -/
theorem sparseAlpha_pos (hsr : 0 < sr) (hsc : 0 < sc) : 0 < sparseAlpha sr sc := by
  exact mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hsr)) (Real.sqrt_pos.2 (Nat.cast_pos.2 hsc))

/-- The complex sparse normalization is nonzero when both slot counts are positive. -/
theorem sparseAlphaComplex_ne_zero (hsr : 0 < sr) (hsc : 0 < sc) :
    sparseAlphaComplex sr sc ≠ 0 := by
  rw [sparseAlphaComplex_eq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (sparseAlpha_pos hsr hsc))

/-- The sparse workspace operator is unitary for legal data with positive row and column slot
counts. -/
theorem sparseOperator_unitary (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (hsr : 0 < sr) (hsc : 0 < sc) :
    sparseOperator D scratchCol scratchRow
      ∈ Matrix.unitaryGroup (SparseWorkspace I O sr sc) ℂ := by
  have hL : leftPrep D scratchCol * (leftPrep D scratchCol)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (leftPrep_unitary D hD scratchCol hsr)
  have hR : (rightPrep D scratchRow)ᴴ * rightPrep D scratchRow = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (rightPrep_unitary D hD scratchRow hsc)
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [sparseOperator, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  calc (rightPrep D scratchRow)ᴴ * (leftPrep D scratchCol * ((leftPrep D scratchCol)ᴴ
        * rightPrep D scratchRow))
      = (rightPrep D scratchRow)ᴴ * ((leftPrep D scratchCol * (leftPrep D scratchCol)ᴴ)
        * rightPrep D scratchRow) := by
        rw [← Matrix.mul_assoc (leftPrep D scratchCol) (leftPrep D scratchCol)ᴴ
          (rightPrep D scratchRow)]
    _ = (rightPrep D scratchRow)ᴴ * (1 * rightPrep D scratchRow) := by rw [hL]
    _ = 1 := by rw [Matrix.one_mul, hR]

/-- Compression between the two basis-vector frames selects the corresponding scratch-address
entry of the workspace matrix. -/
theorem compress_deltaFrame (scratchCol : ColAddr O sr)
    (scratchRow : RowAddr I sc)
    (U : Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ) (i : I) (j : O) :
    compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol) U
        (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) i j
      = U (scratchCol, (.inl i, false)) (.inl j, (scratchRow, false)) := by
  classical
  have hL : ∀ x : SparseWorkspace I O sr sc,
      leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol x i
        = if x = (scratchCol, (.inl i, false)) then 1 else 0 := by
    intro x
    simp [leftFrame, Matrix.of_apply]
  have hR : ∀ y : SparseWorkspace I O sr sc,
      rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow y j
        = if y = (.inl j, (scratchRow, false)) then 1 else 0 := by
    intro y
    simp [rightFrame, Matrix.of_apply]
  have hinner : ∀ y : SparseWorkspace I O sr sc,
      (∑ x : SparseWorkspace I O sr sc,
        star (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol x i) * U x y)
        = U (scratchCol, (.inl i, false)) y := by
    intro y
    have hstar : ∀ x : SparseWorkspace I O sr sc,
        star (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol x i)
          = if x = (scratchCol, (.inl i, false)) then 1 else 0 := by
      intro x
      rw [hL x]
      by_cases h : x = (scratchCol, (.inl i, false))
      · simp [h]
      · simp [h]
    rw [Fintype.sum_eq_single (scratchCol, (.inl i, false))]
    · simp [hstar]
    · intro x hx
      rw [hstar x, if_neg hx]
      simp
  have hsum : (∑ y : SparseWorkspace I O sr sc,
        (∑ x : SparseWorkspace I O sr sc,
          star (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol x i) * U x y)
          * (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow y j))
      = ∑ y : SparseWorkspace I O sr sc,
        U (scratchCol, (.inl i, false)) y
          * (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow y j) := by
    refine Fintype.sum_congr _ _ fun y => ?_
    rw [hinner y]
  rw [compress]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsum]
  rw [Fintype.sum_eq_single (.inl j, (scratchRow, false))]
  · simp [hR]
  · intro y hy
    rw [hR y, if_neg hy]
    simp

/-- The compressed sparse operator has entry `D.entry i j / sparseAlphaComplex sr sc` under
legality and positive slot counts. -/
theorem compress_sparseOperator (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (i : I) (j : O)
    (hsr : 0 < sr) (hsc : 0 < sc) :
    compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
        (sparseOperator D scratchCol scratchRow)
        (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) i j
      = D.entry i j / sparseAlphaComplex sr sc := by
  rw [compress_deltaFrame, sparseOperator]
  rw [sparse_corner D hD scratchCol scratchRow i j hsr hsc]
  rfl

/-- Compression of the sparse operator between the designated frames equals
`SparseAccess.encoded D`. -/
theorem compress_sparseOperator_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (hsr : 0 < sr) (hsc : 0 < sc) :
    compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
        (sparseOperator D scratchCol scratchRow)
        (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)
      = SparseAccess.encoded D := by
  ext i j
  exact compress_sparseOperator D hD scratchCol scratchRow i j hsr hsc

/-- Legal sparse-access data with positive slot counts yields a projected unitary encoding of
its normalized matrix using the sparse operator and the two frames. -/
theorem sparseProjectedUnitaryEncoding (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (hsr : 0 < sr) (hsc : 0 < sc) :
    ProjectedUnitaryEncoding (SparseAccess.encoded D) (sparseOperator D scratchCol scratchRow)
      (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
      (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) := by
  refine ⟨sparseOperator_unitary D hD scratchCol scratchRow hsr hsc,
    leftFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchCol,
    rightFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchRow, ?_⟩
  exact compress_sparseOperator_eq D hD scratchCol scratchRow hsr hsc

/-- Legal sparse-access data with positive slot counts yields an exact block encoding with
normalization `sqrt sr * sqrt sc` and error zero. See [GilyenSuLowWiebe2019]. -/
theorem sparseBlockEncoding (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (hsr : 0 < sr) (hsc : 0 < sc) :
    BlockEncoding (SparseAccess.matrix D) (sparseOperator D scratchCol scratchRow)
      (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
      (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)
      (sparseAlpha sr sc) 0 := by
  refine ⟨sparseOperator_unitary D hD scratchCol scratchRow hsr hsc,
    leftFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchCol,
    rightFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchRow, ?_, le_rfl, ?_⟩
  · exact mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hsr)) (Real.sqrt_pos.2 (Nat.cast_pos.2 hsc))
  · have hzero : SparseAccess.matrix D
        - (sparseAlpha sr sc : ℝ) •
            compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
              (sparseOperator D scratchCol scratchRow)
              (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) = 0 := by
      have hsmul : (sparseAlpha sr sc : ℝ) •
          compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)
          = (sparseAlpha sr sc : ℂ) •
          compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) := by
        ext i j
        simp [Matrix.smul_apply]
      rw [hsmul]
      ext i j
      simp [Matrix.smul_apply, SparseAccess.matrix]
      rw [compress_sparseOperator D hD scratchCol scratchRow i j hsr hsc]
      rw [sparseAlphaComplex_eq]
      have hne : (sparseAlpha sr sc : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (sparseAlpha_pos hsr hsc))
      exact sub_eq_zero.mpr (by
        rw [mul_comm]
        exact (div_mul_cancel₀ _ hne).symm)
    rw [hzero, norm_zero]

/-- The norm of the matrix of legal sparse-access data is at most `sqrt sr * sqrt sc` when both
slot counts are positive. -/
theorem sparseBlockEncoding_norm_le (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (scratchCol : ColAddr O sr) (scratchRow : RowAddr I sc) (hsr : 0 < sr) (hsc : 0 < sc) :
    ‖SparseAccess.matrix D‖ ≤ sparseAlpha sr sc := by
  have hM : ‖compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
        (sparseOperator D scratchCol scratchRow)
        (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)‖ ≤ 1 :=
    l2_norm_compress_le_one
      (leftFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
      (sparseOperator_unitary D hD scratchCol scratchRow hsr hsc)
      (rightFrame_isIsometry (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)
  have hA : SparseAccess.matrix D
      = sparseAlphaComplex sr sc •
          compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) := by
    ext i j
    simp [Matrix.smul_apply, SparseAccess.matrix]
    have hne : sparseAlphaComplex sr sc ≠ 0 := sparseAlphaComplex_ne_zero hsr hsc
    calc D.entry i j
        = sparseAlphaComplex sr sc * (D.entry i j / sparseAlphaComplex sr sc) := by
          rw [mul_comm]
          exact (div_mul_cancel₀ _ hne).symm
      _ = sparseAlphaComplex sr sc *
          compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow) i j := by
          rw [compress_sparseOperator D hD scratchCol scratchRow i j hsr hsc]
  rw [hA]
  calc ‖sparseAlphaComplex sr sc •
          compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)‖
      ≤ ‖sparseAlphaComplex sr sc‖ *
          ‖compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)‖ :=
        NormedSpace.norm_smul_le _ _
    _ = sparseAlpha sr sc *
          ‖compress (leftFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchCol)
            (sparseOperator D scratchCol scratchRow)
            (rightFrame (I := I) (O := O) (sr := sr) (sc := sc) scratchRow)‖ := by
        rw [sparseAlphaComplex_eq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_of_lt (sparseAlpha_pos hsr hsc))]
    _ ≤ sparseAlpha sr sc * 1 :=
        mul_le_mul_of_nonneg_left hM
          (le_of_lt (mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hsr)) (Real.sqrt_pos.2 (Nat.cast_pos.2 hsc))))
    _ = sparseAlpha sr sc := by rw [mul_one]

end Qatlib.Concepts.QsvtCore.PhaseExistence
