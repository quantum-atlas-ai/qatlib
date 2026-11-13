/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Laurent polynomials from Gram matrices

The Lean declarations define generalized matrix traces, matrix Laurent evaluation, symmetric
real Laurent evaluation, and Fejer coefficients. They connect positive semidefinite matrices
with circle nonnegativity, express matching on twisted roots through coefficient identities, and
compute outer Gram evaluations. This supplies matrix tools for the ordered search formulation in
[ChildsLandahlParrilo2007], using positivity concepts from [Bhatia1997].

## Main statements

* `matrixLaurent_real_nonneg_of_posSemidef`: positive semidefinite matrices give real
  nonnegative circle evaluations.
* `fejer_eq_abs_dirichlet_sq`: the Fejer Laurent evaluation is a normalized squared modulus of a
  finite power sum.
* `matrixLaurent_root_matching_iff`: matching at twisted roots is equivalent to trace and
  generalized trace identities.
* `matrixLaurent_outer_eq_abs_sq`: an outer Gram matrix evaluates to a polynomial squared
  modulus on the circle.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open scoped BigOperators
open Matrix

variable {n : ℕ}

/-- The sum of matrix entries whose column index minus row index is the integer offset `j`. -/
def genTrace (A : Matrix (Fin n) (Fin n) ℂ) (j : ℤ) : ℂ :=
  ∑ i : Fin n, ∑ i' : Fin n,
    if ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) = j then A i i' else 0

/-- The Laurent evaluation with coefficients given by the generalized traces of `A` over offsets
from `-n + 1` to `n - 1`. -/
noncomputable def matrixLaurent (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1), genTrace A j * z ^ j

/-- The symmetric Laurent evaluation with constant coefficient `c 0` and paired terms `c j * (z
^ j + z ^ (-j))` for positive indices. -/
noncomputable def laurentEval (c : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin n, if (j : ℕ) = 0 then (c j : ℂ)
    else c j * (z ^ ((j : ℕ) : ℤ) + z ^ (-((j : ℕ) : ℤ)))

/-- The real Fejer coefficients given by `(n - j) / n` for `j : Fin n`. -/
noncomputable def fejerCoeffs (n : ℕ) : Fin n → ℝ := fun j => (n - (j : ℕ)) / n

open scoped ComplexOrder

/-- At nonzero `z`, the matrix Laurent evaluation is the double sum of `z ^ (-i) * A i i' * z ^
i'` over matrix indices. -/
theorem matrixLaurent_eq_quadratic (A : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ≠ 0) :
    matrixLaurent A z = ∑ i : Fin n, ∑ i' : Fin n,
      z ^ (-((i : ℕ) : ℤ)) * A i i' * z ^ ((i' : ℕ) : ℤ) := by
  classical
  unfold matrixLaurent genTrace
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro i' _
  have hm : ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) ∈
      Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1) := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, hm, if_true]
  rw [zpow_sub₀ hz]
  simp only [_root_.zpow_neg]
  ring

/-- The Laurent evaluation of a positive semidefinite matrix has zero imaginary part and
nonnegative real part on the unit circle. -/
theorem matrixLaurent_real_nonneg_of_posSemidef (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) {z : ℂ} (hz : ‖z‖ = 1) :
    (matrixLaurent A z).im = 0 ∧ 0 ≤ (matrixLaurent A z).re := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hi : z⁻¹ = star z := Complex.inv_eq_conj hz
  have he : matrixLaurent A z =
      star (fun i : Fin n => z ^ (i : ℕ)) ⬝ᵥ (A *ᵥ (fun i : Fin n => z ^ (i : ℕ))) := by
    rw [matrixLaurent_eq_quadratic A hn]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro i' _
    simp [_root_.zpow_neg, zpow_natCast, ← inv_pow, hi, star_pow, mul_assoc]
  have hp : 0 ≤ matrixLaurent A z := by
    rw [he]
    exact hA.dotProduct_mulVec_nonneg (fun i => z ^ (i : ℕ))
  have h := Complex.nonneg_iff.mp hp
  exact ⟨h.2.symm, h.1⟩

/-- The generalized trace at offset zero equals the ordinary matrix trace. -/
theorem genTrace_zero (A : Matrix (Fin n) (Fin n) ℂ) : genTrace A 0 = A.trace := by
  classical
  simp [genTrace, Int.sub_eq_zero, Fin.val_inj, Matrix.trace]

/-- Transposing a matrix negates the offset in its generalized trace. -/
theorem genTrace_transpose (A : Matrix (Fin n) (Fin n) ℂ) (j : ℤ) :
    genTrace A.transpose j = genTrace A (-j) := by
  classical
  unfold genTrace
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro i' _
  have he : ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) = j ↔
      ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) = -j := by omega
  simp only [Matrix.transpose_apply, he]

/-- For a constant matrix and a natural offset `j`, the generalized trace is `(n - j)` times the
constant entry, with subtraction in the natural numbers. -/
theorem genTrace_const_nat (a : ℂ) (j : ℕ) :
    genTrace (Matrix.of fun _ _ : Fin n => a) (j : ℤ) = (n - j : ℕ) * a := by
  classical
  have hc : ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ) = (j : ℤ))).card = n - j := by
    rw [← Finset.card_range (n - j)]
    refine Finset.card_bij (fun p _ => (p.1 : ℕ)) ?_ ?_ ?_
    · intro p hp
      have hd := (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_range]
      omega
    · intro p hp q hq he
      change (p.1 : ℕ) = (q.1 : ℕ) at he
      have hd := (Finset.mem_filter.mp hp).2
      have hd' := (Finset.mem_filter.mp hq).2
      exact Prod.ext (Fin.ext he) (Fin.ext (by omega))
    · intro b hb
      have hb' : b < n - j := Finset.mem_range.mp hb
      refine ⟨(⟨b, by omega⟩, ⟨b + j, by omega⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
  unfold genTrace
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ, Matrix.of_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]

/-- For a constant matrix, the generalized trace at integer offset `j` is `(n - j.natAbs)` times
the constant entry, with subtraction in the natural numbers. -/
theorem genTrace_const (a : ℂ) (j : ℤ) :
    genTrace (Matrix.of fun _ _ : Fin n => a) j = (n - j.natAbs : ℕ) * a := by
  cases j with
  | ofNat j => simpa using (genTrace_const_nat (n := n) a j)
  | negSucc j =>
    have h := genTrace_transpose (Matrix.of fun _ _ : Fin n => a) ((j + 1 : ℕ) : ℤ)
    have ht : (Matrix.of fun _ _ : Fin n => a).transpose = Matrix.of (fun _ _ : Fin n => a) := rfl
    rw [ht] at h
    rw [genTrace_const_nat] at h
    change genTrace (Matrix.of fun _ _ : Fin n => a) (Int.negSucc j) =
      (n - (j + 1) : ℕ) * a
    have he : Int.negSucc j = -((j + 1 : ℕ) : ℤ) := by omega
    rw [he]
    exact h.symm

/-- The generalized trace of the all ones matrix divided by `n` is `(n - |j|) / n` when `|j| <
n`, and zero otherwise. -/
theorem genTrace_onesDiv (j : ℤ) :
    genTrace ((n : ℂ)⁻¹ • Matrix.of fun _ _ : Fin n => (1 : ℂ)) j =
      ((if |j| < (n : ℤ) then ((n : ℝ) - (|j| : ℤ)) / n else 0 : ℝ) : ℂ) := by
  have he : (n : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin n => (1 : ℂ)) =
      Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹) := by ext; simp
  rw [he, genTrace_const]
  have hj : ((j.natAbs : ℕ) : ℤ) = |j| := Int.natCast_natAbs j
  by_cases h : |j| < (n : ℤ)
  · have hle : j.natAbs ≤ n := by omega
    rw [if_pos h]
    have hr : (j.natAbs : ℝ) = |(j : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun x : ℤ => (x : ℝ)) hj
    push_cast [Nat.cast_sub hle]
    rw [← hr]
    push_cast
    simp only [div_eq_mul_inv]
  · have hle : n ≤ j.natAbs := by omega
    simp [if_neg h, Nat.sub_eq_zero_of_le hle]

/-- A sum over integer offsets from `-n + 1` to `n - 1` equals the sum over `Fin n` that keeps
the zero term once and pairs opposite nonzero offsets. -/
theorem sum_laurent_window (f : ℤ → ℂ) :
    (∑ j ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1), f j) =
      ∑ i : Fin n, if (i : ℕ) = 0 then f 0 else f ((i : ℕ) : ℤ) + f (-((i : ℕ) : ℤ)) := by
  classical
  let sp := (Finset.univ : Finset (Fin n)).image (fun i : Fin n => ((i : ℕ) : ℤ))
  let sn := ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℕ) ≠ 0)).image
    (fun i : Fin n => -((i : ℕ) : ℤ))
  have hs : Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1) = sp ∪ sn := by
    ext j
    simp only [sp, sn, Finset.mem_Icc, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · intro hj
      by_cases h : 0 ≤ j
      · left
        refine ⟨⟨j.toNat, by omega⟩, ?_⟩
        simp [Int.toNat_of_nonneg h]
      · right
        refine ⟨⟨(-j).toNat, by omega⟩, ?_, ?_⟩
        · change (-j).toNat ≠ 0
          omega
        · change -(((-j).toNat : ℕ) : ℤ) = j
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ -j)]
          simp
    · rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩) <;> constructor <;> omega
  have hd : Disjoint sp sn := by
    apply Finset.disjoint_left.mpr
    intro j hp hn
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
    obtain ⟨i', hi', he'⟩ := Finset.mem_image.mp hn
    have hne := (Finset.mem_filter.mp hi').2
    omega
  rw [hs, Finset.sum_union hd]
  unfold sp sn
  rw [Finset.sum_image, Finset.sum_image, Finset.sum_filter, ← Finset.sum_add_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · intro i _ i' _ he
    dsimp at he
    exact Fin.ext (by omega)
  · intro i _ i' _ he
    dsimp at he
    exact Fin.ext (by omega)

/-- The Laurent evaluation of the all ones matrix divided by `n` equals the symmetric Laurent
evaluation of the Fejer coefficients. -/
theorem matrixLaurent_onesDiv (z : ℂ) :
    matrixLaurent ((n : ℂ)⁻¹ • Matrix.of fun _ _ : Fin n => (1 : ℂ)) z =
      laurentEval (fejerCoeffs n) z := by
  classical
  rw [matrixLaurent, sum_laurent_window]
  unfold laurentEval
  apply Finset.sum_congr rfl
  intro i _
  have hlt : |((i : ℕ) : ℤ)| < (n : ℤ) := by
    simp only [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast i.isLt
  simp only [genTrace_onesDiv]
  by_cases hi : (i : ℕ) = 0
  · have hn : 0 < n := by omega
    simp [hi, fejerCoeffs, hn]
  · simp [hi, abs_neg, fejerCoeffs, mul_add,
      abs_of_nonneg (Int.natCast_nonneg (i : ℕ))]

/-- On the unit circle, the Fejer Laurent evaluation equals the squared norm of the finite sum
of powers of `z`, divided by `n`. -/
theorem fejer_eq_abs_dirichlet_sq {z : ℂ} (hz : ‖z‖ = 1) :
    laurentEval (fejerCoeffs n) z = ((‖∑ j : Fin n, z ^ (j : ℕ)‖ ^ 2 / n : ℝ) : ℂ) := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hi : z⁻¹ = star z := Complex.inv_eq_conj hz
  rw [← matrixLaurent_onesDiv, matrixLaurent_eq_quadratic _ hn]
  have he : (∑ i : Fin n, ∑ i' : Fin n,
      z ^ (-((i : ℕ) : ℤ)) *
        ((n : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin n => (1 : ℂ))) i i' * z ^ ((i' : ℕ) : ℤ)) =
      (n : ℂ)⁻¹ * (star (∑ i : Fin n, z ^ (i : ℕ)) * (∑ i : Fin n, z ^ (i : ℕ))) := by
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro i' _
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one,
      _root_.zpow_neg, zpow_natCast, ← inv_pow, hi, star_pow]
    ring
  rw [he]
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/-- The index reflection that fixes zero and sends each positive index `i` to `n - i`. -/
def mirrorIndex (i : Fin n) : Fin n :=
  if hi : (i : ℕ) = 0 then i else ⟨n - (i : ℕ), by omega⟩

/-- Applying `mirrorIndex` twice returns the original index. -/
theorem mirrorIndex_involutive : Function.Involutive (mirrorIndex (n := n)) := by
  intro i
  by_cases hi : (i : ℕ) = 0
  · simp [mirrorIndex, hi]
  · have hm : n - (i : ℕ) ≠ 0 := by omega
    simp only [mirrorIndex, hi]
    apply Fin.ext
    simp [hm, Nat.sub_sub_self (Nat.le_of_lt i.isLt)]

/-- Reindexing a finite complex sum by `mirrorIndex` preserves the sum. -/
theorem sum_mirrorIndex (f : Fin n → ℂ) :
    (∑ i : Fin n, f (mirrorIndex i)) = ∑ i : Fin n, f i :=
  Fintype.sum_bijective _ mirrorIndex_involutive.bijective _ _ (fun _ => rfl)

/-- For positive `n` and `z ^ n = (-1) ^ t`, a symmetric Laurent evaluation becomes a sum of
nonnegative powers. Each nonconstant coefficient combines `d i` with `(-1) ^ t` times its
mirrored coefficient. -/
theorem laurentEval_at_root (hn : 0 < n) (t : ℕ) (d : Fin n → ℝ)
    (z : ℂ) (hr : z ^ n = (-1 : ℂ) ^ t) :
    laurentEval d z = ∑ i : Fin n,
      (if (i : ℕ) = 0 then (d i : ℂ)
       else (d i : ℂ) + (-1 : ℂ) ^ t * d (mirrorIndex i)) * z ^ (i : ℕ) := by
  classical
  have hzn : z ≠ 0 := by
    intro he
    have hs : (-1 : ℂ) ^ t ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact hs (by simpa [he, Nat.ne_of_gt hn] using hr.symm)
  let p : Fin n → ℂ := fun i =>
    if (i : ℕ) = 0 then (d i : ℂ) else d i * z ^ (i : ℕ)
  let m : Fin n → ℂ := fun i =>
    if (i : ℕ) = 0 then 0 else d i * z ^ (-((i : ℕ) : ℤ))
  have hs : laurentEval d z = (∑ i, p i) + ∑ i, m i := by
    rw [← Finset.sum_add_distrib]
    unfold laurentEval
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) = 0 <;> simp [p, m, hi, mul_add]
  rw [hs, ← sum_mirrorIndex m, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) = 0
  · simp [p, m, mirrorIndex, hi]
  · have hm : (mirrorIndex i : ℕ) = n - (i : ℕ) := by simp [mirrorIndex, hi]
    have hm0 : (mirrorIndex i : ℕ) ≠ 0 := by rw [hm]; omega
    have he : -((mirrorIndex i : ℕ) : ℤ) = ((i : ℕ) : ℤ) - (n : ℤ) := by
      rw [hm]
      omega
    have hp : z ^ (-((mirrorIndex i : ℕ) : ℤ)) = (-1 : ℂ) ^ t * z ^ (i : ℕ) := by
      rw [he, zpow_sub₀ hzn, zpow_natCast, zpow_natCast, hr]
      simp only [div_eq_mul_inv]
      rw [show ((-1 : ℂ) ^ t)⁻¹ = (-1 : ℂ) ^ t from by
        rw [← inv_pow]; norm_num]
      ring
    simp only [p, m, hi, hm0, if_false, hp]
    ring

/-- For positive `n`, if a polynomial with coefficients indexed by `Fin n` vanishes at every
root of `z ^ n = (-1) ^ t`, then every coefficient is zero. -/
theorem coeff_zero_of_twisted_root_evaluations (hn : 0 < n) (t : ℕ) (c : Fin n → ℂ)
    (hc : ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t → ∑ i : Fin n, c i * z ^ (i : ℕ) = 0) :
    ∀ i : Fin n, c i = 0 := by
  classical
  let p : Polynomial ℂ := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (c i)
  let r : Polynomial ℂ := Polynomial.X ^ n - Polynomial.C ((-1 : ℂ) ^ t)
  have hrn : r ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn _
  have hs : r.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots (Polynomial.separable_X_pow_sub_C _
        (by exact_mod_cast hn.ne') (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))))]
    rw [← (IsAlgClosed.splits r).natDegree_eq_card_roots]
    exact Polynomial.natDegree_X_pow_sub_C
  have hpdeg : p.natDegree ≤ n - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le (c i)).trans (by omega)
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p r.roots.toFinset
    · intro z hz
      have he : z ^ n = (-1 : ℂ) ^ t := by
        have he := (Polynomial.mem_roots hrn).mp (Multiset.mem_toFinset.mp hz)
        simpa [r, Polynomial.IsRoot, sub_eq_zero] using he
      simpa [p, Polynomial.eval_finsetSum] using hc z he
    · rw [hs]
      omega
  intro i
  have he := congrArg (fun q : Polynomial ℂ => q.coeff (i : ℕ)) hp0
  simpa [p, Polynomial.coeff_sum, Polynomial.coeff_monomial, Fin.val_inj] using he

/-- For positive `n`, a symmetric Laurent evaluation vanishes at all roots of `z ^ n = (-1) ^ t`
exactly when its constant coefficient is zero and mirrored positive coefficients are
negatives for even `t` and equal for odd `t`. -/
theorem symLaurent_root_vanishing_iff (hn : 0 < n) (t : ℕ) (d : Fin n → ℝ) :
    (∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t → laurentEval d z = 0) ↔
      (d ⟨0, hn⟩ = 0 ∧ ∀ j : ℕ, (hj : 0 < j) → (hjn : j < n) →
        d ⟨j, by omega⟩ = (if 2 ∣ t then (-1 : ℝ) else 1) * d ⟨n - j, by omega⟩) := by
  classical
  have hs : (-1 : ℂ) ^ t = if 2 ∣ t then 1 else -1 := by
    simp only [neg_one_pow_eq_ite, even_iff_two_dvd]
  constructor
  · intro h
    have hc : ∀ i : Fin n,
        (if (i : ℕ) = 0 then (d i : ℂ)
         else (d i : ℂ) + (-1 : ℂ) ^ t * d (mirrorIndex i)) = 0 := by
      apply coeff_zero_of_twisted_root_evaluations hn t
      intro z hz
      rw [← laurentEval_at_root hn t d z hz]
      exact h z hz
    constructor
    · simpa using hc ⟨0, hn⟩
    · intro j hj hjn
      have hR := congrArg Complex.re (hc ⟨j, hjn⟩)
      have hj0 : j ≠ 0 := by omega
      by_cases ht : 2 ∣ t
      · simp [hs, ht, mirrorIndex, hj0] at hR
        simp only [if_pos ht]
        linarith
      · simp [hs, ht, mirrorIndex, hj0] at hR
        simp only [if_neg ht]
        linarith
  · rintro ⟨h0, h⟩ z hz
    have hc : ∀ i : Fin n,
        (if (i : ℕ) = 0 then (d i : ℂ)
         else (d i : ℂ) + (-1 : ℂ) ^ t * d (mirrorIndex i)) = 0 := by
      intro i
      by_cases hi : (i : ℕ) = 0
      · have he : i = ⟨0, hn⟩ := Fin.ext hi
        simp [he, h0]
      · have hR := h (i : ℕ) (by omega) i.isLt
        by_cases ht : 2 ∣ t
        · simp only [if_pos ht] at hR
          apply Complex.ext <;> simp [hi, hs, ht, mirrorIndex]
          linarith
        · simp only [if_neg ht] at hR
          apply Complex.ext <;> simp [hi, hs, ht, mirrorIndex]
          linarith
    rw [laurentEval_at_root hn t d z hz]
    simp_rw [hc, zero_mul]
    simp

/-- For positive `n` and `z ^ n = (-1) ^ t`, a Laurent window sum can be rewritten using
nonnegative powers. The coefficient at a positive index `i` becomes `g i + (-1) ^ t * g (i -
n)`. -/
theorem sum_laurent_window_at_root (hn : 0 < n) (t : ℕ) (g : ℤ → ℂ)
    (z : ℂ) (hr : z ^ n = (-1 : ℂ) ^ t) :
    (∑ j ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1), g j * z ^ j) =
      ∑ i : Fin n, (if (i : ℕ) = 0 then g 0
        else g ((i : ℕ) : ℤ) + (-1 : ℂ) ^ t * g (((i : ℕ) : ℤ) - n)) * z ^ (i : ℕ) := by
  classical
  have hzn : z ≠ 0 := by
    intro he
    have hs : (-1 : ℂ) ^ t ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact hs (by simpa [he, Nat.ne_of_gt hn] using hr.symm)
  let p : Fin n → ℂ := fun i => if (i : ℕ) = 0 then g 0 else g ((i : ℕ) : ℤ) * z ^ (i : ℕ)
  let m : Fin n → ℂ := fun i => if (i : ℕ) = 0 then 0 else g (-((i : ℕ) : ℤ)) * z ^ (-((i : ℕ) : ℤ))
  rw [sum_laurent_window]
  have hs : (∑ i : Fin n, if (i : ℕ) = 0 then g 0 * z ^ (0 : ℤ)
      else g ((i : ℕ) : ℤ) * z ^ ((i : ℕ) : ℤ) + g (-((i : ℕ) : ℤ)) * z ^ (-((i : ℕ) : ℤ))) =
      (∑ i, p i) + ∑ i, m i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) = 0 <;> simp [p, m, hi]
  rw [hs, ← sum_mirrorIndex m, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) = 0
  · simp [p, m, mirrorIndex, hi]
  · have hm : (mirrorIndex i : ℕ) = n - (i : ℕ) := by simp [mirrorIndex, hi]
    have hm0 : (mirrorIndex i : ℕ) ≠ 0 := by rw [hm]; omega
    have he : -((mirrorIndex i : ℕ) : ℤ) = ((i : ℕ) : ℤ) - (n : ℤ) := by rw [hm]; omega
    have hp : z ^ (((i : ℕ) : ℤ) - (n : ℤ)) = (-1 : ℂ) ^ t * z ^ (i : ℕ) := by
      rw [zpow_sub₀ hzn, zpow_natCast, zpow_natCast, hr]
      simp only [div_eq_mul_inv]
      rw [show ((-1 : ℂ) ^ t)⁻¹ = (-1 : ℂ) ^ t from by rw [← inv_pow]; norm_num]
      ring
    simp only [p, m, hi, hm0, if_false, he, hp]
    ring

/-- For positive `n`, two matrix Laurent evaluations agree at every root of `z ^ n = (-1) ^ t`
exactly when their traces and the corresponding twisted pairs of generalized traces agree. -/
theorem matrixLaurent_root_matching_iff (hn : 0 < n) (t : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t → matrixLaurent A z = matrixLaurent B z) ↔
      (A.trace = B.trace ∧ ∀ j : ℕ, 0 < j → j < n →
        genTrace A (j : ℤ) + (-1 : ℂ) ^ t * genTrace A ((j : ℤ) - n) =
        genTrace B (j : ℤ) + (-1 : ℂ) ^ t * genTrace B ((j : ℤ) - n)) := by
  classical
  let c : Fin n → ℂ := fun i =>
    if (i : ℕ) = 0 then genTrace A 0 - genTrace B 0 else
      (genTrace A ((i : ℕ) : ℤ) + (-1 : ℂ) ^ t * genTrace A (((i : ℕ) : ℤ) - n)) -
      (genTrace B ((i : ℕ) : ℤ) + (-1 : ℂ) ^ t * genTrace B (((i : ℕ) : ℤ) - n))
  have he (z : ℂ) (hz : z ^ n = (-1 : ℂ) ^ t) :
      matrixLaurent A z - matrixLaurent B z = ∑ i : Fin n, c i * z ^ (i : ℕ) := by
    unfold matrixLaurent
    rw [sum_laurent_window_at_root hn t _ z hz, sum_laurent_window_at_root hn t _ z hz,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) = 0 <;> simp [c, hi, sub_mul]
  constructor
  · intro h
    have hc : ∀ i, c i = 0 := coeff_zero_of_twisted_root_evaluations hn t c (by
      intro z hz
      rw [← he z hz, h z hz, sub_self])
    constructor
    · have h0 := hc ⟨0, hn⟩
      simpa [c, genTrace_zero, sub_eq_zero] using h0
    · intro j hj hjn
      have hj0 : j ≠ 0 := by omega
      simpa [c, hj0, sub_eq_zero] using hc ⟨j, hjn⟩
  · rintro ⟨h0, h⟩ z hz
    have hc : ∀ i, c i = 0 := by
      intro i
      by_cases hi : (i : ℕ) = 0
      · simp [c, hi, genTrace_zero, h0]
      · simpa [c, hi, sub_eq_zero] using h (i : ℕ) (by omega) i.isLt
    apply sub_eq_zero.mp
    rw [he z hz]
    simp [hc]

/-- The outer Gram matrix with entry `star (v i) * v i'`. -/
def gramOuter (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i i' => star (v i) * v i'

/-- Every outer Gram matrix is positive semidefinite. -/
theorem gramOuter_posSemidef (v : Fin n → ℂ) : (gramOuter v).PosSemidef := by
  let C : Matrix Unit (Fin n) ℂ := fun _ i => v i
  have he : C.conjTranspose * C = gramOuter v := by
    ext i i'
    simp +zetaDelta [C, gramOuter, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self C

/-- The trace of an outer Gram matrix is the sum of the squared norms of its vector entries,
embedded in the complex numbers. -/
theorem gramOuter_trace (v : Fin n → ℂ) :
    (gramOuter v).trace = ((∑ i : Fin n, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, gramOuter, Matrix.of_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]

/-- On the unit circle, the Laurent evaluation of `gramOuter v` is the squared norm of the
polynomial sum with coefficient vector `v`. -/
theorem matrixLaurent_outer_eq_abs_sq (v : Fin n → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    matrixLaurent (gramOuter v) z = ((‖∑ i : Fin n, v i * z ^ (i : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hi : z⁻¹ = star z := Complex.inv_eq_conj hz
  rw [matrixLaurent_eq_quadratic _ hn]
  have he : (∑ i : Fin n, ∑ i' : Fin n,
      z ^ (-((i : ℕ) : ℤ)) * gramOuter v i i' * z ^ ((i' : ℕ) : ℤ)) =
      star (∑ i : Fin n, v i * z ^ (i : ℕ)) * (∑ i : Fin n, v i * z ^ (i : ℕ)) := by
    simp only [star_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro i' _
    simp only [gramOuter, Matrix.of_apply, _root_.zpow_neg, zpow_natCast, ← inv_pow,
      hi, star_mul, star_pow]
    ring
  rw [he, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- For positive `n`, every solution of `z ^ n = (-1) ^ t` lies on the unit circle. -/
theorem norm_eq_one_of_twisted_root (hn : 0 < n) (t : ℕ) {z : ℂ}
    (hz : z ^ n = (-1 : ℂ) ^ t) : ‖z‖ = 1 := by
  have hp : z ^ (n * 2) = 1 := by
    rw [pow_mul, hz, ← pow_mul, Nat.mul_comm t 2, pow_mul]
    norm_num
  exact Complex.norm_eq_one_of_pow_eq_one hp (by omega)

/-- For a Hermitian matrix, the generalized trace at the negative offset is the complex
conjugate of the generalized trace at the positive offset. -/
theorem genTrace_neg_of_isHermitian (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (j : ℤ) : genTrace A (-j) = star (genTrace A j) := by
  classical
  unfold genTrace
  rw [Finset.sum_comm]
  simp only [star_sum, apply_ite, star_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro i' _
  have he : ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) = -j ↔
      ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) = j := by omega
  simp only [he]
  split_ifs <;> first | exact (hA.apply i' i).symm | rfl

/-- On the unit circle, the symmetric Laurent evaluation of the real parts of a Hermitian
matrix's nonnegative generalized traces equals the average of its matrix Laurent evaluations
at `z` and its conjugate. -/
theorem laurentEval_real_genTrace (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {z : ℂ} (hz : ‖z‖ = 1) :
    laurentEval (fun i : Fin n => (genTrace A ((i : ℕ) : ℤ)).re) z =
      (matrixLaurent A z + matrixLaurent A (star z)) / 2 := by
  classical
  unfold matrixLaurent
  rw [sum_laurent_window, sum_laurent_window, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold laurentEval
  apply Finset.sum_congr rfl
  intro i _
  have hs : star z = z⁻¹ := (Complex.inv_eq_conj hz).symm
  have h0 : star (genTrace A 0) = genTrace A 0 := by
    simpa using (genTrace_neg_of_isHermitian A hA 0).symm
  by_cases hi : (i : ℕ) = 0
  · simp only [hi, if_true, Nat.cast_zero, zpow_zero, mul_one]
    rw [Complex.re_eq_add_conj, ← Complex.star_def, h0]
  · simp only [hi, if_false, genTrace_neg_of_isHermitian A hA, hs,
      _root_.inv_zpow, _root_.zpow_neg, inv_inv]
    rw [Complex.re_eq_add_conj, ← Complex.star_def]
    ring

/-- For a positive semidefinite matrix, the symmetric Laurent evaluation formed from the real
parts of its nonnegative generalized traces has nonnegative real part on the unit circle. -/
theorem laurentEval_real_genTrace_nonneg (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (laurentEval (fun i : Fin n => (genTrace A ((i : ℕ) : ℤ)).re) z).re := by
  rw [laurentEval_real_genTrace A hA.isHermitian hz]
  have h1 := (matrixLaurent_real_nonneg_of_posSemidef A hA hz).2
  have h2 := (matrixLaurent_real_nonneg_of_posSemidef A hA
    (by simpa using hz : ‖star z‖ = 1)).2
  simp only [Complex.div_ofNat_re, Complex.add_re]
  linarith

/-- A zero diagonal entry of a positive semidefinite matrix forces every entry in the
corresponding column to be zero. -/
theorem posSemidef_column_zero_of_diag_zero (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (j : Fin n) (hj : A j j = 0) : ∀ i, A i j = 0 := by
  classical
  let x : Fin n → ℂ := Pi.single j 1
  have he : star x ⬝ᵥ (A *ᵥ x) = A j j := by
    simp [x, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, ite_mul]
  have hx : A *ᵥ x = 0 := hA.dotProduct_mulVec_zero_iff.mp (by rw [he, hj])
  intro i
  have hh := congrFun hx i
  simpa [x, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using hh

/-- A diagonal matrix has generalized trace equal to the sum of its diagonal entries at offset
zero, and zero at every other offset. -/
theorem genTrace_diagonal (a : Fin n → ℂ) (j : ℤ) :
    genTrace (Matrix.diagonal a) j = if j = 0 then ∑ i : Fin n, a i else 0 := by
  classical
  by_cases hj : j = 0
  · subst j
    simp [genTrace_zero, Matrix.trace, Matrix.diag_apply]
  · rw [if_neg hj]
    unfold genTrace
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro i' _
    by_cases hi : i = i'
    · subst i'
      simp [hj, eq_comm]
    · simp [hi]

/-- A nonzero positive semidefinite diagonal matrix of positive size has a positive semidefinite
rank one representative with the same generalized traces and a first diagonal entry at least
as large. -/
theorem exists_rank_one_gram_of_diagonal [NeZero n] (a : Fin n → ℂ)
    (hA : (Matrix.diagonal a).PosSemidef) (hA0 : Matrix.diagonal a ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, B.PosSemidef ∧ B.rank = 1 ∧
      (∀ j : ℤ, genTrace B j = genTrace (Matrix.diagonal a) j) ∧ a 0 ≤ B 0 0 := by
  classical
  have ha : ∀ i, 0 ≤ a i := Matrix.posSemidef_diagonal_iff.mp hA
  have hane : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    apply hA0
    ext i j
    simp [Matrix.diagonal, h]
  let T : ℂ := ∑ i : Fin n, a i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => ha i)
  have hT0 : T ≠ 0 := by
    intro hz
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hz
    obtain ⟨i, hi⟩ := hane
    exact hi (hh i (Finset.mem_univ i))
  let b : Fin n → ℂ := fun i => if i = 0 then T else 0
  refine ⟨Matrix.diagonal b, ?_, ?_, ?_, ?_⟩
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simp only [b]
    split_ifs
    · exact hT
    · exact le_rfl
  · rw [Matrix.rank_diagonal]
    simp [b, hT0]
  · intro j
    rw [genTrace_diagonal, genTrace_diagonal]
    simp [b, T]
  · change a 0 ≤ b 0
    simp only [b, if_pos rfl]
    exact Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ 0)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
