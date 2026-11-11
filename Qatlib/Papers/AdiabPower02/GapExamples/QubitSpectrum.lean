/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# One-qubit eigenvalues and tensor energy gaps

Defines the real matrix `qubitH`, explicit eigenvectors `v0` and `v1`, and eigenvalues `lam0`
and `lam1` separated by `gapFun`. The gap is bounded below by `sqrt (1 / 2)`, and the normalized
second component of the lower eigenvector satisfies an amplitude bound on the interpolation
interval.

The scalar tensor energy `tensorEigen` is expressed through Hamming weight. For a nonempty
register, the lowest and first excited energy levels are attained explicitly and their
difference is `gapFun`. See [VanDamMoscaVazirani2001].

## Main statements

* `qubitH_mulVec_v0`: The explicit lower vector satisfies the eigenvector equation.
* `amp_pow_le`: Tensor powers of the lower-state amplitude obey a uniform bound.
* `tensor_gap`: Identifies the two lowest scalar tensor energy levels and their gap.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix

namespace Qatlib.Papers.AdiabPower02.GapExamples

/-- The positive square root of `2 * s ^ 2 - 2 * s + 1`. -/
def gapFun (s : ℝ) : ℝ := Real.sqrt (2 * s ^ 2 - 2 * s + 1)

/-- The lower eigenvalue `(1 - gapFun s) / 2` of the one-qubit matrix. -/
def lam0 (s : ℝ) : ℝ := (1 - gapFun s) / 2

/-- The upper eigenvalue `(1 + gapFun s) / 2` of the one-qubit matrix. -/
def lam1 (s : ℝ) : ℝ := (1 + gapFun s) / 2

/-- The real two-by-two matrix with rows `![(1 - s) / 2, (s - 1) / 2]` and `![(s - 1) / 2, (1 +
s) / 2]`. -/
def qubitH (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - s) / 2, (s - 1) / 2; (s - 1) / 2, (1 + s) / 2]

/-- The explicit lower eigenvector `![gapFun s + s, 1 - s]`. -/
def v0 (s : ℝ) : Fin 2 → ℝ := ![gapFun s + s, 1 - s]

/-- The explicit upper eigenvector `![1 - s, -(gapFun s + s)]`. -/
def v1 (s : ℝ) : Fin 2 → ℝ := ![1 - s, -(gapFun s + s)]

/-- The square of the gap function is `2 * s ^ 2 - 2 * s + 1`. -/
lemma gapFun_sq (s : ℝ) : gapFun s ^ 2 = 2 * s ^ 2 - 2 * s + 1 :=
  Real.sq_sqrt (by nlinarith [sq_nonneg (s - 1 / 2)])

/-- The gap function is nonnegative for every real parameter. -/
lemma gapFun_nonneg (s : ℝ) : 0 ≤ gapFun s := Real.sqrt_nonneg _

/-- The quadratic defining the gap equals `2 * (s - 1 / 2) ^ 2 + 1 / 2`. -/
lemma gap_quad (s : ℝ) : 2 * s ^ 2 - 2 * s + 1 = 2 * (s - 1 / 2) ^ 2 + 1 / 2 := by
  ring

/-- The upper eigenvalue minus the lower eigenvalue equals the gap function. -/
lemma lam1_sub_lam0 (s : ℝ) : lam1 s - lam0 s = gapFun s := by
  simp [lam1, lam0]; ring

/-- The vector `v0 s` satisfies the eigenvector equation for `qubitH s` with eigenvalue `lam0
s`. -/
theorem qubitH_mulVec_v0 (s : ℝ) :
    qubitH s *ᵥ v0 s = lam0 s • v0 s := by
  have hg : gapFun s ^ 2 = 2 * s ^ 2 - 2 * s + 1 := gapFun_sq s
  funext i
  fin_cases i <;>
    simp [qubitH, v0, lam0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hg]

/-- The vector `v1 s` satisfies the eigenvector equation for `qubitH s` with eigenvalue `lam1
s`. -/
theorem qubitH_mulVec_v1 (s : ℝ) :
    qubitH s *ᵥ v1 s = lam1 s • v1 s := by
  have hg : gapFun s ^ 2 = 2 * s ^ 2 - 2 * s + 1 := gapFun_sq s
  funext i
  fin_cases i <;>
    simp [qubitH, v1, lam1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hg]

/-- The sum `gapFun s + s` is strictly positive for every real `s`. -/
lemma gap_plus_s_pos (s : ℝ) : 0 < gapFun s + s := by
  have hg : 0 ≤ gapFun s := gapFun_nonneg s
  rcases le_total 0 s with hs | hs
  · have hsq : s ^ 2 ≤ gapFun s ^ 2 := by
      rw [gapFun_sq]; nlinarith [sq_nonneg (1 - s)]
    have hgs : s ≤ gapFun s := by
      have h := (sq_le_sq.mp hsq)
      rw [abs_of_nonneg hg, abs_of_nonneg hs] at h
      exact h
    rcases eq_or_lt_of_le hs with h0 | h0
    · rw [← h0]; simp [gapFun]
    · linarith
  · have hsq : s ^ 2 < gapFun s ^ 2 := by
      rw [gapFun_sq]; nlinarith [sq_nonneg (1 - s), hs]
    have hlt : |s| < gapFun s := by
      have h := sq_lt_sq.mp hsq
      rwa [abs_of_nonneg hg] at h
    linarith [neg_abs_le s, hlt]

/-- The two explicit eigenvectors form a linearly independent pair. -/
theorem v0_v1_linearIndependent (s : ℝ) :
    LinearIndependent ℝ ![v0 s, v1 s] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g 0 * (gapFun s + s) + g 1 * (1 - s) = 0 := by
    have := congrFun hg 0
    simpa [v0, v1, Fin.sum_univ_two] using this
  have h1 : g 0 * (1 - s) + g 1 * (-(gapFun s + s)) = 0 := by
    have := congrFun hg 1
    simpa [v0, v1, Fin.sum_univ_two] using this
  set u : ℝ := gapFun s + s with hu_def
  set v : ℝ := 1 - s with hv_def
  have hu : 0 < u := by rw [hu_def]; exact gap_plus_s_pos s
  have h0' : g 0 * u + g 1 * v = 0 := h0
  have h1' : g 0 * v - g 1 * u = 0 := by linarith [h1]
  have hdet : g 0 * (u ^ 2 + v ^ 2) = 0 := by
    have h : (g 0 * u + g 1 * v) * u + (g 0 * v - g 1 * u) * v
        = g 0 * (u ^ 2 + v ^ 2) := by ring
    rw [h0', h1'] at h
    simpa using h.symm
  have hd : u ^ 2 + v ^ 2 ≠ 0 := by nlinarith [hu]
  have hg0 : g 0 = 0 := by
    rcases mul_eq_zero.mp hdet with h | h
    · exact h
    · exact absurd h hd
  have hg1 : g 1 = 0 := by
    rw [hg0] at h1'
    simp only [zero_mul, zero_sub, neg_eq_zero] at h1'
    rcases mul_eq_zero.mp h1' with h | h
    · exact h
    · exact absurd h (ne_of_gt hu)
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

/-- The gap function is strictly positive for every real parameter. -/
lemma gapFun_pos (s : ℝ) : 0 < gapFun s := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (s - 1 / 2)]

/-- The gap function is bounded below by `sqrt (1 / 2)`. -/
theorem gapFun_min (s : ℝ) : Real.sqrt (1 / 2) ≤ gapFun s := by
  rw [gapFun]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (s - 1 / 2)]

/-- The square of `sqrt (1 / 2)` is `1 / 2`. -/
lemma sqrt_half_sq : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
  rw [Real.sq_sqrt (by norm_num)]

/-- The squared Euclidean norm of the explicit lower eigenvector. -/
def v0NormSq (s : ℝ) : ℝ := (gapFun s + s) ^ 2 + (1 - s) ^ 2

/-- The second component `1 - s` of the lower eigenvector divided by the square root of
`v0NormSq s`. -/
def amp1 (s : ℝ) : ℝ := (1 - s) / Real.sqrt (v0NormSq s)

/-- The squared norm of the lower eigenvector is strictly positive. -/
lemma v0NormSq_pos (s : ℝ) : 0 < v0NormSq s := by
  have hgs : 0 < gapFun s + s := gap_plus_s_pos s
  have h : 0 < (gapFun s + s) ^ 2 := pow_pos hgs 2
  have h2 : (0 : ℝ) ≤ (1 - s) ^ 2 := sq_nonneg _
  simp only [v0NormSq]; linarith

/-- For `0 ≤ s ≤ 1`, the square of the normalized second component is at most `1 / 2`. -/
theorem amp1_sq_le_half {s : ℝ} (hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    amp1 s ^ 2 ≤ 1 / 2 := by
  have hden : 0 < v0NormSq s := v0NormSq_pos s
  have hkey : (1 - s) ^ 2 ≤ (gapFun s + s) ^ 2 := by
    have hgs : 0 ≤ gapFun s + s := le_of_lt (gap_plus_s_pos s)
    have hg := gapFun_sq s
    nlinarith [mul_nonneg hs0 hgs, hg]
  have hnorm : Real.sqrt (v0NormSq s) ^ 2 = v0NormSq s :=
    Real.sq_sqrt (le_of_lt hden)
  rw [amp1, div_pow, hnorm, v0NormSq]
  rw [div_le_iff₀ (by have h := hden; simp only [v0NormSq] at h; linarith)]
  nlinarith [hkey]

/-- The normalized second component is nonnegative when `s ≤ 1`. -/
lemma amp1_nonneg {s : ℝ} (hs1 : s ≤ 1) : 0 ≤ amp1 s := by
  have hden : 0 < Real.sqrt (v0NormSq s) :=
    Real.sqrt_pos.mpr (v0NormSq_pos s)
  exact div_nonneg (by linarith) (le_of_lt hden)

/-- For `0 ≤ s ≤ 1`, the `n`th power of the normalized second component is at most `(sqrt (1 /
2)) ^ n`. -/
theorem amp_pow_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    amp1 s ^ n ≤ (Real.sqrt (1 / 2)) ^ n := by
  have hβ0 : 0 ≤ amp1 s := amp1_nonneg hs1
  have hβ : amp1 s ≤ Real.sqrt (1 / 2) := by
    have hsq : amp1 s ^ 2 ≤ (Real.sqrt (1 / 2)) ^ 2 := by
      rw [sqrt_half_sq]; exact amp1_sq_le_half hs0 hs1
    nlinarith [hsq, hβ0, Real.sqrt_nonneg (1 / 2 : ℝ)]
  exact pow_le_pow_left₀ hβ0 hβ n

/-- The sum of the scalar energies `b` at true bits and `a` at false bits. -/
def tensorEigen (a b : ℝ) {n : ℕ} (y : Fin n → Bool) : ℝ :=
  ∑ i, if y i = true then b else a

/-- The all-false string has tensor energy `n * a`. -/
lemma tensorEigen_zero (a b : ℝ) (n : ℕ) :
    tensorEigen (n := n) a b (fun _ => false) = (n : ℝ) * a := by
  simp [tensorEigen]

/-- If `a ≤ b`, every tensor energy is at least `n * a`. -/
lemma tensorEigen_ge (a b : ℝ) (hab : a ≤ b) {n : ℕ} (y : Fin n → Bool) :
    (n : ℝ) * a ≤ tensorEigen a b y := by
  have h : ∀ i, a ≤ (if y i = true then b else a) := by
    intro i
    by_cases hi : y i = true
    · simp only [hi, if_true]; exact hab
    · simp [hi]
  calc (n : ℝ) * a = ∑ _i : Fin n, a := by simp
    _ ≤ ∑ i, (if y i = true then b else a) := Finset.sum_le_sum fun i _ => h i
    _ = tensorEigen a b y := rfl

/-- The number of true coordinates of a Boolean string. -/
def boolWeight {n : ℕ} (y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => y i = true)).card

/-- The tensor energy of a string of weight `k` is `(n - k) * a + k * b`. -/
lemma tensorEigen_eq_weight (a b : ℝ) {n : ℕ} (y : Fin n → Bool) :
    tensorEigen a b y = ((n : ℝ) - (boolWeight y : ℝ)) * a + (boolWeight y : ℝ) * b := by
  have h1 : tensorEigen a b y
      = ∑ i : Fin n, (a + (if y i = true then (b - a) else 0)) := by
    rw [tensorEigen]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : y i = true <;> simp [hi]
  have h2 : (∑ i : Fin n, (if y i = true then (b - a) else 0))
      = (boolWeight y : ℝ) * (b - a) := by
    rw [boolWeight,
      ← Finset.sum_filter (s := Finset.univ) (p := fun i => y i = true)
        (f := fun _ => b - a),
      Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.sum_add_distrib, h2, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- If `a ≤ b`, any string other than the all-false string has tensor energy at least `(n - 1) *
a + b`. -/
lemma tensorEigen_ge_of_ne_zero (a b : ℝ) (hab : a ≤ b) {n : ℕ}
    {y : Fin n → Bool} (hy : y ≠ fun _ => false) :
    ((n : ℝ) - 1) * a + b ≤ tensorEigen a b y := by
  rw [tensorEigen_eq_weight]
  have hex : ∃ i, y i = true := by
    by_contra h
    simp only [not_exists] at h
    apply hy
    funext i
    have hne : y i ≠ true := by simpa using h i
    cases hv : y i
    · rfl
    · exact absurd hv hne
  have hw : 0 < boolWeight y := by
    rw [boolWeight]
    exact Finset.card_pos.mpr (by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp [hi]⟩)
  have hw1 : (1 : ℝ) ≤ (boolWeight y : ℝ) := by exact_mod_cast hw
  have hcard : (Finset.univ.filter (fun i : Fin n => y i = true)).card ≤ n := by
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  have hwn : (boolWeight y : ℝ) ≤ (n : ℝ) := by
    rw [boolWeight]; exact_mod_cast hcard
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (boolWeight y : ℝ) - 1)
    (by linarith : (0:ℝ) ≤ b - a)]

/-- For positive `n`, the string whose only true bit is at index zero has tensor energy `(n - 1)
* a + b`. -/
lemma tensorEigen_weight_one (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    tensorEigen a b (fun i : Fin n => decide (i = ⟨0, hn⟩)) = ((n : ℝ) - 1) * a + b := by
  rw [tensorEigen_eq_weight]
  have hw : boolWeight (fun i : Fin n => decide (i = ⟨0, hn⟩)) = 1 := by
    rw [boolWeight]
    have h : (Finset.univ.filter
        (fun i : Fin n => decide (i = ⟨0, hn⟩) = true)) = {⟨0, hn⟩} := by
      ext i
      simp
    rw [h, Finset.card_singleton]
  rw [hw]
  push_cast
  ring

/-- The gap function is at least the real parameter `s`. -/
lemma le_gapFun (s : ℝ) : s ≤ gapFun s := by
  rcases le_total 0 s with hs | hs
  · have hsq : s ^ 2 ≤ gapFun s ^ 2 := by
      rw [gapFun_sq]; nlinarith [sq_nonneg (1 - s)]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (gapFun_nonneg s), abs_of_nonneg hs] at h
  · linarith [gapFun_nonneg s]

/-- For positive `n`, the all-false string attains the lowest scalar tensor energy, a weight-one
string attains the first excited level, and these levels differ by `gapFun s`
[VanDamMoscaVazirani2001]. -/
theorem tensor_gap (s : ℝ) {n : ℕ} (hn : 0 < n) :
    (∀ y : Fin n → Bool, (n : ℝ) * lam0 s ≤ tensorEigen (lam0 s) (lam1 s) y) ∧
    tensorEigen (n := n) (lam0 s) (lam1 s) (fun _ => false) = (n : ℝ) * lam0 s ∧
    (∀ y : Fin n → Bool, y ≠ (fun _ => false) →
      ((n : ℝ) - 1) * lam0 s + lam1 s ≤ tensorEigen (lam0 s) (lam1 s) y) ∧
    tensorEigen (lam0 s) (lam1 s) (fun i : Fin n => decide (i = ⟨0, hn⟩))
      = ((n : ℝ) - 1) * lam0 s + lam1 s ∧
    (((n : ℝ) - 1) * lam0 s + lam1 s) - ((n : ℝ) * lam0 s) = gapFun s := by
  have hle : lam0 s ≤ lam1 s := by
    simp only [lam0, lam1]
    linarith [gapFun_nonneg s]
  refine ⟨fun y => tensorEigen_ge _ _ hle y, tensorEigen_zero _ _ n,
    fun y hy => tensorEigen_ge_of_ne_zero _ _ hle hy,
    tensorEigen_weight_one _ _ hn, ?_⟩
  have h := lam1_sub_lam0 s
  nlinarith

end Qatlib.Papers.AdiabPower02.GapExamples
