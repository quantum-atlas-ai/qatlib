/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma3.MQSPInversion
import Qatlib.Papers.QSPIto26.MainResults.Lemma4.MQSPDegreeEquality
import Qatlib.Papers.QSPIto26.MainResults.Lemma7.MQSPDegreeStep
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

set_option backward.isDefEq.respectTransparency false

/-!
# Non-Constructibility of the Two-Variable M-QSP Counterexample Pair

This module formalizes Section 4 (Eqs. (16)--(17)) of Ito, Mori, Sakamoto, and
Fujii showing that the concrete bivariate Laurent polynomial pair `(P22, Q22)`
has total degree `4`, is rejected by the constructive decision algorithm
`mqspCDA P22 Q22 4 = false`, and cannot be constructed by two-variable M-QSP in
any number of steps `n`.

## Main statements

* `P22`, `Q22`, `degTotal_P22`: explicit bivariate Laurent polynomials of Eqs.
  (16)--(17) and proof that `degTotal P22 = 4`.
* `mqspCDA_P22_Q22_four`: `mqspCDA P22 Q22 4 = false`.
* `ref22_counterexample_no_construction`: `∀ n : ℕ, ¬ Constructible n P22 Q22`.

## References

* [Ito et al., 2026][ItoEtAl2026], Section 4, Eqs. (16)--(17), p. 7.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Counterexample

open Qatlib.Papers.QSPIto26.MainResults.Core

/-- Exponent vector `(k_a, k_b)` for the two-variable Laurent ring. -/
def e2 (ka kb : ℤ) : ExpVec 2 := fun i => if i = (0 : Fin 2) then ka else kb

/-- Bivariate monomial `a^{k_a} b^{k_b}`. -/
def mon2 (ka kb : ℤ) : MLaurent 2 := mono (e2 ka kb)

/-- Common prefactor `(6/25) * √(37/493)` of Eqs. (16)--(17). -/
def pref : ℂ := (6 / 25 : ℂ) * (Real.sqrt (37 / 493 : ℝ) : ℂ)

/-- `P_{2,2}(a, b)` of Eq. (16). -/
def P22 : MLaurent 2 :=
  C' pref *
    (mon2 2 2 + mon2 (-2) (-2)
      - C' ((122 : ℂ) / 37 + ((8 : ℂ) / 37) * Complex.I) * (mon2 0 2 + mon2 0 (-2))
      + C' ((114 : ℂ) / 37 + ((56 : ℂ) / 37) * Complex.I) * (mon2 (-2) 2 + mon2 2 (-2))
      + C' ((362 : ℂ) / 111 - ((248 : ℂ) / 111) * Complex.I) * (mon2 2 0 + mon2 (-2) 0)
      + C' ((692 : ℂ) / 111 - ((719 : ℂ) / 222) * Complex.I))

/-- `Q_{2,2}(a, b)` of Eq. (17). -/
def Q22 : MLaurent 2 :=
  C' pref *
    (mon2 2 2 - mon2 (-2) (-2)
      - C' ((122 : ℂ) / 37 + ((66 : ℂ) / 37) * Complex.I) * (mon2 0 2 - mon2 0 (-2))
      + C' ((56 : ℂ) / 37 + ((114 : ℂ) / 37) * Complex.I) * (mon2 (-2) 2 - mon2 2 (-2))
      + C' ((362 : ℂ) / 111 - ((418 : ℂ) / 111) * Complex.I) * (mon2 2 0 - mon2 (-2) 0))

/-- Multiplication by a constant is scalar multiplication. -/
lemma C'mul_smul {m : ℕ} (c : ℂ) (X : MLaurent m) : C' c * X = c • X := by
  rw [Algebra.smul_def]
  rfl

/-- The exponent encoding `e2` is injective in its two components. -/
lemma e2_inj {ka kb ka' kb' : ℤ} (h : e2 ka kb = e2 ka' kb') : ka = ka' ∧ kb = kb' := by
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h (1 : Fin 2)
  simp [e2] at h0 h1
  exact ⟨h0, h1⟩

/-- The common prefactor of Eqs. (16)--(17) is nonzero. -/
lemma pref_ne_zero : pref ≠ 0 := by
  have h2 : ((Real.sqrt (37 / 493 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by norm_num)
  unfold pref
  exact mul_ne_zero (by norm_num) h2

/-- Evaluation of the constant `C' c` at an exponent. -/
lemma evC (c : ℂ) (k : ExpVec 2) : (C' c).coeff k = if k = (0 : ExpVec 2) then c else 0 := by
  simp [C', AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

/-- Evaluation of a bivariate monomial at an exponent. -/
lemma evM (ka kb : ℤ) (k : ExpVec 2) :
    (mon2 ka kb).coeff k = if k = e2 ka kb then (1 : ℂ) else 0 := by
  simp [mon2, mono, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

/-- Evaluation of a constant multiple. -/
lemma evMulC (c : ℂ) (X : MLaurent 2) (k : ExpVec 2) :
    (C' c * X : MLaurent 2).coeff k = c * X.coeff k := by
  rw [C'mul_smul, AddMonoidAlgebra.coeff_smul_apply]
  simp

/-- Evaluation of a difference. -/
lemma evSub (X Y : MLaurent 2) (k : ExpVec 2) : (X - Y).coeff k = X.coeff k - Y.coeff k := by
  simp [AddMonoidAlgebra.coeff_sub]

/-- Pointwise description of `P22` across its nine-point exponent support. -/
lemma P22_apply (k : ExpVec 2) : P22.coeff k = pref *
    ((if k = e2 2 2 then (1 : ℂ) else 0) + (if k = e2 (-2) (-2) then (1 : ℂ) else 0)
      - ((122 : ℂ) / 37 + ((8 : ℂ) / 37) * Complex.I)
          * ((if k = e2 0 2 then (1 : ℂ) else 0) + (if k = e2 0 (-2) then (1 : ℂ) else 0))
      + ((114 : ℂ) / 37 + ((56 : ℂ) / 37) * Complex.I)
          * ((if k = e2 (-2) 2 then (1 : ℂ) else 0) + (if k = e2 2 (-2) then (1 : ℂ) else 0))
      + ((362 : ℂ) / 111 - ((248 : ℂ) / 111) * Complex.I)
          * ((if k = e2 2 0 then (1 : ℂ) else 0) + (if k = e2 (-2) 0 then (1 : ℂ) else 0))
      + (if k = (0 : ExpVec 2) then ((692 : ℂ) / 111 - ((719 : ℂ) / 222) * Complex.I) else 0)) := by
  simp only [P22, evMulC, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, evSub, evM, evC]

/-- Pointwise description of `Q22` across its eight-point exponent support. -/
private lemma Q22_apply (k : ExpVec 2) : Q22.coeff k = pref *
    ((if k = e2 2 2 then (1 : ℂ) else 0) - (if k = e2 (-2) (-2) then (1 : ℂ) else 0)
      - ((122 : ℂ) / 37 + ((66 : ℂ) / 37) * Complex.I)
          * ((if k = e2 0 2 then (1 : ℂ) else 0) - (if k = e2 0 (-2) then (1 : ℂ) else 0))
      + ((56 : ℂ) / 37 + ((114 : ℂ) / 37) * Complex.I)
          * ((if k = e2 (-2) 2 then (1 : ℂ) else 0) - (if k = e2 2 (-2) then (1 : ℂ) else 0))
      + ((362 : ℂ) / 111 - ((418 : ℂ) / 111) * Complex.I)
          * ((if k = e2 2 0 then (1 : ℂ) else 0) - (if k = e2 (-2) 0 then (1 : ℂ) else 0))) := by
  simp only [Q22, evMulC, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, evSub, evM]

private lemma e2_eq_iff {a b c d : ℤ} : e2 a b = e2 c d ↔ a = c ∧ b = d := by
  exact ⟨e2_inj, fun ⟨h, h'⟩ => by rw [h, h']⟩

private lemma e2_eq_zero {a b : ℤ} : e2 a b = 0 ↔ a = 0 ∧ b = 0 := by
  have hz : e2 0 0 = 0 := by ext i; simp [e2]
  rw [← hz, e2_eq_iff]

private lemma top_coefficients :
    P22.coeff (e2 2 2) = pref ∧ Q22.coeff (e2 2 2) = pref := by
  norm_num [P22_apply, Q22_apply, e2_eq_iff, e2_eq_zero]

private lemma slices_not_proportional (j : Fin 2) :
    ∃ k : ExpVec 2, k j = 2 ∧
      P22.coeff (e2 2 2) * Q22.coeff k ≠ Q22.coeff (e2 2 2) * P22.coeff k := by
  fin_cases j
  · refine ⟨e2 2 0, by simp [e2], ?_⟩
    rw [top_coefficients.1, top_coefficients.2]
    norm_num [P22_apply, Q22_apply, e2_eq_iff, e2_eq_zero]
    intro h
    exact pref_ne_zero h
  · refine ⟨e2 0 2, by simp [e2], ?_⟩
    rw [top_coefficients.1, top_coefficients.2]
    norm_num [P22_apply, Q22_apply, e2_eq_iff, e2_eq_zero]
    intro h
    exact pref_ne_zero h

/-- The total degree of `P_{2,2}` is `4`. -/
theorem degTotal_P22 : degTotal P22 = 4 := by
  have hzero : ∀ k : ExpVec 2, k ≠ e2 2 2 → k ≠ e2 (-2) (-2) → k ≠ e2 0 2 → k ≠ e2 0 (-2)
      → k ≠ e2 (-2) 2 → k ≠ e2 2 (-2) → k ≠ e2 2 0 → k ≠ e2 (-2) 0 → k ≠ (0 : ExpVec 2)
      → P22.coeff k = 0 := by
    intro k h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [P22_apply]
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have hmem : e2 2 2 ∈ P22.coeff.support := by
    have hn1 : e2 2 2 ≠ e2 (-2) (-2) := by decide
    have hn2 : e2 2 2 ≠ e2 0 2 := by decide
    have hn3 : e2 2 2 ≠ e2 0 (-2) := by decide
    have hn4 : e2 2 2 ≠ e2 (-2) 2 := by decide
    have hn5 : e2 2 2 ≠ e2 2 (-2) := by decide
    have hn6 : e2 2 2 ≠ e2 2 0 := by decide
    have hn7 : e2 2 2 ≠ e2 (-2) 0 := by decide
    have hn8 : e2 2 2 ≠ (0 : ExpVec 2) := by decide
    rw [Finsupp.mem_support_iff, P22_apply]
    simp only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8,
      reduceIte, add_zero, mul_zero, sub_zero, mul_one]
    exact pref_ne_zero
  have hub : ∀ k ∈ P22.coeff.support, ∀ j : Fin 2, Int.natAbs (k j) ≤ 2 := by
    intro k hk j
    rw [Finsupp.mem_support_iff] at hk
    by_cases h1 : k = e2 2 2
    · subst h1; fin_cases j <;> simp [e2]
    by_cases h2 : k = e2 (-2) (-2)
    · subst h2; fin_cases j <;> simp [e2]
    by_cases h3 : k = e2 0 2
    · subst h3; fin_cases j <;> simp [e2]
    by_cases h4 : k = e2 0 (-2)
    · subst h4; fin_cases j <;> simp [e2]
    by_cases h5 : k = e2 (-2) 2
    · subst h5; fin_cases j <;> simp [e2]
    by_cases h6 : k = e2 2 (-2)
    · subst h6; fin_cases j <;> simp [e2]
    by_cases h7 : k = e2 2 0
    · subst h7; fin_cases j <;> simp [e2]
    by_cases h8 : k = e2 (-2) 0
    · subst h8; fin_cases j <;> simp [e2]
    by_cases h9 : k = (0 : ExpVec 2)
    · subst h9; fin_cases j <;> simp
    exact absurd (hzero k h1 h2 h3 h4 h5 h6 h7 h8 h9) hk
  have hlow : ∀ j : Fin 2, (2 : ℕ) ≤ degVar j P22 := by
    intro j
    have h2 := Finset.le_sup (f := fun k => Int.natAbs (k j)) hmem
    exact le_trans (by fin_cases j <;> simp [e2]) h2
  have e0 : degVar 0 P22 = 2 := le_antisymm (Finset.sup_le fun k hk => hub k hk 0) (hlow 0)
  have e1 : degVar 1 P22 = 2 := le_antisymm (Finset.sup_le fun k hk => hub k hk 1) (hlow 1)
  simp [degTotal, Fin.sum_univ_two, e0, e1]

/-- The constructive decision algorithm rejects `(P_{2,2}, Q_{2,2})` at `n = 4`. -/
theorem mqspCDA_P22_Q22_four : mqspCDA P22 Q22 4 = false := by
  classical
  have hd (j : Fin 2) : degVar j P22 = 2 := by
    have hm : e2 2 2 ∈ P22.coeff.support := by
      rw [Finsupp.mem_support_iff, top_coefficients.1]
      exact pref_ne_zero
    have hb (i : Fin 2) : 2 ≤ degVar i P22 := by
      have h := Finset.le_sup (f := fun k => Int.natAbs (k i)) hm
      exact le_trans (by fin_cases i <;> simp [e2]) h
    have ht := degTotal_P22
    simp only [degTotal, Fin.sum_univ_two] at ht
    have h0 := hb 0
    have h1 := hb 1
    fin_cases j <;> dsimp at * <;> omega
  have hno : ¬ ∃ j : Fin 2, ∃ φ : ℝ,
      sliceVar j (degVar j P22) P22 = C' (Complex.exp (2 * Complex.I * (φ : ℂ))) *
        sliceVar j (degVar j P22) Q22 := by
    rintro ⟨j, φ, h⟩
    obtain ⟨k, hk, hne⟩ := slices_not_proportional j
    have ht : e2 2 2 j = 2 := by fin_cases j <;> simp [e2]
    have he (v : ExpVec 2) (hv : v j = 2) :
        P22.coeff v = Complex.exp (2 * Complex.I * (φ : ℂ)) * Q22.coeff v := by
      have hc := congrArg (fun X : MLaurent 2 => X.coeff v) h
      simpa [evMulC, sliceVar, hd, Finsupp.filter_apply, hv] using hc
    apply hne
    rw [he _ ht, he _ hk]
    ring
  rw [mqspCDA]
  simp [degTotal_P22, hno]

private lemma coeff_substInv {m : ℕ} (X : MLaurent m) (k : ExpVec m) :
    (substInv m X).coeff k = X.coeff (-k) := by
  change Finsupp.mapDomain (fun a : ExpVec m => -a) X.coeff k = _
  simpa using Finsupp.mapDomain_apply_of_injective
    (neg_injective : Function.Injective (fun a : ExpVec m => -a)) X.coeff (-k)

private lemma coeff_starOp {m : ℕ} (X : MLaurent m) (k : ExpVec m) :
    (starOp X).coeff k = star (X.coeff (-k)) := by
  rw [starOp, coeff_substInv]
  rfl

private lemma coeff_degree_bound {m : ℕ} (j : Fin m) (X : MLaurent m)
    (k : ExpVec m) (hk : X.coeff k ≠ 0) : Int.natAbs (k j) ≤ degVar j X :=
  Finset.le_sup (f := fun k => Int.natAbs (k j)) (Finsupp.mem_support_iff.mpr hk)

private lemma degVar_starOp_le {m : ℕ} (j : Fin m) (X : MLaurent m) :
    degVar j (starOp X) ≤ degVar j X := by
  apply Finset.sup_le
  intro k hk
  rw [Finsupp.mem_support_iff, coeff_starOp, star_ne_zero] at hk
  have hb := coeff_degree_bound j X (-k) hk
  simpa using hb

private lemma degVar_neg_eq {m : ℕ} (j : Fin m) (X : MLaurent m) :
    degVar j (-X) = degVar j X := by
  simp [degVar]

private lemma degVar_Q22_le (j : Fin 2) : degVar j Q22 ≤ 2 := by
  apply Finset.sup_le
  intro k hk
  rw [Finsupp.mem_support_iff] at hk
  by_cases h1 : k = e2 2 2
  · subst h1; fin_cases j <;> simp [e2]
  by_cases h2 : k = e2 (-2) (-2)
  · subst h2; fin_cases j <;> simp [e2]
  by_cases h3 : k = e2 0 2
  · subst h3; fin_cases j <;> simp [e2]
  by_cases h4 : k = e2 0 (-2)
  · subst h4; fin_cases j <;> simp [e2]
  by_cases h5 : k = e2 (-2) 2
  · subst h5; fin_cases j <;> simp [e2]
  by_cases h6 : k = e2 2 (-2)
  · subst h6; fin_cases j <;> simp [e2]
  by_cases h7 : k = e2 2 0
  · subst h7; fin_cases j <;> simp [e2]
  by_cases h8 : k = e2 (-2) 0
  · subst h8; fin_cases j <;> simp [e2]
  exfalso
  apply hk
  rw [Q22_apply]
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

private abbrev Mat (m : ℕ) := Matrix (Fin 2) (Fin 2) (MLaurent m)

private def matrixDegree {m : ℕ} (j : Fin m) (M : Mat m) : ℕ :=
  Finset.univ.sup fun r => Finset.univ.sup fun c => degVar j (M r c)

private lemma matrixDegree_le {m : ℕ} (j : Fin m) (M : Mat m) (d : ℕ) :
    matrixDegree j M ≤ d ↔ ∀ r c, degVar j (M r c) ≤ d := by
  simp [matrixDegree, Finset.sup_le_iff]

private lemma entry_degree_le {m : ℕ} (j : Fin m) (M : Mat m) (r c : Fin 2) :
    degVar j (M r c) ≤ matrixDegree j M :=
  (matrixDegree_le j M _).mp le_rfl r c

private lemma matrixDegree_mul_le {m : ℕ} (j : Fin m) (M N : Mat m) :
    matrixDegree j (M * N) ≤ matrixDegree j M + matrixDegree j N := by
  apply (matrixDegree_le j _ _).mpr
  intro r c
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  apply (Lemma4.degVar_add_le j _ _).trans
  exact max_le
    ((Lemma4.degVar_mul_le j _ _).trans
      (Nat.add_le_add (entry_degree_le j M r 0) (entry_degree_le j N 0 c)))
    ((Lemma4.degVar_mul_le j _ _).trans
      (Nat.add_le_add (entry_degree_le j M r 1) (entry_degree_le j N 1 c)))

private lemma slice_mul_top {m : ℕ} (j : Fin m) (p q : ℕ) (X Y : MLaurent m)
    (hX : degVar j X ≤ p) (hY : degVar j Y ≤ q) :
    sliceVar j (p + q : ℕ) (X * Y) = sliceVar j p X * sliceVar j q Y := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp only [sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
    AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, Finsupp.support_filter,
    Finset.sum_filter]
  by_cases hk : k j = (p + q : ℕ)
  · simp only [hk, reduceIte]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hup : u j = (p : ℤ)
    · have hv : (-u + k) j = (q : ℤ) := by change -u j + k j = _; omega
      simp [hup, hv]
    · have huB := (coeff_degree_bound j X u (Finsupp.mem_support_iff.mp hu)).trans hX
      have hy0 : Y.coeff (-u + k) = 0 := by
        by_contra hn
        have hvB := (coeff_degree_bound j Y (-u + k) hn).trans hY
        change Int.natAbs (-u j + k j) ≤ q at hvB
        omega
      simp [hup, hy0]
  · simp only [hk, reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro u _
    by_cases hup : u j = (p : ℤ)
    · have hv : (-u + k) j ≠ (q : ℤ) := by
        change -u j + k j ≠ _
        omega
      have hv' : -(p : ℤ) + k j ≠ (q : ℤ) := by simpa [hup] using hv
      simp [hup, hv']
    · simp [hup]

private def sliceMatrix {m : ℕ} (j : Fin m) (d : ℕ) (M : Mat m) : Mat m :=
  fun r c => sliceVar j d (M r c)

private lemma sliceMatrix_mul {m : ℕ} (j : Fin m) (p q : ℕ) (M N : Mat m)
    (hM : matrixDegree j M ≤ p) (hN : matrixDegree j N ≤ q) :
    sliceMatrix j (p + q) (M * N) = sliceMatrix j p M * sliceMatrix j q N := by
  ext r c
  simp only [sliceMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have hadd (X Y : MLaurent m) : sliceVar j (p + q : ℕ) (X + Y) =
      sliceVar j (p + q : ℕ) X + sliceVar j (p + q : ℕ) Y := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp [sliceVar, Finsupp.filter_apply]
  rw [hadd, slice_mul_top j p q _ _ ((matrixDegree_le j M p).mp hM r 0)
    ((matrixDegree_le j N q).mp hN 0 c),
    slice_mul_top j p q _ _ ((matrixDegree_le j M p).mp hM r 1)
      ((matrixDegree_le j N q).mp hN 1 c)]

private abbrev Generator (m : ℕ) := Fin m ⊕ ℝ

private def generatorMatrix {m : ℕ} : Generator m → Mat m
  | .inl j => signalOp j
  | .inr φ => phaseOp φ

private def product {m : ℕ} (L : List (Generator m)) : Mat m :=
  (L.map generatorMatrix).prod

private def count {m : ℕ} (j : Fin m) (L : List (Generator m)) : ℕ :=
  (L.map fun g => match g with
    | .inl i => if j = i then 1 else 0
    | .inr _ => 0).sum

private lemma product_append {m : ℕ} (L R : List (Generator m)) :
    product (L ++ R) = product L * product R := by simp [product, List.prod_append]

private lemma count_append {m : ℕ} (j : Fin m) (L R : List (Generator m)) :
    count j (L ++ R) = count j L + count j R := by simp [count]

private def generatorInv {m : ℕ} : Generator m → Mat m
  | .inl j => Lemma7.signalOpInv j
  | .inr φ => phaseOp (-φ)

private lemma generatorInv_mul {m : ℕ} (g : Generator m) :
    generatorInv g * generatorMatrix g = 1 := by
  cases g with
  | inl j => exact Lemma7.inv_mul_signalOp j
  | inr φ =>
    rw [generatorInv, generatorMatrix, Lemma3.phaseOp_mul, neg_add_cancel, Lemma3.phaseOp_zero]

private def productInv {m : ℕ} (L : List (Generator m)) : Mat m :=
  (L.reverse.map generatorInv).prod

private lemma productInv_mul {m : ℕ} (L : List (Generator m)) :
    productInv L * product L = 1 := by
  induction L with
  | nil => simp [productInv, product]
  | cons g L ih =>
    have hrev : productInv (g :: L) = productInv L * generatorInv g := by
      simp [productInv, List.prod_append]
    calc productInv (g :: L) * product (g :: L)
        = productInv L * (generatorInv g * generatorMatrix g) * product L := by
            simp only [hrev, product, List.map_cons, List.prod_cons, Matrix.mul_assoc]
      _ = productInv L * product L := by rw [generatorInv_mul, mul_one]
      _ = 1 := ih

private lemma mul_productInv {m : ℕ} (L : List (Generator m)) :
    product L * productInv L = 1 := by
  rw [mul_eq_one_comm, productInv_mul]

private lemma product_degree {m : ℕ} (j : Fin m) (L : List (Generator m)) :
    matrixDegree j (product L) ≤ count j L := by
  have hp (φ : ℝ) : matrixDegree j (phaseOp φ : Mat m) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (matrixDegree_le j _ _).mpr
    intro r c
    fin_cases r <;> fin_cases c <;>
      simp [phaseOp, Lemma7.degVar_C', Lemma4.degVar_zero]
  have hs (i : Fin m) : matrixDegree j (signalOp i) ≤ if j = i then 1 else 0 := by
    apply (matrixDegree_le j _ _).mpr
    intro r c
    fin_cases r <;> fin_cases c
    all_goals
      simp only [signalOp, Matrix.of_apply, Matrix.cons_val']
      apply (Lemma4.degVar_mul_le j _ _).trans
      simp only [Lemma7.degVar_C', zero_add]
    · exact Lemma7.degVar_varSum_le j i
    · exact Lemma7.degVar_varDiff_le j i
    · exact Lemma7.degVar_varDiff_le j i
    · exact Lemma7.degVar_varSum_le j i
  induction L with
  | nil =>
    apply (matrixDegree_le j _ _).mpr
    intro r c
    fin_cases r <;> fin_cases c <;>
      simp [product, count, Lemma4.degVar_one, Lemma4.degVar_zero]
  | cons g L ih =>
    have h := matrixDegree_mul_le j (generatorMatrix g) (product L)
    cases g with
    | inl i => exact h.trans (Nat.add_le_add (hs i) ih)
    | inr φ => simpa [product, generatorMatrix, count, hp] using
        h.trans (Nat.add_le_add (le_of_eq (hp φ)) ih)

private lemma count_zero {m : ℕ} (j : Fin m) (L : List (Generator m))
    (h : Sum.inl j ∉ L) : count j L = 0 := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    have ht : Sum.inl j ∉ L := fun hh => h (List.mem_cons_of_mem _ hh)
    cases g with
    | inl i =>
      have hi : j ≠ i := by intro he; subst he; exact h List.mem_cons_self
      simpa [count, hi] using ih ht
    | inr _ => simpa [count] using ih ht

private def inversionForm {m : ℕ} (M : Mat m) : Prop :=
  substInv m (M 0 0) = M 0 0 ∧ substInv m (M 0 1) = -M 0 1 ∧
  substInv m (M 1 0) = -M 1 0 ∧ substInv m (M 1 1) = M 1 1

private lemma inversionForm_mul {m : ℕ} {M N : Mat m}
    (hM : inversionForm M) (hN : inversionForm N) : inversionForm (M * N) := by
  rcases hM with ⟨h00, h01, h10, h11⟩
  rcases hN with ⟨g00, g01, g10, g11⟩
  simp only [inversionForm, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul,
    h00, h01, h10, h11, g00, g01, g10, g11]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private lemma product_inversion {m : ℕ} (L : List (Generator m)) :
    inversionForm (product L) := by
  induction L with
  | nil => simp [product, inversionForm]
  | cons g L ih =>
    apply inversionForm_mul (N := product L) _ ih
    cases g with
    | inl j =>
      simp [generatorMatrix, inversionForm, signalOp, Lemma3.substInv_C',
        Lemma3.substInv_var, Lemma3.substInv_varInv, sub_eq_add_neg, add_comm,
        mul_add]
    | inr φ => simp [generatorMatrix, inversionForm, phaseOp, Lemma3.substInv_C']

private def plusSum {m : ℕ} (M : Mat m) : MLaurent m :=
  M 0 0 + M 0 1 + M 1 0 + M 1 1

private lemma sandwich_cancel {m : ℕ} (j : Fin m) (L : List (Generator m))
    (h : plusSum (product L) = 0) : signalOp j * product L * signalOp j = product L := by
  rcases product_inversion L with ⟨h00, h01, h10, h11⟩
  have hh := congrArg (substInv m) h
  simp only [plusSum, map_add, map_zero, h00, h01, h10, h11] at hh
  have h' : product L 0 0 + product L 0 1 + product L 1 0 + product L 1 1 = 0 := h
  have hhalf2 : (C' (1 / 2 : ℂ) : MLaurent m) * (2 : MLaurent m) = 1 := by
    have h2 : (2 : MLaurent m) = C' (2 : ℂ) := rfl
    rw [h2, Lemma4.C'_mul_C', show (1 / 2 : ℂ) * 2 = 1 by norm_num]
    simp [C', AddMonoidAlgebra.one_def]
  have ha : product L 1 1 = -product L 0 0 := by
    have he : (2 : MLaurent m) * (product L 1 1 + product L 0 0) = 0 := by
      linear_combination h' + hh
    have hz : product L 1 1 + product L 0 0 = 0 := by
      calc product L 1 1 + product L 0 0
          = (C' (1 / 2 : ℂ) * (2 : MLaurent m)) * (product L 1 1 + product L 0 0) := by
              rw [hhalf2, one_mul]
        _ = C' (1 / 2 : ℂ) * ((2 : MLaurent m) * (product L 1 1 + product L 0 0)) := by
              rw [mul_assoc]
        _ = 0 := by rw [he, mul_zero]
    linear_combination hz
  have hb : product L 1 0 = -product L 0 1 := by
    have he : (2 : MLaurent m) * (product L 1 0 + product L 0 1) = 0 := by
      linear_combination h' - hh
    have hz : product L 1 0 + product L 0 1 = 0 := by
      calc product L 1 0 + product L 0 1
          = (C' (1 / 2 : ℂ) * (2 : MLaurent m)) * (product L 1 0 + product L 0 1) := by
              rw [hhalf2, one_mul]
        _ = C' (1 / 2 : ℂ) * ((2 : MLaurent m) * (product L 1 0 + product L 0 1)) := by
              rw [mul_assoc]
        _ = 0 := by rw [he, mul_zero]
    linear_combination hz
  have he : signalOp j * product L = product L * Lemma7.signalOpInv j := by
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Lemma7.signalOp_entry,
        Lemma7.signalOpInv_entry, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, ha, hb] <;>
      ring
  rw [he, mul_assoc, Lemma7.inv_mul_signalOp, mul_one]

private def reduced {m : ℕ} (L : List (Generator m)) : Prop :=
  ∀ (U V R : List (Generator m)) (j : Fin m),
    L = U ++ Sum.inl j :: (V ++ Sum.inl j :: R) → plusSum (product V) ≠ 0

private lemma reduced_suffix {m : ℕ} {L R : List (Generator m)} (h : reduced (L ++ R)) :
    reduced R := by
  intro U V W j he
  apply h (L ++ U) V W j
  simp only [he, List.append_assoc]

private lemma exists_reduced {m : ℕ} (L : List (Generator m)) :
    ∃ L' : List (Generator m), reduced L' ∧ product L' = product L := by
  classical
  induction hlen : L.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hred : reduced L
    · exact ⟨L, hred, rfl⟩
    · simp only [reduced, not_forall, Classical.not_not] at hred
      obtain ⟨U, V, R, j, hL, hV⟩ := hred
      have hlt : (U ++ V ++ R).length < n := by
        subst hlen
        rw [hL]
        simp only [List.length_append, List.length_cons]
        omega
      obtain ⟨L', hred', hprod'⟩ := ih _ hlt (U ++ V ++ R) rfl
      refine ⟨L', hred', ?_⟩
      rw [hprod', hL]
      have h1 : product (U ++ V ++ R) = product U * (product V * product R) := by
        simp only [product_append, Matrix.mul_assoc]
      have h2 : product (U ++ Sum.inl j :: (V ++ Sum.inl j :: R)) =
          product U * (signalOp j * (product V * (signalOp j * product R))) := by
        simp only [product, List.map_append, List.prod_append, List.map_cons,
          List.prod_cons, generatorMatrix]
      rw [h1, h2]
      have hsc := sandwich_cancel j V hV
      calc product U * (product V * product R)
          = product U * ((signalOp j * product V * signalOp j) * product R) := by rw [hsc]
        _ = product U * (signalOp j * (product V * (signalOp j * product R))) := by
              simp only [Matrix.mul_assoc]

private lemma first_split {α : Type*} [DecidableEq α] (a : α) (L : List α) (h : a ∈ L) :
    ∃ U V, L = U ++ a :: V ∧ a ∉ U := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    by_cases hb : a = b
    · exact ⟨[], L, by simp [hb], by simp⟩
    · have ht : a ∈ L := (List.mem_cons.mp h).resolve_left hb
      obtain ⟨U, V, he, hu⟩ := ih ht
      refine ⟨b :: U, V, by simp [he], ?_⟩
      intro hm
      rcases List.mem_cons.mp hm with h1 | h2
      · exact hb h1
      · exact hu h2

private def onesMat {m : ℕ} : Mat m := !![1, 1; 1, 1]

private lemma onesMat_mul_onesMat {m : ℕ} (M : Mat m) :
    onesMat * M * onesMat = plusSum M • onesMat := by
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    simp only [onesMat, plusSum, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Matrix.smul_apply, smul_eq_mul] <;>
    ring

private lemma sliceMatrix_zero_of_deg_zero {m : ℕ} (j : Fin m) (M : Mat m)
    (hM : matrixDegree j M ≤ 0) : sliceMatrix j 0 M = M := by
  refine Matrix.ext fun r c => ?_
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp only [sliceMatrix, sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
    Nat.cast_zero]
  by_cases hk : k j = 0
  · simp only [hk, reduceIte]
  · simp only [hk, reduceIte]
    symm
    by_contra hn
    have hb := (coeff_degree_bound j (M r c) k hn).trans ((matrixDegree_le j M 0).mp hM r c)
    omega

private lemma half_var_ne_zero {m : ℕ} (j : Fin m) :
    (C' (1 / 2 : ℂ) * var j : MLaurent m) ≠ 0 := by
  intro h
  have hc := congrArg (fun X : MLaurent m => X.coeff (Pi.single j (1 : ℤ))) h
  rw [C'mul_smul, AddMonoidAlgebra.coeff_smul_apply] at hc
  simp only [var, mono, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul, mul_one] at hc
  norm_num at hc

private lemma sliceMatrix_signalOp_self {m : ℕ} (j : Fin m) :
    sliceMatrix j 1 (signalOp j) = (C' (1 / 2 : ℂ) * var j) • onesMat := by
  have hvp : sliceVar j 1 (var j + varInv j) = var j := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp only [sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, var, varInv, mono,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hk : k j = 1
    · have hne : Pi.single j (-1 : ℤ) ≠ k := by
        intro he
        have := congrFun he j
        simp at this
        omega
      simp [hk, hne]
    · have hne : Pi.single j (1 : ℤ) ≠ k := by
        intro he
        have := congrFun he j
        simp at this
        omega
      simp [hk, hne]
  have hvm : sliceVar j 1 (var j - varInv j) = var j := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp only [sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
      AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, var, varInv, mono,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hk : k j = 1
    · have hne : Pi.single j (-1 : ℤ) ≠ k := by
        intro he
        have := congrFun he j
        simp at this
        omega
      simp [hk, hne]
    · have hne : Pi.single j (1 : ℤ) ≠ k := by
        intro he
        have := congrFun he j
        simp at this
        omega
      simp [hk, hne]
  have hC : sliceVar j 0 (C' (1 / 2 : ℂ) : MLaurent m) = C' (1 / 2 : ℂ) := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp only [sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply, C',
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hk : k = 0
    · subst hk; simp
    · have hne : (0 : ExpVec m) ≠ k := Ne.symm hk
      simp [hne]
  have hp := slice_mul_top j 0 1 (C' (1 / 2 : ℂ)) (var j + varInv j)
    (by simp [Lemma7.degVar_C']) (by simpa using Lemma7.degVar_varSum_le j j)
  have hm := slice_mul_top j 0 1 (C' (1 / 2 : ℂ)) (var j - varInv j)
    (by simp [Lemma7.degVar_C']) (by simpa using Lemma7.degVar_varDiff_le j j)
  simp only [zero_add, Nat.cast_zero, Nat.cast_one] at hp hm
  rw [hC, hvp] at hp
  rw [hC, hvm] at hm
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c
  · simpa [sliceMatrix, Lemma7.signalOp_entry, onesMat] using hp
  · simpa [sliceMatrix, Lemma7.signalOp_entry, onesMat] using hm
  · simpa [sliceMatrix, Lemma7.signalOp_entry, onesMat] using hm
  · simpa [sliceMatrix, Lemma7.signalOp_entry, onesMat] using hp

private lemma reduced_slice_form {m : ℕ} (j : Fin m) (L : List (Generator m))
    (hred : reduced L) (hmem : Sum.inl j ∈ L) :
    ∃ (V0 W0 U R : List (Generator m)) (α : MLaurent m),
      L = V0 ++ Sum.inl j :: W0 ∧ Sum.inl j ∉ V0 ∧
      L = U ++ Sum.inl j :: R ∧ Sum.inl j ∉ R ∧
      α ≠ 0 ∧
      sliceMatrix j (count j L) (product L) = α • (product V0 * onesMat * product R) := by
  classical
  induction hlen : L.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
    obtain ⟨V0, W, hL, hV0⟩ := first_split (Sum.inl j) L hmem
    have hcV0 : count j V0 = 0 := count_zero j V0 hV0
    have hdV0 : matrixDegree j (product V0) ≤ 0 := (product_degree j V0).trans (le_of_eq hcV0)
    have hsV0 : sliceMatrix j 0 (product V0) = product V0 := sliceMatrix_zero_of_deg_zero j _ hdV0
    have hdSig : matrixDegree j (signalOp j) ≤ 1 := by
      simpa [product, generatorMatrix, count] using product_degree j [Sum.inl j]
    have hsLeft : sliceMatrix j 1 (product V0 * signalOp j) =
        (C' (1 / 2 : ℂ) * var j) • (product V0 * onesMat) := by
      have hm := sliceMatrix_mul j 0 1 (product V0) (signalOp j) hdV0 hdSig
      simpa [zero_add, hsV0, sliceMatrix_signalOp_self, Matrix.mul_smul] using hm
    by_cases hW : Sum.inl j ∈ W
    · have hlt : W.length < n := by
        subst hlen
        rw [hL]
        simp only [List.length_append, List.length_cons]
        omega
      have hredW : reduced W := by
        rw [hL] at hred
        exact reduced_suffix (L := V0 ++ [Sum.inl j]) (by simpa using hred)
      obtain ⟨V1, W1, U', R, α', hW1, _, hW2, hR, hα', hsW⟩ := ih _ hlt W hredW hW rfl
      have hplus : plusSum (product V1) ≠ 0 := by
        apply hred V0 V1 W1 j
        rw [hL, hW1]
      have hcL : count j L = 1 + count j W := by
        rw [hL, count_append, hcV0, zero_add]
        simp [count]
      have hpL : product L = (product V0 * signalOp j) * product W := by
        rw [hL, product_append]
        simp [product, generatorMatrix, Matrix.mul_assoc]
      have hdLeft : matrixDegree j (product V0 * signalOp j) ≤ 1 :=
        (matrixDegree_mul_le j _ _).trans (by omega)
      have hsTot := sliceMatrix_mul j 1 (count j W) (product V0 * signalOp j) (product W)
        hdLeft (product_degree j W)
      rw [hsLeft, hsW, ← hpL, ← hcL] at hsTot
      refine ⟨V0, W, V0 ++ Sum.inl j :: U', R,
        (C' (1 / 2 : ℂ) * var j) * α' * plusSum (product V1), hL, hV0, ?_, hR, ?_, ?_⟩
      · rw [hL, hW2]
        simp [List.append_assoc]
      · exact mul_ne_zero (mul_ne_zero (half_var_ne_zero j) hα') hplus
      · rw [hsTot]
        have hassoc : product V0 * onesMat * (product V1 * onesMat * product R) =
            (onesMat * product V1 * onesMat |> fun X => product V0 * X * product R) := by
          simp only [Matrix.mul_assoc]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [hassoc, onesMat_mul_onesMat]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        congr 1
        ring
    · have hcW : count j W = 0 := count_zero j W hW
      have hdW : matrixDegree j (product W) ≤ 0 := (product_degree j W).trans (le_of_eq hcW)
      have hsW : sliceMatrix j 0 (product W) = product W := sliceMatrix_zero_of_deg_zero j _ hdW
      have hcL : count j L = 1 := by
        rw [hL, count_append, hcV0, zero_add]
        simpa [count] using hcW
      have hpL : product L = (product V0 * signalOp j) * product W := by
        rw [hL, product_append]
        simp [product, generatorMatrix, Matrix.mul_assoc]
      have hdLeft : matrixDegree j (product V0 * signalOp j) ≤ 1 :=
        (matrixDegree_mul_le j _ _).trans (by omega)
      have hsTot := sliceMatrix_mul j 1 0 (product V0 * signalOp j) (product W) hdLeft hdW
      rw [add_zero, hsLeft, hsW, ← hpL] at hsTot
      refine ⟨V0, W, V0, W, C' (1 / 2 : ℂ) * var j, hL, hV0, hL, hW, half_var_ne_zero j, ?_⟩
      rw [hcL]
      simpa [Matrix.smul_mul, Matrix.mul_assoc] using hsTot

private lemma reduced_matrixDegree {m : ℕ} (j : Fin m) (L : List (Generator m))
    (hred : reduced L) : matrixDegree j (product L) = count j L := by
  by_cases hmem : Sum.inl j ∈ L
  · obtain ⟨V0, _, _, R, α, _, _, _, _, hα, hslice⟩ := reduced_slice_form j L hred hmem
    apply le_antisymm (product_degree j L)
    by_contra hlt
    have hle : matrixDegree j (product L) < count j L := Nat.lt_of_not_ge hlt
    have hzero : sliceMatrix j (count j L) (product L) = 0 := by
      refine Matrix.ext fun r c => ?_
      apply AddMonoidAlgebra.coeff_injective
      ext k
      simp only [sliceMatrix, sliceVar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply,
        Matrix.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_cases hk : k j = (count j L : ℤ)
      · simp only [hk, reduceIte]
        by_contra hn
        have hb := coeff_degree_bound j (product L r c) k hn
        have hm := entry_degree_le j (product L) r c
        omega
      · simp [hk]
    rw [hzero] at hslice
    have hcancel : α • onesMat = (0 : Mat m) := by
      calc α • onesMat
          = (productInv V0 * product V0) * (α • onesMat) * (product R * productInv R) := by
              rw [productInv_mul, mul_productInv, one_mul, mul_one]
        _ = productInv V0 * (α • (product V0 * onesMat * product R)) * productInv R := by
              simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = 0 := by rw [← hslice, mul_zero, zero_mul]
    have h00 := congrArg (fun M : Mat m => M 0 0) hcancel
    simp [onesMat] at h00
    exact hα h00
  · have hc := count_zero j L hmem
    have hd := (product_degree j L).trans (le_of_eq hc)
    omega

private lemma last_signal_split {m : ℕ} (L : List (Generator m))
    (hex : ∃ i : Fin m, Sum.inl i ∈ L) :
    ∃ (U R : List (Generator m)) (j : Fin m),
      L = U ++ Sum.inl j :: R ∧ ∀ i : Fin m, Sum.inl i ∉ R := by
  induction L with
  | nil =>
    obtain ⟨i, hi⟩ := hex
    simp at hi
  | cons g L ih =>
    by_cases hexL : ∃ i : Fin m, Sum.inl i ∈ L
    · obtain ⟨U, R, j, hL, hR⟩ := ih hexL
      exact ⟨g :: U, R, j, by simp [hL], hR⟩
    · obtain ⟨i, hi⟩ := hex
      rcases List.mem_cons.mp hi with h1 | h2
      · refine ⟨[], L, i, by simp [h1], ?_⟩
        intro k hk
        exact hexL ⟨k, hk⟩
      · exact absurd ⟨i, h2⟩ hexL

private lemma last_split_unique {α : Type*} (a : α) :
    ∀ (U R U' R' : List α),
      U ++ a :: R = U' ++ a :: R' → a ∉ R → a ∉ R' → R = R' := by
  intro U R U' R' he hR hR'
  induction U generalizing U' with
  | nil =>
    cases U' with
    | nil =>
      simp at he
      exact he
    | cons b U' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, htail⟩
      exfalso
      apply hR
      rw [htail]
      exact List.mem_append_right U' List.mem_cons_self
  | cons b U ih =>
    cases U' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      rcases he with ⟨rfl, htail⟩
      exfalso
      apply hR'
      rw [← htail]
      exact List.mem_append_right U List.mem_cons_self
    | cons c U' =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact ih U' he.2

private lemma phases_only_product {m : ℕ} (R : List (Generator m))
    (hR : ∀ i : Fin m, Sum.inl i ∉ R) :
    ∃ Φ : ℝ, product R = phaseOp Φ := by
  induction R with
  | nil =>
    exact ⟨0, by simp [product, Lemma3.phaseOp_zero]⟩
  | cons g R ih =>
    have hR' : ∀ i : Fin m, Sum.inl i ∉ R := fun i hi => hR i (List.mem_cons_of_mem _ hi)
    cases g with
    | inl i => exact absurd List.mem_cons_self (hR i)
    | inr ψ =>
      obtain ⟨Φ, hΦ⟩ := ih hR'
      refine ⟨ψ + Φ, ?_⟩
      rw [product, List.map_cons, List.prod_cons, generatorMatrix, ← product, hΦ,
        Lemma3.phaseOp_mul]

private def wordToList {m : ℕ} :
    ∀ (n : ℕ), (Fin n → ℝ) → (Fin n → Fin m) → List (Generator m)
  | 0, _, _ => []
  | n + 1, ψ, s =>
      Sum.inl (s 0) :: Sum.inr (ψ 0) ::
        wordToList n (fun k => ψ k.succ) (fun k => s k.succ)

private lemma product_wordToList {m : ℕ} :
    ∀ (n : ℕ) (ψ : Fin n → ℝ) (s : Fin n → Fin m),
      product (wordToList n ψ s) =
        (List.ofFn fun k : Fin n => signalOp (s k) * phaseOp (ψ k)).prod
  | 0, _, _ => by simp [wordToList, product]
  | n + 1, ψ, s => by
      rw [wordToList, List.ofFn_succ, List.prod_cons, ← product_wordToList n]
      simp [product, generatorMatrix, Matrix.mul_assoc]

/-- The counterexample pair `(P_{2,2}, Q_{2,2})` is not constructible at any step count `n`. -/
theorem ref22_counterexample_no_construction :
    ∀ n : ℕ, ¬ Constructible n P22 Q22 := by
  rintro n ⟨φ, s, hW⟩
  set W : Mat 2 := !![P22, Q22; -starOp Q22, starOp P22]
  have hprod0 : product (Sum.inr (φ 0) :: wordToList n (fun k => φ k.succ) s) = W := by
    rw [product, List.map_cons, List.prod_cons, generatorMatrix, ← product,
      product_wordToList, ← wordMatrix, hW]
  obtain ⟨L, hred, hprod⟩ :=
    exists_reduced (Sum.inr (φ 0) :: wordToList n (fun k => φ k.succ) s)
  rw [hprod0] at hprod
  have hdP (j : Fin 2) : degVar j P22 = 2 := by
    have hm : e2 2 2 ∈ P22.coeff.support := by
      rw [Finsupp.mem_support_iff, top_coefficients.1]
      exact pref_ne_zero
    have hb (i : Fin 2) : 2 ≤ degVar i P22 := by
      have h := Finset.le_sup (f := fun k => Int.natAbs (k i)) hm
      exact le_trans (by fin_cases i <;> simp [e2]) h
    have ht := degTotal_P22
    simp only [degTotal, Fin.sum_univ_two] at ht
    have h0 := hb 0
    have h1 := hb 1
    fin_cases j <;> dsimp at * <;> omega
  have hdW (j : Fin 2) : matrixDegree j W = 2 := by
    apply le_antisymm
    · apply (matrixDegree_le j W 2).mpr
      intro r c
      fin_cases r <;> fin_cases c
      · simp [W, hdP j]
      · simpa [W] using degVar_Q22_le j
      · simpa [W, degVar_neg_eq] using (degVar_starOp_le j Q22).trans (degVar_Q22_le j)
      · simpa [W, hdP j] using degVar_starOp_le j P22
    · have h00 : degVar j (W 0 0) ≤ matrixDegree j W := entry_degree_le j W 0 0
      simpa [W, hdP j] using h00
  have hcnt (j : Fin 2) : count j L = 2 := by
    have hm := reduced_matrixDegree j L hred
    rw [hprod, hdW j] at hm
    exact hm.symm
  have hmem0 : Sum.inl (0 : Fin 2) ∈ L := by
    by_contra h0
    have hc0 := count_zero 0 L h0
    have hc02 := hcnt 0
    omega
  obtain ⟨U_last, R_last, j, hL_last, hR_last⟩ := last_signal_split L ⟨0, hmem0⟩
  have hmemj : Sum.inl j ∈ L := by
    rw [hL_last]
    exact List.mem_append_right U_last List.mem_cons_self
  obtain ⟨V0, _, U, R, α, _, _, hLU, hR, _, hslice⟩ := reduced_slice_form j L hred hmemj
  have hReq : R = R_last :=
    last_split_unique (Sum.inl j) U R U_last R_last (hLU.symm.trans hL_last) hR (hR_last j)
  subst hReq
  obtain ⟨Φ, hΦ⟩ := phases_only_product R hR_last
  rw [hprod, hcnt j, hΦ] at hslice
  have hs00 := congrArg (fun M : Mat 2 => M 0 0) hslice
  have hs01 := congrArg (fun M : Mat 2 => M 0 1) hslice
  simp only [sliceMatrix, W, onesMat, phaseOp, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero, zero_add] at hs00 hs01
  have hexp : C' (Complex.exp (2 * Complex.I * (Φ : ℂ)) : ℂ) *
      C' (Complex.exp (-(Complex.I * (Φ : ℂ))) : ℂ) =
      (C' (Complex.exp (Complex.I * (Φ : ℂ)) : ℂ) : MLaurent 2) := by
    rw [Lemma4.C'_mul_C', ← Complex.exp_add]
    congr 1
    congr 1
    ring
  have hprop : sliceVar j (2 : ℕ) P22 =
      C' (Complex.exp (2 * Complex.I * (Φ : ℂ))) * sliceVar j (2 : ℕ) Q22 := by
    rw [hs00, hs01]
    calc α * ((product V0 0 0 + product V0 0 1) * C' (Complex.exp (Complex.I * (Φ : ℂ))))
        = α * ((product V0 0 0 + product V0 0 1) *
            (C' (Complex.exp (2 * Complex.I * (Φ : ℂ))) *
              C' (Complex.exp (-(Complex.I * (Φ : ℂ)))))) := by rw [hexp]
      _ = C' (Complex.exp (2 * Complex.I * (Φ : ℂ))) *
            (α * ((product V0 0 0 + product V0 0 1) *
              C' (Complex.exp (-(Complex.I * (Φ : ℂ)))))) := by ring
  obtain ⟨k, hk, hne⟩ := slices_not_proportional j
  have ht : e2 2 2 j = 2 := by fin_cases j <;> simp [e2]
  have he (v : ExpVec 2) (hv : v j = 2) :
      P22.coeff v = Complex.exp (2 * Complex.I * (Φ : ℂ)) * Q22.coeff v := by
    have hc := congrArg (fun X : MLaurent 2 => X.coeff v) hprop
    simpa [evMulC, sliceVar, Finsupp.filter_apply, hv] using hc
  apply hne
  rw [he _ ht, he _ hk]
  ring

end Qatlib.Papers.QSPIto26.MainResults.Counterexample
