/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma8.MQSPPrefixDegree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Angle Integrality and Step Reduction in Multivariable QSP

This module formalizes Lemma 2 of Ito, Mori, Sakamoto, and Fujii: when a
multivariable QSP prefix word starts and ends on the same variable `s_0 = s_{l-1}`
without intermediate occurrences, reaches maximal total degree `l - 1` at step
`l - 1`, and eliminates `a_{s_{l-1}}` at step `l`, all intermediate phase angles
`φ_0, ..., φ_{l-2}` lie in `(π / 2) ℤ` and the resulting polynomial pair is
constructible in `l - 2` steps.

## Main statements

* `lemma2_angle_integrality`: Lemma 2, proving `φ_k ∈ (π / 2) ℤ` for
  `k ≤ l - 2` and `Constructible (l - 2)` for `(prefixP, prefixQ)`.

## References

* [Ito et al., 2026][ItoEtAl2026], Appendix A, Lemma 2, Eqs. (18)--(19), pp. 13--14.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma2

open Qatlib.Papers.QSPIto26.MainResults.Core

open scoped Matrix BigOperators

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

private lemma matrixDegree_phase {m : ℕ} (j : Fin m) (θ : ℝ) :
    matrixDegree j (phaseOp θ : Mat m) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (matrixDegree_le j _ _).mpr
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [phaseOp, Lemma7.degVar_C', Lemma4.degVar_zero]

private lemma matrixDegree_signal {m : ℕ} (j t : Fin m) :
    matrixDegree j (signalOp t) ≤ if j = t then 1 else 0 := by
  apply (matrixDegree_le j _ _).mpr
  intro r c
  fin_cases r <;> fin_cases c
  all_goals
    simp only [signalOp, Matrix.of_apply, Matrix.cons_val']
    apply (Lemma4.degVar_mul_le j _ _).trans
    simp only [Lemma7.degVar_C', zero_add]
  · exact Lemma7.degVar_varSum_le j t
  · exact Lemma7.degVar_varDiff_le j t
  · exact Lemma7.degVar_varDiff_le j t
  · exact Lemma7.degVar_varSum_le j t

private def factors {m : ℕ} (L : List (Fin m × ℝ)) : Mat m :=
  (L.map fun p => signalOp p.1 * phaseOp p.2).prod

private def occurrences {m : ℕ} (j : Fin m) (L : List (Fin m × ℝ)) : ℕ :=
  (L.map fun p => if j = p.1 then 1 else 0).sum

private lemma factors_append {m : ℕ} (L R : List (Fin m × ℝ)) :
    factors (L ++ R) = factors L * factors R := by
  simp [factors, List.prod_append]

private lemma occurrences_append {m : ℕ} (j : Fin m) (L R : List (Fin m × ℝ)) :
    occurrences j (L ++ R) = occurrences j L + occurrences j R := by
  simp [occurrences]

private lemma matrixDegree_factors_le {m : ℕ} (j : Fin m) (L : List (Fin m × ℝ)) :
    matrixDegree j (factors L) ≤ occurrences j L := by
  induction L with
  | nil =>
    apply (matrixDegree_le j _ _).mpr
    intro r c
    fin_cases r <;> fin_cases c <;>
      simp [factors, occurrences, Lemma4.degVar_one, Lemma4.degVar_zero]
  | cons p L ih =>
    have hb := matrixDegree_mul_le j (signalOp p.1 * phaseOp p.2) (factors L)
    have hf := matrixDegree_mul_le j (signalOp p.1) (phaseOp p.2)
    rw [matrixDegree_phase, add_zero] at hf
    simpa [factors, occurrences] using
      hb.trans (Nat.add_le_add (hf.trans (matrixDegree_signal j p.1)) ih)

private lemma occurrences_sum {m : ℕ} (L : List (Fin m × ℝ)) :
    ∑ j : Fin m, occurrences j L = L.length := by
  induction L with
  | nil => simp [occurrences]
  | cons p L ih =>
    simp only [occurrences, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at *
    rw [ih]
    simp [Nat.add_comm]

private lemma coeff_zero_of_degree_lt {m : ℕ} (j : Fin m) (P : MLaurent m)
    (k : ExpVec m) (h : degVar j P < Int.natAbs (k j)) : P.coeff k = 0 := by
  by_contra hk
  have hb : Int.natAbs (k j) ≤ degVar j P :=
    Finset.le_sup (f := fun x => Int.natAbs (x j)) (Finsupp.mem_support_iff.mpr hk)
  omega

private lemma matrixDegree_witness {m : ℕ} (j : Fin m) (M : Mat m) (d : ℕ)
    (hd : 0 < d) (hM : matrixDegree j M = d) :
    ∃ r c k, (M r c).coeff k ≠ 0 ∧ Int.natAbs (k j) = d := by
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun r => Finset.univ.sup fun c => degVar j (M r c))
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun c => degVar j (M r c))
  have hrc : degVar j (M r c) = d := hc.symm.trans (hr.symm.trans hM)
  have hs : (M r c).coeff.support.Nonempty := by
    by_contra he
    have he' := Finset.not_nonempty_iff_eq_empty.mp he
    simp [degVar, he'] at hrc
    omega
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup _ hs (fun k => Int.natAbs (k j))
  exact ⟨r, c, k, Finsupp.mem_support_iff.mp hk, he.symm.trans hrc⟩

private lemma coeff_C_mul {m : ℕ} (c : ℂ) (P : MLaurent m) (k : ExpVec m) :
    (C' c * P).coeff k = c * P.coeff k := by
  simp [C', AddMonoidAlgebra.coeff_single_mul_apply]

private lemma coeff_mul_C {m : ℕ} (c : ℂ) (P : MLaurent m) (k : ExpVec m) :
    (P * C' c).coeff k = P.coeff k * c := by
  simp [C', AddMonoidAlgebra.coeff_mul_single_apply]

private lemma inv_exponent {m : ℕ} (j : Fin m) :
    (Pi.single j (-1 : ℤ) : ExpVec m) = -(Pi.single j (1 : ℤ)) := by
  ext i
  by_cases h : i = j <;> simp [h]

private lemma coeff_mul_var {m : ℕ} (j : Fin m) (P : MLaurent m) (k : ExpVec m) :
    (P * var j).coeff k = P.coeff (k - Pi.single j (1 : ℤ)) := by
  simp [var, mono, AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

private lemma coeff_mul_varInv {m : ℕ} (j : Fin m) (P : MLaurent m) (k : ExpVec m) :
    (P * varInv j).coeff k = P.coeff (k + Pi.single j (1 : ℤ)) := by
  simp [varInv, mono, AddMonoidAlgebra.coeff_mul_single_apply, inv_exponent]

private lemma append_coeff_zero {m : ℕ} (M : Mat m) (j : Fin m) (θ : ℝ)
    (r : Fin 2) (k : ExpVec m) :
    (((M * signalOp j * phaseOp θ) : Mat m) r 0).coeff k =
      Complex.exp (Complex.I * (θ : ℂ)) / 2 *
        ((M r 0).coeff (k - Pi.single j (1 : ℤ)) +
          (M r 1).coeff (k - Pi.single j (1 : ℤ)) +
          (M r 0).coeff (k + Pi.single j (1 : ℤ)) -
          (M r 1).coeff (k + Pi.single j (1 : ℤ))) := by
  have he : (M * signalOp j * phaseOp θ : Mat m) r 0 =
      C' (Complex.exp (Complex.I * (θ : ℂ)) / 2) *
        (M r 0 * (var j + varInv j) + M r 1 * (var j - varInv j)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, signalOp, phaseOp,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (M r 0 * (var j + varInv j) + M r 1 * (var j - varInv j)) *
      Lemma7.half_mul_exp (m := m) θ
  rw [he, coeff_C_mul]
  simp only [mul_add, mul_sub, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply,
    coeff_mul_var, coeff_mul_varInv]
  ring

private lemma append_coeff_one {m : ℕ} (M : Mat m) (j : Fin m) (θ : ℝ)
    (r : Fin 2) (k : ExpVec m) :
    (((M * signalOp j * phaseOp θ) : Mat m) r 1).coeff k =
      Complex.exp (-(Complex.I * (θ : ℂ))) / 2 *
        ((M r 0).coeff (k - Pi.single j (1 : ℤ)) +
          (M r 1).coeff (k - Pi.single j (1 : ℤ)) -
          (M r 0).coeff (k + Pi.single j (1 : ℤ)) +
          (M r 1).coeff (k + Pi.single j (1 : ℤ))) := by
  have he : (M * signalOp j * phaseOp θ : Mat m) r 1 =
      C' (Complex.exp (-(Complex.I * (θ : ℂ))) / 2) *
        (M r 0 * (var j - varInv j) + M r 1 * (var j + varInv j)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, signalOp, phaseOp,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (M r 0 * (var j - varInv j) + M r 1 * (var j + varInv j)) *
      Lemma7.half_mul_exp_neg (m := m) θ
  rw [he, coeff_C_mul]
  simp only [mul_add, mul_sub, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply,
    coeff_mul_var, coeff_mul_varInv]
  ring

private def Pure {m : ℕ} (M : Mat m) (c : ℂ) : Prop :=
  ∀ r b, starL (M r b) = c • M r b

private lemma pure_coeff {m : ℕ} {M : Mat m} {c : ℂ} (h : Pure M c)
    (r b : Fin 2) (k : ExpVec m) :
    (starRingEnd ℂ) ((M r b).coeff k) = c * (M r b).coeff k := by
  have he := congrArg (fun P : MLaurent m => P.coeff k) (h r b)
  exact he

private lemma pure_mul {m : ℕ} {M N : Mat m} {c d : ℂ}
    (hM : Pure M c) (hN : Pure N d) : Pure (M * N) (c * d) := by
  intro r b
  change ∀ r b, starL (M r b) = c • M r b at hM
  change ∀ r b, starL (N r b) = d • N r b at hN
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Lemma7.starL_add, Lemma7.starL_mul,
    hM, hN, smul_mul_smul, ← smul_add]

private lemma pure_signalInv {m : ℕ} (j : Fin m) : Pure (Lemma7.signalOpInv j) 1 := by
  intro r c
  fin_cases r <;> fin_cases c <;>
    norm_num [Lemma7.signalOpInv, Lemma7.starL_mul, Lemma7.starL_add,
      sub_eq_add_neg, Lemma7.starL_neg, Lemma7.starL_C', Lemma7.starL_var,
      Lemma7.starL_varInv, Lemma7.conjC, map_ofNat]

private def word {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) : Mat m :=
  phaseOp θ * factors L

private lemma word_append {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) (p : Fin m × ℝ) :
    word θ (L ++ [p]) = word θ L * signalOp p.1 * phaseOp p.2 := by
  simp [word, factors, mul_assoc]

private lemma matrixDegree_word_le {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ))
    (j : Fin m) : matrixDegree j (word θ L) ≤ occurrences j L := by
  have h := matrixDegree_mul_le j (phaseOp θ) (factors L)
  rw [matrixDegree_phase, zero_add] at h
  exact h.trans (matrixDegree_factors_le j L)

private def RealForm {m : ℕ} (M : Mat m) : Prop :=
  ∀ r c, starL (M r c) = M r.rev c.rev

private lemma realForm_mul {m : ℕ} {M N : Mat m} (hM : RealForm M)
    (hN : RealForm N) : RealForm (M * N) := by
  change ∀ r c, starL (M r c) = M r.rev c.rev at hM
  change ∀ r c, starL (N r c) = N r.rev c.rev at hN
  intro r c
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Lemma7.starL_add,
    Lemma7.starL_mul, hM, hN]
  simp [add_comm]

private lemma realForm_signal {m : ℕ} (j : Fin m) : RealForm (signalOp j) := by
  intro r c
  fin_cases r <;> fin_cases c <;>
    norm_num [signalOp, Lemma7.starL_mul, Lemma7.starL_add, sub_eq_add_neg,
      Lemma7.starL_neg, Lemma7.starL_C', Lemma7.starL_var, Lemma7.starL_varInv,
      Lemma7.conjC, map_ofNat]

private lemma realForm_phase {m : ℕ} (θ : ℝ) : RealForm (phaseOp θ : Mat m) := by
  intro r c
  fin_cases r <;> fin_cases c
  · change starL (C' (Complex.exp (Complex.I * (θ : ℂ)))) = _
    rw [Lemma7.starL_C', Lemma8.conjC_exp]
    rfl
  · change starL (0 : MLaurent m) = 0
    rw [Lemma7.starL_eq, map_zero]
  · change starL (0 : MLaurent m) = 0
    rw [Lemma7.starL_eq, map_zero]
  · change starL (C' (Complex.exp (-(Complex.I * (θ : ℂ))))) =
      C' (Complex.exp (Complex.I * (θ : ℂ)))
    have h := Lemma8.conjC_exp (-θ)
    simp only [Complex.ofReal_neg, mul_neg, neg_neg] at h
    rw [Lemma7.starL_C', h]

private lemma realForm_factors {m : ℕ} (L : List (Fin m × ℝ)) :
    RealForm (factors L) := by
  induction L with
  | nil =>
    intro r c
    fin_cases r <;> fin_cases c <;>
      simp [factors, Lemma7.starL_eq]
  | cons p L ih =>
    exact realForm_mul (realForm_mul (realForm_signal p.1) (realForm_phase p.2)) ih

private lemma realForm_word {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) :
    RealForm (word θ L) :=
  realForm_mul (realForm_phase θ) (realForm_factors L)

private def doublePhase (θ : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ))

private lemma doublePhase_mul_neg (θ : ℝ) :
    doublePhase θ * Complex.exp (-(Complex.I * (θ : ℂ))) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [doublePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ratio_real {p q c a : ℂ} (hc : c ≠ 0) (hq : q ≠ 0)
    (hp : (starRingEnd ℂ) p = c * p) (hqc : (starRingEnd ℂ) q = c * q)
    (ha : p = a * q) : (starRingEnd ℂ) a = a := by
  have he := congrArg (starRingEnd ℂ) ha
  rw [map_mul, hp, hqc, ha] at he
  have hz : ((starRingEnd ℂ) a - a) * (c * q) = 0 := by
    linear_combination -he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (mul_ne_zero hc hq))

private lemma angle_of_doublePhase_real (θ : ℝ)
    (h : (starRingEnd ℂ) (doublePhase θ) = doublePhase θ) :
    ∃ z : ℤ, θ = (z : ℝ) * (Real.pi / 2) := by
  have hi := congrArg Complex.im h
  have hz : (doublePhase θ).im = 0 := by
    simp only [Complex.conj_im] at hi
    linear_combination -hi / 2
  have he : Complex.I * ((2 * θ : ℝ) : ℂ) = ((2 * θ : ℝ) : ℂ) * Complex.I := mul_comm _ _
  have hs : Real.sin (2 * θ) = 0 := by
    simpa only [doublePhase, he, Complex.exp_ofReal_mul_I_im] using hz
  obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hs
  exact ⟨z, by linarith⟩

private lemma smul_C {m : ℕ} (a b : ℂ) : a • (C' b : MLaurent m) = C' (a * b) := by
  rw [← Lemma3.C'_smul, Lemma3.C'_mul_C']

private lemma pure_phase_neg {m : ℕ} (θ : ℝ)
    (h : (starRingEnd ℂ) (doublePhase θ) = doublePhase θ) :
    Pure (phaseOp (-θ) : Mat m) (doublePhase θ) := by
  have hr : doublePhase θ = Complex.exp (-(Complex.I * ((2 * θ : ℝ) : ℂ))) := by
    exact h.symm.trans (Lemma8.conjC_exp (2 * θ))
  have hm : doublePhase θ * Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (-(Complex.I * (θ : ℂ))) := by
    rw [hr, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  intro r b
  fin_cases r <;> fin_cases b
  · change starL (C' (Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)))) =
      doublePhase θ • C' (Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)))
    rw [Lemma7.starL_C', Lemma8.conjC_exp, smul_C]
    simp only [Complex.ofReal_neg, mul_neg, neg_neg]
    rw [doublePhase_mul_neg]
  · change starL (0 : MLaurent m) = doublePhase θ • (0 : MLaurent m)
    rw [Lemma7.starL_eq, map_zero, smul_zero]
  · change starL (0 : MLaurent m) = doublePhase θ • (0 : MLaurent m)
    rw [Lemma7.starL_eq, map_zero, smul_zero]
  · change starL (C' (Complex.exp (-(Complex.I * ((-θ : ℝ) : ℂ))))) =
      doublePhase θ • C' (Complex.exp (-(Complex.I * ((-θ : ℝ) : ℂ))))
    simp only [Complex.ofReal_neg, mul_neg, neg_neg]
    rw [Lemma7.starL_C', Lemma8.conjC_exp, smul_C, hm]

private lemma prepend_coeff {m : ℕ} (M : Mat m) (j : Fin m)
    (b : Fin 2) (k : ExpVec m) :
    ((signalOp j * M) 0 b).coeff k = (1 / 2 : ℂ) *
      ((M 0 b).coeff (k - Pi.single j (1 : ℤ)) +
        (M 1 b).coeff (k - Pi.single j (1 : ℤ)) +
        (M 0 b).coeff (k + Pi.single j (1 : ℤ)) -
        (M 1 b).coeff (k + Pi.single j (1 : ℤ))) := by
  have he : (signalOp j * M) 0 b = C' (1 / 2) *
      (M 0 b * (var j + varInv j) + M 1 b * (var j - varInv j)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, signalOp,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [he, coeff_C_mul]
  simp only [mul_add, mul_sub, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply,
    coeff_mul_var, coeff_mul_varInv]
  ring

private lemma sandwich_relations {m : ℕ} (M : Mat m) (j : Fin m) (θ : ℝ)
    (hM : matrixDegree j M = 0)
    (hP : degVar j ((signalOp j * M * signalOp j * phaseOp θ : Mat m) 0 0) = 0) :
    M 1 1 = -M 0 0 ∧ M 1 0 = -M 0 1 := by
  have hcoef : ∀ r b k, k j ≠ 0 → (M r b).coeff k = 0 := by
    intro r b k hk
    apply coeff_zero_of_degree_lt j
    have hb := entry_degree_le j M r b
    rw [hM] at hb
    have hk' : 0 < Int.natAbs (k j) := Int.natAbs_pos.mpr hk
    omega
  have hs : ∀ k, (M 0 0).coeff k + (M 1 1).coeff k = 0 ∧
      (M 0 1).coeff k + (M 1 0).coeff k = 0 := by
    intro k
    by_cases hk : k j = 0
    · let e : ExpVec m := Pi.single j (1 : ℤ)
      have he : e j = 1 := Pi.single_eq_same j 1
      have hzplus : ∀ r b, (M r b).coeff (k + e + e) = 0 := by
        intro r b
        apply hcoef
        simp [Pi.add_apply, hk, he]
      have hzplus' : ∀ r b, (M r b).coeff (k + e + e + e + e) = 0 := by
        intro r b
        apply hcoef
        simp [Pi.add_apply, hk, he]
      have hzminus : ∀ r b, (M r b).coeff (k - e - e) = 0 := by
        intro r b
        apply hcoef
        simp [Pi.sub_apply, hk, he]
      have hzminus' : ∀ r b, (M r b).coeff (k - e - e - e - e) = 0 := by
        intro r b
        apply hcoef
        simp [Pi.sub_apply, hk, he]
      have hplus := append_coeff_zero (signalOp j * M) j θ 0 (k + e + e)
      have hminus := append_coeff_zero (signalOp j * M) j θ 0 (k - e - e)
      have hpz : ((signalOp j * M * signalOp j * phaseOp θ : Mat m) 0 0).coeff
          (k + e + e) = 0 := by
        apply coeff_zero_of_degree_lt j
        rw [hP]
        simp [Pi.add_apply, hk, he]
      have hmz : ((signalOp j * M * signalOp j * phaseOp θ : Mat m) 0 0).coeff
          (k - e - e) = 0 := by
        apply coeff_zero_of_degree_lt j
        rw [hP]
        simp [Pi.sub_apply, hk, he]
      rw [hpz] at hplus
      rw [hmz] at hminus
      simp only [prepend_coeff, ← show e = Pi.single j (1 : ℤ) from rfl,
        add_sub_cancel_right, sub_add_cancel, hzplus, hzplus', hzminus, hzminus']
        at hplus hminus
      have he0 : Complex.exp (Complex.I * (θ : ℂ)) / 2 ≠ 0 :=
        div_ne_zero (Complex.exp_ne_zero _) (by norm_num)
      have hplus' := (mul_eq_zero.mp hplus.symm).resolve_left he0
      have hminus' := (mul_eq_zero.mp hminus.symm).resolve_left he0
      constructor
      · linear_combination hplus' + hminus'
      · linear_combination hplus' - hminus'
    · simp [hcoef 0 0 k hk, hcoef 0 1 k hk, hcoef 1 0 k hk, hcoef 1 1 k hk]
  constructor
  · apply AddMonoidAlgebra.coeff_injective
    ext k
    simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] using
      (eq_neg_of_add_eq_zero_right (hs k).1)
  · apply AddMonoidAlgebra.coeff_injective
    ext k
    simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] using
      (eq_neg_of_add_eq_zero_right (hs k).2)

private lemma sandwich_cancel {m : ℕ} (M : Mat m) (j : Fin m)
    (h : M 1 1 = -M 0 0 ∧ M 1 0 = -M 0 1) :
    signalOp j * M * signalOp j = M := by
  have he : signalOp j * M = M * Lemma7.signalOpInv j := by
    apply Matrix.ext
    intro r b
    fin_cases r <;> fin_cases b <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, signalOp, Lemma7.signalOpInv,
        h.1, h.2] <;> ring
  rw [he, mul_assoc, Lemma7.inv_mul_signalOp, mul_one]

private lemma pure_of_relations {m : ℕ} (M : Mat m) (hM : RealForm M)
    (h : M 1 1 = -M 0 0 ∧ M 1 0 = -M 0 1) : Pure M (-1) := by
  intro r b
  rw [hM r b]
  fin_cases r <;> fin_cases b <;> simp [h.1, h.2]

private lemma word_saturation {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ))
    (h : degTotal (word θ L 0 0) = L.length) :
    ∀ j, matrixDegree j (word θ L) = occurrences j L := by
  have hb : ∀ j, degVar j (word θ L 0 0) ≤ occurrences j L :=
    fun j => (entry_degree_le j _ 0 0).trans (matrixDegree_word_le θ L j)
  have he : ∀ j, degVar j (word θ L 0 0) = occurrences j L := by
    intro j
    by_contra hn
    have hs := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => hb i)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hb j) hn⟩
    rw [occurrences_sum] at hs
    change degTotal (word θ L 0 0) < L.length at hs
    omega
  intro j
  exact le_antisymm (matrixDegree_word_le θ L j)
    ((he j).symm.trans_le (entry_degree_le j _ 0 0))

private lemma saturated_last_angle {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ))
    (p : Fin m × ℝ) (c : ℂ) (hc : c ≠ 0)
    (hp : Pure (word θ (L ++ [p])) c)
    (hd : matrixDegree p.1 (word θ (L ++ [p])) = occurrences p.1 (L ++ [p])) :
    (starRingEnd ℂ) (doublePhase p.2) = doublePhase p.2 := by
  have ho : occurrences p.1 (L ++ [p]) = occurrences p.1 L + 1 := by
    simp [occurrences]
  obtain ⟨r, b, k, hk, hkd⟩ := matrixDegree_witness p.1 (word θ (L ++ [p]))
    (occurrences p.1 L + 1) (by omega) (hd.trans ho)
  have hb := matrixDegree_word_le θ L p.1
  have hbound : ∀ a : Fin 2, degVar p.1 (word θ L r a) ≤ occurrences p.1 L :=
    fun a => (entry_degree_le p.1 _ r a).trans hb
  have hpos : k p.1 = (occurrences p.1 L : ℤ) + 1 ∨
      k p.1 = -((occurrences p.1 L : ℤ) + 1) := by
    omega
  have he : ∃ a : ℂ, (starRingEnd ℂ) a = a ∧
      (word θ (L ++ [p]) r 0).coeff k =
        (a * doublePhase p.2) * (word θ (L ++ [p]) r 1).coeff k ∧ a ≠ 0 := by
    rcases hpos with hpos | hneg
    · have hz : ∀ a : Fin 2,
          (word θ L r a).coeff (k + Pi.single p.1 (1 : ℤ)) = 0 := by
        intro a
        apply coeff_zero_of_degree_lt p.1
        simp only [Pi.add_apply, Pi.single_eq_same]
        have hba := hbound a
        omega
      refine ⟨1, by simp, ?_, one_ne_zero⟩
      rw [word_append, append_coeff_zero, append_coeff_one, hz 0, hz 1]
      simp only [add_zero, sub_zero, one_mul, div_eq_mul_inv, ← mul_assoc]
      rw [doublePhase_mul_neg]
    · have hz : ∀ a : Fin 2,
          (word θ L r a).coeff (k - Pi.single p.1 (1 : ℤ)) = 0 := by
        intro a
        apply coeff_zero_of_degree_lt p.1
        simp only [Pi.sub_apply, Pi.single_eq_same]
        have hba := hbound a
        omega
      refine ⟨-1, by simp, ?_, neg_ne_zero.mpr one_ne_zero⟩
      rw [word_append, append_coeff_zero, append_coeff_one, hz 0, hz 1]
      have hx := doublePhase_mul_neg p.2
      linear_combination
        -((word θ L r 0).coeff (k + Pi.single p.1 (1 : ℤ)) -
          (word θ L r 1).coeff (k + Pi.single p.1 (1 : ℤ))) / 2 * hx
  obtain ⟨a, ha, he, ha0⟩ := he
  have hq : (word θ (L ++ [p]) r 1).coeff k ≠ 0 := by
    intro hq
    have hp0 : (word θ (L ++ [p]) r 0).coeff k = 0 := by rw [he, hq, mul_zero]
    fin_cases b <;> simp_all
  have hr := ratio_real hc hq (pure_coeff hp r 0 k) (pure_coeff hp r 1 k) he
  rw [map_mul, ha] at hr
  exact mul_left_cancel₀ ha0 hr

private lemma pure_word_angles {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ))
    (c : ℂ) (hc : c ≠ 0) (hp : Pure (word θ L) c)
    (hd : ∀ j, matrixDegree j (word θ L) = occurrences j L) :
    (∃ z : ℤ, θ = (z : ℝ) * (Real.pi / 2)) ∧
      ∀ p ∈ L, ∃ z : ℤ, p.2 = (z : ℝ) * (Real.pi / 2) := by
  induction L using List.reverseRecOn generalizing c with
  | nil =>
    have hp' : Pure (phaseOp θ : Mat m) c := by simpa [word, factors] using hp
    have h0' : (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ))) =
        c * Complex.exp (Complex.I * (θ : ℂ)) := by
      simpa [phaseOp, C'] using pure_coeff hp' 0 0 0
    have h1' : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (θ : ℂ)))) =
        c * Complex.exp (-(Complex.I * (θ : ℂ))) := by
      simpa [phaseOp, C'] using pure_coeff hp' 1 1 0
    exact ⟨angle_of_doublePhase_real θ
      (ratio_real hc (Complex.exp_ne_zero _) h0' h1' (doublePhase_mul_neg θ).symm),
      by simp⟩
  | append_singleton L p ih =>
    have ha := saturated_last_angle θ L p c hc hp (hd p.1)
    have hpeel : word θ L = word θ (L ++ [p]) * phaseOp (-p.2) *
        Lemma7.signalOpInv p.1 := by
      rw [word_append, mul_assoc (word θ L * signalOp p.1),
        Lemma7.phaseOp_mul_neg, mul_one, mul_assoc, Lemma7.signalOp_mul_inv, mul_one]
    have hp' : Pure (word θ L) (c * doublePhase p.2) := by
      rw [hpeel]
      simpa using pure_mul (pure_mul hp (pure_phase_neg p.2 ha)) (pure_signalInv p.1)
    have hd' : ∀ j, matrixDegree j (word θ L) = occurrences j L := by
      intro j
      have hb := matrixDegree_mul_le j (word θ L * signalOp p.1) (phaseOp p.2)
      have hb' := matrixDegree_mul_le j (word θ L) (signalOp p.1)
      rw [← word_append, hd, matrixDegree_phase, add_zero] at hb
      have hs := matrixDegree_signal j p.1
      have ho : occurrences j (L ++ [p]) = occurrences j L +
          (if j = p.1 then 1 else 0) := by simp [occurrences]
      have hu := matrixDegree_word_le θ L j
      omega
    obtain ⟨hθ, hL⟩ := ih (c * doublePhase p.2)
      (mul_ne_zero hc (Complex.exp_ne_zero _)) hp' hd'
    refine ⟨hθ, ?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hL q hq
    · simpa only [List.mem_singleton.mp hq] using angle_of_doublePhase_real p.2 ha

private lemma word_form {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) :
    word θ L = !![word θ L 0 0, word θ L 0 1;
      -starOp (word θ L 0 1), starOp (word θ L 0 0)] := by
  induction L using List.reverseRecOn with
  | nil =>
    simpa [word, factors, phaseOp] using (Lemma8.phaseOp_form (m := m) θ)
  | append_singleton L p ih =>
    have he : word θ (L ++ [p]) =
        Lemma7.appendWord (word θ L 0 0) (word θ L 0 1) p.1 p.2 := by
      rw [word_append]
      conv_lhs => lhs; lhs; rw [ih]
      rfl
    have hf := Lemma7.append_form (word θ L 0 0) (word θ L 0 1) p.1 p.2
    apply Matrix.ext
    intro r b
    fin_cases r <;> fin_cases b
    · rfl
    · rfl
    · simpa [he] using hf.1
    · simpa [he] using hf.2

private lemma word_phase_realization {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) (ψ : ℝ) :
    ∃ (φ : Fin (L.length + 1) → ℝ) (s : Fin L.length → Fin m),
      wordMatrix L.length φ s = word θ L * phaseOp ψ := by
  induction L using List.reverseRecOn generalizing ψ with
  | nil =>
    refine ⟨fun _ => θ + ψ, Fin.elim0, ?_⟩
    simp [wordMatrix, word, factors, Lemma3.phaseOp_mul]
  | append_singleton L p ih =>
    obtain ⟨φ, s, hw⟩ := ih 0
    simp only [Lemma3.phaseOp_zero, mul_one] at hw
    have he : (L ++ [p]).length = L.length + 1 := by simp
    rw [he]
    refine ⟨Fin.snoc φ (p.2 + ψ), Fin.snoc s p.1, ?_⟩
    rw [Lemma7.wordMatrix_append, hw, word_append, ← Lemma3.phaseOp_mul]
    simp only [mul_assoc]

private lemma constructible_word_phase {m : ℕ} (θ : ℝ) (L : List (Fin m × ℝ)) (ψ : ℝ) :
    Constructible L.length ((word θ L * phaseOp ψ : Mat m) 0 0)
      ((word θ L * phaseOp ψ : Mat m) 0 1) := by
  have hf : ∀ ψ : ℝ, word θ L * phaseOp ψ =
      !![(word θ L * phaseOp ψ : Mat m) 0 0, (word θ L * phaseOp ψ : Mat m) 0 1;
        -starOp ((word θ L * phaseOp ψ : Mat m) 0 1),
        starOp ((word θ L * phaseOp ψ : Mat m) 0 0)] := by
    intro ψ
    induction L using List.reverseRecOn with
    | nil =>
      simpa [word, factors, Lemma3.phaseOp_mul] using
        (word_form (m := m) (θ + ψ) [])
    | append_singleton L p _ =>
      have he : word θ (L ++ [p]) * phaseOp ψ =
          Lemma7.appendWord (word θ L 0 0) (word θ L 0 1) p.1 (p.2 + ψ) := by
        rw [word_append, mul_assoc, Lemma3.phaseOp_mul]
        conv_lhs => lhs; lhs; rw [word_form θ L]
        rfl
      have hf := Lemma7.append_form (word θ L 0 0) (word θ L 0 1) p.1 (p.2 + ψ)
      apply Matrix.ext
      intro r b
      fin_cases r <;> fin_cases b
      · rfl
      · rfl
      · simpa [he] using hf.1
      · simpa [he] using hf.2
  obtain ⟨φ, s, hw⟩ := word_phase_realization θ L ψ
  exact ⟨φ, s, hw.trans (hf ψ)⟩

/-- Lemma 2 (Eqs. (18)--(19)): intermediate phase angles lie in `(π / 2) ℤ` and
`(prefixP, prefixQ)` is constructible in `l - 2` steps. -/
theorem lemma2_angle_integrality {m l : ℕ} (hl : 2 ≤ l)
    (φ : Fin l → ℝ) (s : Fin l → Fin m)
    (h1 : s ⟨0, by omega⟩ = s ⟨l - 1, by omega⟩)
    (h2 : ∀ k : Fin l, 1 ≤ k.1 → k.1 ≤ l - 2 → s k ≠ s ⟨l - 1, by omega⟩)
    (h3 : degTotal (prefixP l φ s (l - 1) (by omega)) = l - 1)
    (h4 : degVar (s ⟨l - 1, by omega⟩) (prefixP l φ s l le_rfl) = 0) :
    (∀ k : Fin l, k.1 ≤ l - 2 →
        ∃ z : ℤ, φ k = (z : ℝ) * (Real.pi / 2)) ∧
      Constructible (l - 2) (prefixP l φ s l le_rfl) (prefixQ l φ s l le_rfl) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  have hn1 : n + 2 - 1 = n + 1 := by omega
  have hn2 : n + 2 - 2 = n := by omega
  simp only [hn1, hn2] at h1 h2 h3 h4 ⊢
  let j : Fin m := s ⟨n + 1, by omega⟩
  let θ : ℝ := φ ⟨0, by omega⟩
  let ψ : ℝ := φ ⟨n + 1, by omega⟩
  let L : List (Fin m × ℝ) := List.ofFn fun k : Fin n =>
    (s ⟨k.1 + 1, by omega⟩, φ ⟨k.1 + 1, by omega⟩)
  have hj : s ⟨0, by omega⟩ = j := by simpa [j] using h1
  have hlen : L.length = n := List.length_ofFn
  have hpre : prefixMatrix (n + 2) φ s (n + 1) (by omega) =
      signalOp j * word θ L := by
    simp only [prefixMatrix, List.ofFn_succ, List.prod_cons]
    dsimp only [word, factors, L, θ]
    rw [List.map_ofFn, ← mul_assoc, ← hj]
    rfl
  have hfull : prefixMatrix (n + 2) φ s (n + 2) le_rfl =
      signalOp j * word θ L * signalOp j * phaseOp ψ := by
    unfold prefixMatrix
    rw [List.ofFn_succ', List.prod_concat]
    change prefixMatrix (n + 2) φ s (n + 1) (by omega) *
      (signalOp j * phaseOp ψ) = _
    rw [hpre, ← mul_assoc]
  have hocc : occurrences j L = 0 := by
    simp only [occurrences, L, List.map_ofFn]
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    have hkn := k.isLt
    change (if j = s ⟨k.1 + 1, by omega⟩ then 1 else 0) = 0
    have hk : j ≠ s ⟨k.1 + 1, by omega⟩ :=
      Ne.symm (h2 ⟨k.1 + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega))
    simp [hk]
  have hfree : matrixDegree j (word θ L) = 0 :=
    Nat.eq_zero_of_le_zero ((matrixDegree_word_le θ L j).trans_eq hocc)
  have hP : degVar j ((signalOp j * word θ L * signalOp j * phaseOp ψ : Mat m) 0 0) = 0 := by
    simpa only [prefixP, hfull, j] using h4
  have hrel := sandwich_relations (word θ L) j ψ hfree hP
  have hpure := pure_of_relations (word θ L) (realForm_word θ L) hrel
  have hzero : word 0 ((j, θ) :: L) = signalOp j * word θ L := by
    simp [word, factors, Lemma3.phaseOp_zero, mul_assoc]
  have hdeg : degTotal (word 0 ((j, θ) :: L) 0 0) = ((j, θ) :: L).length := by
    simpa only [prefixP, hpre, ← hzero, List.length_cons, hlen,
      Nat.add_sub_cancel] using h3
  have hsat := word_saturation 0 ((j, θ) :: L) hdeg
  have hmid : ∀ i, matrixDegree i (word θ L) = occurrences i L := by
    intro i
    have hb := matrixDegree_mul_le i (signalOp j) (word θ L)
    rw [← hzero, hsat] at hb
    have hs := matrixDegree_signal i j
    have hu := matrixDegree_word_le θ L i
    have ho : occurrences i ((j, θ) :: L) =
        (if i = j then 1 else 0) + occurrences i L := rfl
    omega
  obtain ⟨hθ, hangles⟩ := pure_word_angles θ L (-1) (by norm_num) hpure hmid
  constructor
  · intro k hk
    by_cases hk0 : k.1 = 0
    · have he : k = ⟨0, by omega⟩ := Fin.ext hk0
      simpa only [he, θ] using hθ
    · have hkn : k.1 - 1 < n := by omega
      have hmem : (s k, φ k) ∈ L := by
        apply List.mem_ofFn.mpr
        refine ⟨⟨k.1 - 1, hkn⟩, ?_⟩
        have he : (⟨k.1 - 1 + 1, by omega⟩ : Fin (n + 2)) = k := Fin.ext (by dsimp; omega)
        dsimp only
        rw [he]
      exact hangles (s k, φ k) hmem
  · have hcancel := sandwich_cancel (word θ L) j hrel
    have he : prefixMatrix (n + 2) φ s (n + 2) le_rfl = word θ L * phaseOp ψ := by
      rw [hfull, hcancel]
    simpa only [prefixP, prefixQ, he, Nat.add_sub_cancel, hlen] using
      constructible_word_phase θ L ψ

end Qatlib.Papers.QSPIto26.MainResults.Lemma2
