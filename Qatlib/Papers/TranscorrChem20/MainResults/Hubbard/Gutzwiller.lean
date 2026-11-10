/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Matrix NormedSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical

namespace Qatlib.Papers.TranscorrChem20.MainResults.Hubbard

def mode {N : ℕ} (i : Fin N) (σ : Bool) : Fin (2*N) :=
  ⟨2*i.val + if σ then 1 else 0, by cases σ <;> simp; all_goals omega⟩

theorem mode_eq {N : ℕ} (i j : Fin N) (σ τ : Bool) :
    mode i σ = mode j τ ↔ i=j ∧ σ=τ := by
  cases σ <;> cases τ <;> simp [mode, Fin.ext_iff] <;> omega

theorem mode_site_ne {N : ℕ} {i j : Fin N} (h : i ≠ j) (σ τ : Bool) :
    mode i σ ≠ mode j τ := fun hEq => h ((mode_eq i j σ τ).mp hEq).1

theorem mode_other_ne {N : ℕ} (i : Fin N) (σ : Bool) :
    mode i (!σ) ≠ mode i σ := by
  intro h
  have hspin := ((mode_eq i i (!σ) σ).mp h).2
  cases σ <;> simp_all

def occ (b : Bool) : ℂ := if b then 1 else 0

noncomputable def doubleCount {N : ℕ} (x : Reg (2*N)) : ℂ :=
  ∑ i : Fin N, occ (x (mode i false)) * occ (x (mode i true))

theorem doubleCount_update {N : ℕ} (x : Reg (2*N)) (i : Fin N) (σ b : Bool) :
    doubleCount (Function.update x (mode i σ) b) = doubleCount x +
      (occ b - occ (x (mode i σ))) * occ (x (mode i (!σ))) := by
  have hd : doubleCount (Function.update x (mode i σ) b) - doubleCount x =
      (occ b - occ (x (mode i σ))) * occ (x (mode i (!σ))) := by
    unfold doubleCount
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · cases σ <;>
        simp [mode_eq] <;> ring
    · intro j _ hji
      simp [Function.update_of_ne (mode_site_ne hji false σ),
        Function.update_of_ne (mode_site_ne hji true σ)]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  linear_combination hd

theorem hop_support {m : ℕ} (a b : Fin m) (hab : a ≠ b) (y x : Reg m)
    (h : (creation a * annihilation b) y x ≠ 0) :
    x b = true ∧ x a = false ∧
      y = Function.update (Function.update x b false) a true := by
  rw [Matrix.mul_apply] at h
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ha := (mul_ne_zero_iff.mp hz).2
  have hc := (mul_ne_zero_iff.mp hz).1
  rw [ann_apply] at ha
  rw [cre_apply] at hc
  split_ifs at ha with hax
  · rcases hax with ⟨hxb, rfl⟩
    split_ifs at hc with hcx
    · refine ⟨hxb, ?_, hcx.2⟩
      simpa only [Function.update_of_ne hab, Bool.not_eq_true] using! hcx.1
    · exact (hc rfl).elim
  · exact (ha rfl).elim

noncomputable def doubleOp (N : ℕ) : Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  ∑ i : Fin N, numberOp (mode i false) * numberOp (mode i true)

noncomputable def hop {N : ℕ} (i j : Fin N) (σ : Bool) : Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  creation (mode i σ) * annihilation (mode j σ)

noncomputable def qOp {N : ℕ} (i j : Fin N) (σ : Bool) : Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  numberOp (mode j (!σ)) - numberOp (mode i (!σ))

theorem hop_doubleCount {N : ℕ} (i j : Fin N) (hij : i ≠ j) (σ : Bool)
    (y x : Reg (2*N)) (h : hop i j σ y x ≠ 0) :
    doubleCount y = doubleCount x + occ (x (mode i (!σ))) - occ (x (mode j (!σ))) := by
  obtain ⟨hxb, hxa, rfl⟩ := hop_support (mode i σ) (mode j σ) (mode_site_ne hij σ σ) y x h
  rw [doubleCount_update, doubleCount_update]
  simp only [Function.update_of_ne (mode_site_ne hij σ σ),
    Function.update_of_ne (mode_site_ne hij (!σ) σ), hxa, hxb, occ,
    Bool.false_eq_true, if_false, if_true, zero_sub, sub_zero]
  ring

theorem number_diagonal {m : ℕ} (a : Fin m) :
    numberOp a = diagonal (fun x => occ (x a)) := by
  ext y x
  by_cases h : y=x
  · subst y
    simp [num_apply, occ]
  · simp [num_apply, h, Ne.symm h]

theorem doubleOp_diagonal (N : ℕ) : doubleOp N = diagonal (fun x => doubleCount x) := by
  simp only [doubleOp, number_diagonal, Matrix.diagonal_mul_diagonal]
  ext y x
  by_cases h : y=x
  · subst y
    simp [doubleCount, Matrix.sum_apply]
  · simp [Matrix.sum_apply, h]

theorem qOp_diagonal {N : ℕ} (i j : Fin N) (σ : Bool) :
    qOp i j σ = diagonal (fun x => occ (x (mode j (!σ))) - occ (x (mode i (!σ)))) := by
  simp only [qOp, number_diagonal, ← Matrix.diagonal_sub]

theorem actual_hop_semiconj {N : ℕ} (i j : Fin N) (hij : i ≠ j) (σ : Bool) :
    doubleOp N * hop i j σ = hop i j σ * (doubleOp N - qOp i j σ) := by
  rw [mul_sub, doubleOp_diagonal, qOp_diagonal]
  ext y x
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]
  by_cases h : hop i j σ y x = 0
  · simp [h]
  · rw [hop_doubleCount i j hij σ y x h]
    ring

theorem exp_scaled_diagonal {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℂ) (J : ℂ) :
    exp (J • diagonal v) = diagonal (fun x => Complex.exp (J * v x)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext x
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rfl

theorem actual_gutzwiller_hop {N : ℕ} (i j : Fin N) (hij : i ≠ j) (σ : Bool) (J : ℂ) :
    exp ((-J) • doubleOp N) * hop i j σ * exp (J • doubleOp N) =
      hop i j σ * exp (J • qOp i j σ) := by
  rw [doubleOp_diagonal, qOp_diagonal, exp_scaled_diagonal, exp_scaled_diagonal,
      exp_scaled_diagonal]
  ext y x
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : hop i j σ y x = 0
  · simp [h]
  · calc
      _ = hop i j σ y x * Complex.exp ((-J) * doubleCount y + J * doubleCount x) := by
        rw [Complex.exp_add]
        ring
      _ = _ := by
        congr 2
        rw [hop_doubleCount i j hij σ y x h]
        ring

noncomputable def correction {N : ℕ} (i j : Fin N) (σ : Bool) (J : ℂ) :
    Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  (Complex.exp J - 1) • numberOp (mode j (!σ)) +
  (Complex.exp (-J) - 1) • numberOp (mode i (!σ)) -
  (2 * (Complex.cosh J - 1)) • (numberOp (mode i (!σ)) * numberOp (mode j (!σ)))

theorem actual_q_exponential {N : ℕ} (i j : Fin N) (σ : Bool) (J : ℂ) :
    exp (J • qOp i j σ) = 1 + correction i j σ J := by
  rw [qOp_diagonal, exp_scaled_diagonal]
  simp only [correction, number_diagonal, Matrix.diagonal_mul_diagonal]
  ext y x
  by_cases h : y=x
  · subst y
    cases hi : x (mode i (!σ)) <;> cases hj : x (mode j (!σ)) <;>
      simp [occ, hi, hj, Complex.cosh]
    all_goals ring
  · simp [h]

theorem actual_gutzwiller_hop_expanded {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (σ : Bool) (J : ℂ) :
    exp ((-J) • doubleOp N) * hop i j σ * exp (J • doubleOp N) =
      hop i j σ + hop i j σ * correction i j σ J := by
  rw [actual_gutzwiller_hop i j hij σ J, actual_q_exponential, mul_add, mul_one]

theorem actual_gutzwiller_edge {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (σ : Bool) (J : ℂ) :
    exp ((-J) • doubleOp N) * (hop i j σ + hop j i σ) * exp (J • doubleOp N) =
      hop i j σ + hop j i σ +
        (hop i j σ * correction i j σ J + hop j i σ * correction j i σ J) := by
  rw [mul_add, add_mul, actual_gutzwiller_hop_expanded i j hij σ J,
    actual_gutzwiller_hop_expanded j i hij.symm σ J]
  abel

theorem correction_real {N : ℕ} (i j : Fin N) (σ : Bool) (J : ℝ) :
    correction i j σ (J : ℂ) =
      ((Real.exp J - 1 : ℝ) : ℂ) • numberOp (mode j (!σ)) +
      ((Real.exp (-J) - 1 : ℝ) : ℂ) • numberOp (mode i (!σ)) -
      ((2 * (Real.cosh J - 1) : ℝ) : ℂ) •
        (numberOp (mode i (!σ)) * numberOp (mode j (!σ))) := by
  simp only [correction, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_cosh, Complex.ofReal_neg]

theorem actual_gutzwiller_diagonal {N : ℕ} (v : Reg (2*N) → ℂ) (J : ℂ) :
    exp ((-J) • doubleOp N) * diagonal v * exp (J • doubleOp N) = diagonal v := by
  rw [doubleOp_diagonal, exp_scaled_diagonal, exp_scaled_diagonal]
  ext y x
  by_cases h : y=x
  · subst y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_apply_eq]
    calc
      _ = v x * Complex.exp ((-J) * doubleCount x + J * doubleCount x) := by
        rw [Complex.exp_add]
        ring
      _ = _ := by rw [show (-J) * doubleCount x + J * doubleCount x = 0 by ring]; simp
  · simp [Matrix.mul_diagonal, h]

theorem actual_gutzwiller_doubleOp (N : ℕ) (J : ℂ) :
    exp ((-J) • doubleOp N) * doubleOp N * exp (J • doubleOp N) = doubleOp N := by
  conv_lhs => arg 1; arg 2; rw [doubleOp_diagonal]
  rw [actual_gutzwiller_diagonal, doubleOp_diagonal]

noncomputable def hubbard {N e : ℕ} (src dst : Fin e → Fin N) (t U : ℂ) :
    Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  (-t) • (∑ a : Fin e, ∑ σ : Bool, (hop (src a) (dst a) σ + hop (dst a) (src a) σ)) +
    U • doubleOp N

noncomputable def hubbardCorrection {N e : ℕ} (src dst : Fin e → Fin N) (t J : ℂ) :
    Matrix (Reg (2*N)) (Reg (2*N)) ℂ :=
  (-t) • (∑ a : Fin e, ∑ σ : Bool,
    (hop (src a) (dst a) σ * correction (src a) (dst a) σ J +
    hop (dst a) (src a) σ * correction (dst a) (src a) σ J))

theorem actual_gutzwiller_hubbard {N e : ℕ} (src dst : Fin e → Fin N)
    (hedge : ∀ a, src a ≠ dst a) (t U J : ℂ) :
    exp ((-J) • doubleOp N) * hubbard src dst t U * exp (J • doubleOp N) =
      hubbard src dst t U + hubbardCorrection src dst t J := by
  have hs : exp ((-J) • doubleOp N) *
      (∑ a : Fin e, ∑ σ : Bool, (hop (src a) (dst a) σ + hop (dst a) (src a) σ)) *
      exp (J • doubleOp N) =
      ∑ a : Fin e, ∑ σ : Bool,
        ((hop (src a) (dst a) σ + hop (dst a) (src a) σ) +
          (hop (src a) (dst a) σ * correction (src a) (dst a) σ J +
           hop (dst a) (src a) σ * correction (dst a) (src a) σ J)) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro σ _
    exact actual_gutzwiller_edge (src a) (dst a) (hedge a) σ J
  unfold hubbard
  rw [mul_add, add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hs, actual_gutzwiller_doubleOp]
  unfold hubbardCorrection
  simp only [Finset.sum_add_distrib, smul_add]
  abel

end Qatlib.Papers.TranscorrChem20.MainResults.Hubbard
