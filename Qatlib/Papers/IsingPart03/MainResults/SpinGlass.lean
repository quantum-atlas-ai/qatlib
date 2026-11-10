/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def sgn (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn (0 : ZMod 2) = 1 := by simp [sgn]

@[simp] lemma sgn_one : sgn (1 : ZMod 2) = -1 := by rw [sgn]; exact if_neg (by decide)

lemma eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = ({0, 1} : Finset (ZMod 2)) := by decide
  have hx : x ∈ ({0, 1} : Finset (ZMod 2)) := by rw [← h]; exact Finset.mem_univ x
  simpa using hx

lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl
  · simp
  · simp
  · simp
  · have h : ((1 : ZMod 2) + 1) = 0 := by decide
    simp [sgn, h]

lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma sgn_natCast_mul (x : ZMod 2) (n : ℕ) : sgn ((n : ZMod 2) * x) = sgn x ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, sgn_add, ih, one_mul, pow_succ]

lemma natCast_val (x : ZMod 2) : ((x.val : ℕ) : ZMod 2) = x := by
  rcases eq_zero_or_one x with rfl | rfl <;> decide

lemma mul_self (x : ZMod 2) : x * x = x := by
  rcases eq_zero_or_one x with rfl | rfl <;> decide

lemma sum_zmod2 (g : ZMod 2 → ℂ) : (∑ x : ZMod 2, g x) = g 0 + g 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h, Finset.sum_pair (by decide)]

def incidence (ends : E → V × V) : Matrix V E (ZMod 2) :=
  fun v e => if (ends e).1 = v ∨ (ends e).2 = v then 1 else 0

def parity (ends : E → V × V) (b : E → ZMod 2) : V → ZMod 2 := (incidence ends).mulVec b

def suppCard (b : E → ZMod 2) : ℕ := ∑ e, (b e).val

def bDotW (b w : E → ZMod 2) : ZMod 2 := ∑ e, b e * w e

def alphaDotS (ends : E → V × V) (b : E → ZMod 2) (s : V → ZMod 2) : ZMod 2 :=
  ∑ v, parity ends b v * s v

def edgeSpinDot (ends : E → V × V) (b : E → ZMod 2) (s : V → ZMod 2) : ZMod 2 :=
  ∑ e, b e * (s (ends e).1 + s (ends e).2)

def edgeFactor (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2) (e : E) : ℂ :=
  sgn (w e + s (ends e).1 + s (ends e).2)

def boltzmann (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) (s : V → ZMod 2) : ℂ :=
  Θ * ∏ e, (1 + edgeFactor ends w s e * lam)

def partition (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) : ℂ :=
  ∑ s : V → ZMod 2, boltzmann ends w Θ lam s

omit [Fintype E] [DecidableEq E] in

lemma sum_incidence_mul (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (s : V → ZMod 2) (e : E) :
    (∑ v, incidence ends v e * s v) = s (ends e).1 + s (ends e).2 := by
  classical
  have happ : ∀ v, incidence ends v e * s v
      = (if v = (ends e).1 then s v else 0) + (if v = (ends e).2 then s v else 0) := by
    intro v
    by_cases h1 : v = (ends e).1
    · by_cases h2 : v = (ends e).2
      · exact absurd (h1.symm.trans h2) (hLoop e)
      · have h1' : (ends e).1 = v := h1.symm
        have hi : incidence ends v e = 1 := by simp [incidence, h1']
        rw [hi, if_pos h1, if_neg h2]; ring
    · by_cases h2 : v = (ends e).2
      · have h2' : (ends e).2 = v := h2.symm
        have hi : incidence ends v e = 1 := by simp [incidence, h2']
        rw [hi, if_neg h1, if_pos h2]; ring
      · have h1' : ¬ (ends e).1 = v := fun h => h1 h.symm
        have h2' : ¬ (ends e).2 = v := fun h => h2 h.symm
        have hi : incidence ends v e = 0 := by
          simp [incidence, h1', h2']
        rw [hi, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun v _ => happ v), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

omit [DecidableEq E] in

lemma edgeSpinDot_eq_alphaDotS (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (b : E → ZMod 2) (s : V → ZMod 2) :
    edgeSpinDot ends b s = alphaDotS ends b s := by
  classical
  have hstep : ∀ e : E, b e * (s (ends e).1 + s (ends e).2)
      = b e * (∑ v, incidence ends v e * s v) := by
    intro e; rw [sum_incidence_mul ends hLoop s e]
  calc edgeSpinDot ends b s
      = ∑ e, b e * (∑ v, incidence ends v e * s v) := by
          simp only [edgeSpinDot]
          exact Finset.sum_congr rfl (fun e _ => hstep e)
    _ = ∑ e, ∑ v, b e * (incidence ends v e * s v) := by
          simp [Finset.mul_sum]
    _ = ∑ v, ∑ e, b e * (incidence ends v e * s v) := Finset.sum_comm
    _ = ∑ v, (∑ e, incidence ends v e * b e) * s v := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun e _ => by ring)
    _ = alphaDotS ends b s := rfl

@[simp] lemma val_zero : (0 : ZMod 2).val = 0 := by decide

@[simp] lemma val_one : (1 : ZMod 2).val = 1 := by decide

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

lemma edgeFactor_eq_paper (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2) (e : E) :
    edgeFactor ends w s e
      = sgn (w e) * (sgn (s (ends e).1) * sgn (s (ends e).2)) := by
  simp only [edgeFactor, sgn_add, mul_assoc]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in

lemma prod_edgeFactor_pow (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2)
    (b : E → ZMod 2) (lam : ℂ) :
    (∏ e, (edgeFactor ends w s e * lam) ^ (b e).val)
      = lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
  classical
  have hf : ∀ e, edgeFactor ends w s e ^ (b e).val
      = sgn (b e * (w e + s (ends e).1 + s (ends e).2)) := by
    intro e
    rw [edgeFactor, ← sgn_natCast_mul, natCast_val]
  have hsum : (∑ e, b e * (w e + s (ends e).1 + s (ends e).2))
      = bDotW b w + edgeSpinDot ends b s := by
    simp only [bDotW, edgeSpinDot, mul_add, Finset.sum_add_distrib]
    abel
  calc (∏ e, (edgeFactor ends w s e * lam) ^ (b e).val)
      = (∏ e, edgeFactor ends w s e ^ (b e).val) * (∏ e, lam ^ (b e).val) := by
          simp_rw [mul_pow, Finset.prod_mul_distrib]
    _ = (∏ e, sgn (b e * (w e + s (ends e).1 + s (ends e).2))) * lam ^ suppCard b := by
          rw [Finset.prod_pow_eq_pow_sum, suppCard]
          simp only [hf]
    _ = sgn (∑ e, b e * (w e + s (ends e).1 + s (ends e).2)) * lam ^ suppCard b := by
          rw [sgn_sum]
    _ = lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
          rw [hsum, sgn_add, sgn_add]
          ring

omit [Fintype V] [DecidableEq V] in

lemma boltzmann_expand (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) (s : V → ZMod 2) :
    boltzmann ends w Θ lam s
      = Θ * ∑ b : E → ZMod 2, lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
  classical
  unfold boltzmann
  congr 1
  have h1 : ∀ e : E, (1 + edgeFactor ends w s e * lam)
      = ∑ x : ZMod 2, (edgeFactor ends w s e * lam) ^ x.val := by
    intro e
    rw [sum_zmod2]
    simp
  calc ∏ e, (1 + edgeFactor ends w s e * lam)
      = ∏ e, ∑ x : ZMod 2, (edgeFactor ends w s e * lam) ^ x.val :=
          Finset.prod_congr rfl (fun e _ => h1 e)
    _ = ∑ b ∈ Fintype.piFinset (fun _ : E => (Finset.univ : Finset (ZMod 2))),
          ∏ e, (edgeFactor ends w s e * lam) ^ (b e).val :=
          Finset.prod_univ_sum _ _
    _ = ∑ b : E → ZMod 2, ∏ e, (edgeFactor ends w s e * lam) ^ (b e).val := by
          rw [Fintype.piFinset_univ]
    _ = ∑ b : E → ZMod 2, lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) :=
          Finset.sum_congr rfl (fun b _ => prod_edgeFactor_pow ends w s b lam)

theorem source_prop1_double_fourier (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam : ℂ) :
    partition ends w Θ lam
      = Θ * ∑ s : V → ZMod 2, ∑ b : E → ZMod 2,
          lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w) := by
  classical
  simp only [partition]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [boltzmann_expand]
  congr 1
  exact Finset.sum_congr rfl (fun b _ => by rw [edgeSpinDot_eq_alphaDotS ends hLoop b s])

omit [DecidableEq E] in

theorem source_eq20_spin_summation (ends : E → V × V) (b : E → ZMod 2) :
    (∑ s : V → ZMod 2, sgn (alphaDotS ends b s))
      = if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0 := by
  classical
  have hfac : ∀ s : V → ZMod 2, sgn (alphaDotS ends b s)
      = ∏ v, sgn (parity ends b v * s v) := by
    intro s
    rw [alphaDotS, sgn_sum]
  calc (∑ s : V → ZMod 2, sgn (alphaDotS ends b s))
      = ∑ s : V → ZMod 2, ∏ v, sgn (parity ends b v * s v) :=
          Finset.sum_congr rfl (fun s _ => hfac s)
    _ = ∏ v, ∑ x : ZMod 2, sgn (parity ends b v * x) := by
          rw [Finset.prod_univ_sum]
          simp
    _ = ∏ v, (1 + sgn (parity ends b v)) := by
          apply Finset.prod_congr rfl
          intro v _
          rw [sum_zmod2]
          simp
    _ = if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0 := by
          by_cases hp : parity ends b = 0
          · rw [if_pos hp]
            have h2 : ∀ v, (1 + sgn (parity ends b v)) = (2 : ℂ) := by
              intro v
              have hv : parity ends b v = 0 := by rw [hp]; simp
              rw [hv]
              simp only [sgn_zero]
              norm_num
            rw [Finset.prod_congr rfl (fun v _ => h2 v), Finset.prod_const]
            norm_num
          · rw [if_neg hp]
            obtain ⟨v, hv⟩ := Function.ne_iff.mp hp
            have hv1 : parity ends b v = 1 := by
              rcases eq_zero_or_one (parity ends b v) with h | h
              · exact absurd h hv
              · exact h
            rw [Finset.prod_eq_zero (Finset.mem_univ v)]
            rw [hv1]
            simp

theorem source_eq23_zero_parity (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam : ℂ) :
    partition ends w Θ lam
      = (2 : ℂ) ^ Fintype.card V * Θ *
          ∑ b : E → ZMod 2,
            if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0 := by
  classical
  rw [source_prop1_double_fourier ends hLoop w Θ lam, Finset.sum_comm]
  have hstep : ∀ b : E → ZMod 2,
      (∑ s : V → ZMod 2, lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w))
        = (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
            (lam ^ suppCard b * sgn (bDotW b w)) := by
    intro b
    have hsplit : (∑ s : V → ZMod 2, lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w))
        = ∑ s : V → ZMod 2, sgn (alphaDotS ends b s) * (lam ^ suppCard b * sgn (bDotW b w)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [sgn_add]
      ring
    rw [hsplit]
    calc (∑ s : V → ZMod 2, sgn (alphaDotS ends b s) * (lam ^ suppCard b * sgn (bDotW b w)))
        = (∑ s : V → ZMod 2, sgn (alphaDotS ends b s)) *
            (lam ^ suppCard b * sgn (bDotW b w)) := (Finset.sum_mul ..).symm
      _ = (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
            (lam ^ suppCard b * sgn (bDotW b w)) := by
            rw [source_eq20_spin_summation]
  rw [Finset.sum_congr rfl (fun b _ => hstep b)]
  have hfac : ∀ b : E → ZMod 2,
      (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
          (lam ^ suppCard b * sgn (bDotW b w))
        = (2 : ℂ) ^ Fintype.card V *
            (if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0) := by
    intro b
    by_cases hp : parity ends b = 0 <;> simp [hp]
  rw [Finset.sum_congr rfl (fun b _ => hfac b), ← Finset.mul_sum]
  ring

def qwgt (A : Matrix V E (ZMod 2)) (B : Matrix E E (ZMod 2)) (x y : ℂ) : ℂ :=
  ∑ b : E → ZMod 2,
    if A.mulVec b = 0 then
      sgn (∑ e, b e * (B.mulVec b) e) * x ^ suppCard b * y ^ (Fintype.card E - suppCard b)
    else 0

def dg (w : E → ZMod 2) : Matrix E E (ZMod 2) := Matrix.diagonal w

lemma qwgt_incidence_dg (ends : E → V × V) (w : E → ZMod 2) (x : ℂ) :
    qwgt (incidence ends) (dg w) x 1
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 then sgn (bDotW b w) * x ^ suppCard b else 0 := by
  classical
  unfold qwgt dg parity
  apply Finset.sum_congr rfl
  intro b _
  have hb : ∀ e : E, b e * ((Matrix.diagonal w).mulVec b) e = b e * w e := by
    intro e
    rw [Matrix.mulVec_diagonal]
    calc b e * (w e * b e) = (b e * b e) * w e := by ring
      _ = b e * w e := by rw [mul_self]
  have hsum : (∑ e, b e * ((Matrix.diagonal w).mulVec b) e) = bDotW b w := by
    rw [bDotW]
    exact Finset.sum_congr rfl (fun e _ => hb e)
  by_cases hp : (incidence ends).mulVec b = 0
  · rw [if_pos hp, if_pos hp, hsum]
    simp
  · rw [if_neg hp, if_neg hp]

theorem source_theorem2_qwgt (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam μ : ℂ) (hΘ : Θ * μ ^ Fintype.card E = 1) :
    μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V * partition ends w Θ lam
      = qwgt (incidence ends) (dg w) lam 1 := by
  classical
  set S : ℂ := ∑ b : E → ZMod 2,
    if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0 with hS
  rw [source_eq23_zero_parity ends hLoop w Θ lam]
  · have h2 : ((2 : ℂ) ^ Fintype.card V) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hμΘ : μ ^ Fintype.card E * Θ = 1 := by
      rw [mul_comm]
      exact hΘ
    have hcalc : μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V *
        ((2 : ℂ) ^ Fintype.card V * Θ * S) = S := by
      field_simp
      rw [mul_comm (μ ^ Fintype.card E * Θ) S, hμΘ, mul_one]
    rw [hcalc]
    rw [qwgt_incidence_dg]
    rw [hS]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hp : parity ends b = 0 <;> simp [hp, mul_comm]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in

lemma source_boltzmann_paper_form (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2)
    (lam : ℂ) :
    (∏ e, (1 + sgn (w e) * (sgn (s (ends e).1) * sgn (s (ends e).2)) * lam))
      = ∏ e, (1 + edgeFactor ends w s e * lam) := by
  apply Finset.prod_congr rfl
  intro e _
  rw [← edgeFactor_eq_paper]

theorem source_cosh_tanh_parameters (β J : ℝ) (nE : ℕ) :
    ((((Real.cosh (β * J))⁻¹ : ℝ) : ℂ) ^ 2 = 1 - ((Real.tanh (β * J) : ℝ) : ℂ) ^ 2) ∧
      (((Real.cosh (β * J) : ℝ) : ℂ) ^ nE *
        ((((Real.cosh (β * J))⁻¹ : ℝ) : ℂ)) ^ nE = 1) := by
  have hc : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
  constructor
  · have hreal : (Real.cosh (β * J))⁻¹ ^ 2 = 1 - (Real.tanh (β * J)) ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      nlinarith [Real.cosh_sq_sub_sinh_sq (β * J)]
    rw [← Complex.ofReal_pow, hreal]
    push_cast
    ring
  · rw [← mul_pow, ← Complex.ofReal_mul, mul_inv_cancel₀ hc]
    simp

end Qatlib.Papers.IsingPart03.MainResults
