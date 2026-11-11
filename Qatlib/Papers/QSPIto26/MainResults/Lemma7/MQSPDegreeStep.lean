/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma3.MQSPInversion
import Qatlib.Papers.QSPIto26.MainResults.Lemma4.MQSPDegreeEquality
import Qatlib.Papers.QSPIto26.MainResults.Lemma6.MQSPParity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 — degree change after appending one signal operator

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 7 (Appendix A, pp. 12--13),
Eqs. (51)--(52).

Lemma 7. If `(P,Q)` is constructible by m-variable M-QSP in `n` steps and
`(P̃,Q̃)` is defined by Eq. (51) (right-multiplying by `A(a_s)e^{iφσ_z}`), then the degree with
respect to `a_s` changes by `±1` and every other per-variable degree is unchanged.

The proof follows the paper: Eq. (53) gives the upper bounds by expanding the entries of
the appended word matrix; Eqs. (54)–(55) invert the appended factor via the explicit
Laurent inverse of `A(a_s)`, which gives the reverse bounds (Lemma 4 trades the `Q̃`-degree
for the `P̃`-degree); Lemma 6 supplies the parity that rules out equality when `j = s`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma7

open Qatlib.Papers.QSPIto26.MainResults.Core

/-! ### The `starL` conjugation -/

/-- Coefficientwise complex conjugation, as a plain function on scalars. -/
def conjC (c : ℂ) : ℂ := (starRingEnd ℂ) c

/-- Conjugation fixes the scalar `1`. -/
@[simp] lemma conjC_one : conjC 1 = 1 := map_one _

/-- `starL` is the ring homomorphism on Laurent polynomials induced by conjugation. -/
lemma starL_eq {m : ℕ} (Z : MLaurent m) :
    Core.starL Z = AddMonoidAlgebra.mapRingHom (ExpVec m) (starRingEnd ℂ) Z := rfl

/-- `starL` is additive. -/
lemma starL_add {m : ℕ} (X Y : MLaurent m) :
    Core.starL (X + Y) = Core.starL X + Core.starL Y := by
  rw [starL_eq, starL_eq, starL_eq, map_add]

/-- `starL` is odd. -/
lemma starL_neg {m : ℕ} (X : MLaurent m) : Core.starL (-X) = -Core.starL X := by
  rw [starL_eq, starL_eq, map_neg]

/-- `starL` is multiplicative. -/
lemma starL_mul {m : ℕ} (X Y : MLaurent m) :
    Core.starL (X * Y) = Core.starL X * Core.starL Y := by
  rw [starL_eq, starL_eq, starL_eq, map_mul]

/-- `starL` conjugates the coefficient of a monomial. -/
lemma starL_single {m : ℕ} (k : ExpVec m) (c : ℂ) :
    Core.starL (AddMonoidAlgebra.single k c)
      = AddMonoidAlgebra.single k (conjC c) := by
  rw [starL_eq]
  exact AddMonoidAlgebra.mapRingHom_single (starRingEnd ℂ) k c

/-- `starL` of a constant is the conjugate constant. -/
lemma starL_C' {m : ℕ} (c : ℂ) : Core.starL (C' c) = (C' (conjC c) : MLaurent m) :=
  starL_single 0 c

/-- `starL` fixes `a_j` (real coefficient). -/
lemma starL_var {m : ℕ} (j : Fin m) : Core.starL (var j) = var j := by
  have h := starL_single (Pi.single j (1 : ℤ)) 1
  rw [conjC_one] at h
  exact h

/-- `starL` fixes `a_j^{-1}` (real coefficient). -/
lemma starL_varInv {m : ℕ} (j : Fin m) : Core.starL (varInv j) = varInv j := by
  have h := starL_single (Pi.single j (-1 : ℤ)) 1
  rw [conjC_one] at h
  exact h

/-! ### The `starOp` involution -/

/-- `starOp` is additive. -/
lemma starOp_add {m : ℕ} (X Y : MLaurent m) : starOp (X + Y) = starOp X + starOp Y := by
  simp only [starOp, starL_add, map_add]

/-- `starOp` is odd. -/
lemma starOp_neg {m : ℕ} (X : MLaurent m) : starOp (-X) = -starOp X := by
  simp only [starOp, starL_neg, map_neg]

/-- `starOp` is compatible with subtraction. -/
lemma starOp_sub {m : ℕ} (X Y : MLaurent m) : starOp (X - Y) = starOp X - starOp Y := by
  have h1 : starOp (X - Y) = starOp (X + -Y) := by rw [sub_eq_add_neg]
  rw [h1, starOp_add, starOp_neg, sub_eq_add_neg]

/-- `starOp` is a ring homomorphism on Laurent polynomials (the involution
`a_j ↦ a_j^{-1}` combined with coefficient conjugation). -/
lemma starOp_mul {m : ℕ} (X Y : MLaurent m) : starOp (X * Y) = starOp X * starOp Y := by
  simp only [starOp, starL_mul, map_mul]

/-- `starOp` of a constant is the conjugate constant. -/
lemma starOp_C' {m : ℕ} (c : ℂ) : starOp (C' c) = (C' (conjC c) : MLaurent m) := by
  rw [starOp, starL_C', Lemma3.substInv_C']

/-- `starOp` exchanges `a_j` and `a_j^{-1}`. -/
lemma starOp_var {m : ℕ} (j : Fin m) : starOp (var j) = varInv j := by
  rw [starOp, starL_var, Lemma3.substInv_var]

/-- `starOp` exchanges `a_j^{-1}` and `a_j`. -/
lemma starOp_varInv {m : ℕ} (j : Fin m) : starOp (varInv j) = var j := by
  rw [starOp, starL_varInv, Lemma3.substInv_varInv]

/-! ### Degrees of the generators -/

/-- Degree of a constant in any variable is zero. -/
lemma degVar_C' {m : ℕ} (j : Fin m) (c : ℂ) : degVar j (C' c) = 0 := by
  have hle : degVar j (C' c) ≤ 0 := by
    refine Finset.sup_le fun k hk => ?_
    have hk0 : k = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    rw [hk0]
    simp
  exact Nat.le_antisymm hle (Nat.zero_le _)

/-- Degree of `a_{j'}` in variable `a_j`. -/
lemma degVar_var {m : ℕ} (j j' : Fin m) : degVar j (var j') = if j = j' then 1 else 0 := by
  have hsupp : (var j').coeff.support = {Pi.single j' (1 : ℤ)} := by simp [var, mono]
  rw [degVar, hsupp, Finset.sup_singleton]
  by_cases h : j = j'
  · subst h
    simp
  · rw [if_neg h]
    simp [h]

/-- Degree of `a_{j'}^{-1}` in variable `a_j`. -/
lemma degVar_varInv {m : ℕ} (j j' : Fin m) : degVar j (varInv j') = if j = j' then 1 else 0 := by
  have hsupp : (varInv j').coeff.support = {Pi.single j' (-1 : ℤ)} := by simp [varInv, mono]
  rw [degVar, hsupp, Finset.sup_singleton]
  by_cases h : j = j'
  · subst h
    simp
  · rw [if_neg h]
    simp [h]

/-- Negation does not change per-variable degrees. -/
lemma degVar_neg {m : ℕ} (j : Fin m) (X : MLaurent m) : degVar j (-X) = degVar j X := by
  have hneg : ∀ k : ExpVec m, (-X : MLaurent m).coeff k = -(X.coeff k) := fun _ => rfl
  have hsupp : (-X : MLaurent m).coeff.support = X.coeff.support := by
    ext k
    simp only [Finsupp.mem_support_iff, hneg]
    simp
  rw [degVar, degVar, hsupp]

/-- Subtraction bound for degrees. -/
lemma degVar_sub_le {m : ℕ} (j : Fin m) (X Y : MLaurent m) :
    degVar j (X - Y) ≤ max (degVar j X) (degVar j Y) := by
  have h := Lemma4.degVar_add_le j X (-Y)
  rw [degVar_neg] at h
  rw [sub_eq_add_neg]
  exact h

/-- Bound for `a_s + a_s^{-1}`. -/
lemma degVar_varSum_le {m : ℕ} (j s : Fin m) :
    degVar j (var s + varInv s) ≤ if j = s then 1 else 0 := by
  have h := Lemma4.degVar_add_le j (var s) (varInv s)
  rw [degVar_var, degVar_varInv] at h
  by_cases hjs : j = s
  · subst hjs
    simp only [if_pos rfl] at h ⊢
    simpa using h
  · rw [if_neg hjs] at h
    rw [if_neg hjs]
    simpa using h

/-- Bound for `a_s - a_s^{-1}`. -/
lemma degVar_varDiff_le {m : ℕ} (j s : Fin m) :
    degVar j (var s - varInv s) ≤ if j = s then 1 else 0 := by
  have h := degVar_sub_le j (var s) (varInv s)
  rw [degVar_var, degVar_varInv] at h
  by_cases hjs : j = s
  · subst hjs
    simp only [if_pos rfl] at h ⊢
    simpa using h
  · rw [if_neg hjs] at h
    rw [if_neg hjs]
    simpa using h

/-- Bound for `a_s^{-1} - a_s`. -/
lemma degVar_varDiff_le' {m : ℕ} (j s : Fin m) :
    degVar j (varInv s - var s) ≤ if j = s then 1 else 0 := by
  have h := degVar_sub_le j (varInv s) (var s)
  rw [degVar_var, degVar_varInv] at h
  by_cases hjs : j = s
  · subst hjs
    simp only [if_pos rfl] at h ⊢
    simpa using h
  · rw [if_neg hjs] at h
    rw [if_neg hjs]
    simpa using h

/-- Bound for a leading-constant scaled sum of appended-word entry shapes. -/
lemma degVar_bound_sum {m : ℕ} (j s : Fin m) (c : ℂ) (X Y : MLaurent m) :
    degVar j (C' c * (X * (var s + varInv s) + Y * (var s - varInv s)))
      ≤ max (degVar j X) (degVar j Y) + (if j = s then 1 else 0) := by
  have h1 : degVar j (C' c * (X * (var s + varInv s) + Y * (var s - varInv s)))
      ≤ degVar j (X * (var s + varInv s) + Y * (var s - varInv s)) := by
    have h := Lemma4.degVar_mul_le j (C' c)
      (X * (var s + varInv s) + Y * (var s - varInv s))
    rwa [degVar_C', zero_add] at h
  refine Nat.le_trans h1 ?_
  have h2 := Lemma4.degVar_add_le j (X * (var s + varInv s)) (Y * (var s - varInv s))
  have h3 : degVar j (X * (var s + varInv s)) ≤ degVar j X + (if j = s then 1 else 0) := by
    have h := Lemma4.degVar_mul_le j X (var s + varInv s)
    have hvs := degVar_varSum_le j s
    omega
  have h4 : degVar j (Y * (var s - varInv s)) ≤ degVar j Y + (if j = s then 1 else 0) := by
    have h := Lemma4.degVar_mul_le j Y (var s - varInv s)
    have hvs := degVar_varDiff_le j s
    omega
  omega

/-- Bound for a pair of differently scaled appended-word entry shapes. -/
lemma degVar_bound_pair {m : ℕ} (j s : Fin m) (c d : ℂ) (X Y : MLaurent m) :
    degVar j (X * (C' c * (var s + varInv s)) + Y * (C' d * (varInv s - var s)))
      ≤ max (degVar j X) (degVar j Y) + (if j = s then 1 else 0) := by
  have h2 := Lemma4.degVar_add_le j (X * (C' c * (var s + varInv s)))
    (Y * (C' d * (varInv s - var s)))
  have h3 : degVar j (X * (C' c * (var s + varInv s)))
      ≤ degVar j X + (if j = s then 1 else 0) := by
    have h := Lemma4.degVar_mul_le j X (C' c * (var s + varInv s))
    have hc := Lemma4.degVar_mul_le j (C' c) (var s + varInv s)
    rw [degVar_C'] at hc
    have hvs := degVar_varSum_le j s
    omega
  have h4 : degVar j (Y * (C' d * (varInv s - var s)))
      ≤ degVar j Y + (if j = s then 1 else 0) := by
    have h := Lemma4.degVar_mul_le j Y (C' d * (varInv s - var s))
    have hc := Lemma4.degVar_mul_le j (C' d) (varInv s - var s)
    rw [degVar_C'] at hc
    have hvs := degVar_varDiff_le' j s
    omega
  omega

/-! ### The inverse signal factor -/

/-- The quadratic identity `(a+a⁻¹)² + (a−a⁻¹)(a⁻¹−a) = 4`. -/
lemma varSum_sq {m : ℕ} (s : Fin m) :
    (var s + varInv s) * (var s + varInv s)
      + (var s - varInv s) * (varInv s - var s) = (4 : MLaurent m) := by
  linear_combination 4 * Lemma4.var_mul_varInv s

/-- Explicit entries of the signal operator `A(a_s)`. -/
lemma signalOp_entry {m : ℕ} (s : Fin m) :
    (signalOp s : Matrix (Fin 2) (Fin 2) (MLaurent m))
      = !![C' (1 / 2) * (var s + varInv s), C' (1 / 2) * (var s - varInv s);
           C' (1 / 2) * (var s - varInv s), C' (1 / 2) * (var s + varInv s)] := rfl

/-- The inverse of the signal operator `A(a_s)`, Eq. (54): since `det A(a_s) = 1`,
the inverse is the adjugate, again a Laurent matrix in `a_s`. -/
def signalOpInv {m : ℕ} (s : Fin m) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  let half : MLaurent m := C' (1 / 2)
  let sp := var s + varInv s
  let sm := varInv s - var s
  !![half * sp, half * sm; half * sm, half * sp]

/-- Explicit entries of `signalOpInv`. -/
lemma signalOpInv_entry {m : ℕ} (s : Fin m) :
    (signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m))
      = !![C' (1 / 2) * (var s + varInv s), C' (1 / 2) * (varInv s - var s);
           C' (1 / 2) * (varInv s - var s), C' (1 / 2) * (var s + varInv s)] := rfl

/-- `A(a_s)` times its inverse is the identity. -/
lemma signalOp_mul_inv {m : ℕ} (s : Fin m) :
    (signalOp s : Matrix (Fin 2) (Fin 2) (MLaurent m)) * signalOpInv s = 1 := by
  have ha4 : C' ((1 / 2 : ℂ)) * C' ((1 / 2 : ℂ)) * (4 : MLaurent m) = 1 := by
    have h4 : (4 : MLaurent m) = C' ((4 : ℂ)) := rfl
    rw [h4, Lemma4.C'_mul_C', Lemma4.C'_mul_C',
      show ((1 / 2 : ℂ) * (1 / 2 : ℂ)) * (4 : ℂ) = 1 by norm_num]
    simp [C', AddMonoidAlgebra.one_def]
  have h00 : ((signalOp s * signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m))) 0 0
      = (1 : MLaurent m) := by
    rw [signalOp_entry, signalOpInv_entry]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one]
    linear_combination C' ((1 / 2 : ℂ)) * C' ((1 / 2 : ℂ)) * varSum_sq s + ha4
  have h01 : ((signalOp s * signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m))) 0 1
      = (0 : MLaurent m) := by
    rw [signalOp_entry, signalOpInv_entry]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one]
    ring
  have h10 : ((signalOp s * signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m))) 1 0
      = (0 : MLaurent m) := by
    rw [signalOp_entry, signalOpInv_entry]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one]
    ring
  have h11 : ((signalOp s * signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m))) 1 1
      = (1 : MLaurent m) := by
    rw [signalOp_entry, signalOpInv_entry]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one]
    linear_combination C' ((1 / 2 : ℂ)) * C' ((1 / 2 : ℂ)) * varSum_sq s + ha4
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- The inverse of `A(a_s)` times `A(a_s)` is the identity. -/
lemma inv_mul_signalOp {m : ℕ} (s : Fin m) :
    (signalOpInv s : Matrix (Fin 2) (Fin 2) (MLaurent m)) * signalOp s = 1 := by
  rw [mul_eq_one_comm, signalOp_mul_inv]

/-- `e^{iφσ_z} e^{-iφσ_z} = 1`. -/
lemma phaseOp_mul_neg {m : ℕ} (φ : ℝ) :
    (phaseOp φ : Matrix (Fin 2) (Fin 2) (MLaurent m)) * phaseOp (-φ) = 1 := by
  rw [Lemma3.phaseOp_mul, add_neg_cancel, Lemma3.phaseOp_zero]

/-! ### Constant merges for the entry formulas -/

/-- Merging the half-constant with the positive phase constant. -/
lemma half_mul_exp {m : ℕ} (φ : ℝ) :
    (C' ((1 / 2 : ℂ)) : MLaurent m) * C' (Complex.exp (Complex.I * (φ : ℂ)))
      = C' (Complex.exp (Complex.I * (φ : ℂ)) / 2) := by
  rw [Lemma4.C'_mul_C']
  congr 1
  ring

/-- Merging the half-constant with the negative phase constant. -/
lemma half_mul_exp_neg {m : ℕ} (φ : ℝ) :
    (C' ((1 / 2 : ℂ)) : MLaurent m) * C' (Complex.exp (-(Complex.I * (φ : ℂ))))
      = C' (Complex.exp (-(Complex.I * (φ : ℂ))) / 2) := by
  rw [Lemma4.C'_mul_C']
  congr 1
  ring

/-- Conjugating the phase constant `e^{-iφ}/2` gives `e^{iφ}/2`. -/
lemma conj_exp_half (φ : ℝ) :
    conjC (Complex.exp (-(Complex.I * (φ : ℂ))) / 2)
      = Complex.exp (Complex.I * (φ : ℂ)) / 2 := by
  have hd : ∀ a b : ℂ, (starRingEnd ℂ) (a / b)
      = (starRingEnd ℂ) a / (starRingEnd ℂ) b := fun a b => map_div₀ _ _ _
  have hn : (starRingEnd ℂ) (-(Complex.I * (φ : ℂ))) = Complex.I * (φ : ℂ) := by
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h2 : (starRingEnd ℂ) ((2 : ℂ)) = (2 : ℂ) := map_natCast _ _
  show (starRingEnd ℂ) (Complex.exp (-(Complex.I * (φ : ℂ))) / 2)
      = Complex.exp (Complex.I * (φ : ℂ)) / 2
  rw [hd, ← Complex.exp_conj, hn, h2]

/-- Conjugating the phase constant `e^{iφ}/2` gives `e^{-iφ}/2`. -/
lemma conj_exp_half' (φ : ℝ) :
    conjC (Complex.exp (Complex.I * (φ : ℂ)) / 2)
      = Complex.exp (-(Complex.I * (φ : ℂ))) / 2 := by
  have hd : ∀ a b : ℂ, (starRingEnd ℂ) (a / b)
      = (starRingEnd ℂ) a / (starRingEnd ℂ) b := fun a b => map_div₀ _ _ _
  have hn : (starRingEnd ℂ) (Complex.I * (φ : ℂ)) = -(Complex.I * (φ : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h2 : (starRingEnd ℂ) ((2 : ℂ)) = (2 : ℂ) := map_natCast _ _
  show (starRingEnd ℂ) (Complex.exp (Complex.I * (φ : ℂ)) / 2)
      = Complex.exp (-(Complex.I * (φ : ℂ))) / 2
  rw [hd, ← Complex.exp_conj, hn, h2]

/-! ### Appending one factor to the word -/

/-- The SU(2)-shaped matrix `!![P, Q; -Q^*, P^*]` built from a pair `(P, Q)`. -/
def pairMatrix {m : ℕ} (P Q : MLaurent m) : Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  !![P, Q; -starOp Q, starOp P]

/-- The word matrix after appending `A(a_s) e^{iφσ_z}` to `!![P, Q; -Q^*, P^*]`, Eq. (51). -/
def appendWord {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    Matrix (Fin 2) (Fin 2) (MLaurent m) :=
  pairMatrix P Q * signalOp s * phaseOp φ

/-- Entry `(0,0)` of the appended word, in normalized form (Eq. (53)). -/
lemma append_entry00 {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    appendWord P Q s φ 0 0
      = C' (Complex.exp (Complex.I * (φ : ℂ)) / 2)
          * (P * (var s + varInv s) + Q * (var s - varInv s)) := by
  simp only [appendWord, pairMatrix, signalOp_entry, phaseOp, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.cons_val_one]
  linear_combination (P * (var s + varInv s) + Q * (var s - varInv s))
    * half_mul_exp (m := m) φ

/-- Entry `(0,1)` of the appended word, in normalized form (Eq. (53)). -/
lemma append_entry01 {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    appendWord P Q s φ 0 1
      = C' (Complex.exp (-(Complex.I * (φ : ℂ))) / 2)
          * (P * (var s - varInv s) + Q * (var s + varInv s)) := by
  simp only [appendWord, pairMatrix, signalOp_entry, phaseOp, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.cons_val_one]
  linear_combination (P * (var s - varInv s) + Q * (var s + varInv s))
    * half_mul_exp_neg (m := m) φ

/-- Entry `(1,0)` of the appended word, in normalized form (Eq. (53)). -/
lemma append_entry10 {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    appendWord P Q s φ 1 0
      = C' (Complex.exp (Complex.I * (φ : ℂ)) / 2)
          * (starOp P * (var s - varInv s) - starOp Q * (var s + varInv s)) := by
  simp only [appendWord, pairMatrix, signalOp_entry, phaseOp, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.cons_val_one]
  linear_combination (starOp P * (var s - varInv s) - starOp Q * (var s + varInv s))
    * half_mul_exp (m := m) φ

/-- Entry `(1,1)` of the appended word, in normalized form (Eq. (53)). -/
lemma append_entry11 {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    appendWord P Q s φ 1 1
      = C' (Complex.exp (-(Complex.I * (φ : ℂ))) / 2)
          * (starOp P * (var s + varInv s) - starOp Q * (var s - varInv s)) := by
  simp only [appendWord, pairMatrix, signalOp_entry, phaseOp, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Matrix.cons_val_one]
  linear_combination (starOp P * (var s + varInv s) - starOp Q * (var s - varInv s))
    * half_mul_exp_neg (m := m) φ

/-! ### The SU(2) form is preserved -/

/-- The appended word matrix again has the form `!![P̃, Q̃; -Q̃^*, P̃^*]`, Eqs. (6)/(51). -/
lemma append_form {m : ℕ} (P Q : MLaurent m) (s : Fin m) (φ : ℝ) :
    appendWord P Q s φ 1 0 = -starOp (appendWord P Q s φ 0 1)
      ∧ appendWord P Q s φ 1 1 = starOp (appendWord P Q s φ 0 0) := by
  constructor
  · rw [append_entry10, append_entry01, starOp_mul, starOp_add, starOp_mul, starOp_mul,
      starOp_C', starOp_sub, starOp_add, starOp_var, starOp_varInv, conj_exp_half]
    ring
  · rw [append_entry11, append_entry00, starOp_mul, starOp_add, starOp_mul, starOp_mul,
      starOp_C', starOp_sub, starOp_add, starOp_var, starOp_varInv, conj_exp_half']
    ring

/-! ### Snoc lemmas -/

/-- Appending `A(a_sn)e^{iφn σ_z}` to an `n`-step word gives the `(n+1)`-step word with
`Fin.snoc` parameters, Eq. (51). -/
lemma wordMatrix_append {m n : ℕ} (φ : Fin (n + 1) → ℝ) (φn : ℝ) (s : Fin n → Fin m)
    (sn : Fin m) :
    wordMatrix (n + 1) (Fin.snoc φ φn) (Fin.snoc s sn)
      = wordMatrix n φ s * signalOp sn * phaseOp φn := by
  have h0 : (Fin.snoc φ φn : Fin (n + 2) → ℝ) 0 = φ 0 := by
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl, Fin.snoc_castSucc]
  have hlastS : (Fin.snoc s sn : Fin (n + 1) → Fin m) (Fin.last n) = sn := by
    simp only [Fin.snoc_last]
  have hlastP : (Fin.snoc φ φn : Fin (n + 2) → ℝ) ((Fin.last n).succ) = φn := by
    rw [show (Fin.last n).succ = Fin.last (n + 1) from Fin.ext (by simp), Fin.snoc_last]
  rw [wordMatrix, wordMatrix, h0, List.ofFn_succ', List.prod_concat]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
  rw [hlastS, hlastP]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- The count of indices equal to `s` after appending one more `s`. -/
lemma count_snoc {m n : ℕ} (s₀ : Fin n → Fin m) (s : Fin m) :
    (Finset.univ.filter (fun k : Fin (n + 1) => (Fin.snoc s₀ s : Fin (n + 1) → Fin m) k = s)).card
      = (Finset.univ.filter (fun k : Fin n => s₀ k = s)).card + 1 := by
  have hcard : ∀ {N : ℕ} (t : Fin N → Fin m) (u : Fin m),
      (Finset.univ.filter (fun k => t k = u)).card
        = ∑ k, (if t k = u then 1 else 0) := by
    intro N t u
    rw [← Finset.sum_filter (fun k => t k = u) (fun _ => (1 : ℕ)), Finset.card_eq_sum_ones]
  rw [hcard, hcard, Fin.sum_univ_castSucc]
  have hs : (Fin.snoc s₀ s : Fin (n + 1) → Fin m) (Fin.last n) = s := by
    simp only [Fin.snoc_last]
  simp only [hs, Fin.snoc_castSucc]
  simp

/-! ### Lemma 7 -/

/-- Lemma 7 (arXiv:2410.02332v3, pp. 12--13, Eq. (52)): appending `A(a_s)e^{iφσ_z}` changes
`deg_{a_s}` by `±1` and leaves all other `deg_{a_j}` unchanged. Complete given the
lex-leading-monomial interface hypothesis `hlead` of Lemmas 4--6. -/
theorem lemma7_degree_step {m n : ℕ} (P Q : MLaurent m) (h : Constructible n P Q)
    (hlead : ∀ (X : MLaurent m) (j : Fin m), X ≠ 0 →
      degVar j (X * starOp X) = 2 * degVar j X)
    (s : Fin m) (φ : ℝ) :
    (degVar s (appendWord P Q s φ 0 0) = degVar s P - 1 ∨
      degVar s (appendWord P Q s φ 0 0) = degVar s P + 1) ∧
      (∀ j : Fin m, j ≠ s → degVar j (appendWord P Q s φ 0 0) = degVar j P) := by
  obtain ⟨φ₀, s₀, hw⟩ := h
  classical
  set M : Matrix (Fin 2) (Fin 2) (MLaurent m) := appendWord P Q s φ with hM
  -- The word identity for the appended pair.
  have hword : wordMatrix (n + 1) (Fin.snoc φ₀ φ) (Fin.snoc s₀ s) = M := by
    rw [wordMatrix_append, hw]
    rfl
  -- The SU(2) form of the appended matrix.
  have hM00 : M 0 0 = C' (Complex.exp (Complex.I * (φ : ℂ)) / 2)
      * (P * (var s + varInv s) + Q * (var s - varInv s)) := append_entry00 P Q s φ
  have hM10 : M 1 0 = -starOp (M 0 1) := (append_form P Q s φ).1
  have hM11 : M 1 1 = starOp (M 0 0) := (append_form P Q s φ).2
  have hMlit : (!![M 0 0, M 0 1; -starOp (M 0 1), starOp (M 0 0)] :
      Matrix (Fin 2) (Fin 2) (MLaurent m)) = M := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · show -starOp (M 0 1) = M 1 0
      exact hM10.symm
    · show starOp (M 0 0) = M 1 1
      exact hM11.symm
  -- The appended pair is constructible in n+1 steps.
  have hcon : Constructible (n + 1) (M 0 0) (M 0 1) :=
    ⟨Fin.snoc φ₀ φ, Fin.snoc s₀ s, by rw [hword, hMlit]⟩
  -- Lemma 4 degrees for both pairs.
  have hdP := Lemma4.lemma4_degree_eq P Q ⟨φ₀, s₀, hw⟩ hlead
  have hdM := Lemma4.lemma4_degree_eq (M 0 0) (M 0 1) hcon hlead
  -- Upper bound, Eq. (53).
  have hub : ∀ j : Fin m,
      degVar j (M 0 0) ≤ max (degVar j P) (degVar j Q) + (if j = s then 1 else 0) := by
    intro j
    have hbb := degVar_bound_sum j s (Complex.exp (Complex.I * (φ : ℂ)) / 2) P Q
    rw [hM00]
    exact hbb
  -- Reverse bound via the inverse factor, Eqs. (54)--(55).
  have hMinv : pairMatrix P Q = M * (phaseOp (-φ) * signalOpInv s) := by
    have h1 : M * (phaseOp (-φ) * signalOpInv s)
        = (pairMatrix P Q * signalOp s * phaseOp φ) * (phaseOp (-φ) * signalOpInv s) := by
      rfl
    have h2 : phaseOp φ * (phaseOp (-φ) * signalOpInv s) = signalOpInv s := by
      rw [← Matrix.mul_assoc, phaseOp_mul_neg, one_mul]
    rw [h1, Matrix.mul_assoc, h2, Matrix.mul_assoc, signalOp_mul_inv, Matrix.mul_one]
  have hrev00 : P = M 0 0
      * (C' (Complex.exp (Complex.I * ((-φ : ℝ) : ℂ)) / 2) * (var s + varInv s))
      + M 0 1 * (C' (Complex.exp (-(Complex.I * ((-φ : ℝ) : ℂ))) / 2) * (varInv s - var s)) := by
    have e0 : ((M * (phaseOp (-φ) * signalOpInv s) :
        Matrix (Fin 2) (Fin 2) (MLaurent m))) 0 0 = P := by
      rw [← hMinv]
      rfl
    rw [← e0]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, phaseOp,
      signalOpInv_entry]
    linear_combination
      M 0 0 * (var s + varInv s) * half_mul_exp (m := m) (-φ)
        + M 0 1 * (varInv s - var s) * half_mul_exp_neg (m := m) (-φ)
  have hrev : ∀ j : Fin m,
      degVar j P ≤ max (degVar j (M 0 0)) (degVar j (M 0 1)) + (if j = s then 1 else 0) := by
    intro j
    have hbb := degVar_bound_pair j s
      (Complex.exp (Complex.I * ((-φ : ℝ) : ℂ)) / 2)
      (Complex.exp (-(Complex.I * ((-φ : ℝ) : ℂ))) / 2) (M 0 0) (M 0 1)
    rw [hrev00]
    exact hbb
  constructor
  · -- The j = s case: bounded difference plus Lemma 6 parity.
    have hubb := hub s
    have hrevs := hrev s
    rw [show (if s = s then 1 else 0 : ℕ) = 1 from if_pos rfl] at hubb hrevs
    have hdPs : degVar s P = degVar s Q := hdP s
    have hdMs : degVar s (M 0 0) = degVar s (M 0 1) := hdM s
    have hparOld := Lemma6.lemma6_parity (m := m) φ₀ s₀ P Q hw hlead
    have hparNew := Lemma6.lemma6_parity (m := m) (Fin.snoc φ₀ φ) (Fin.snoc s₀ s)
      (M 0 0) (M 0 1) (by rw [hword, hMlit]) hlead
    have hp0 := hparOld.1 s
    have hp1 := hparNew.1 s
    rw [count_snoc] at hp1
    have hubb' : degVar s (M 0 0) ≤ degVar s P + 1 := by omega
    have hrevs' : degVar s P ≤ degVar s (M 0 0) + 1 := by omega
    omega
  · intro j hj
    have hubb := hub j
    have hrevj := hrev j
    rw [if_neg hj] at hubb hrevj
    have hdPj : degVar j P = degVar j Q := hdP j
    have hdMj : degVar j (M 0 0) = degVar j (M 0 1) := hdM j
    have h1 : degVar j (M 0 0) ≤ degVar j P := by omega
    have h2 : degVar j P ≤ degVar j (M 0 0) := by omega
    exact Nat.le_antisymm h1 h2

end Qatlib.Papers.QSPIto26.MainResults.Lemma7
