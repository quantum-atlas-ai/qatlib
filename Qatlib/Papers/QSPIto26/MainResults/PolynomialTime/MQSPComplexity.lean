/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSPIto26.MainResults.Lemma8.MQSPPrefixDegree

@[expose] public section


/-!
# Constructive soundness of M-QSP-CDA

The variable count is positive, as required by the paper's definition of M-QSP.
The procedure is a noncomputable Boolean specification; totality alone gives no runtime bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.PolynomialTime

open Qatlib.Papers.QSPIto26.MainResults.Core
open Qatlib.Papers.QSPIto26.MainResults.Lemma3
open Qatlib.Papers.QSPIto26.MainResults.Lemma7
open Qatlib.Papers.QSPIto26.MainResults.Lemma8

/-- The product of per-variable support bounds used in Eq. (13). -/
def termCount {m : ℕ} (P Q : MLaurent m) : ℕ :=
  ∏ j : Fin m, (2 * max (degVar j P) (degVar j Q) + 1)

/-- A zero-step pair has the required phase-word representation. -/
private theorem zero_constructible {m : ℕ} (P Q : MLaurent m)
    (h : ZeroStep P Q) : Constructible 0 P Q := by
  rcases h with ⟨φ, rfl, rfl⟩
  exact ⟨fun _ => φ, Fin.elim0, by rw [wordMatrix_zero, phaseOp_form]⟩

/-- A phase of pi/2 conjugates a signal to its inverse. -/
private theorem signal_cancel {m : ℕ} (j : Fin m) :
    signalOp j * phaseOp (Real.pi / 2) * signalOp j * phaseOp (-(Real.pi / 2)) = 1 := by
  have hc : phaseOp (Real.pi / 2) * signalOp j =
      signalOpInv j * (phaseOp (Real.pi / 2) : Matrix (Fin 2) (Fin 2) (MLaurent m)) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [signalOp, signalOpInv, phaseOp, Complex.ofReal_div, Complex.ofReal_ofNat,
        exp_I_pi_half, exp_neg_I_pi_half, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero]
    all_goals simp [C', AddMonoidAlgebra.single_neg]; ring
  rw [mul_assoc (signalOp j), hc, ← mul_assoc, signalOp_mul_inv, one_mul,
    phaseOp_mul_neg]

/-- Positive variable count permits insertion of a cancelling pair of signal steps. -/
private theorem pad_two {m n : ℕ} (hm : 0 < m) (P Q : MLaurent m)
    (h : Constructible n P Q) : Constructible (n + 2) P Q := by
  rcases h with ⟨φ, s, hw⟩
  let j : Fin m := ⟨0, hm⟩
  refine ⟨Fin.snoc (Fin.snoc φ (Real.pi / 2)) (-(Real.pi / 2)),
    Fin.snoc (Fin.snoc s j) j, ?_⟩
  rw [wordMatrix_append, wordMatrix_append]
  calc
    _ = wordMatrix n φ s *
        (signalOp j * phaseOp (Real.pi / 2) * signalOp j * phaseOp (-(Real.pi / 2))) := by
      simp only [mul_assoc]
    _ = _ := by rw [signal_cancel, mul_one, hw]

/-- Reattaching the removed signal recovers both upper entries. -/
private theorem reduce_append {m : ℕ} (P Q : MLaurent m) (j : Fin m) (φ : ℝ) :
    appendWord (reduceP j φ P Q) (reduceQ j φ P Q) j φ 0 0 = P ∧
      appendWord (reduceP j φ P Q) (reduceQ j φ P Q) j φ 0 1 = Q := by
  have he : C' (Complex.exp (Complex.I * (φ : ℂ))) *
      (C' (Complex.exp (-(Complex.I * (φ : ℂ)))) : MLaurent m) = 1 := by
    rw [C'_mul_C', ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rfl
  have hh : (4 : MLaurent m) * C' (1 / 2) * C' (1 / 2) = 1 := by
    change C' (4 : ℂ) * C' (1 / 2) * C' (1 / 2) = 1
    rw [C'_mul_C', C'_mul_C']
    norm_num
    rfl
  have hv := Qatlib.Papers.QSPIto26.MainResults.Lemma4.var_mul_varInv j
  constructor
  · rw [append_entry00]
    unfold reduceP reduceQ
    rw [← half_mul_exp]
    linear_combination (norm := ring_nf)
      4 * P * C' (1 / 2) * C' (1 / 2) * var j * varInv j * he +
      4 * P * C' (1 / 2) * C' (1 / 2) * hv + P * hh
  · rw [append_entry01]
    unfold reduceP reduceQ
    rw [← half_mul_exp_neg]
    linear_combination (norm := ring_nf)
      4 * Q * C' (1 / 2) * C' (1 / 2) * var j * varInv j * he +
      4 * Q * C' (1 / 2) * C' (1 / 2) * hv + Q * hh

/-- A constructible reduced pair can be extended by its removed signal and phase. -/
private theorem extend_reduced {m n : ℕ} (P Q : MLaurent m) (j : Fin m) (φ : ℝ)
    (h : Constructible n (reduceP j φ P Q) (reduceQ j φ P Q)) :
    Constructible (n + 1) P Q := by
  rcases h with ⟨θ, s, hw⟩
  refine ⟨Fin.snoc θ φ, Fin.snoc s j, ?_⟩
  rw [wordMatrix_append, hw]
  have he := reduce_append P Q j φ
  have hf := append_form (reduceP j φ P Q) (reduceQ j φ P Q) j φ
  change appendWord (reduceP j φ P Q) (reduceQ j φ P Q) j φ = _
  apply Matrix.ext
  intro a b
  fin_cases a <;> fin_cases b
  · exact he.1
  · exact he.2
  · change appendWord _ _ j φ 1 0 = -starOp Q
    simpa only [he.2] using hf.1
  · change appendWord _ _ j φ 1 1 = starOp P
    simpa only [he.1] using hf.2

/-- With a positive variable count, acceptance gives angle and signal-index witnesses. -/
theorem mqspCDA_constructive {m n : ℕ} (P Q : MLaurent m)
    (hm : 0 < m) (hcda : mqspCDA P Q n = true) : Constructible n P Q := by
  classical
  induction n using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    cases n with
    | zero =>
      have hz : ZeroStep P Q := by
        by_contra hn
        simp [mqspCDA, hn] at hcda
      exact zero_constructible P Q hz
    | succ k =>
      rw [mqspCDA] at hcda
      split at hcda
      next hd =>
        have hk : k + 1 - 2 < k + 1 := by omega
        have hp := pad_two hm P Q (ih _ hk P Q hcda)
        convert hp using 1
        omega
      next hd =>
        split at hcda
        next heq =>
          split at hcda
          next hex =>
            exact extend_reduced P Q (Classical.choose hex)
              (Classical.choose (Classical.choose_spec hex))
              (ih k (by omega) _ _ hcda)
          next hno => contradiction
        next hne => contradiction

/-- Every input has a Boolean value in this noncomputable specification. -/
theorem mqspCDA_total {m : ℕ} (P Q : MLaurent m) (n : ℕ) :
    ∃ b : Bool, mqspCDA P Q n = b := ⟨mqspCDA P Q n, rfl⟩

end Qatlib.Papers.QSPIto26.MainResults.PolynomialTime
