/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Aux2
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.TimeOrdered

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
set_option warningAsError false

section Duhamel

variable {N : Type} [Fintype N] [DecidableEq N]

theorem taylorODESolution_eq_diag (A V D : Matrix N N ℂ) (hA : A = V * D * V⁻¹)
    (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (b x_in : QState N) (t : ℝ) :
    taylorODESolution A b x_in t =
      V *ᵥ (fun n => Complex.exp (D n n * t) * ((V⁻¹ *ᵥ x_in) n +
        ∫ s in 0..t, Complex.exp (-(D n n) * s) * (V⁻¹ *ᵥ b) n)) := by
  classical
  set y : QState N := V⁻¹ *ᵥ x_in with hy
  set βc : QState N := V⁻¹ *ᵥ b with hβc
  set F : ℝ → QState N :=
    fun t n => Complex.exp (D n n * t) * (y n + ∫ s in 0..t, Complex.exp (-(D n n) * s) * βc n)
    with hF
  have hunit : V *ᵥ y = x_in := by
    rw [hy, Matrix.mulVec_mulVec, hV1, Matrix.one_mulVec]
  have hunitb : V *ᵥ βc = b := by
    rw [hβc, Matrix.mulVec_mulVec, hV1, Matrix.one_mulVec]
  have hu0 : V *ᵥ F 0 = x_in := by
    have hI : ∀ n : N, (∫ s in 0..0, Complex.exp (-(D n n) * s) * βc n) = 0 :=
      fun n => intervalIntegral.integral_same
    have hexp : ∀ n : N, Complex.exp (D n n * 0) = 1 := fun n => by simp
    have hFeq : F 0 = y := by
      funext n
      simp [hF]
    rw [hFeq, hunit]

  have hf : ∀ (n : N) (t : ℝ),
      HasDerivAt (F · n) (D n n * F t n + βc n) t := by
    intro n t
    have hexpd : HasDerivAt (fun s : ℝ => Complex.exp (D n n * (s : ℝ)))
        (Complex.exp (D n n * (t : ℝ)) * (D n n * (1 : ℂ))) t := by
      have h0 := (Complex.ofRealCLM.hasDerivAt (x := t)).const_smul (D n n)
      simpa only [smul_eq_mul] using! h0.cexp
    have hcont : Continuous fun s => Complex.exp (-(D n n) * (s : ℝ)) * βc n := by continuity
    have hIntd : HasDerivAt (fun s : ℝ => ∫ r in 0..s, Complex.exp (-(D n n) * (r : ℝ)) * βc n)
        (Complex.exp (-(D n n) * (t : ℝ)) * βc n) t :=
      intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
        hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
    have hmul : HasDerivAt (F · n)
        (Complex.exp (D n n * (t : ℝ)) * (D n n * (1 : ℂ)) *
            (y n + ∫ r in 0..t, Complex.exp (-(D n n) * (r : ℝ)) * βc n) +
          Complex.exp (D n n * (t : ℝ)) *
            (Complex.exp (-(D n n) * (t : ℝ)) * βc n)) t := by
      have h := (hexpd).mul (hIntd.const_add (y n))
      simpa only [hF] using! h
    refine hmul.congr_deriv ?_
    have hcancel : Complex.exp (D n n * (t : ℝ)) * Complex.exp (-(D n n) * (t : ℝ)) = 1 := by
      rw [← Complex.exp_add]
      simp
    simp only [hF]
    linear_combination βc n * hcancel

  have huder : ∀ t : ℝ, HasDerivAt (fun s => V *ᵥ F s)
      (A *ᵥ (V *ᵥ F t) + b) t := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    have hsum : HasDerivAt (fun s : ℝ => ∑ n : N, V i n * F s n)
      (∑ n : N, V i n * (D n n * F t n + βc n)) t :=
      HasDerivAt.fun_sum (fun n _ => ((hf n t).const_mul (V i n)))
    have hlhs : (fun s : ℝ => ∑ n : N, V i n * F s n) = fun s : ℝ => (V *ᵥ F s) i := by
      funext s
      rfl
    rw [hlhs] at hsum
    convert! hsum using 1
    have e1 : A *ᵥ (V *ᵥ F t) = V *ᵥ (D *ᵥ F t) := by
      have hinner : V⁻¹ *ᵥ (V *ᵥ F t) = F t := by
        rw [Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
      rw [hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinner]
    have hb : b i = ∑ n : N, V i n * βc n := by
      have h0 : (V *ᵥ βc) i = ∑ n : N, V i n * βc n := rfl
      rw [← h0, hunitb]
    have hsumeq : (V *ᵥ (D *ᵥ F t)) i = ∑ n : N, V i n * (D n n * F t n) := by
      show ∑ n : N, V i n * (D *ᵥ F t) n = ∑ n : N, V i n * (D n n * F t n)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [diag_mulVec D hd (F t) n]
    rw [e1, Pi.add_apply, hb, hsumeq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hfun := orderedForcedSolution_unique (fun _ => -A) (fun _ => b)
    (by continuity) (by continuity) 0 x_in (fun s => V *ᵥ F s) hu0
    (by
      intro s
      convert! huder s using 1
      simp only [Matrix.neg_mulVec, neg_neg])
  exact (congrFun hfun t).symm

end Duhamel

section BlockConj

variable {N : Type} [Fintype N] [DecidableEq N]

theorem taylorV2_inBlockClosed (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ) (x_in b : QState N)
    (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (a : ℕ) (ha : a < m) :
    ∀ (i : ℕ) (hi : i ≤ k),
    taylorBlock x ⟨a * (k + 1) + i, step_label_lt a m k p i ha hi⟩ =
      (((Nat.factorial i : ℕ) : ℂ)⁻¹) • (M ^ i *ᵥ
        taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩)
      + (if i = 0 then 0 else
          (((Nat.factorial i : ℕ) : ℂ)⁻¹) • (h • (M ^ (i - 1) *ᵥ b))) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hlab : (⟨a * (k + 1) + 0, step_label_lt a m k p 0 ha (Nat.zero_le k)⟩ :
        Fin (m * (k + 1) + p + 1)) =
        ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩ := by
      apply Fin.ext
      show a * (k + 1) + 0 = a * (k + 1)
      omega
    rw [hlab]
    simp
  | succ i ih =>
    intro hi
    have hstep := taylorV2_block_step m k p M h x_in b x hx a (i + 1) ha (by omega) hi
    have hprev : (⟨a * (k + 1) + (i + 1) - 1,
        pred_label_lt a m k p (i + 1) ha hi (by omega)⟩ : Fin (m * (k + 1) + p + 1)) =
        ⟨a * (k + 1) + i, step_label_lt a m k p i ha (by omega)⟩ := by
      apply Fin.ext
      show a * (k + 1) + (i + 1) - 1 = a * (k + 1) + i
      omega
    rw [hprev, ih (by omega)] at hstep
    rw [hstep]
    by_cases h0 : i = 0
    · subst h0
      simp
    · have him1 : ¬(i + 1 = 1) := by omega
      rw [if_neg (by omega : ¬(i = 0)), if_neg him1, if_neg (by omega : ¬(i + 1 = 0)), add_zero]
      have hexp : M ^ ((i + 1) - 1) = M ^ i := by
        congr 1
      rw [hexp]
      have hexp2 : M ^ ((i - 1) + 1) = M ^ i := by
        congr 1
        omega
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← pow_succ', Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        ← pow_succ', smul_add, smul_smul, smul_smul, hexp2]
      have hfacc : (((i + 1 : ℕ) : ℂ) * ((Nat.factorial i : ℕ) : ℂ))⁻¹ =
          (((Nat.factorial (i + 1) : ℕ) : ℂ))⁻¹ := by
        rw [show ((i + 1 : ℕ) : ℂ) * ((Nat.factorial i : ℕ) : ℂ) =
          ((Nat.factorial (i + 1) : ℕ) : ℂ) from by
          rw [Nat.factorial_succ, Nat.cast_mul]]
      rw [← mul_inv (((i + 1 : ℕ) : ℂ)) ((Nat.factorial i : ℕ) : ℂ), hfacc]

end BlockConj

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
