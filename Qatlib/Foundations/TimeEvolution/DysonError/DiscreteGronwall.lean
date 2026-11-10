/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.DysonError

def propagatedError (eps gain : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n,eps j*∏ k ∈ Finset.Icc (j+1) n,(1+gain k)

theorem propagatedError_succ (eps gain : ℕ → ℝ) (n : ℕ) :
    propagatedError eps gain (n+1)=(1+gain (n+1))*propagatedError eps gain n+eps (n+1) := by
  unfold propagatedError
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hlast : eps (n+1)*∏ k ∈ Finset.Icc (n+1+1) (n+1),(1+gain k)=eps (n+1) := by
    rw [Finset.Icc_eq_empty (by omega),Finset.prod_empty,mul_one]
  rw [hlast]
  have hfac : (∑ j ∈ Finset.Icc 1 n,eps j*∏ k ∈ Finset.Icc (j+1) (n+1),(1+gain k))=
      (∑ j ∈ Finset.Icc 1 n,eps j*∏ k ∈ Finset.Icc (j+1) n,(1+gain k))*(1+gain (n+1)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.prod_Icc_succ_top (by have h:=(Finset.mem_Icc.mp hj).2;omega)]
    ring
  rw [hfac]
  ring

theorem error_le_propagated (error eps gain : ℕ → ℝ) (hzero : error 0=0)
    (hgain : ∀ n,0≤gain n)
    (hstep : ∀ n,error (n+1)≤(1+gain (n+1))*error n+eps (n+1)) :
    ∀ n,error n≤propagatedError eps gain n
  | 0 => by simp [propagatedError,hzero]
  | n+1 => by
    rw [propagatedError_succ]
    have hi:=error_le_propagated error eps gain hzero hgain hstep n
    have hm:=mul_le_mul_of_nonneg_left hi (show 0≤1+gain (n+1) by linarith [hgain (n+1)])
    linarith [hstep n]
end Qatlib.Foundations.TimeEvolution.DysonError
