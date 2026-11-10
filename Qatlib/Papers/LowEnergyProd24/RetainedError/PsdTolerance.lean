/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedError.PsdChain
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace Qatlib.Papers.LowEnergyProd24.RetainedError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

theorem polynomial_exp_decay (P : Polynomial ℝ) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => P.eval x*Real.exp (-(c*x))) atTop (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    · funext x
      simp only [Polynomial.eval_add, add_mul]
    · simp only [zero_add]
  | monomial n a =>
    have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (tendsto_id.const_mul_atTop hc)
    have hcne : c ≠ 0 := hc.ne'
    convert hh.const_mul (a/c^n) using 1
    · funext x
      simp only [Polynomial.eval_monomial, Function.comp_apply, id_eq]
      rw [mul_pow]
      field_simp
    · simp only [mul_zero]

def chainPolynomial (L k d : ℕ) (J : ℝ) : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, _ => 0
  | n+1, D => 2*(D+Polynomial.X)*chainPolynomial L k d J n (D+Polynomial.X)+
      Polynomial.C (sourceEll L k d J n)

theorem chainRemainder_factor (L k d : ℕ) (J gap : ℝ) (n : ℕ) (D : Polynomial ℝ) :
    chainRemainder L k d J n (D.eval gap) gap =
      (2*Real.exp (-2*(1/(2*J*k*d))*gap)*sourceEll L k d J 0)*
        (chainPolynomial L k d J n D).eval gap := by
  induction n generalizing D with
  | zero => simp only [chainRemainder, chainPolynomial, Polynomial.eval_zero, mul_zero]
  | succ n ih =>
    simp only [chainRemainder, chainPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_C]
    have hrec := ih (D+Polynomial.X)
    simp only [Polynomial.eval_add, Polynomial.eval_X] at hrec
    rw [hrec]
    ring

theorem actual_chainRemainder_decay (L k d n : ℕ) (J : ℝ) (hJ : 0 < J)
    (hk : 0 < k) (hd : 0 < d) (Δ : ℝ) :
    Tendsto (fun gap : ℝ => chainRemainder L k d J n Δ gap) atTop (𝓝 0) := by
  let c : ℝ := 2*(1/(2*J*k*d))
  have hc : 0 < c := by dsimp [c]; positivity
  have hp := (polynomial_exp_decay (chainPolynomial L k d J n (Polynomial.C Δ)) c hc).const_mul
    (2*sourceEll L k d J 0)
  convert hp using 1
  · funext gap
    have hf := chainRemainder_factor L k d J gap n (Polynomial.C Δ)
    simp only [Polynomial.eval_C] at hf
    rw [hf]
    have he : -2*(1/(2*J*k*d))*gap=-(c*gap) := by dsimp [c]; ring
    rw [he]
    ring
  · simp only [mul_zero]

theorem actual_psd_tolerance_cutoffs (h : Hamiltonian N R M k d J)
    (hp : ∀ i, (h.term i).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (L : ℕ) (hL : ∀ m, (h.labels m).card ≤ L) (seed : Fin M) (xs : List (Fin M))
    (Δ θ : ℝ) (hΔ : 0 ≤ Δ) (hθ : 0 < θ) :
    ∃ gap : ℝ, 0 < gap ∧
      ‖low h.total h.total_hermitian Δ*nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
        2^xs.length*(Δ+xs.length*gap)^(xs.length+1)+θ := by
  have hdecay := actual_chainRemainder_decay L k d xs.length J hJ hk hd Δ
  have he : ∀ᶠ gap : ℝ in atTop, chainRemainder L k d J xs.length Δ gap < θ :=
    hdecay.eventually (gt_mem_nhds hθ)
  obtain ⟨gap, hrem, hg⟩ := (he.and (eventually_ge_atTop (1 : ℝ))).exists
  have hgap : 0 < gap := lt_of_lt_of_le zero_lt_one hg
  exact ⟨gap, hgap, (actual_psd_cutoff_chain h hp hJ hk hd L hL seed xs Δ gap hΔ hgap.le).trans
    (add_le_add le_rfl hrem.le)⟩
end Qatlib.Papers.LowEnergyProd24.RetainedError
