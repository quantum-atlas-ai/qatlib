/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.CommutingCopyExactTightnessStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.SupNormTightCopyBudgetQuan
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs

/-!
# Exact commuting examples for copy exponentiation

This module analyzes fresh-copy partial-swap evolution for a two-dimensional commuting family.
One step rescales the second diagonal weight by cos² θ, so repeated equal-angle steps give an
exact error formula.

`commutingCopyExactTightness` also supplies a lower bound on the resulting cosine deficit,
illustrating the copy dependence of density-matrix exponentiation [LloydMohseniRebentrost2014].

## Main statements

* `diag_run`: computes the repeated partial-swap output on the diagonal family.
* `commutingCopyExactTightness`: proves the exact error and cosine lower-bound specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder
set_option autoImplicit false

/-- The two-dimensional diagonal projector with diagonal entries one and zero. -/
private noncomputable def rho2 : Operator 2 :=
  Matrix.diagonal fun b => if b=0 then 1 else 0
/-- The two-dimensional diagonal operator with diagonal entries `1 - s` and `s`. -/
private noncomputable def sigma2 (s : ℝ) : Operator 2 :=
  Matrix.diagonal fun b => if b=0 then ((1-s:ℝ):ℂ) else (s:ℂ)

/-- The diagonal projector `rho2` is a density operator. -/
private theorem rho2_density : IsDensityOperator rho2 := by
  constructor
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split <;> norm_num
  · simp [rho2, Matrix.trace]

/-- A partial-swap step on the diagonal family replaces `s` by `cos² θ * s`, with a
one-dimensional reference factor. -/
private theorem diag_step (θ s : ℝ) :
    partialSwapReferenceOutput rho2 θ 1 (TensorGate (sigma2 s) (1:Operator 1)) =
      TensorGate (sigma2 ((Real.cos θ)^2*s)) (1:Operator 1) := by
  have ht : Matrix.traceLeft (TensorGate (sigma2 s) (1:Operator 1)) = 1 := by
    ext i j
    simp [Matrix.traceLeft, tensorGate_apply, sigma2, Fin.sum_univ_two]
    ring
  rw [(partial_swap_reference_output_formula rho2 rho2_density θ 1 _).1, ht]
  have hsc := Real.cos_sq_add_sin_sq θ
  ext ⟨i,a⟩ ⟨j,b⟩
  have ha : a=0 := Subsingleton.elim _ _
  have hb : b=0 := Subsingleton.elim _ _
  subst a
  subst b
  fin_cases i <;> fin_cases j <;>
    simp [tensorGate_apply, rho2, sigma2, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, Matrix.diagonal_apply]
  have hc : Complex.cos (θ:ℂ)^2 + Complex.sin (θ:ℂ)^2 = 1 := by
    have hh := congrArg Complex.ofReal hsc
    simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.ofReal_one] at hh
    exact hh
  linear_combination hc

/-- Repeating the same partial-swap angle `n` times replaces the diagonal weight `s` by `cos θ`
to the power `2 * n` times `s`. -/
private theorem diag_run (θ s : ℝ) (n : ℕ) :
    freshCopyReferenceRun rho2 (List.replicate n θ) 1
      (TensorGate (sigma2 s) (1:Operator 1)) =
      TensorGate (sigma2 ((Real.cos θ)^(2*n)*s)) (1:Operator 1) := by
  induction n generalizing s with
  | zero => simp [freshCopyReferenceRun]
  | succ n ih =>
    change freshCopyReferenceRun rho2 (List.replicate n θ) 1
      (partialSwapReferenceOutput rho2 θ 1 (TensorGate (sigma2 s) (1:Operator 1))) = _
    rw [diag_step, ih]
    congr 2
    rw [show 2*(n+1)=2*n+2 by omega, pow_add]
    ring

/-- For `0 ≤ y ≤ 1` and `n * y ≤ 1`, the deficit `1 - (1 - y)^n` is at least `n * y / 2`. -/
private theorem bernoulli_lower (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (n : ℕ) (hny : (n:ℝ)*y ≤ 1) :
    (n:ℝ)*y/2 ≤ 1-(1-y)^n := by
  have hp : (1-y)^n*(1+(n:ℝ)*y) ≤ 1 := by
    clear hny
    induction n with
    | zero => simp
    | succ n ih =>
      have hfac : (1-y)*(1+((n+1:ℕ):ℝ)*y) ≤ 1+(n:ℝ)*y := by
        push_cast
        nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) (sq_nonneg y)]
      have hpow : 0 ≤ (1-y)^n := pow_nonneg (by linarith) _
      calc
        (1-y)^(n+1)*(1+((n+1:ℕ):ℝ)*y) =
          (1-y)^n*((1-y)*(1+((n+1:ℕ):ℝ)*y)) := by rw [pow_succ]; ring
        _ ≤ (1-y)^n*(1+(n:ℝ)*y) := mul_le_mul_of_nonneg_left hfac hpow
        _ ≤ 1 := ih
  have hq : 0 ≤ (1-y)^n := pow_nonneg (by linarith) _
  have hr : (1-y)^n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hh : 0 ≤ (1-(n:ℝ)*y)*(1-(1-y)^n) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- For `t ≥ 0`, `n > 0`, and `t² ≤ n`, the deficit `1 - cos(t/n)^(2n)` is at least `t²/(8n)`. -/
private theorem cosine_lower (t : ℝ) (n : ℕ) (ht : 0 ≤ t) (hn : 0 < n)
    (hsq : t^2 ≤ (n:ℝ)) :
    t^2/(8*(n:ℝ)) ≤ 1-(Real.cos (t/(n:ℝ)))^(2*n) := by
  let τ := t/(n:ℝ)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hnr1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have htau0 : 0 ≤ τ := by dsimp [τ]; positivity
  have htau1 : τ ≤ 1 := by
    apply (div_le_iff₀ hnr).mpr
    nlinarith [hsq]
  have hsin : τ/2 ≤ Real.sin τ := by
    rcases eq_or_lt_of_le htau0 with hz | hp
    · simp [← hz]
    · have h : τ - τ ^ 3 / 4 < Real.sin τ := by
        linarith [Real.sin_gt_sub_cube hp, pow_nonneg hp.le 3]
      have hτsq : τ^2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hτsq htau0]
  have hs0 : 0 ≤ Real.sin τ := by linarith
  have hsmall : (n:ℝ)*τ^2 ≤ 1 := by
    dsimp [τ]
    field_simp
    nlinarith [hsq]
  have htrig := Real.cos_sq_add_sin_sq τ
  have hy1 : (Real.sin τ)^2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos τ)]
  have hny : (n:ℝ)*(Real.sin τ)^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x:=τ)) (by positivity)).trans hsmall
  have hb := bernoulli_lower ((Real.sin τ)^2) (sq_nonneg _) hy1 n hny
  rw [show 1-(Real.sin τ)^2 = (Real.cos τ)^2 by linarith, ← pow_mul] at hb
  have hsl : τ^2/4 ≤ (Real.sin τ)^2 := by nlinarith
  have hh : (n:ℝ)*τ^2/8 ≤ 1-(Real.cos τ)^(2*n) := by
    nlinarith [mul_le_mul_of_nonneg_left hsl (show (0:ℝ)≤n by positivity)]
  convert hh using 1
  dsimp [τ]
  field_simp

/-- Proves the exact commuting-family output and trace-norm formulas together with the cosine
deficit lower bound. This quantifies the fresh-copy error in the density-matrix
exponentiation setting of [LloydMohseniRebentrost2014]. -/
theorem commutingCopyExactTightness : CommutingCopyExactTightness := by
  intro t n s ht hn hsq hs0 _hs1
  let q := (Real.cos (t/(n:ℝ)))^(2*n)
  have hr := diag_run (t/(n:ℝ)) s n
  have he : freshCopyReferenceRun rho2 (List.replicate n (t/(n:ℝ))) 1
      (TensorGate (sigma2 s) (1:Operator 1)) - TensorGate (sigma2 s) (1:Operator 1) =
      (1-q) • (TensorGate rho2 (1:Operator 1)-TensorGate (sigma2 s) (1:Operator 1)) := by
    rw [hr]
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases i <;> fin_cases j <;>
      simp [tensorGate_apply, rho2, sigma2, Subsingleton.elim a b, q] <;> ring
  have hnorm : Matrix.traceNorm (TensorGate rho2 (1:Operator 1)-
      TensorGate (sigma2 s) (1:Operator 1)) = 2*s := by
    rw [tensorGate_sub_left, traceNorm_tensor_one]
    have hd : rho2-sigma2 s = Matrix.diagonal (fun b : Fin 2 =>
        ((if b=0 then s else -s : ℝ):ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rho2,sigma2]
    rw [hd, real_diagonal_traceNorm]
    simp [Fin.sum_univ_two, abs_of_nonneg hs0]
    ring
  have hq : q ≤ 1 := by
    dsimp [q]
    rw [pow_mul]
    apply pow_le_one₀ (sq_nonneg _)
    have hh := Real.cos_sq_add_sin_sq (t/(n:ℝ))
    nlinarith [sq_nonneg (Real.sin (t/(n:ℝ)))]
  refine ⟨he, ?_, cosine_lower t n ht hn hsq⟩
  change Matrix.traceNorm (freshCopyReferenceRun rho2 _ 1 (TensorGate (sigma2 s) _) -
    TensorGate (sigma2 s) _) = _
  rw [he, RCLike.real_smul_eq_coe_smul (K:=ℂ), Matrix.traceNorm_smul, hnorm]
  change ‖((1-q:ℝ):ℂ)‖*(2*s) = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-q)]
  ring
end Qatlib.Concepts.CopyEvolution.CopyExponent
