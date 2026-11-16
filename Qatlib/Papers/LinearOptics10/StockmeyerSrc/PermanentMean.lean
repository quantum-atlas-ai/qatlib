/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.SignChar
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.RyserBound
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section


/-! # Actual Boolean Ryser averaging and the permanent norm bound

Aaronson--Arkhipov, arXiv:1011.3245v1, Lemma 63 and Corollary 65.
Finite distributivity expands the real estimator. Missing-coordinate
sign flips kill exactly the nonpermutation assignments, giving the true
permanent identity before applying the already proved spectral bound.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentMean
open Qatlib.Foundations.ProbabilityCore.Concentration
open Qatlib.Foundations.PureStateMath.LinearChange.MatrixNorm
open SignMoments SignChar RyserBound

/-- Genuine finite permutations are precisely the bijective self-assignment functions. -/
def permEquiv (I : Type*) :
    Equiv.Perm I ≃ {f : I → I // Function.Bijective f} where
  toFun e := ⟨e, e.bijective⟩
  invFun f := Equiv.ofBijective f.1 f.2
  left_inv e := by ext i; rfl
  right_inv f := Subtype.ext rfl

/-- Summing genuine bijective assignment weights is the actual permutation sum. -/
theorem permSum {I : Type*} [Fintype I] [DecidableEq I] (w : (I → I) → ℂ) :
    (∑ e : Equiv.Perm I, w e) = ∑ f : I → I, if Function.Bijective f then w f else 0 := by
  calc
    _ = ∑ f : {f : I → I // Function.Bijective f}, w f.1 :=
      Fintype.sum_equiv (permEquiv I) _ _ (fun _ => rfl)
    _ = ∑ f ∈ Finset.univ.filter Function.Bijective, w f :=
      (Finset.sum_subtype _ (fun f => by simp) w).symm
    _ = _ := by rw [Finset.sum_filter]

/-- The actual signed row-product estimator expands into genuine assignment characters. -/
theorem expansion (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → Bool) :
    rysSum V (fun i => rSign (b i)) =
      ∑ f : Fin n → Fin n, (∏ i, V i (f i))*character b f := by
  simp only [rysSum, Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib, character]
  ring

/-- Actual averaging of the signed estimator is exactly the matrix permanent times its number of seeds. -/
theorem sumEstimator (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) :
    (∑ b : Fin n → Bool, rysSum V (fun i => rSign (b i))) =
      (Fintype.card (Fin n → Bool) : ℂ)*Matrix.permanent V := by
  simp_rw [expansion]
  rw [Finset.sum_comm]
  have he : (∑ f : Fin n → Fin n, (∏ i, V i (f i)) * ∑ b : Fin n → Bool, character b f) =
      (Fintype.card (Fin n → Bool) : ℂ) *
        ∑ f : Fin n → Fin n, if Function.Bijective f then (∏ i, V i (f i)) else 0 := by
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [characterSum]
    split_ifs <;> ring
  simp_rw [← Finset.mul_sum]
  rw [he, ← permSum]
  have hp : (∑ e : Equiv.Perm (Fin n), ∏ i, V i (e i)) = Matrix.permanent V := by
    change Matrix.permanent Vᵀ = Matrix.permanent V
    exact Matrix.permanent_transpose V
  rw [hp]

/-- The entire original permanent spectral-norm bound follows from the actual finite signed average. -/
theorem permanentBound (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.permanent V‖ ≤ matOpNorm V^n := by
  have hc : (0 : ℝ) < Fintype.card (Fin n → Bool) := by exact_mod_cast Fintype.card_pos
  have hb (b : Fin n → Bool) : ‖rysSum V (fun i => rSign (b i))‖ ≤ matOpNorm V^n := by
    apply estimatorBound n V _
    intro i
    cases b i <;> simp [rSign]
  have he : (Fintype.card (Fin n → Bool) : ℝ)*‖Matrix.permanent V‖ ≤
      (Fintype.card (Fin n → Bool) : ℝ)*matOpNorm V^n := by
    calc
      _ = ‖(Fintype.card (Fin n → Bool) : ℂ)*Matrix.permanent V‖ := by simp
      _ = ‖∑ b : Fin n → Bool, rysSum V (fun i => rSign (b i))‖ := by rw [sumEstimator]
      _ ≤ ∑ b : Fin n → Bool, ‖rysSum V (fun i => rSign (b i))‖ := norm_sum_le _ _
      _ ≤ ∑ _b : Fin n → Bool, matOpNorm V^n := Finset.sum_le_sum fun b _ => hb b
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ hc).mp he

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentMean
