/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOneDimErrorStat
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOriginalContract
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceTaylor

/-!
# One-dimensional central-difference error and the step sign

`centralDifferenceOneDimError` proves the exponential Taylor-remainder bound for nonnegative
step size. The proof uses exactness on the Taylor polynomial and an absolute weighted power-sum
estimate.

`not_centralDifferenceOneDimError` refutes the legacy unrestricted-step contract: at a negative
step, its ordered derivative-bound interval can be empty. See [GilyenArunachalamWiebe2019] for
background.

## Main statements

* `not_centralDifferenceOneDimError`: The legacy error contract without a nonnegative-step
  hypothesis is false, as witnessed by a cubic at a negative step.
* `centralDifferenceOneDimError`: For nonnegative step `δ`, the stated smoothness and derivative
  bound give central-difference error at most `exp (-(1 / 2) * m) * B * |δ| ^ (2 * m + 1)`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.DifferenceError

/-- The legacy error contract without a nonnegative-step hypothesis is false, as witnessed by a
cubic at a negative step. -/
theorem not_centralDifferenceOneDimError : ¬CentralDifferenceOneDimErrorLegacy := by
  intro h
  have he := h 1 (by norm_num) (-1) 0 (fun x : ℝ => x ^ 3) (contDiff_id.pow 3) (by
    intro ξ hξ
    rcases hξ with ⟨hlo, hhi⟩
    norm_num at hlo hhi
    linarith)
  have hs : Finset.Ico (-1 : ℤ) 2 = {-1, 0, 1} := by decide
  norm_num [hs, centralDiffCoeff, deriv_pow_field] at he

/-- For nonnegative step `δ`, the stated smoothness and derivative bound give central-difference
error at most `exp (-(1 / 2) * m) * B * |δ| ^ (2 * m + 1)`. -/
theorem centralDifferenceOneDimError : CentralDifferenceOneDimError := by
  intro m hm δ B hδ f hf hbound
  let S := Finset.Ico (-(m : ℤ)) ((m : ℤ)+1)
  have hs0 : (∑ l∈S,centralDiffCoeff m l)=0 := by
    simpa [S] using! centralDiffCoeff_even_moment m 0
  by_cases hd0 : δ=0
  · subst δ
    have hsum : (∑ l∈S,centralDiffCoeff m l*f 0)=0 := by rw [← Finset.sum_mul,hs0,zero_mul]
    simp only [mul_zero,abs_zero,zero_pow (by omega : 2*m+1≠0),mul_zero]
    change |0-(∑ l∈S,centralDiffCoeff m l*f 0)|≤0
    rw [hsum]
    norm_num
  · have hd : 0<δ := lt_of_le_of_ne hδ (Ne.symm hd0)
    have h0 : (0 : ℝ)∈Set.Icc (-(m : ℝ)*δ) ((m : ℝ)*δ) := by
      constructor <;> nlinarith [(Nat.cast_nonneg m : (0 : ℝ)≤m)]
    have hB : 0≤B := (abs_nonneg _).trans (hbound 0 h0)
    let J := fun x : ℝ => centralDiffTaylorJet f (2*m) x
    have hjet : (∑ l∈S,centralDiffCoeff m l*J ((l : ℝ)*δ))=deriv f 0*δ :=
      centralDiff_taylor_jet_action m hm f δ
    have herr : deriv f 0*δ-(∑ l∈S,centralDiffCoeff m l*f ((l : ℝ)*δ))=
        ∑ l∈S,centralDiffCoeff m l*(J ((l : ℝ)*δ)-f ((l : ℝ)*δ)) := by
      rw [← hjet]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hlocal (l : ℤ) (hl : l∈S) :
        |centralDiffCoeff m l*(J ((l : ℝ)*δ)-f ((l : ℝ)*δ))|≤
          (B*|δ|^(2*m+1)/(Nat.factorial (2*m+1) : ℝ))*|centralDiffCoeff m l*(l : ℝ)^(2*m+1)| := by
      by_cases hl0 : l=0
      · subst l; simp [centralDiffCoeff]
      · have hlr : (l : ℝ)≠0 := by exact_mod_cast hl0
        have hx : (l : ℝ)*δ≠0 := mul_ne_zero hlr hd0
        have hmem := Finset.mem_Ico.mp hl
        have hlo : -(m : ℝ)≤(l : ℝ) := by exact_mod_cast hmem.1
        have hhi : (l : ℝ)≤(m : ℝ) := by
          exact_mod_cast (by omega : l≤(m : ℤ))
        have hleft := mul_le_mul_of_nonneg_right hlo hδ
        have hright := mul_le_mul_of_nonneg_right hhi hδ
        have hb (u : ℝ) (hu : u∈Set.uIcc 0 ((l : ℝ)*δ)) : |iteratedDeriv (2*m+1) f u|≤B := by
          apply hbound u
          rcases Set.mem_uIcc.mp hu with hu|hu <;> constructor <;> linarith
        have hr := centralDiff_taylor_remainder f (2*m) hf ((l : ℝ)*δ) B hx hb
        rw [abs_sub_comm] at hr
        have hmul := mul_le_mul_of_nonneg_left hr (abs_nonneg (centralDiffCoeff m l))
        convert! hmul using 1
        all_goals try dsimp [J]
        all_goals simp only [abs_mul,abs_pow,mul_pow]
        all_goals ring
    have htail := centralDifferencePowerSumBound m (2*m) hm le_rfl
    have hpref := centralDiff_remainder_prefactor m hm
    have hfactor : 0≤B*|δ|^(2*m+1)/(Nat.factorial (2*m+1) : ℝ) := by positivity
    rw [herr]
    calc
      _ ≤ ∑ l∈S,|centralDiffCoeff m l*(J ((l : ℝ)*δ)-f ((l : ℝ)*δ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l∈S,(B*|δ|^(2*m+1)/(Nat.factorial (2*m+1) : ℝ))*|centralDiffCoeff m l*(l : ℝ)^(2*m+1)| :=
        Finset.sum_le_sum hlocal
      _ = (B*|δ|^(2*m+1)/(Nat.factorial (2*m+1) : ℝ))*(∑ l∈S,|centralDiffCoeff m l*(l : ℝ)^(2*m+1)|) := by rw [Finset.mul_sum]
      _ ≤ (B*|δ|^(2*m+1)/(Nat.factorial (2*m+1) : ℝ))*
          (6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^(((2*m : ℕ) : ℝ)+3/2)) :=
        mul_le_mul_of_nonneg_left htail hfactor
      _ = (B*|δ|^(2*m+1))*(6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^(((2*m : ℕ) : ℝ)+3/2)/(Nat.factorial (2*m+1) : ℝ)) := by ring
      _ ≤ (B*|δ|^(2*m+1))*Real.exp (-(1/2 : ℝ)*(m : ℝ)) :=
        mul_le_mul_of_nonneg_left hpref (by positivity)
      _ = _ := by ring

end Qatlib.Concepts.GradientOracle.DifferenceError
