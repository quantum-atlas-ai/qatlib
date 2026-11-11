/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Moment bounds on symmetric product grids

This module proves covariance and even-moment inequalities for coordinate sums on finite
symmetric grids. It also bounds the second moment of a tensor polynomial by the corresponding
even moment of the coordinate sum, providing the concentration estimates used with
[GilyenArunachalamWiebe2019].

## Main statements

* `tensorGrid_even_moment_bound`: the `2*k` moment sum is at most `|S|^d * (d*k/2)^k`.
* `tensorGrid_tensor_second_moment`: bounded tensor coefficients give a second moment controlled
  by the coordinate-sum moment.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

/-- For `j ≤ 2*k`, the symmetric pair `a^j*b^(2*k-j) + a^(2*k-j)*b^j` is bounded by
`a^(2*k)+b^(2*k)` for real `a` and `b`. -/
private theorem tensorGrid_mixed_pair (a b : ℝ) (k j : ℕ) (hj : j≤2*k) :
    a^j*b^(2*k-j)+a^(2*k-j)*b^j≤a^(2*k)+b^(2*k) := by
  have hp : |a|^j*|b|^(2*k-j)+|a|^(2*k-j)*|b|^j≤|a|^(2*k)+|b|^(2*k) := by
    have he : |a|^(2*k)+|b|^(2*k)-(|a|^j*|b|^(2*k-j)+|a|^(2*k-j)*|b|^j)=
        (|a|^j-|b|^j)*(|a|^(2*k-j)-|b|^(2*k-j)) := by
      have ha : |a|^j*|a|^(2*k-j)=|a|^(2*k) := by rw [← pow_add,show j+(2*k-j)=2*k by omega]
      have hb : |b|^j*|b|^(2*k-j)=|b|^(2*k) := by rw [← pow_add,show j+(2*k-j)=2*k by omega]
      calc
        _ = |a|^j*|a|^(2*k-j)+|b|^j*|b|^(2*k-j)-
          (|a|^j*|b|^(2*k-j)+|a|^(2*k-j)*|b|^j) := by rw [ha,hb]
        _ = _ := by ring
    rcases le_total |a| |b| with h|h
    · have h1 := pow_le_pow_left₀ (abs_nonneg _) h j
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h (2*k-j)
      have hmul := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
      nlinarith
    · have h1 := pow_le_pow_left₀ (abs_nonneg _) h j
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h (2*k-j)
      have hmul := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
      nlinarith
  have hleft : a^j*b^(2*k-j)+a^(2*k-j)*b^j≤|a|^j*|b|^(2*k-j)+|a|^(2*k-j)*|b|^j := by
    simpa only [abs_mul,abs_pow] using
        add_le_add (le_abs_self (a^j*b^(2*k-j))) (le_abs_self (a^(2*k-j)*b^j))
  have ha : |a|^(2*k)=a^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  have hb : |b|^(2*k)=b^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  exact hleft.trans (by simpa only [ha,hb] using hp)

/-- Twice the degree-`2*k` mixed-power sum is at most `(2*k+1)*(a^(2*k)+b^(2*k))` for real `a`
and `b`. -/
private theorem tensorGrid_geometric_sum_bound (a b : ℝ) (k : ℕ) :
    2*(∑ j∈Finset.range (2*k+1),a^j*b^(2*k-j))≤(2*k+1 : ℝ)*(a^(2*k)+b^(2*k)) := by
  have hr : (∑ j∈Finset.range (2*k+1),a^(2*k-j)*b^j)=
      ∑ j∈Finset.range (2*k+1),a^j*b^(2*k-j) := by
    have h := Finset.sum_range_reflect (fun j => a^j*b^(2*k-j)) (2*k+1)
    simp only [Nat.add_sub_cancel] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show 2*k-(2*k-j)=j by omega]
  have h := Finset.sum_le_sum (s := Finset.range (2*k+1))
    (fun j hj => tensorGrid_mixed_pair a b k j (by have := Finset.mem_range.mp hj; omega))
  rw [Finset.sum_add_distrib,hr] at h
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,two_mul] using h

/-- For `|x| ≤ 1/2`, bounds `x*((z+x)^(2*k+1)-(z-x)^(2*k+1))` by `(2*k+1)/4` times the sum of
the adjacent even powers. -/
theorem tensorGrid_covariance_pair (z x : ℝ) (k : ℕ) (hx : |x|≤1/2) :
    x*((z+x)^(2*k+1)-(z-x)^(2*k+1))≤
      ((2*k+1 : ℝ)/4)*((z+x)^(2*k)+(z-x)^(2*k)) := by
  let a := z+x
  let b := z-x
  let T := ∑ j∈Finset.range (2*k+1),a^j*b^(2*k-j)
  have hg := (Commute.all a b).mul_geom_sum₂ (2*k+1)
  simp only [Nat.add_sub_cancel] at hg
  have he : x*(a^(2*k+1)-b^(2*k+1))=2*x^2*T := by
    rw [← hg]
    dsimp [a,b,T]
    ring
  have hsum := tensorGrid_geometric_sum_bound a b k
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg x)
  have hx2 : x^2≤(1/4 : ℝ) := by
    have h := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ)≤1/2)).mpr hx
    norm_num [sq_abs] at h
    exact h
  have heven0 : 0≤a^(2*k)+b^(2*k) := by
    apply add_nonneg <;> rw [pow_mul]
    · exact pow_nonneg (sq_nonneg a) k
    · exact pow_nonneg (sq_nonneg b) k
  have hnonneg : 0≤(2*k+1 : ℝ)*(a^(2*k)+b^(2*k)) := mul_nonneg (by positivity) heven0
  have hupper := mul_le_mul_of_nonneg_right hx2 hnonneg
  change x*(a^(2*k+1)-b^(2*k+1))≤_
  rw [he]
  dsimp [T] at *
  nlinarith

/-- Negating the argument permutes the sum of any real-valued function over a finite set closed
under negation. -/
theorem tensorGrid_sum_neg (S : Finset ℝ) (hS : ∀ v∈S,-v∈S) (F : ℝ → ℝ) :
    (∑ v∈S,F (-v))=∑ v∈S,F v := by
  apply Finset.sum_bij (fun v _ => -v)
  · exact hS
  · intro a _ b _ h; exact neg_injective h
  · intro v hv; exact ⟨-v,hS v hv,neg_neg v⟩
  · intro v _; rfl

/-- On a finite symmetric set in `[-1/2, 1/2]`, the sum of `v*(z+v)^(2*k+1)` is at most
`(2*k+1)/4` times the sum of `(z+v)^(2*k)`. -/
theorem tensorGrid_coordinate_covariance (S : Finset ℝ) (hS : ∀ v∈S,-v∈S)
    (hbound : ∀ v∈S,|v|≤1/2) (z : ℝ) (k : ℕ) :
    (∑ v∈S,v*(z+v)^(2*k+1))≤((2*k+1 : ℝ)/4)*(∑ v∈S,(z+v)^(2*k)) := by
  have hsum :=
      Finset.sum_le_sum (s := S) (fun v hv => tensorGrid_covariance_pair z v k (hbound v hv))
  have hminus : (∑ v∈S,v*(z-v)^(2*k+1))=-(∑ v∈S,v*(z+v)^(2*k+1)) := by
    have h := tensorGrid_sum_neg S hS (fun v => v*(z+v)^(2*k+1))
    simp only [neg_mul,← sub_eq_add_neg,Finset.sum_neg_distrib] at h
    linarith
  have heven : (∑ v∈S,(z-v)^(2*k))=∑ v∈S,(z+v)^(2*k) := by
    simpa only [← sub_eq_add_neg] using tensorGrid_sum_neg S hS (fun v => (z+v)^(2*k))
  simp only [mul_sub,Finset.sum_sub_distrib] at hsum
  rw [← Finset.mul_sum,Finset.sum_add_distrib,hminus,heven] at hsum
  nlinarith

/-- The involutive equivalence that exchanges coordinate `i` of a grid vector with an additional
grid element. -/
def tensorGridSwap {d : ℕ} (S : Finset ℝ) (i : Fin d) :
    ((Fin d → S)×S)≃((Fin d → S)×S) where
  toFun p := (Function.update p.1 i p.2,p.1 i)
  invFun p := (Function.update p.1 i p.2,p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j=i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j=i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp

/-- Summing a function over every grid vector and every replacement of one fixed coordinate
gives `S.card` times its sum over the grid. -/
theorem tensorGrid_sum_update {d : ℕ} (S : Finset ℝ) (i : Fin d) (F : (Fin d → S) → ℝ) :
    (∑ y : Fin d → S,∑ v : S,F (Function.update y i v))=(S.card : ℝ)*(∑ y : Fin d → S,F y) := by
  have h := (tensorGridSwap S i).sum_comp (fun p : (Fin d → S)×S => F p.1)
  simp only [Fintype.sum_prod_type,tensorGridSwap,Equiv.coe_fn_mk,Finset.sum_const,
    Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at h
  simpa only [Finset.mul_sum,mul_comm] using h

/-- Replacing coordinate `i` changes the coordinate sum by subtracting the old entry and adding
the replacement. -/
theorem tensorGrid_coordinate_sum_update {d : ℕ} (S : Finset ℝ) (i : Fin d) (y : Fin d → S) (v : S) :
    (∑ j : Fin d,((Function.update y i v) j : ℝ))=
      (∑ j : Fin d,(y j : ℝ))-(y i : ℝ)+(v : ℝ) := by
  have h1 := Finset.add_sum_erase Finset.univ (fun j : Fin d => (y j : ℝ)) (Finset.mem_univ i)
  have h2 :=
      Finset.add_sum_erase Finset.univ (fun j : Fin d => ((Function.update y i v) j : ℝ))
      (Finset.mem_univ i)
  have he : (∑ j∈Finset.univ.erase i,((Function.update y i v) j : ℝ))=∑ j∈Finset.univ.erase i,(y j : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he] at h2
  simp only [Function.update_self] at h2
  linarith

/-- On a nonempty symmetric bounded product grid, the mixed moment of one coordinate with the
odd power of the coordinate sum is at most `(2*k+1)/4` times the corresponding even moment. -/
theorem tensorGrid_full_coordinate_covariance (d : ℕ) (S : Finset ℝ) (hS : ∀ v∈S,-v∈S)
    (hbound : ∀ v∈S,|v|≤1/2) (hne : S.Nonempty) (i : Fin d) (k : ℕ) :
    (∑ y : Fin d → S,(y i : ℝ)*(∑ j : Fin d,(y j : ℝ))^(2*k+1))≤
      ((2*k+1 : ℝ)/4)*(∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k)) := by
  have hp (y : Fin d → S) :
      (∑ v : S,(v : ℝ)*(∑ j : Fin d,((Function.update y i v) j : ℝ))^(2*k+1))≤
        ((2*k+1 : ℝ)/4)*(∑ v : S,(∑ j : Fin d,((Function.update y i v) j : ℝ))^(2*k)) := by
    simp_rw [tensorGrid_coordinate_sum_update]
    have h := tensorGrid_coordinate_covariance S hS hbound ((∑ j : Fin d,(y j : ℝ))-(y i : ℝ)) k
    rw [← Finset.sum_coe_sort S (fun v : ℝ => v*((∑ j : Fin d,(y j : ℝ))-(y i : ℝ)+v)^(2*k+1)),
      ← Finset.sum_coe_sort S (fun v : ℝ => ((∑ j : Fin d,(y j : ℝ))-(y i : ℝ)+v)^(2*k))] at h
    exact h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hp y)
  have hl : (∑ y : Fin d → S,∑ v : S,(v : ℝ)*(∑ j : Fin d,((Function.update y i v) j : ℝ))^(2*k+1))=
      (S.card : ℝ)*(∑ y : Fin d → S,(y i : ℝ)*(∑ j : Fin d,(y j : ℝ))^(2*k+1)) := by
    simpa only [Function.update_self] using tensorGrid_sum_update S i
      (fun y => (y i : ℝ)*(∑ j : Fin d,(y j : ℝ))^(2*k+1))
  have hr := tensorGrid_sum_update S i (fun y => (∑ j : Fin d,(y j : ℝ))^(2*k))
  rw [hl,← Finset.mul_sum,hr] at hsum
  have hc : (0 : ℝ)<S.card := by exact_mod_cast hne.card_pos
  nlinarith

/-- On a nonempty symmetric grid in `[-1/2, 1/2]`, the sum of the `2*k` powers of the coordinate
sum is at most `|S|^d*(d*k/2)^k`. -/
theorem tensorGrid_even_moment_bound (d k : ℕ) (S : Finset ℝ) (hS : ∀ v∈S,-v∈S)
    (hbound : ∀ v∈S,|v|≤1/2) (hne : S.Nonempty) :
    (∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k))≤
      ((S.card : ℝ)^d)*((d : ℝ)*k/2)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*(k+1)))=
        ∑ i : Fin d,∑ y : Fin d → S,(y i : ℝ)*(∑ j : Fin d,(y j : ℝ))^(2*k+1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul,show 2*(k+1)=2*k+1+1 by omega,pow_succ]
      ring
    rw [he]
    have hc : 0≤(2*k+1 : ℝ)/4 := by positivity
    have hnext : (2*k+1 : ℝ)/4*(d : ℝ)≤(d : ℝ)*(k+1)/2 := by
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ)≤d)]
    have hp : ((d : ℝ)*k/2)^k≤((d : ℝ)*(k+1)/2)^k := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ)≤d)]
    calc
      _ ≤ ∑ _i : Fin d,((2*k+1 : ℝ)/4)*(∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k)) :=
        Finset.sum_le_sum (fun i _ => tensorGrid_full_coordinate_covariance d S hS hbound hne i k)
      _ = ((2*k+1 : ℝ)/4)*(d : ℝ)*(∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k)) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ ((2*k+1 : ℝ)/4)*(d : ℝ)*(((S.card : ℝ)^d)*((d : ℝ)*k/2)^k) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg hc (Nat.cast_nonneg d))
      _ ≤ ((2*k+1 : ℝ)/4)*(d : ℝ)*(((S.card : ℝ)^d)*((d : ℝ)*(k+1)/2)^k) := by gcongr
      _ ≤ ((d : ℝ)*(k+1)/2)*(((S.card : ℝ)^d)*((d : ℝ)*(k+1)/2)^k) :=
        mul_le_mul_of_nonneg_right hnext (by positivity)
      _ = _ := by push_cast; rw [pow_succ]; ring

/-- Every power sum over a finite real set closed under negation is nonnegative. -/
theorem tensorGrid_scalar_moment_nonneg (S : Finset ℝ) (hS : ∀ v∈S,-v∈S) (n : ℕ) :
    0≤∑ v∈S,v^n := by
  rcases Nat.even_or_odd n with he|ho
  · exact Finset.sum_nonneg (fun v _ => he.pow_nonneg v)
  · have h := tensorGrid_sum_neg S hS (fun v => v^n)
    simp only [ho.neg_pow,Finset.sum_neg_distrib] at h
    linarith

/-- The sum of a coordinate monomial over a finite symmetric product grid is nonnegative,
including repeated coordinate indices. -/
theorem tensorGrid_monomial_sum_nonneg {J : Type} [Fintype J] (d : ℕ) (S : Finset ℝ)
    (hS : ∀ v∈S,-v∈S) (a : J → Fin d) :
    0≤∑ y : Fin d → S,∏ i : J,(y (a i) : ℝ) := by
  classical
  let c := fun j : Fin d => (Finset.univ.filter fun i : J => a i=j).card
  have hprod (y : Fin d → S) : (∏ i : J,(y (a i) : ℝ))=∏ j : Fin d,(y j : ℝ)^(c j) := by
    have h := Finset.prod_fiberwise' (Finset.univ : Finset J) a (fun j => (y j : ℝ))
    simpa only [Finset.prod_const] using h.symm
  simp_rw [hprod]
  have hp := Fintype.prod_sum (fun j : Fin d => fun v : S => (v : ℝ)^(c j))
  rw [← hp]
  apply Finset.prod_nonneg
  intro j _
  have h := tensorGrid_scalar_moment_nonneg S hS (c j)
  rw [← Finset.sum_coe_sort S (fun v : ℝ => v^(c j))] at h
  exact h

/-- For tensor coefficients bounded in absolute value by one on a finite symmetric grid, the
tensor polynomial's second-moment sum is at most the `2*k` moment sum of the coordinate sum. -/
theorem tensorGrid_tensor_second_moment (d k : ℕ) (S : Finset ℝ) (hS : ∀ v∈S,-v∈S)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ a,|H a|≤1) :
    (∑ y : Fin d → S,(∑ a : Fin k → Fin d,H a*(∏ i : Fin k,(y (a i) : ℝ)))^2)≤
      ∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k) := by
  classical
  have hm (a b : Fin k → Fin d) : 0≤∑ y : Fin d → S,
      (∏ i : Fin k,(y (a i) : ℝ))*(∏ i : Fin k,(y (b i) : ℝ)) := by
    simpa only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr] using
      tensorGrid_monomial_sum_nonneg (J := Fin k⊕Fin k) d S hS (Sum.elim a b)
  have hcoef (a b : Fin k → Fin d) : H a*H b≤1 := by
    have hp := mul_le_mul (hH a) (hH b) (abs_nonneg (H b)) zero_le_one
    exact (le_abs_self _).trans (by simpa only [abs_mul,one_mul] using hp)
  have hpower (y : Fin d → S) : (∑ a : Fin k → Fin d,∏ i : Fin k,(y (a i) : ℝ))=(∑ j : Fin d,(y j : ℝ))^k := by
    have h := Fintype.prod_sum (fun _ : Fin k => fun j : Fin d => (y j : ℝ))
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h.symm
  have hexpand (F : (Fin k → Fin d) → ℝ) (y : Fin d → S) :
      (∑ a : Fin k → Fin d,F a*(∏ i : Fin k,(y (a i) : ℝ)))^2=
        ∑ a : Fin k → Fin d,∑ b : Fin k → Fin d,
          (F a*F b)*((∏ i : Fin k,(y (a i) : ℝ))*(∏ i : Fin k,(y (b i) : ℝ))) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have heq (F : (Fin k → Fin d) → ℝ) :
      (∑ y : Fin d → S,(∑ a : Fin k → Fin d,F a*(∏ i : Fin k,(y (a i) : ℝ)))^2)=
        ∑ a : Fin k → Fin d,∑ b : Fin k → Fin d,(F a*F b)*
          (∑ y : Fin d → S,(∏ i : Fin k,(y (a i) : ℝ))*(∏ i : Fin k,(y (b i) : ℝ))) := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  have hunweighted :
      (∑ a : Fin k → Fin d,∑ b : Fin k → Fin d,
        ∑ y : Fin d → S,(∏ i : Fin k,(y (a i) : ℝ))*(∏ i : Fin k,(y (b i) : ℝ)))=
          ∑ y : Fin d → S,(∑ j : Fin d,(y j : ℝ))^(2*k) := by
    have h := heq (fun _ => 1)
    simp only [one_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro y _
    simp only [hpower]
    rw [← pow_mul,Nat.mul_comm]
  rw [heq,← hunweighted]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_of_le_one_left (hm a b) (hcoef a b)

end Qatlib.Concepts.GradientOracle.GradientAlgo
