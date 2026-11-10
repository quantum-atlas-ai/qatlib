/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentHami
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators Classical

private theorem plus_product_factorial (k q : ℕ) :
    (∏ j ∈ Finset.range k, (q+j+2 : ℝ)) * ((q+1).factorial : ℝ) =
      ((k+q+1).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    calc
      _ = (q+k+2 : ℝ) * ((∏ j ∈ Finset.range k, (q+j+2 : ℝ)) *
        ((q+1).factorial : ℝ)) := by ring
      _ = (q+k+2 : ℝ) * ((k+q+1).factorial : ℝ) := by rw [ih]
      _ = _ := by
        conv_rhs => rw [show k+1+q+1 = (k+q+1)+1 by omega, Nat.factorial_succ]
        push_cast
        ring

private theorem minus_product_factorial (k q : ℕ) (hq : q < k) :
    (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else (q : ℝ)-j) =
      (q.factorial : ℝ) * (-1 : ℝ)^(k-q-1) * ((k-q-1).factorial : ℝ) := by
  have hk : k = (q+1)+(k-q-1) := by omega
  rw [hk, Finset.prod_range_add, Finset.prod_range_succ]
  have hl : (∏ j ∈ Finset.range q, if j=q then (1 : ℝ) else (q : ℝ)-j) =
      (q.factorial : ℝ) := by
    calc
      _ = ∏ j ∈ Finset.range q, (q-j : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (by have h := Finset.mem_range.mp hj; omega)]
      _ = _ := by
        rw [Finset.prod_range_natCast_sub]
        norm_cast
        rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hr : (∏ j ∈ Finset.range (k-q-1), if q+1+j=q then (1 : ℝ) else
      (q : ℝ)-(q+1+j)) = (-1 : ℝ)^(k-q-1) * ((k-q-1).factorial : ℝ) := by
    calc
      _ = ∏ j ∈ Finset.range (k-q-1), (-1 : ℝ)*(j+1) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [if_neg (by omega)]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_range]
        congr 1
        norm_cast
        exact Finset.prod_range_add_one_eq_factorial _
  rw [hl]
  simp only [ite_true, mul_one]
  have ht : q+1+(k-q-1)-q-1 = k-q-1 := by omega
  simp only [ht]
  push_cast
  rw [hr]
  ring

private theorem denominator_factorial (k q : ℕ) (hq : q < k) :
    (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else
      (q+1 : ℝ)^2-(j+1 : ℝ)^2) * (2*(q+1 : ℝ)^2) =
      (-1 : ℝ)^(k-q-1) * (((k+q+1).factorial : ℝ)*((k-q-1).factorial : ℝ)) := by
  let a := ∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else (q : ℝ)-j
  let b := ∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else (q+j+2 : ℝ)
  have hab : (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else
      (q+1 : ℝ)^2-(j+1 : ℝ)^2) = a*b := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : j=q <;> simp only [h, if_true, if_false]
    all_goals ring
  have ha : a = (q.factorial : ℝ)*(-1 : ℝ)^(k-q-1)*((k-q-1).factorial : ℝ) :=
    minus_product_factorial k q hq
  have hb : b * (2*(q+1 : ℝ)) * ((q+1).factorial : ℝ) = ((k+q+1).factorial : ℝ) := by
    have hm := Finset.mem_range.mpr hq
    have he : b*(2*(q+1 : ℝ)) = ∏ j ∈ Finset.range k, (q+j+2 : ℝ) := by
      rw [← Finset.prod_erase_mul (Finset.range k) (fun j => (q+j+2 : ℝ)) hm]
      change b * (2*(q+1 : ℝ)) = _ * (q+q+2 : ℝ)
      have hb' : b = ∏ j ∈ (Finset.range k).erase q, (q+j+2 : ℝ) := by
        dsimp [b]
        rw [← Finset.prod_erase_mul (Finset.range k) _ hm]
        simp only [ite_true, mul_one]
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_erase.mp hj).1]
      rw [hb']
      ring
    rw [he]
    exact plus_product_factorial k q
  rw [hab, ha]
  calc
    _ = (-1 : ℝ)^(k-q-1)*((k-q-1).factorial : ℝ)*
      (b*(2*(q+1 : ℝ))*((q+1).factorial : ℝ)) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
    _ = _ := by rw [hb]; ring

private theorem small_product_numerator (k q : ℕ) (hq : q < k) :
    (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else
      (q+1 : ℝ)^2/((q+1 : ℝ)^2-(j+1 : ℝ)^2)) *
    (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else
      (q+1 : ℝ)^2-(j+1 : ℝ)^2) = (q+1 : ℝ)^(2*(k-1)) := by
  have he : (∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else (q+1 : ℝ)^2) =
      ((q+1 : ℝ)^2)^(k-1) := by
    rw [← Finset.prod_erase_mul (Finset.range k) _ (Finset.mem_range.mpr hq)]
    simp only [ite_true, mul_one]
    calc
      _ = ∏ _j ∈ (Finset.range k).erase q, (q+1 : ℝ)^2 := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_erase.mp hj).1]
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hq)]
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ j ∈ Finset.range k, if j=q then (1 : ℝ) else (q+1 : ℝ)^2 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j=q
      · simp [h]
      · simp only [if_neg h]
        have hd : (q+1 : ℝ)^2-(j+1 : ℝ)^2 ≠ 0 := by
          apply sub_ne_zero.mpr
          intro he
          have hEq := (sq_eq_sq₀ (by positivity : (0 : ℝ) ≤ q+1)
            (by positivity : (0 : ℝ) ≤ j+1)).mp he
          have hn : q+1 = j+1 := by exact_mod_cast hEq
          omega
        exact div_mul_cancel₀ _ hd
    _ = _ := by rw [he, ← pow_mul]

private theorem coefficient_split (k : ℕ) (N : ℝ) (q : Fin (k+1)) (hq : q.val < k) :
    mCoeff k N q =
      (∏ j ∈ Finset.range k, if j=q.val then (1 : ℝ) else
        (q.val+1 : ℝ)^2/((q.val+1 : ℝ)^2-(j+1 : ℝ)^2)) *
          ((q.val+1 : ℝ)^2/((q.val+1 : ℝ)^2-N^2)) := by
  have hlast : (Fin.last k : Fin (k+1)) ≠ q := by
    intro h
    have he := congrArg Fin.val h
    simp at he
    omega
  calc
    _ = (∏ j : Fin k, if j.val=q.val then (1 : ℝ) else
          (q.val+1 : ℝ)^2/((q.val+1 : ℝ)^2-(j.val+1 : ℝ)^2)) *
          ((q.val+1 : ℝ)^2/((q.val+1 : ℝ)^2-N^2)) := by
      unfold mCoeff
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        simp [mNode, hq, Fin.ext_iff]
      · simp [mNode, hq, hlast]
    _ = _ := by
      rw [Fin.prod_univ_eq_prod_range
        (fun j => if j=q.val then (1 : ℝ) else
          (q.val+1 : ℝ)^2/((q.val+1 : ℝ)^2-(j+1 : ℝ)^2)) k]

theorem multiproductCoeffClosedForm : MultiproductCoeffClosedForm := by
  intro k hk N hN hd q hq
  let p : ℝ := q.val+1
  let a : ℝ := ∏ j ∈ Finset.range k, if j=q.val then (1 : ℝ) else p^2/(p^2-(j+1 : ℝ)^2)
  let d : ℝ := ∏ j ∈ Finset.range k, if j=q.val then (1 : ℝ) else p^2-(j+1 : ℝ)^2
  let sign : ℝ := (-1 : ℝ)^(k-q.val-1)
  have hsign : sign*sign = 1 := by
    dsimp [sign]
    rw [← mul_pow]
    norm_num
  have hden : p^2-N^2 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have he : mNode k N q^2 = mNode k N (Fin.last k)^2 := by simpa [p, mNode, hq] using h
    have hq' := multiproduct_squared_nodes_injective k N hN hd he
    have hv := congrArg Fin.val hq'
    simp at hv
    omega
  have hc : mCoeff k N q*(p^2-N^2) = a*p^2 := by
    rw [coefficient_split k N q hq]
    change (a*(p^2/(p^2-N^2)))*(p^2-N^2) = _
    rw [mul_assoc, div_mul_cancel₀ _ hden]
  have hn : a*d = p^(2*(k-1)) := small_product_numerator k q.val hq
  have hdf : d*(2*p^2) = sign*
      (((k+q.val+1).factorial : ℝ)*((k-q.val-1).factorial : ℝ)) :=
    denominator_factorial k q.val hq
  have hf : (((k+q.val+1).factorial : ℝ)*((k-q.val-1).factorial : ℝ)) = sign*d*(2*p^2) := by
    calc
      _ = (sign*sign)*(((k+q.val+1).factorial : ℝ)*((k-q.val-1).factorial : ℝ)) := by rw [hsign, one_mul]
      _ = sign*(sign*(((k+q.val+1).factorial : ℝ)*((k-q.val-1).factorial : ℝ))) := by ring
      _ = sign*(d*(2*p^2)) := by rw [hdf]
      _ = _ := by ring
  change mCoeff k N q*(p^2-N^2)*
      (((k+q.val+1).factorial : ℝ)*((k-q.val-1).factorial : ℝ)) = sign*2*p^(2*(k+1))
  rw [hc, hf]
  calc
    _ = sign*2*(a*d)*p^4 := by ring
    _ = sign*2*p^(2*(k-1))*p^4 := by rw [hn]
    _ = _ := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

end Qatlib.Papers.HamLCUSim12.Multiproduct
