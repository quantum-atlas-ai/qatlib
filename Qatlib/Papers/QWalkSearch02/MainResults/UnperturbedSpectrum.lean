/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSearch02.MainResults.WalkDefs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace Qatlib.Papers.QWalkSearch02.MainResults

def W (n i : ℕ) : ℝ := Real.sqrt ((Nat.choose (n-1) i : ℝ) / (2:ℝ)^n)

lemma choose_succ_real {n i : ℕ} (hi : i + 1 < n) :
    (Nat.choose (n-1) (i+1) : ℝ) = (Nat.choose (n-1) i : ℝ) * (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)) := by
  have h := Nat.choose_succ_right_eq (n-1) i
  have h' : (Nat.choose (n-1) (i+1) : ℝ) * ((i:ℝ)+1) = (Nat.choose (n-1) i : ℝ) * ((n:ℝ)-1-(i:ℝ)) := by
    have hc : ((n - 1 - i : ℕ) : ℝ) = (n:ℝ) - 1 - (i:ℝ) := by
      rw [Nat.cast_sub (show i ≤ n-1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
      push_cast; ring
    have hcast : ((Nat.choose (n-1) (i+1) * (i+1) : ℕ) : ℝ) = ((Nat.choose (n-1) i * (n-1-i) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_mul] at hcast
    push_cast at hcast
    rw [hc] at hcast
    linarith [hcast]
  have hi1 : ((i:ℝ)+1) ≠ 0 := by positivity
  field_simp
  linarith [h']

lemma W_succ_mul {n i : ℕ} (hi : i + 1 < n) :
    W n (i+1) = W n i * Real.sqrt (((n:ℝ) - 1 - (i:ℝ)) / ((i:ℝ)+1)) := by
  unfold W
  rw [choose_succ_real hi]
  rw [show (Nat.choose (n-1) i : ℝ) * (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)) / (2:ℝ)^n
        = ((Nat.choose (n-1) i : ℝ)/(2:ℝ)^n) * (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)) by ring]
  rw [Real.sqrt_mul (by positivity)]

lemma sqrt_ratio_mul {n i : ℕ} (hi : i + 1 < n) :
    Real.sqrt (((i:ℝ)+1) * ((n:ℝ)-1-(i:ℝ)))
      * Real.sqrt (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)) = ((n:ℝ)-1-(i:ℝ)) := by
  have hi1 : (0:ℝ) < (i:ℝ)+1 := by positivity
  have hnr : (0:ℝ) < (n:ℝ)-1-(i:ℝ) := by
    have : (i:ℝ)+1 < (n:ℝ) := by exact_mod_cast hi
    linarith
  rw [← Real.sqrt_mul (le_of_lt (mul_pos hi1 hnr))]
  have hsq : (((i:ℝ)+1) * ((n:ℝ)-1-(i:ℝ))) * (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)) = ((n:ℝ)-1-(i:ℝ))^2 := by
    field_simp
  rw [hsq]
  exact Real.sqrt_sq (le_of_lt hnr)

lemma sinOmega_succ_eq {n i : ℕ} :
    sinOmega n ((i:ℕ)+1) = (2/(n:ℝ)) * Real.sqrt (((i:ℝ)+1) * ((n:ℝ)-1-(i:ℝ))) := by
  unfold sinOmega
  push_cast
  congr 1
  ring_nf

lemma cosOmega_succ_eq {n i : ℕ} :
    cosOmega n ((i:ℕ)+1) = 1 - 2*((i:ℝ)+1)/(n:ℝ) := by
  unfold cosOmega
  push_cast
  ring

lemma rowR {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    (if h : (i:ℕ)+1 < n then sinOmega n ((i:ℕ)+1) * W n ((i:ℕ)+1) else 0)
      - cosOmega n ((i:ℕ)+1) * W n (i:ℕ) = W n (i:ℕ) := by
  by_cases h : (i:ℕ)+1 < n
  · rw [dif_pos h, sinOmega_succ_eq, W_succ_mul h]
    rw [show 2 / (n:ℝ) * Real.sqrt (((i:ℝ)+1) * ((n:ℝ)-1-(i:ℝ)))
          * (W n (i:ℕ) * Real.sqrt (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1)))
        = (2/(n:ℝ) * W n (i:ℕ))
          * (Real.sqrt (((i:ℝ)+1) * ((n:ℝ)-1-(i:ℝ)))
             * Real.sqrt (((n:ℝ)-1-(i:ℝ))/((i:ℝ)+1))) by ring]
    rw [sqrt_ratio_mul h, cosOmega_succ_eq]
    have hnn : (0:ℝ) < n := by exact_mod_cast hn
    field_simp
    ring
  · rw [dif_neg h]
    have hi : (i:ℕ)+1 = n := by have := i.isLt; omega
    have hnn : (0:ℝ) < n := by exact_mod_cast hn
    have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnn
    have hc : cosOmega n n = -1 := by unfold cosOmega; field_simp; ring
    rw [hi, hc]
    ring

lemma W_sq {n k : ℕ} : (W n k)^2 = (Nat.choose (n-1) k : ℝ)/(2:ℝ)^n := by
  unfold W
  rw [Real.sq_sqrt (by positivity)]

lemma choose_pred_real {n i : ℕ} (h0 : 0 < i) (hin : i < n) :
    (Nat.choose (n-1) (i-1) : ℝ) = (Nat.choose (n-1) i : ℝ) * ((i:ℝ)/((n:ℝ)-(i:ℝ))) := by
  have h := choose_succ_real (n:=n) (i:=i-1) (by omega : (i-1)+1 < n)
  have h1 : (i-1)+1 = i := by omega
  have h2 : (((i-1:ℕ):ℝ)) = (i:ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ i by omega)]; push_cast; ring
  rw [h1, h2] at h
  have hn1 : ((n:ℝ)-1-((i:ℝ)-1)) = (n:ℝ)-(i:ℝ) := by ring
  have hi1 : (((i:ℝ)-1)+1) = (i:ℝ) := by ring
  rw [hn1, hi1] at h
  have hi : (i:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h0)
  have hlt : (i:ℝ) < (n:ℝ) := by exact_mod_cast hin
  have hni : (n:ℝ)-(i:ℝ) ≠ 0 := by linarith
  field_simp at h ⊢
  linarith [h]

lemma W_pred_mul {n i : ℕ} (h0 : 0 < i) (hin : i < n) :
    W n (i-1) = W n i * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))) := by
  have hlt : (i:ℝ) < (n:ℝ) := by exact_mod_cast hin
  have hni : (0:ℝ) < (n:ℝ)-(i:ℝ) := by linarith
  have hi : (0:ℝ) < (i:ℝ) := by exact_mod_cast h0
  have hR : 0 ≤ W n i * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (W n (i-1))^2 = (W n i * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))))^2 := by
    rw [W_sq, mul_pow, W_sq, Real.sq_sqrt (le_of_lt (div_pos hi hni))]
    rw [show (Nat.choose (n-1) i : ℝ)/(2:ℝ)^n * ((i:ℝ)/((n:ℝ)-(i:ℝ)))
          = (Nat.choose (n-1) (i-1) : ℝ)/(2:ℝ)^n by
      rw [choose_pred_real h0 hin]; field_simp]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have : 0 ≤ W n (i-1) := Real.sqrt_nonneg _
    linarith

lemma sqrt_ratio_mul2 {n i : ℕ} (h0 : 0 < i) (hin : i < n) :
    Real.sqrt ((i:ℝ)*((n:ℝ)-(i:ℝ))) * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))) = (i:ℝ) := by
  have hi : (0:ℝ) < (i:ℝ) := by exact_mod_cast h0
  have hlt : (i:ℝ) < (n:ℝ) := by exact_mod_cast hin
  have hni : (0:ℝ) < (n:ℝ)-(i:ℝ) := by linarith
  rw [← Real.sqrt_mul (le_of_lt (mul_pos hi hni))]
  have hsq : ((i:ℝ)*((n:ℝ)-(i:ℝ))) * ((i:ℝ)/((n:ℝ)-(i:ℝ))) = (i:ℝ)^2 := by field_simp
  rw [hsq, Real.sqrt_sq (le_of_lt hi)]

lemma rowL {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    cosOmega n (i:ℕ) * W n (i:ℕ)
      + (if h : 0 < (i:ℕ) then sinOmega n (i:ℕ) * W n ((i:ℕ)-1) else 0) = W n (i:ℕ) := by
  by_cases h0 : 0 < (i:ℕ)
  · rw [dif_pos h0, W_pred_mul h0 i.isLt]
    have hs : sinOmega n (i:ℕ) * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))) = (2/(n:ℝ))*(i:ℝ) := by
      rw [show sinOmega n (i:ℕ) = (2/(n:ℝ)) * Real.sqrt ((i:ℝ)*((n:ℝ)-(i:ℝ))) from rfl]
      rw [mul_assoc]
      congr 1
      exact sqrt_ratio_mul2 h0 i.isLt
    rw [show sinOmega n (i:ℕ) * (W n (i:ℕ) * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ))))
          = (sinOmega n (i:ℕ) * Real.sqrt ((i:ℝ)/((n:ℝ)-(i:ℝ)))) * W n (i:ℕ) by ring]
    rw [hs]
    rw [show cosOmega n (i:ℕ) = 1 - 2*(i:ℝ)/(n:ℝ) from rfl]
    have hnn : (0:ℝ) < n := by exact_mod_cast hn
    field_simp
    ring
  · rw [dif_neg h0]
    have hz : (i:ℕ) = 0 := by omega
    rw [hz]
    have hc : cosOmega n 0 = 1 := by unfold cosOmega; simp
    rw [hc]
    ring

lemma sum_ite_succ {n : ℕ} (i : Fin n) (f : ℕ → ℂ) :
    (∑ j : Fin n, if (j:ℕ) = (i:ℕ)+1 then f (j:ℕ) else 0)
      = if h : (i:ℕ)+1 < n then f ((i:ℕ)+1) else 0 := by
  by_cases h : (i:ℕ)+1 < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨(i:ℕ)+1, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      have hc : ¬ ((b:ℕ) = (i:ℕ)+1) := by
        intro he; exact hb (Fin.ext (by simpa using he))
      rw [if_neg hc]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have hc : ¬ ((b:ℕ) = (i:ℕ)+1) := by omega
    rw [if_neg hc]

lemma sum_ite_self {n : ℕ} (i : Fin n) (f : ℕ → ℂ) :
    (∑ j : Fin n, if (j:ℕ) = (i:ℕ) then f (j:ℕ) else 0) = f (i:ℕ) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hc : ¬ ((b:ℕ) = (i:ℕ)) := by
      intro he; exact hb (Fin.ext he)
    rw [if_neg hc]
  · intro hh; exact absurd (Finset.mem_univ _) hh

lemma sum_ite_pred {n : ℕ} (i : Fin n) (f : ℕ → ℂ) :
    (∑ j : Fin n, if (i:ℕ) = (j:ℕ)+1 then f (j:ℕ) else 0)
      = if h : 0 < (i:ℕ) then f ((i:ℕ)-1) else 0 := by
  by_cases h : 0 < (i:ℕ)
  · rw [dif_pos h, Finset.sum_eq_single (⟨(i:ℕ)-1, by omega⟩ : Fin n)]
    · simp only [Fin.val_mk]
      rw [if_pos (by omega)]
    · intro b _ hb
      have hc : ¬ ((i:ℕ) = (b:ℕ)+1) := by
        intro he; exact hb (Fin.ext (by simp only [Fin.val_mk]; omega))
      rw [if_neg hc]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have hc : ¬ ((i:ℕ) = (b:ℕ)+1) := by omega
    rw [if_neg hc]

theorem lineWalk_mulVec_linePsi0 {n : ℕ} (hn : 1 ≤ n) :
    lineWalk n *ᵥ linePsi0 n = linePsi0 n := by
  funext s
  rcases s with i | i
  · rw [show (lineWalk n *ᵥ linePsi0 n) (Sum.inl i)
          = ∑ j : LineIdx n, lineWalk n (Sum.inl i) j * linePsi0 n j from by
      rw [Matrix.mulVec]; simp [dotProduct]]
    rw [Fintype.sum_sum_type]
    rw [show linePsi0 n (Sum.inl i) = ((W n (i:ℕ) : ℝ) : ℂ) from rfl]
    have h1 : (∑ j : Fin n, lineWalk n (Sum.inl i) (Sum.inl j) * linePsi0 n (Sum.inl j))
        = (if h : (i:ℕ)+1 < n then ((sinOmega n ((i:ℕ)+1) * W n ((i:ℕ)+1) : ℝ) : ℂ) else 0) := by
      rw [show (∑ j : Fin n, lineWalk n (Sum.inl i) (Sum.inl j) * linePsi0 n (Sum.inl j))
            = ∑ j : Fin n, (if (j:ℕ) = (i:ℕ)+1 then ((sinOmega n (j:ℕ) * W n (j:ℕ) : ℝ) : ℂ) else 0) by
          apply Finset.sum_congr rfl
          intro j _
          rw [show linePsi0 n (Sum.inl j) = ((W n (j:ℕ) : ℝ) : ℂ) from rfl]
          simp only [lineWalk]
          split <;> simp [Complex.ofReal_mul]]
      exact sum_ite_succ i (fun k => ((sinOmega n k * W n k : ℝ) : ℂ))
    have h2 : (∑ j : Fin n, lineWalk n (Sum.inl i) (Sum.inr j) * linePsi0 n (Sum.inr j))
        = ((-cosOmega n ((i:ℕ)+1) * W n (i:ℕ) : ℝ) : ℂ) := by
      rw [show (∑ j : Fin n, lineWalk n (Sum.inl i) (Sum.inr j) * linePsi0 n (Sum.inr j))
            = ∑ j : Fin n, (if (j:ℕ) = (i:ℕ) then ((-cosOmega n ((i:ℕ)+1) * W n (j:ℕ) : ℝ) : ℂ) else 0) by
          apply Finset.sum_congr rfl
          intro j _
          rw [show linePsi0 n (Sum.inr j) = ((W n (j:ℕ) : ℝ) : ℂ) from rfl]
          simp only [lineWalk]
          split <;> simp [Complex.ofReal_mul]]
      exact sum_ite_self i (fun k => ((-cosOmega n ((i:ℕ)+1) * W n k : ℝ) : ℂ))
    rw [h1, h2]
    rw [show (if h : (i:ℕ)+1 < n then ((sinOmega n ((i:ℕ)+1) * W n ((i:ℕ)+1) : ℝ) : ℂ) else 0)
          = ((if h : (i:ℕ)+1 < n then sinOmega n ((i:ℕ)+1) * W n ((i:ℕ)+1) else 0 : ℝ) : ℂ) by
        split <;> simp]
    rw [← Complex.ofReal_add]
    congr 1
    linarith [rowR hn i]
  · rw [show (lineWalk n *ᵥ linePsi0 n) (Sum.inr i)
          = ∑ j : LineIdx n, lineWalk n (Sum.inr i) j * linePsi0 n j from by
      rw [Matrix.mulVec]; simp [dotProduct]]
    rw [Fintype.sum_sum_type]
    rw [show linePsi0 n (Sum.inr i) = ((W n (i:ℕ) : ℝ) : ℂ) from rfl]
    have h1 : (∑ j : Fin n, lineWalk n (Sum.inr i) (Sum.inl j) * linePsi0 n (Sum.inl j))
        = ((cosOmega n (i:ℕ) * W n (i:ℕ) : ℝ) : ℂ) := by
      rw [show (∑ j : Fin n, lineWalk n (Sum.inr i) (Sum.inl j) * linePsi0 n (Sum.inl j))
            = ∑ j : Fin n, (if (j:ℕ) = (i:ℕ) then ((cosOmega n (i:ℕ) * W n (j:ℕ) : ℝ) : ℂ) else 0) by
          apply Finset.sum_congr rfl
          intro j _
          rw [show linePsi0 n (Sum.inl j) = ((W n (j:ℕ) : ℝ) : ℂ) from rfl]
          simp only [lineWalk]
          split <;> simp [Complex.ofReal_mul]]
      exact sum_ite_self i (fun k => ((cosOmega n (i:ℕ) * W n k : ℝ) : ℂ))
    have h2 : (∑ j : Fin n, lineWalk n (Sum.inr i) (Sum.inr j) * linePsi0 n (Sum.inr j))
        = (if h : 0 < (i:ℕ) then ((sinOmega n (i:ℕ) * W n ((i:ℕ)-1) : ℝ) : ℂ) else 0) := by
      rw [show (∑ j : Fin n, lineWalk n (Sum.inr i) (Sum.inr j) * linePsi0 n (Sum.inr j))
            = ∑ j : Fin n, (if (i:ℕ) = (j:ℕ)+1 then ((sinOmega n (i:ℕ) * W n (j:ℕ) : ℝ) : ℂ) else 0) by
          apply Finset.sum_congr rfl
          intro j _
          rw [show linePsi0 n (Sum.inr j) = ((W n (j:ℕ) : ℝ) : ℂ) from rfl]
          simp only [lineWalk]
          split <;> simp [Complex.ofReal_mul]]
      exact sum_ite_pred i (fun k => ((sinOmega n (i:ℕ) * W n k : ℝ) : ℂ))
    rw [h1, h2]
    rw [show (if h : 0 < (i:ℕ) then ((sinOmega n (i:ℕ) * W n ((i:ℕ)-1) : ℝ) : ℂ) else 0)
          = ((if h : 0 < (i:ℕ) then sinOmega n (i:ℕ) * W n ((i:ℕ)-1) else 0 : ℝ) : ℂ) by
        split <;> simp]
    rw [← Complex.ofReal_add]
    congr 1
    linarith [rowL hn i]

theorem perturbedLineWalk_mulVec_linePsi0 {n : ℕ} (hn : 1 ≤ n) (o : Fin n) :
    perturbedLineWalk n o *ᵥ linePsi0 n
      = linePsi0 n - (fun (s : LineIdx n) => if s = (Sum.inr o : LineIdx n) then (2:ℂ) * linePsi0 n (Sum.inl o) else 0) := by
  have hB : perturbedLineWalk n o
      = lineWalk n - Matrix.of (fun (s t : LineIdx n) => if s = Sum.inr o ∧ t = Sum.inl o then (2:ℂ) else 0) := rfl
  rw [hB, Matrix.sub_mulVec, lineWalk_mulVec_linePsi0 hn]
  congr 1
  funext s
  rw [show (Matrix.of (fun (s t : LineIdx n) => if s = Sum.inr o ∧ t = Sum.inl o then (2:ℂ) else 0) *ᵥ linePsi0 n) s
        = ∑ t : LineIdx n, (if s = Sum.inr o ∧ t = Sum.inl o then (2:ℂ) else 0) * linePsi0 n t from by
      rw [Matrix.mulVec]; simp [dotProduct]]
  by_cases hs : s = Sum.inr o
  · subst hs
    rw [if_pos rfl, Finset.sum_eq_single (Sum.inl o)]
    · simp
    · intro b _ hb
      have hc : ¬ ((Sum.inr o : LineIdx n) = Sum.inr o ∧ b = (Sum.inl o : LineIdx n)) := by
        intro hh; exact hb hh.2
      rw [if_neg hc]; simp
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro b _
    have hc : ¬ (s = (Sum.inr o : LineIdx n) ∧ b = (Sum.inl o : LineIdx n)) := by
      intro hh; exact hs hh.1
    rw [if_neg hc]; simp

lemma cosOmega_sq_add_sinOmega_sq {n x : ℕ} (hn : 0 < n) (hx : x ≤ n) :
    cosOmega n x ^ 2 + sinOmega n x ^ 2 = 1 := by
  unfold cosOmega sinOmega
  have hnn : (0:ℝ) < n := by exact_mod_cast hn
  have hx' : (x:ℝ) ≤ (n:ℝ) := by exact_mod_cast hx
  have hprod : (0:ℝ) ≤ (x:ℝ) * ((n:ℝ) - (x:ℝ)) := by
    apply mul_nonneg (by positivity); linarith
  rw [mul_pow, Real.sq_sqrt hprod]
  field_simp
  ring

lemma choose_sum_fin {n : ℕ} (hn : 1 ≤ n) :
    (∑ i : Fin n, (Nat.choose (n - 1) (i:ℕ) : ℝ)) = (2:ℝ)^(n-1) := by
  have hr : Finset.range n = Finset.range ((n-1)+1) := by congr 1; omega
  rw [Fin.sum_univ_eq_sum_range (fun i => ((Nat.choose (n-1) i : ℕ) : ℝ)) n, hr]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

lemma half_eq {n : ℕ} (hn : 1 ≤ n) :
    ((2:ℝ)^(n-1) / (2:ℝ)^n) = 1/2 := by
  have hpow : (2:ℝ)^n = (2:ℝ)^(n-1) * 2 := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  rw [hpow]
  have hpos : ((2:ℝ)^(n-1)) ≠ 0 := by positivity
  field_simp

lemma innerC_linePsi0_self {n : ℕ} (hn : 1 ≤ n) :
    innerC (linePsi0 n) (linePsi0 n) = 1 := by
  unfold innerC linePsi0 lineIdxNat
  rw [Fintype.sum_sum_type]
  have key : ∀ i : Fin n,
      star (↑(Real.sqrt (((Nat.choose (n - 1) (i:ℕ) : ℝ) / (2:ℝ)^n))) : ℂ) *
        (↑(Real.sqrt (((Nat.choose (n - 1) (i:ℕ) : ℝ) / (2:ℝ)^n))) : ℂ)
      = (((Nat.choose (n - 1) (i:ℕ) : ℝ) / (2:ℝ)^n) : ℂ) := by
    intro i
    have hnn : (0:ℝ) ≤ ((Nat.choose (n - 1) (i:ℕ) : ℝ) / (2:ℝ)^n) := by positivity
    rw [show star ((Real.sqrt ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n) : ℝ) : ℂ)
          = ((Real.sqrt ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n) : ℝ) : ℂ) by simp]
    rw [← Complex.ofReal_mul]
    rw [show Real.sqrt ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n) *
          Real.sqrt ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n)
        = (Real.sqrt ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n))^2 by ring,
        Real.sq_sqrt hnn, Complex.ofReal_div, Complex.ofReal_pow]
  have hreal : (∑ i : Fin n, ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n)) = (1/2:ℝ) := by
    rw [← Finset.sum_div, choose_sum_fin hn, half_eq hn]
  have hS : (∑ i : Fin n, (((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n) : ℂ)) = (1/2:ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, ← hreal]
    simpa using (Complex.ofReal_sum Finset.univ
      (fun i : Fin n => ((Nat.choose (n-1) (i:ℕ) : ℝ) / (2:ℝ)^n))).symm
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [hS]; norm_num

lemma linePsi0_inl_eq_inr (n : ℕ) (i : Fin n) :
    linePsi0 n (Sum.inl i) = linePsi0 n (Sum.inr i) := rfl

lemma linePsi1_inr_eq_neg (m : ℕ) (i : Fin (2*m)) :
    linePsi1 m (Sum.inr i) = - linePsi1 m (Sum.inl i) := by
  unfold linePsi1
  by_cases h : (i:ℕ) < m
  · simp [h]
  · simp [h]

lemma innerC_linePsi0_linePsi1 (m : ℕ) :
    innerC (linePsi0 (2*m)) (linePsi1 m) = 0 := by
  unfold innerC
  rw [Fintype.sum_sum_type]
  have hstar : ∀ i : Fin (2*m),
      star (linePsi0 (2*m) (Sum.inl i)) = linePsi0 (2*m) (Sum.inl i) := by
    intro i; unfold linePsi0 lineIdxNat
    simp
  have h2 : (∑ i : Fin (2*m), star (linePsi0 (2*m) (Sum.inr i)) * linePsi1 m (Sum.inr i))
      = - (∑ i : Fin (2*m), star (linePsi0 (2*m) (Sum.inl i)) * linePsi1 m (Sum.inl i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [linePsi0_inl_eq_inr, linePsi1_inr_eq_neg]
    ring
  rw [h2]
  ring
end Qatlib.Papers.QWalkSearch02.MainResults
