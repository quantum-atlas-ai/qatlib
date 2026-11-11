/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressNativePilot
import Mathlib.Algebra.BigOperators.Intervals

set_option backward.isDefEq.respectTransparency false

/-!
Scalar Poincare on an even-length open path. A midpoint anchor and Cauchy
bound give variance <= ell/4 times the sum over actual adjacent path edges.
The endpoint energy excludes any wraparound edge. This is the one-dimensional
component; tensorization and original-grid energy transport remain separate.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxPoincare

/-- Construction for path Energy in the partial address path poincare model. -/
def pathEnergy (f : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico a b,(f (j+1)-f j)^2

/-- Complete original `energy_nonneg` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem energy_nonneg (f : ℕ → ℝ) (a b : ℕ) : 0 ≤ pathEnergy f a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Complete original `interval_square` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem interval_square (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (f b-f a)^2 ≤ ((b-a : ℕ) : ℝ)*pathEnergy f a b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico a b)
    (fun j => f (j+1)-f j) (fun _ => (1 : ℝ))
  simpa only [mul_one,one_pow,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,
    Finset.sum_Ico_sub f hab,pathEnergy,mul_comm] using h

/-- Complete original `energy_mono` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem energy_mono (f : ℕ → ℝ) (a b c d : ℕ) (hac : a ≤ c) (hdb : d ≤ b) :
    pathEnergy f c d ≤ pathEnergy f a b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · intro j _ _
    exact sq_nonneg _

/-- Complete original `left_anchor` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem left_anchor (f : ℕ → ℝ) (m i : ℕ) (hi : i< m) :
    (f i-f m)^2 ≤ (m : ℝ)*pathEnergy f 0 m := by
  have hs := interval_square f i m hi.le
  have he := energy_mono f 0 m i m (Nat.zero_le _) le_rfl
  have hc : ((m-i : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m i
  have hprod := mul_le_mul hc he (energy_nonneg f i m) (Nat.cast_nonneg m)
  nlinarith

/-- Complete original `right_anchor` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem right_anchor (f : ℕ → ℝ) (m i : ℕ) (hi0 : m ≤ i) (hi1 : i<2*m) :
    (f i-f m)^2 ≤ (m : ℝ)*pathEnergy f m (2*m-1) := by
  have hs := interval_square f m i hi0
  have he := energy_mono f m (2*m-1) m i le_rfl (by omega)
  have hc : ((i-m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show i-m ≤ m by omega)
  exact hs.trans (mul_le_mul hc he (energy_nonneg f m i) (Nat.cast_nonneg m))

/-- Complete original `anchor_sum` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem anchor_sum (f : ℕ → ℝ) (m : ℕ) (hm : 0< m) :
    (∑ i : Fin (2*m),(f i.val-f m)^2) ≤
      (m : ℝ)^2*pathEnergy f 0 (2*m-1) := by
  have hsplit : (∑ i : Fin (2*m),(f i.val-f m)^2)=
      (∑ i : Fin m,(f i.val-f m)^2)+(∑ i : Fin m,(f (m+i.val)-f m)^2) := by
    rw [show 2*m=m+m by omega]
    simpa only [Fin.val_castAdd,Fin.val_natAdd] using
      Fin.sum_univ_add (fun i : Fin (m+m) => (f i.val-f m)^2)
  rw [hsplit]
  calc
    _ ≤ (∑ _ : Fin m,(m : ℝ)*pathEnergy f 0 m)+
        (∑ _ : Fin m,(m : ℝ)*pathEnergy f m (2*m-1)) :=
      add_le_add (Finset.sum_le_sum fun i _ => left_anchor f m i.val i.isLt)
        (Finset.sum_le_sum fun i _ => right_anchor f m (m+i.val) (by omega) (by omega))
    _ = (m : ℝ)^2*(pathEnergy f 0 m+pathEnergy f m (2*m-1)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ = _ := by rw [pathEnergy,pathEnergy,pathEnergy,Finset.sum_Ico_consecutive _ (Nat.zero_le m) (by omega)]

/-- Construction for path Mean in the partial address path poincare model. -/
noncomputable def pathMean (f : ℕ → ℝ) (ell : ℕ) : ℝ :=
  (∑ i : Fin ell,f i.val)/(ell : ℝ)

/-- Complete original `centered_le_anchor` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem centered_le_anchor (f : ℕ → ℝ) (ell : ℕ) (hell : 0<ell) (a : ℝ) :
    (∑ i : Fin ell,(f i.val-pathMean f ell)^2) ≤ ∑ i : Fin ell,(f i.val-a)^2 := by
  have hp : (ell : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hell
  have he : (∑ i : Fin ell,(f i.val-a)^2)=
      (∑ i : Fin ell,(f i.val-pathMean f ell)^2)+(ell : ℝ)*(pathMean f ell-a)^2 := by
    have hsum : (∑ i : Fin ell,f i.val)=(ell : ℝ)*pathMean f ell := by
      unfold pathMean
      field_simp
    have hterm (i : Fin ell) : (f i.val-a)^2=(f i.val-pathMean f ell)^2+
        2*(f i.val-pathMean f ell)*(pathMean f ell-a)+(pathMean f ell-a)^2 := by ring
    have hcross : (∑ i : Fin ell,2*(f i.val-pathMean f ell)*(pathMean f ell-a))=0 := by
      rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_sub_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [hsum]
      ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [hcross]
    ring
  have hpos := mul_nonneg (Nat.cast_nonneg ell) (sq_nonneg (pathMean f ell-a))
  linarith

/-- Complete original `even_path_poincare` guarantee for `PartialAddressPathPoincare`; all source hypotheses and output obligations are retained. -/
theorem even_path_poincare (f : ℕ → ℝ) (m : ℕ) (hm : 0< m) :
    (∑ i : Fin (2*m),(f i.val-pathMean f (2*m))^2)/((2*m : ℕ) : ℝ) ≤
      (((2*m : ℕ) : ℝ)/4)*pathEnergy f 0 (2*m-1) := by
  have hs := (centered_le_anchor f (2*m) (by omega) (f m)).trans (anchor_sum f m hm)
  have hp : (0 : ℝ)<((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0<2*m by omega)
  apply (div_le_iff₀ hp).mpr
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hs ⊢
  nlinarith

#print axioms interval_square
#print axioms energy_mono
#print axioms anchor_sum
#print axioms centered_le_anchor
#print axioms even_path_poincare
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxPoincare
