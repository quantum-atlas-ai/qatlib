/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.HermitianRankLogStability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open MeasureTheory
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Matrix
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K]

def factorKernel (a : K → I → ℂ) (b : K → J → ℂ) : Matrix I J ℂ :=
  fun i j => ∑ k,a k i*b k j

omit [Fintype J] [DecidableEq J] [DecidableEq I] in

theorem weighted_vector_energy (a : K → I → ℂ) (u : EuclideanSpace ℂ I) (R : ℝ)
    (ha : ∀ i,∑ k,‖a k i‖^2≤R) :
    (∑ k,‖(WithLp.toLp 2 (fun i => a k i*u i):EuclideanSpace ℂ I)‖^2)≤R*‖u‖^2 := by
  have he (k : K) : ‖(WithLp.toLp 2 (fun i => a k i*u i):EuclideanSpace ℂ I)‖^2=
      ∑ i,‖a k i‖^2*‖u i‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change ‖a k i*u i‖^2=‖a k i‖^2*‖u i‖^2
    rw [norm_mul,mul_pow]
  simp only [he,EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)

omit [DecidableEq I] in

theorem factorKernel_pairing (a : K → I → ℂ) (b : K → J → ℂ) (X : Matrix I J ℂ)
    (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J) :
    inner ℂ u ((factorKernel a b ⊙ X).toEuclideanLin v)=
      ∑ k,inner ℂ (WithLp.toLp 2 (fun i => star (a k i)*u i))
        (X.toEuclideanLin (WithLp.toLp 2 (fun j => b k j*v j))) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Matrix.toLpLin_apply,
    Matrix.mulVec,Matrix.hadamard_apply,factorKernel,
    Pi.star_apply,star_mul,star_star]
  simp only [Finset.sum_mul]
  conv_lhs => enter [2,i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem factorKernel_norm_le (a : K → I → ℂ) (b : K → J → ℂ) (X : Matrix I J ℂ)
    (R C : ℝ)
    (ha : ∀ i,∑ k,‖a k i‖^2≤R) (hb : ∀ j,∑ k,‖b k j‖^2≤C) :
    ‖factorKernel a b ⊙ X‖≤Real.sqrt R*Real.sqrt C*‖X‖ := by
  apply l2_opNorm_le_of_inner_le _ (by positivity)
  intro u v hu hv
  rw [factorKernel_pairing]
  let U : K → EuclideanSpace ℂ I := fun k => WithLp.toLp 2 (fun i => star (a k i)*u i)
  let V : K → EuclideanSpace ℂ J := fun k => WithLp.toLp 2 (fun j => b k j*v j)
  have hU : (∑ k,‖U k‖^2)≤R := by
    have hh := weighted_vector_energy (fun k i => star (a k i)) u R
      (by intro i; simpa only [norm_star] using ha i)
    simpa only [hu,one_pow,mul_one] using hh
  have hV : (∑ k,‖V k‖^2)≤C := by
    simpa only [hv,one_pow,mul_one] using weighted_vector_energy b v C hb
  change ‖∑ k,inner ℂ (U k) (X.toEuclideanLin (V k))‖≤_
  calc
    _ ≤ ∑ k,‖inner ℂ (U k) (X.toEuclideanLin (V k))‖ := norm_sum_le _ _
    _ ≤ ∑ k,‖U k‖*(‖X‖*‖V k‖) := by
      apply Finset.sum_le_sum
      intro k _
      have hX : ‖X.toEuclideanLin (V k)‖≤‖X‖*‖V k‖ := Matrix.l2_opNorm_mulVec X (V k)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
    _ = ‖X‖*(∑ k,‖U k‖*‖V k‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ‖X‖*(Real.sqrt (∑ k,‖U k‖^2)*Real.sqrt (∑ k,‖V k‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _) (norm_nonneg _)
    _ ≤ ‖X‖*(Real.sqrt R*Real.sqrt C) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg X)
      exact mul_le_mul (Real.sqrt_le_sqrt hU) (Real.sqrt_le_sqrt hV)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem sum_tail_shift {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n r : ℕ) :
    (∑ k∈Finset.range n,if r≤k then f (k-r) else 0)=∑ q∈Finset.range (n-r),f q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hr : r≤n
    · rw [if_pos hr,show n+1-r=(n-r)+1 by omega,Finset.sum_range_succ]
    · simp only [if_neg hr,Nat.sub_eq_zero_of_le (by omega : n≤r),
        Nat.sub_eq_zero_of_le (by omega : n+1≤r),Finset.range_zero,Finset.sum_empty,add_zero]

theorem sum_prefix_reverse {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n r : ℕ) (hr : r≤n) :
    (∑ k∈Finset.range n,if k<r then f (r-1-k) else 0)=∑ q∈Finset.range r,f q := by
  calc
    _ = ∑ k∈Finset.range r,if k<r then f (r-1-k) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro k _ hk
      exact if_neg (by simpa only [Finset.mem_range] using hk)
    _ = ∑ k∈Finset.range r,f (r-1-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_range.mp hk)]
    _ = _ := Finset.sum_range_reflect f r

def evenPowerSum (n : ℕ) (t : ℝ) : ℝ := ∑ q∈Finset.range n,t^(2*q)

theorem evenPowerSum_nonneg (n : ℕ) (t : ℝ) (ht : 0≤t) : 0≤evenPowerSum n t :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)

def upperAlpha (n : ℕ) (r : I → Fin (n+1)) (t : ℝ) (k : Fin n) (i : I) : ℂ :=
  if (r i).val≤k.val then (t^(k.val-(r i).val):ℝ) else 0

def upperBeta (n : ℕ) (c : J → Fin (n+1)) (d : Fin n → ℂ) (t : ℝ) (k : Fin n) (j : J) : ℂ :=
  if k.val<(c j).val then d k*(t^((c j).val-1-k.val):ℝ) else 0

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] in

theorem upperAlpha_energy (n : ℕ) (r : I → Fin (n+1)) (t : ℝ) (ht : 0≤t) (i : I) :
    (∑ k : Fin n,‖upperAlpha n r t k i‖^2)≤evenPowerSum n t := by
  have he (k : Fin n) : ‖upperAlpha n r t k i‖^2=
      if (r i).val≤k.val then t^(2*(k.val-(r i).val)) else 0 := by
    unfold upperAlpha
    split_ifs
    · rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,← pow_mul]
      congr 1
      omega
    · norm_num
  simp only [he]
  rw [← Finset.sum_range (fun k : ℕ => if (r i).val≤k then t^(2*(k-(r i).val)) else 0),
    sum_tail_shift (fun q => t^(2*q)) n (r i).val]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le n _))
    (fun _ _ _ => pow_nonneg ht _)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] in

theorem upperBeta_energy (n : ℕ) (c : J → Fin (n+1)) (d : Fin n → ℂ) (D : ℝ)
    (hD : 0≤D) (hd : ∀ k,‖d k‖≤D) (t : ℝ) (ht : 0≤t) (j : J) :
    (∑ k : Fin n,‖upperBeta n c d t k j‖^2)≤D^2*evenPowerSum n t := by
  have he (k : Fin n) : ‖upperBeta n c d t k j‖^2≤
      D^2*(if k.val<(c j).val then t^(2*((c j).val-1-k.val)) else 0) := by
    unfold upperBeta
    split_ifs
    · rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,← pow_mul]
      have hp : ((c j).val-1-k.val)*2=2*((c j).val-1-k.val) := by omega
      rw [hp]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hD).mpr (hd k)) (pow_nonneg ht _)
    · norm_num
  calc
    _ ≤ ∑ k : Fin n,D^2*(if k.val<(c j).val then t^(2*((c j).val-1-k.val)) else 0) :=
      Finset.sum_le_sum (fun k _ => he k)
    _ = D^2*(∑ k : Fin n,if k.val<(c j).val then t^(2*((c j).val-1-k.val)) else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ = D^2*(∑ q∈Finset.range (c j).val,t^(2*q)) := by
      congr 1
      rw [← Finset.sum_range (fun k : ℕ => if k<(c j).val then t^(2*((c j).val-1-k)) else 0)]
      exact sum_prefix_reverse (fun q => t^(2*q)) n (c j).val (by have := (c j).isLt; omega)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by have := (c j).isLt; omega))
        (fun _ _ _ => pow_nonneg ht _)) (sq_nonneg D)

theorem upperKernel_pointwise (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (D : ℝ) (hD : 0≤D) (hd : ∀ k,‖d k‖≤D)
    (t : ℝ) (ht : 0≤t) (X : Matrix I J ℂ) :
    ‖factorKernel (upperAlpha n r t) (upperBeta n c d t) ⊙ X‖≤
      D*evenPowerSum n t*‖X‖ := by
  have hS := evenPowerSum_nonneg n t ht
  have hh := factorKernel_norm_le (upperAlpha n r t) (upperBeta n c d t) X
    (evenPowerSum n t) (D^2*evenPowerSum n t)
    (upperAlpha_energy n r t ht) (upperBeta_energy n c d D hD hd t ht)
  apply hh.trans_eq
  rw [Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq hD,← mul_assoc]
  rw [mul_comm (Real.sqrt (evenPowerSum n t)) D,mul_assoc D,
    Real.mul_self_sqrt hS]

def oddHarmonic (n : ℕ) : ℝ := ∑ q∈Finset.range n,1/(2*q+1:ℝ)

theorem oddHarmonic_le (n : ℕ) : oddHarmonic n≤1+Real.log n := by
  apply (Finset.sum_le_sum (s := Finset.range n) (f := fun q : ℕ => (1:ℝ)/(2*q+1))
    (g := fun q : ℕ => (1:ℝ)/(q+1)) (fun q _ => ?_)).trans
    (sum_range_one_div_le_one_add_log n)
  apply one_div_le_one_div_of_le (by positivity)
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  nlinarith

theorem evenPowerSum_integral (n : ℕ) :
    (∫ t in (0:ℝ)..1,evenPowerSum n t)=oddHarmonic n := by
  unfold evenPowerSum oddHarmonic
  calc
    _ = ∑ q∈Finset.range n,∫ t in (0:ℝ)..1,t^(2*q) :=
      intervalIntegral.integral_finsetSum (fun q _ =>
        (show Continuous (fun t : ℝ => t^(2*q)) from continuous_id.pow (2*q)).intervalIntegrable 0 1)
    _ = _ := Finset.sum_congr rfl (fun q _ => by simp [integral_pow])

def upperAction (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (X : Matrix I J ℂ) : Matrix I J ℂ :=
  ∫ t in (0:ℝ)..1,factorKernel (upperAlpha n r t) (upperBeta n c d t) ⊙ X

theorem upperAction_norm (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (D : ℝ) (hD : 0≤D) (hd : ∀ k,‖d k‖≤D) (X : Matrix I J ℂ) :
    ‖upperAction n r c d X‖≤D*oddHarmonic n*‖X‖ := by
  have hg : IntervalIntegrable (fun t : ℝ => D*evenPowerSum n t*‖X‖) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold evenPowerSum
    fun_prop
  have hh : ‖upperAction n r c d X‖≤∫ t in (0:ℝ)..1,D*evenPowerSum n t*‖X‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall (fun t ht => upperKernel_pointwise n r c d D hD hd t ht.1.le X)) hg
  apply hh.trans_eq
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,evenPowerSum_integral]

omit [DecidableEq I] [Fintype K] in
def entryCLM (i : I) (j : J) : Matrix I J ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [DecidableEq I] [Fintype K] in

theorem integral_entry (F : ℝ → Matrix I J ℂ) (hF : IntervalIntegrable F volume 0 1)
    (i : I) (j : J) : (∫ t in (0:ℝ)..1,F t) i j=∫ t in (0:ℝ)..1,F t i j :=
  ((entryCLM i j).intervalIntegral_comp_comm hF).symm

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] in

theorem upperAction_continuous (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (X : Matrix I J ℂ) :
    Continuous (fun t : ℝ => factorKernel (upperAlpha n r t) (upperBeta n c d t) ⊙ X) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => (∑ k : Fin n,upperAlpha n r t k i*upperBeta n c d t k j)*X i j)
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro k _
  unfold upperAlpha upperBeta
  split_ifs <;> fun_prop

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] in

theorem upperKernel_monomial (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (t : ℝ) (i : I) (j : J) :
    factorKernel (upperAlpha n r t) (upperBeta n c d t) i j =
      if (r i).val<(c j).val then
        (∑ k : Fin n,if (r i).val≤k.val ∧ k.val<(c j).val then d k else 0)*
          (t^((c j).val-1-(r i).val):ℝ)
      else 0 := by
  by_cases hrc : (r i).val<(c j).val
  · rw [factorKernel,if_pos hrc,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    unfold upperAlpha upperBeta
    by_cases hrk : (r i).val≤k.val
    · by_cases hkc : k.val<(c j).val
      · simp only [if_pos hrk,if_pos hkc,if_pos (And.intro hrk hkc)]
        calc
          _ = d k*((t^(k.val-(r i).val)*t^((c j).val-1-k.val):ℝ):ℂ) := by push_cast; ring
          _ = _ := by
            rw [← pow_add,show k.val-(r i).val+((c j).val-1-k.val)=(c j).val-1-(r i).val by omega]
      · simp [hrk,hkc]
    · simp [hrk]
  · rw [factorKernel,if_neg hrc]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hrk : (r i).val≤k.val
    · have hkc : ¬k.val<(c j).val := by omega
      simp [upperAlpha,upperBeta,hrk,hkc]
    · simp [upperAlpha,hrk]

omit [DecidableEq I] in

theorem upperAction_apply (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (X : Matrix I J ℂ) (i : I) (j : J) :
    upperAction n r c d X i j =
      if (r i).val<(c j).val then
        ((∑ k : Fin n,if (r i).val≤k.val ∧ k.val<(c j).val then d k else 0)/
          (((c j).val-(r i).val:ℕ):ℂ))*X i j
      else 0 := by
  rw [upperAction,integral_entry _ ((upperAction_continuous n r c d X).intervalIntegrable 0 1)]
  change (∫ t in (0:ℝ)..1,factorKernel (upperAlpha n r t) (upperBeta n c d t) i j*X i j)=_
  simp_rw [upperKernel_monomial]
  by_cases hrc : (r i).val<(c j).val
  · simp only [if_pos hrc]
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]
    have hp : (∫ t in (0:ℝ)..1,t^((c j).val-1-(r i).val))=
        1/((((c j).val-1-(r i).val+1:ℕ):ℝ)) := by simp [integral_pow]
    rw [hp,show (c j).val-1-(r i).val+1=(c j).val-(r i).val by omega]
    push_cast
    ring
  · simp only [if_neg hrc,zero_mul,intervalIntegral.integral_zero]

def gridIncrement (n : ℕ) (z : ℕ → ℂ) (k : Fin n) : ℂ := z (k.val+1)-z k.val

theorem gridIncrement_sum (n : ℕ) (z : ℕ → ℂ) (r c : ℕ) (hrc : r≤c) (hc : c≤n) :
    (∑ k : Fin n,if r≤k.val ∧ k.val<c then gridIncrement n z k else 0)=z c-z r := by
  simp only [gridIncrement]
  rw [← Finset.sum_range (fun k : ℕ => if r≤k ∧ k<c then z (k+1)-z k else 0),
    ← Finset.sum_filter]
  have he : (Finset.range n).filter (fun k => r≤k ∧ k<c)=Finset.Ico r c := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [he]
  exact Finset.sum_Ico_sub z hrc

omit [DecidableEq I] in

theorem upperAction_grid_apply (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) (X : Matrix I J ℂ) (i : I) (j : J) :
    upperAction n r c (gridIncrement n z) X i j =
      if (r i).val<(c j).val then
        ((z (c j).val-z (r i).val)/(((c j).val-(r i).val:ℕ):ℂ))*X i j
      else 0 := by
  rw [upperAction_apply]
  by_cases hrc : (r i).val<(c j).val
  · rw [if_pos hrc,if_pos hrc,gridIncrement_sum n z _ _ hrc.le (by have := (c j).isLt; omega)]
  · rw [if_neg hrc,if_neg hrc]

def lowerAction (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (X : Matrix I J ℂ) : Matrix I J ℂ :=
  ∫ t in (0:ℝ)..1,factorKernel (upperBeta n r d t) (upperAlpha n c t) ⊙ X

theorem lowerKernel_pointwise (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (D : ℝ) (hD : 0≤D) (hd : ∀ k,‖d k‖≤D)
    (t : ℝ) (ht : 0≤t) (X : Matrix I J ℂ) :
    ‖factorKernel (upperBeta n r d t) (upperAlpha n c t) ⊙ X‖≤D*evenPowerSum n t*‖X‖ := by
  have hS := evenPowerSum_nonneg n t ht
  have hh := factorKernel_norm_le (upperBeta n r d t) (upperAlpha n c t) X
    (D^2*evenPowerSum n t) (evenPowerSum n t)
    (upperBeta_energy n r d D hD hd t ht) (upperAlpha_energy n c t ht)
  apply hh.trans_eq
  rw [Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq hD,mul_assoc D,Real.mul_self_sqrt hS]

theorem lowerAction_norm (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (D : ℝ) (hD : 0≤D) (hd : ∀ k,‖d k‖≤D) (X : Matrix I J ℂ) :
    ‖lowerAction n r c d X‖≤D*oddHarmonic n*‖X‖ := by
  have hg : IntervalIntegrable (fun t : ℝ => D*evenPowerSum n t*‖X‖) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold evenPowerSum
    fun_prop
  have hh : ‖lowerAction n r c d X‖≤∫ t in (0:ℝ)..1,D*evenPowerSum n t*‖X‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall (fun t ht => lowerKernel_pointwise n r c d D hD hd t ht.1.le X)) hg
  apply hh.trans_eq
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,evenPowerSum_integral]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] in

theorem lowerAction_continuous (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (d : Fin n → ℂ) (X : Matrix I J ℂ) :
    Continuous (fun t : ℝ => factorKernel (upperBeta n r d t) (upperAlpha n c t) ⊙ X) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => (∑ k : Fin n,upperBeta n r d t k i*upperAlpha n c t k j)*X i j)
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro k _
  unfold upperAlpha upperBeta
  split_ifs <;> fun_prop

omit [DecidableEq I] in

theorem lowerAction_grid_apply (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) (X : Matrix I J ℂ) (i : I) (j : J) :
    lowerAction n r c (gridIncrement n z) X i j =
      if (c j).val<(r i).val then
        ((z (r i).val-z (c j).val)/(((r i).val-(c j).val:ℕ):ℂ))*X i j
      else 0 := by
  calc
    _ = upperAction n c r (gridIncrement n z) X.transpose j i := by
      rw [lowerAction,upperAction,
        integral_entry _ ((lowerAction_continuous n r c _ X).intervalIntegrable 0 1),
        integral_entry _ ((upperAction_continuous n c r _ X.transpose).intervalIntegrable 0 1)]
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ k,upperBeta n r (gridIncrement n z) t k i*upperAlpha n c t k j)*X i j=
        (∑ k,upperAlpha n c t k j*upperBeta n r (gridIncrement n z) t k i)*X i j
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := upperAction_grid_apply n c r z X.transpose j i

def gridDividedDifference (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) : Matrix I J ℂ := fun i j =>
  if (r i).val=(c j).val then 0 else
    (z (r i).val-z (c j).val)/(((r i).val:ℂ)-((c j).val:ℂ))

omit [DecidableEq I] in

theorem gridDividedDifference_decomposition (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) (X : Matrix I J ℂ) :
    gridDividedDifference n r c z ⊙ X=
      upperAction n r c (gridIncrement n z) X+lowerAction n r c (gridIncrement n z) X := by
  ext i j
  rw [Matrix.hadamard_apply,Matrix.add_apply,upperAction_grid_apply,lowerAction_grid_apply]
  by_cases hrc : (r i).val=(c j).val
  · simp [gridDividedDifference,hrc]
  · rcases lt_or_gt_of_ne hrc with hlt | hgt
    · have hnot : ¬(c j).val<(r i).val := by omega
      simp only [gridDividedDifference,if_neg hrc,if_pos hlt,if_neg hnot,add_zero]
      have he : (((c j).val-(r i).val:ℕ):ℂ)=-(((r i).val:ℂ)-((c j).val:ℂ)) := by
        rw [Nat.cast_sub hlt.le]
        ring
      rw [he,show z (c j).val-z (r i).val=-(z (r i).val-z (c j).val) by ring,neg_div_neg_eq]
    · have hnot : ¬(r i).val<(c j).val := by omega
      simp only [gridDividedDifference,if_neg hrc,if_pos hgt,if_neg hnot,zero_add]
      rw [Nat.cast_sub hgt.le]

theorem gridSchur_bound (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) (D : ℝ) (hD : 0≤D) (hd : ∀ k,‖gridIncrement n z k‖≤D) (X : Matrix I J ℂ) :
    ‖gridDividedDifference n r c z ⊙ X‖≤2*D*oddHarmonic n*‖X‖ := by
  rw [gridDividedDifference_decomposition]
  apply (norm_add_le _ _).trans
  exact (add_le_add (upperAction_norm n r c _ D hD hd X)
    (lowerAction_norm n r c _ D hD hd X)).trans_eq (by ring)

end Qatlib.Concepts.NonNormalSpec.ResolventWord
