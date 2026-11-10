/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.CommutatorTupleCounting
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem pfAdPower_add (X B C : Matrix I I ℂ) (n : ℕ) :
    pfAdPower X (B+C) n=pfAdPower X B n+pfAdPower X C n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pfAdPower_succ,ih,pfAdPower_succ,pfAdPower_succ];unfold pfComm;noncomm_ring

omit [DecidableEq I] in

theorem pfAdPower_smul (X B : Matrix I I ℂ) (n : ℕ) (a : ℝ) :
    pfAdPower X (a • B) n=a • pfAdPower X B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pfAdPower_succ,ih,pfAdPower_succ]
    simp only [pfComm,mul_smul_comm,smul_mul_assoc,smul_sub]

def pfAdPowerLinear (X : Matrix I I ℂ) (n : ℕ) : Matrix I I ℂ→ₗ[ℝ]Matrix I I ℂ where
  toFun := fun B=>pfAdPower X B n
  map_add' := fun B C=>pfAdPower_add X B C n
  map_smul' := fun a B=>pfAdPower_smul X B n a

def pfConjExpLinear (X : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ→ₗ[ℝ]Matrix I I ℂ where
  toFun := fun B=>pfConjExp X B t
  map_add' := by intro B C;unfold pfConjExp;noncomm_ring
  map_smul' := by intro a B;simp only [pfConjExp,mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

def pfConjCoeff : List (Matrix I I ℂ)→Matrix I I ℂ→ℕ→Matrix I I ℂ
  | [], B, 0 => B
  | [], _, _+1 => 0
  | X::xs, B, n => ∑ j : Fin (n+1),((j.val.factorial:ℝ)⁻¹) • pfAdPower X (pfConjCoeff xs B (n-j.val)) j.val

theorem pfConjCoeff_linear_norm_le (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (n : ℕ)
    (L : Matrix I I ℂ→ₗ[ℝ]Matrix I I ℂ) :
    ‖L (pfConjCoeff xs B n)‖≤∑ idx : Fin n→Fin xs.length,‖L (pfNestedCommList (B::pfChosenList xs idx))‖ := by
  induction xs generalizing n L with
  | nil =>
    cases n with
    | zero => simp [pfConjCoeff,pfChosenList,pfNestedCommList]
    | succ n => simp [pfConjCoeff]
  | cons X xs ih =>
    rw [pfConjCoeff,map_sum]
    calc _≤∑ j : Fin (n+1),‖L (((j.val.factorial:ℝ)⁻¹) • pfAdPower X (pfConjCoeff xs B (n-j.val)) j.val)‖ := norm_sum_le _ _
         _≤∑ j : Fin (n+1),‖L (pfAdPower X (pfConjCoeff xs B (n-j.val)) j.val)‖ := by
           apply Finset.sum_le_sum
           intro j _
           rw [map_smul,norm_smul,Real.norm_of_nonneg (by positivity)]
           apply mul_le_of_le_one_left (norm_nonneg _)
           have hf : (1:ℝ)≤j.val.factorial := by
             exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j.val)
           exact inv_le_one_of_one_le₀ hf
         _≤∑ j : Fin (n+1),∑ idx : Fin (n-j.val)→Fin xs.length,
             ‖L (pfAdPower X (pfNestedCommList (B::pfChosenList xs idx)) j.val)‖ := by
           apply Finset.sum_le_sum
           intro j _
           exact ih (n-j.val) (L.comp (pfAdPowerLinear X j.val))
         _≤_ := pf_inner_block_sum_le_map X B xs n L

def pfTriangleEquiv (p : ℕ) : ((n : Fin p) × Fin (n.val+1)) ≃ ((k : Fin p) × Fin (p-k.val)) where
  toFun := fun z=>⟨⟨z.1.val-z.2.val,by have hn:=z.1.isLt;have hj:=z.2.isLt;omega⟩,
    ⟨z.2.val,by have hn:=z.1.isLt;have hj:=z.2.isLt;dsimp only at *;omega⟩⟩
  invFun := fun z=>⟨⟨z.1.val+z.2.val,by have hk:=z.1.isLt;have hj:=z.2.isLt;omega⟩,
    ⟨z.2.val,by (try dsimp only);omega⟩⟩
  left_inv := by
    rintro ⟨⟨n,hn⟩,⟨j,hj⟩⟩
    dsimp
    (try dsimp only at hj)
    have he : n-j+j=n := by omega
    apply Sigma.ext (Fin.ext he)
    exact (Fin.heq_ext_iff (congrArg (fun x=>x+1) he)).mpr rfl
  right_inv := by
    rintro ⟨⟨k,hk⟩,⟨j,hj⟩⟩
    dsimp
    have he : k+j-j=k := Nat.add_sub_cancel_right _ _
    apply Sigma.ext (Fin.ext he)
    exact (Fin.heq_ext_iff (congrArg (fun x=>p-x) he)).mpr rfl

theorem pfConjExp_taylor_ad_sum (X B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    pfTaylorBefore (pfConjExp X B) p t=
      ∑ j : Fin p,(t^j.val/(j.val.factorial:ℝ)) • pfAdPower X B j.val := by
  unfold pfTaylorBefore
  simp only [pfConjExp_iteratedDeriv,pfConjExp,neg_zero,zero_smul,NormedSpace.exp_zero,one_mul,mul_one]
  exact (Fin.sum_univ_eq_sum_range (fun j=>(t^j/(j.factorial:ℝ)) • pfAdPower X B j) p).symm

def pfConjTrunc (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) : Matrix I I ℂ :=
  ∑ n : Fin p,t^n.val • pfConjCoeff xs B n.val

theorem pfConjTrunc_cons (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    pfConjTrunc (X::xs) B p t=
      ∑ k : Fin p,t^k.val • pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t := by
  let g := fun z : (k : Fin p) × Fin (p-k.val)=>
    (t^(z.1.val+z.2.val)/(z.2.val.factorial:ℝ)) • pfAdPower X (pfConjCoeff xs B z.1.val) z.2.val
  have hl : pfConjTrunc (X::xs) B p t=
      ∑ z : (n : Fin p) × Fin (n.val+1),g (pfTriangleEquiv p z) := by
    rw [Fintype.sum_sigma]
    unfold pfConjTrunc
    apply Finset.sum_congr rfl
    intro n _
    rw [pfConjCoeff,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g,pfTriangleEquiv,Equiv.coe_fn_mk]
    rw [Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
    simp only [smul_smul,div_eq_mul_inv]
  have hr : (∑ z : (k : Fin p) × Fin (p-k.val),g z)=
      ∑ k : Fin p,t^k.val • pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    rw [pfConjExp_taylor_ad_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g]
    simp only [pow_add,div_eq_mul_inv,smul_smul,mul_assoc]
  exact hl.trans (((pfTriangleEquiv p).sum_comp g).trans hr)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
