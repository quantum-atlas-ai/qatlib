/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.BellCircuit
import Mathlib.LinearAlgebra.UnitaryGroup
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.HomOverlap
open Matrix

abbrev HomBits (n : ℕ) := Fin n→Bool×Bool

def homTensorReal (n : ℕ) : Matrix (HomBits n) (HomBits n) ℝ :=
  fun z x => ∏i,homBell (z i) (x i)

def homTensor (n : ℕ) : Matrix (HomBits n) (HomBits n) ℂ :=
  fun z x => (homTensorReal n z x:ℂ)

def homParity (n : ℕ) (z : HomBits n) : ℝ := ∏i,homPairSign (z i)

def homSwap (n : ℕ) (x : HomBits n) : HomBits n := fun i => ((x i).2,(x i).1)

theorem hom_prod_delta {I B : Type} [Fintype I] [DecidableEq B] (x y : I→B) :
    (∏i,if x i=y i then (1:ℝ) else 0)=if x=y then 1 else 0 := by
  by_cases h : x=y
  · subst y
    simp
  · rw [if_neg h]
    have hn : ¬∀i,x i=y i := fun heq => h (funext heq)
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem homTensorReal_orthogonal (n : ℕ) (x y : HomBits n) :
    (∑z,homTensorReal n z x*homTensorReal n z y)=if x=y then 1 else 0 := by
  calc
    _ = ∑z : HomBits n,∏i,homBell (z i) (x i)*homBell (z i) (y i) := by
      simp only [homTensorReal,Finset.prod_mul_distrib]
    _ = ∏i,∑z,homBell z (x i)*homBell z (y i) := (Fintype.prod_sum (fun (i : Fin n) (z : Bool×Bool) => homBell z (x i)*homBell z (y i))).symm
    _ = _ := by simp only [homBell_orthogonal,hom_prod_delta]

theorem homTensor_unitary (n : ℕ) : homTensor n∈Matrix.unitaryGroup (HomBits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,
    homTensor,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum,
    homTensorReal_orthogonal,Matrix.one_apply]
  split_ifs <;> rfl

theorem homTensorReal_parity_swap (n : ℕ) (x y : HomBits n) :
    (∑z,homTensorReal n z x*homParity n z*homTensorReal n z y)=
      if x=homSwap n y then 1 else 0 := by
  calc
    _ = ∑z : HomBits n,∏i,homBell (z i) (x i)*homPairSign (z i)*homBell (z i) (y i) := by
      simp only [homTensorReal,homParity,Finset.prod_mul_distrib]
    _ = ∏i,∑z,homBell z (x i)*homPairSign z*homBell z (y i) := (Fintype.prod_sum (fun (i : Fin n) (z : Bool×Bool) => homBell z (x i)*homPairSign z*homBell z (y i))).symm
    _ = ∏i,if x i=(homSwap n y) i then 1 else 0 := by simpa only [homSwap] using! (Finset.prod_congr rfl (fun i _ => homBell_parity_swap (x i) (y i)))
    _ = _ := hom_prod_delta x (homSwap n y)

theorem homParity_sq (n : ℕ) (z : HomBits n) : homParity n z^2=1 := by
  rw [homParity,← Finset.prod_pow]
  have hs (i : Fin n) : homPairSign (z i)^2=1 := by unfold homPairSign; split_ifs <;> norm_num
  simp_rw [hs]
  simp

theorem hom_measured_card (n : ℕ) : Fintype.card (HomBits n)=2^(2*n) := by
  simp only [HomBits,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  rw [show 2*2=2^2 by norm_num,← pow_mul]

def homGateWord (n : ℕ) : List (Fin n×Bool) :=
  (List.ofFn fun i : Fin n => [(i,false),(i,true)]).flatten

theorem homGateWord_length (n : ℕ) : (homGateWord n).length=2*n := by
  simp [homGateWord,List.length_flatten,List.sum_ofFn]
  omega

end Qatlib.Papers.HHLManyBody22.HomOverlap
