/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.PartialTrace
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical ComplexOrder Kronecker
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorPair
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Reduction

noncomputable def localPair (a : Fin 3) : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ :=
  fun u v => pauliMatrix a u.1 v.1 * pauliMatrix a u.2 v.2

theorem pair_eq_lift {n : ℕ} (i j : Fin n) (hij : i≠j) (a : Fin 3) :
    pairPauli i j a = lift i j hij (localPair a) := by
  ext x y
  change (∏ h : Fin n, (if h=i ∨ h=j then pauliMatrix a else (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (boolEquivFin2 (x h)) (boolEquivFin2 (y h))) =
    (pauliMatrix a (boolEquivFin2 (x i)) (boolEquivFin2 (y i)) *
      pauliMatrix a (boolEquivFin2 (x j)) (boolEquivFin2 (y j))) *
        (1 : Matrix (Rest i j→Bool) (Rest i j→Bool) ℂ) (fun h => x h.val) (fun h => y h.val)
  by_cases hr : (fun h : Rest i j => x h.val) = (fun h : Rest i j => y h.val)
  · rw [hr,Matrix.one_apply_eq,mul_one]
    have hf : ∀ h : Fin n,
        (if h=i ∨ h=j then pauliMatrix a else (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (boolEquivFin2 (x h)) (boolEquivFin2 (y h)) =
        (if h=i then pauliMatrix a (boolEquivFin2 (x i)) (boolEquivFin2 (y i)) else 1)*
        (if h=j then pauliMatrix a (boolEquivFin2 (x j)) (boolEquivFin2 (y j)) else 1) := by
      intro h
      by_cases hi : h=i
      · subst h
        simp [hij]
      · by_cases hj : h=j
        · subst h
          simp [hi]
        · have hxy := congrFun hr (⟨h,hi,hj⟩ : Rest i j)
          change x h=y h at hxy
          simp only [hi,hj,false_or,ite_false,one_mul]
          exact (congrArg (fun b => (1 : Matrix (Fin 2) (Fin 2) ℂ) (boolEquivFin2 b)
            (boolEquivFin2 (y h))) hxy).trans (Matrix.one_apply_eq _)
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    simp
  · rw [Matrix.one_apply_ne hr,mul_zero]
    obtain ⟨h,hh⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ h.val)
    have hxy : boolEquivFin2 (x h.val) ≠ boolEquivFin2 (y h.val) :=
        fun he => hh (boolEquivFin2.injective he)
    simp [h.property.1,h.property.2,hxy]

theorem local_xx : localPair 0 = Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opXX := rfl

theorem local_yy : localPair 1 = Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opYY := rfl

theorem local_zz : localPair 2 = Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opZZ := rfl

theorem tensor_zz_bound {n : ℕ} (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    ((pairPauli i j 2*ρ).trace).re ≤
      1-2*|(((pairPauli i j 0*ρ).trace).re+((pairPauli i j 1*ρ).trace).re)/2| := by
  simpa only [pair_eq_lift i j hij,local_xx,local_yy,local_zz] using
      global_zz_bound i j hij ρ hρ htr
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorPair
