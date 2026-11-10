/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.AffineLift.AffineHomogenization
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.Pi
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model

def tensorPower {J : Type} (n : ℕ) (y : J→ℂ) : (Fin n→J)→ℂ :=fun u=>∏ k,y (u k)

def tensorMatrix {J : Type} (n : ℕ) (M : Fin n→Matrix J J ℂ) : Matrix (Fin n→J) (Fin n→J) ℂ :=
  fun u v=>∏ k,M k (u k) (v k)

theorem tensorMatrix_action {J : Type} [Fintype J] (n : ℕ) (M : Fin n→Matrix J J ℂ) (y : J→ℂ) (u : Fin n→J) :
    (tensorMatrix n M*ᵥ tensorPower n y) u=∏ k,(M k*ᵥ y) (u k) := by
  change (∑ v : Fin n→J,(∏ k,M k (u k) (v k))*(∏ k,y (v k)))=_
  simp_rw [← Finset.prod_mul_distrib]
  have h := Finset.prod_univ_sum (κ:=fun _ : Fin n=>J) (t:=fun _=>Finset.univ)
    (f:=fun k a=>M k (u k) a*y a)
  rw [Fintype.piFinset_univ] at h
  exact h.symm

def oneBody {J : Type} [DecidableEq J] (n : ℕ) (B : Matrix J J ℂ) (k : Fin n) : Matrix (Fin n→J) (Fin n→J) ℂ :=
  tensorMatrix n (fun j=>if j=k then B else 1)

def tensorSum {J : Type} [DecidableEq J] (n : ℕ) (B : Matrix J J ℂ) : Matrix (Fin n→J) (Fin n→J) ℂ :=
  ∑ k : Fin n,oneBody n B k

theorem oneBody_action {J : Type} [Fintype J] [DecidableEq J] (n : ℕ) (B : Matrix J J ℂ)
    (y : J→ℂ) (u : Fin n→J) (k : Fin n) :
    (oneBody n B k*ᵥ tensorPower n y) u=(B*ᵥ y) (u k)*∏ j∈Finset.univ.erase k,y (u j) := by
  rw [oneBody,tensorMatrix_action,← Finset.mul_prod_erase Finset.univ
    (fun j : Fin n=>((if j=k then B else 1)*ᵥ y) (u j)) (Finset.mem_univ k)]
  simp only
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem tensorSum_action {J : Type} [Fintype J] [DecidableEq J] (n : ℕ) (B : Matrix J J ℂ)
    (y : J→ℂ) (u : Fin n→J) :
    (tensorSum n B*ᵥ tensorPower n y) u=
      ∑ k : Fin n,(B*ᵥ y) (u k)*∏ j∈Finset.univ.erase k,y (u j) := by
  simp only [tensorSum,Matrix.sum_mulVec,Finset.sum_apply,oneBody_action]

theorem tensorPower_hasDerivAt {J : Type} [Fintype J] [DecidableEq J] (n : ℕ) (B : Matrix J J ℂ)
    (y : ℝ→J→ℂ) (t : ℝ) (hy : HasDerivAt y (B*ᵥ y t) t) :
    HasDerivAt (fun s=>tensorPower n (y s)) (tensorSum n B*ᵥ tensorPower n (y t)) t := by
  rw [hasDerivAt_pi]
  intro u
  have hd := HasDerivAt.fun_finsetProd (u:=Finset.univ) (f:=fun k s=>y s (u k))
    (f':=fun k=>(B*ᵥ y t) (u k)) (fun k _=>(hasDerivAt_pi.mp hy) (u k))
  convert! hd using 1
  rw [tensorSum_action]
  apply Finset.sum_congr rfl
  intro k _
  simp [smul_eq_mul,mul_comm]

theorem forced_affine_tensor_evolution {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Matrix I I ℂ) (b : I→ℂ) (x : ℝ→I→ℂ) (t : ℝ)
    (hx : HasDerivAt x (A*ᵥ x t+b) t) :
    HasDerivAt (fun s=>tensorPower n (homogenize (x s)))
      (tensorSum n (affineMatrix A b)*ᵥ tensorPower n (homogenize (x t))) t :=
  tensorPower_hasDerivAt n (affineMatrix A b) _ t (affine_hasDerivAt A b x t hx)

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
