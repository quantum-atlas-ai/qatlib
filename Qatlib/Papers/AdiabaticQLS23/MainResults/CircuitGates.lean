/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS23.MainResults.BlockEncoding
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
open Matrix
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem block_one : block2 (1 : Matrix K K ℂ) 0 0 1 = 1 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> simp [block2, Matrix.one_apply]

omit [DecidableEq K] in

theorem block_star (A B C D : Matrix K K ℂ) :
    (block2 A B C D)ᴴ = block2 Aᴴ Cᴴ Bᴴ Dᴴ := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> simp [block2, Matrix.conjTranspose_apply]

theorem block_diag_unitary (A D : Matrix K K ℂ)
    (hA : A ∈ Matrix.unitaryGroup K ℂ) (hD : D ∈ Matrix.unitaryGroup K ℂ) :
    block2 A 0 0 D ∈ Matrix.unitaryGroup (Fin 2 × K) ℂ := by
  have hAA : A*Aᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using hA.2
  have hDD : D*Dᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using hD.2
  rw [Matrix.mem_unitaryGroup_iff]
  change block2 A 0 0 D * (block2 A 0 0 D)ᴴ = 1
  rw [block_star, block2_mul]
  simpa [hAA, hDD] using (block_one (K:=K))

theorem involution_unitary (U : Matrix K K ℂ) (hs : Uᴴ = U) (hi : U*U=1) :
    U ∈ Matrix.unitaryGroup K ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change U*Uᴴ=1
  rw [hs,hi]

def xGate : Matrix (Fin 2 × K) (Fin 2 × K) ℂ := block2 0 1 1 0

theorem xGate_unitary : xGate (K:=K) ∈ Matrix.unitaryGroup (Fin 2 × K) ℂ := by
  apply involution_unitary
  · simp [xGate,block_star]
  · simp only [xGate,block2_mul,mul_zero,mul_one,zero_add,add_zero]
    exact block_one

def oracleFlip (U : Matrix K K ℂ) : Matrix (Fin 2 × K) (Fin 2 × K) ℂ :=
  block2 0 U Uᴴ 0

theorem oracleFlip_unitary (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ) :
    oracleFlip U ∈ Matrix.unitaryGroup (Fin 2 × K) ℂ := by
  have hright : U*Uᴴ=1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hleft : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hU
  apply involution_unitary
  · simp [oracleFlip,block_star]
  · simp only [oracleFlip,block2_mul,mul_zero,zero_mul,zero_add,add_zero]
    rw [hright,hleft]
    exact block_one

def selectGate (U : Matrix K K ℂ) : Matrix (Fin 2 × (Fin 2 × K)) (Fin 2 × (Fin 2 × K)) ℂ :=
  block2 xGate 0 0 (oracleFlip U)

theorem selectGate_unitary (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ) :
    selectGate U ∈ Matrix.unitaryGroup (Fin 2 × (Fin 2 × K)) ℂ :=
  block_diag_unitary _ _ xGate_unitary (oracleFlip_unitary U hU)

def diagonal (a b : ℝ) : Matrix (Fin 2 × K) (Fin 2 × K) ℂ :=
  block2 (a • (1 : Matrix K K ℂ)) 0 0 (b • (1 : Matrix K K ℂ))

def rotationGate (u v c : ℝ) :
    Matrix (Fin 2 × (Fin 2 × K)) (Fin 2 × (Fin 2 × K)) ℂ :=
  block2 (diagonal u c) (diagonal v c) (diagonal v c) (diagonal (-u) (-c))

theorem rotationGate_star (u v c : ℝ) :
    (rotationGate (K:=K) u v c)ᴴ = rotationGate u v c := by
  ext ⟨i,⟨h,x⟩⟩ ⟨j,⟨k,y⟩⟩
  by_cases hxy : x=y
  · subst y
    fin_cases i <;> fin_cases j <;> fin_cases h <;> fin_cases k <;>
      simp [rotationGate,diagonal,block2,Matrix.conjTranspose_apply]
  · have hyx : y ≠ x := Ne.symm hxy
    fin_cases i <;> fin_cases j <;> fin_cases h <;> fin_cases k <;>
      simp [rotationGate,diagonal,block2,Matrix.conjTranspose_apply,hxy,hyx]

theorem rotationGate_unitary (u v c : ℝ) (huv : u^2+v^2=1) (hc : 2*c^2=1) :
    rotationGate (K:=K) u v c ∈ Matrix.unitaryGroup (Fin 2 × (Fin 2 × K)) ℂ := by
  have huvC : (u:ℂ)^2+(v:ℂ)^2=1 := by exact_mod_cast huv
  have hcC : 2*(c:ℂ)^2=1 := by exact_mod_cast hc
  apply involution_unitary _ (rotationGate_star u v c)
  ext ⟨i,⟨h,x⟩⟩ ⟨j,⟨k,y⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases h <;> fin_cases k <;>
    by_cases hxy : x=y <;>
    simp [rotationGate,diagonal,block2,Matrix.one_apply,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,hxy] <;>
    solve | ring | linear_combination huvC | linear_combination hcC

theorem diagonal_same (a : ℝ) : diagonal (K:=K) a a = a • (1 : Matrix (Fin 2 × K) _ ℂ) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> simp [diagonal,block2,Matrix.one_apply]

def hadamardGate (c : ℝ) : Matrix (Fin 2 × K) (Fin 2 × K) ℂ :=
  block2 (c • (1 : Matrix K K ℂ)) (c • 1) (c • 1) ((-c) • 1)

theorem hadamardGate_unitary (c : ℝ) (hc : 2*c^2=1) :
    hadamardGate (K:=K) c ∈ Matrix.unitaryGroup (Fin 2 × K) ℂ := by
  have hcC : 2*(c:ℂ)^2=1 := by exact_mod_cast hc
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hadamardGate, block_star,
    block2_mul]
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> by_cases hxy : x=y <;>
    simp [block2,Matrix.one_apply,hxy] <;>
    solve | ring | linear_combination hcC

def middle (U : Matrix K K ℂ) (u v c : ℝ) :
    Matrix (Fin 2 × (Fin 2 × K)) (Fin 2 × (Fin 2 × K)) ℂ :=
  rotationGate u v c * selectGate U * rotationGate u v c

theorem middle_unitary (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ)
    (u v c : ℝ) (huv : u^2+v^2=1) (hc : 2*c^2=1) :
    middle U u v c ∈ Matrix.unitaryGroup _ ℂ := by
  have hR := rotationGate_unitary (K:=K) u v c huv hc
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem hR (selectGate_unitary U hU)) hR

def qControl (R : Matrix K K ℂ) :
    Matrix (Fin 2 × (Fin 2 × K)) (Fin 2 × (Fin 2 × K)) ℂ :=
  block2 (block2 1 0 0 R) 0 0 (block2 1 0 0 R)

def reflectGate (R : Matrix K K ℂ) :
    Matrix (Fin 2 × (Fin 2 × (Fin 2 × K))) (Fin 2 × (Fin 2 × (Fin 2 × K))) ℂ :=
  block2 1 0 0 (qControl R)

theorem reflectGate_unitary (R : Matrix K K ℂ) (hR : R ∈ Matrix.unitaryGroup K ℂ) :
    reflectGate R ∈ Matrix.unitaryGroup _ ℂ := by
  have ht := block_diag_unitary (1 : Matrix K K ℂ) R (Submonoid.one_mem _) hR
  exact block_diag_unitary _ _ (Submonoid.one_mem _) (block_diag_unitary _ _ ht ht)

def fullCircuit (U R : Matrix K K ℂ) (u v c : ℝ) :
    Matrix (Fin 2 × (Fin 2 × (Fin 2 × K))) (Fin 2 × (Fin 2 × (Fin 2 × K))) ℂ :=
  hadamardGate c * reflectGate R * block2 (middle U u v c) 0 0 (middle U u v c) *
    reflectGate R * hadamardGate c

theorem fullCircuit_unitary (U R : Matrix K K ℂ)
    (hU : U ∈ Matrix.unitaryGroup K ℂ) (hR : R ∈ Matrix.unitaryGroup K ℂ)
    (u v c : ℝ) (huv : u^2+v^2=1) (hc : 2*c^2=1) :
    fullCircuit U R u v c ∈ Matrix.unitaryGroup _ ℂ := by
  have hh := hadamardGate_unitary (K:=Fin 2 × (Fin 2 × K)) c hc
  have hr := reflectGate_unitary R hR
  have hm := middle_unitary U hU u v c huv hc
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem
      ((Matrix.unitaryGroup _ ℂ).mul_mem
        ((Matrix.unitaryGroup _ ℂ).mul_mem hh hr) (block_diag_unitary _ _ hm hm)) hr) hh

end
end Qatlib.Papers.AdiabaticQLS23.MainResults.SourceCircuit
