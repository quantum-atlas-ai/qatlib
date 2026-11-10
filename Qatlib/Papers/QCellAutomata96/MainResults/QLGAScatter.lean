/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Diagonal

set_option autoImplicit false
noncomputable section

open Complex
open scoped Matrix

namespace Qatlib.Papers.QCellAutomata96.MainResults

abbrev PairState : Type := Fin 4

def pairParticles : PairState → ℕ := ![0, 1, 1, 2]

@[simp] theorem pairParticles_zero : pairParticles 0 = 0 := rfl

@[simp] theorem pairParticles_one : pairParticles 1 = 1 := rfl

@[simp] theorem pairParticles_two : pairParticles 2 = 1 := rfl

@[simp] theorem pairParticles_three : pairParticles 3 = 2 := rfl

theorem exp_I_mul_star (α : ℝ) :
    Complex.exp (I * (α : ℂ)) * star (Complex.exp (I * (α : ℂ))) = 1 := by
  rw [show star (Complex.exp (I * (α : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (I * (α : ℂ))) from rfl]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have hzero : I * (α : ℂ) + (starRingEnd ℂ) (I * (α : ℂ)) = 0 := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hzero, Complex.exp_zero]

theorem star_exp_I_mul (α : ℝ) :
    star (Complex.exp (I * (α : ℂ))) = Complex.exp (-(I * (α : ℂ))) := by
  rw [show star (Complex.exp (I * (α : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (I * (α : ℂ))) from rfl]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

def scatterMatrix (θ α β : ℝ) : Matrix PairState PairState ℂ :=
  !![1, 0, 0, 0;
     0, I * (Real.sin θ : ℂ) * Complex.exp (I * (α : ℂ)),
        (Real.cos θ : ℂ) * Complex.exp (I * (α : ℂ)), 0;
     0, (Real.cos θ : ℂ) * Complex.exp (I * (α : ℂ)),
        I * (Real.sin θ : ℂ) * Complex.exp (I * (α : ℂ)), 0;
     0, 0, 0, Complex.exp (I * (β : ℂ))]

theorem unitary_pair_form (a b f : ℂ)
    (h1 : a * star a + b * star b = 1)
    (h2 : a * star b + b * star a = 0)
    (h3 : f * star f = 1) :
    (!![1, 0, 0, 0; 0, a, b, 0; 0, b, a, 0; 0, 0, 0, f] :
      Matrix (Fin 4) (Fin 4) ℂ) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have h1' : b * star b + a * star a = 1 := by rw [add_comm]; exact h1
  have h2' : b * star a + a * star b = 0 := by rw [add_comm]; exact h2
  have h1s : a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 := h1
  have h1s' : b * (starRingEnd ℂ) b + a * (starRingEnd ℂ) a = 1 := h1'
  have h2s : a * (starRingEnd ℂ) b + b * (starRingEnd ℂ) a = 0 := h2
  have h2s' : b * (starRingEnd ℂ) a + a * (starRingEnd ℂ) b = 0 := h2'
  have h3s : f * (starRingEnd ℂ) f = 1 := h3
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      h1s, h1s', h2s, h2s', h3s]

theorem scatterMatrix_mem_unitary (θ α β : ℝ) :
    scatterMatrix θ α β ∈ Matrix.unitaryGroup PairState ℂ := by
  rw [show scatterMatrix θ α β =
      !![1, 0, 0, 0;
         0, I * (Real.sin θ : ℂ) * Complex.exp (I * (α : ℂ)),
            (Real.cos θ : ℂ) * Complex.exp (I * (α : ℂ)), 0;
         0, (Real.cos θ : ℂ) * Complex.exp (I * (α : ℂ)),
            I * (Real.sin θ : ℂ) * Complex.exp (I * (α : ℂ)), 0;
         0, 0, 0, Complex.exp (I * (β : ℂ))] from rfl]
  apply unitary_pair_form
  · set p : ℂ := Complex.exp (I * (α : ℂ))
    set s : ℂ := (Real.sin θ : ℂ)
    set c : ℂ := (Real.cos θ : ℂ)
    have hp : p * star p = 1 := exp_I_mul_star α
    have hs : star s = s := by
      simp only [s]
      rw [Complex.star_def, Complex.conj_ofReal]
    have hc : star c = c := by
      simp only [c]
      rw [Complex.star_def, Complex.conj_ofReal]
    have hI : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
    have hII : (I : ℂ) * I = -1 := Complex.I_mul_I
    have hsa : star (I * s * p) = -(I * s * star p) := by
      rw [star_mul, star_mul]
      simp [hI, hs]
      ring
    have hsb : star (c * p) = c * star p := by
      rw [star_mul, hc]
      ring
    rw [hsa, hsb]
    have hsc : s ^ 2 + c ^ 2 = 1 := by
      simp only [s, c, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq, Complex.ofReal_one]
    calc (I * s * p) * (-(I * s * star p)) + (c * p) * (c * star p)
        = -((I * I) * (s * s) * (p * star p)) + (c * c) * (p * star p) := by
          ring
      _ = -((-1) * (s * s) * 1) + (c * c) * 1 := by rw [hII, hp]
      _ = s ^ 2 + c ^ 2 := by ring
      _ = 1 := hsc
  · set p : ℂ := Complex.exp (I * (α : ℂ))
    set s : ℂ := (Real.sin θ : ℂ)
    set c : ℂ := (Real.cos θ : ℂ)
    have hp : p * star p = 1 := exp_I_mul_star α
    have hs : star s = s := by
      simp only [s]
      rw [Complex.star_def, Complex.conj_ofReal]
    have hc : star c = c := by
      simp only [c]
      rw [Complex.star_def, Complex.conj_ofReal]
    have hI : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
    have hsa : star (I * s * p) = -(I * s * star p) := by
      rw [star_mul, star_mul]
      simp [hI, hs]
      ring
    have hsb : star (c * p) = c * star p := by
      rw [star_mul, hc]
      ring
    rw [hsa, hsb]
    calc (I * s * p) * (c * star p) + (c * p) * (-(I * s * star p))
        = (I * (s * c)) * (p * star p) + (-(I * (c * s))) * (p * star p) := by
          ring
      _ = 0 := by rw [hp]; ring
  · exact exp_I_mul_star β

def particleNumberOp : Matrix PairState PairState ℂ :=
  Matrix.diagonal (fun i => (pairParticles i : ℂ))

theorem scatterMatrix_comm_particleNumber (θ α β : ℝ) :
    scatterMatrix θ α β * particleNumberOp = particleNumberOp * scatterMatrix θ α β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scatterMatrix, particleNumberOp, Matrix.mul_apply, Matrix.diagonal] <;>
    ring

def oneParticleBlock (M : Matrix PairState PairState ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 1 1, M 1 2; M 2 1, M 2 2]

theorem scatterMatrix_oneParticleBlock (θ α β : ℝ) :
    oneParticleBlock (scatterMatrix θ α β) =
      Complex.exp (I * (α : ℂ)) •
        !![I * (Real.sin θ : ℂ), (Real.cos θ : ℂ);
           (Real.cos θ : ℂ), I * (Real.sin θ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneParticleBlock, scatterMatrix, Matrix.smul_apply] <;>
    ring

theorem scatterMatrix_eq_zero_of_particles_ne (θ α β : ℝ) {i k : PairState}
    (h : pairParticles i ≠ pairParticles k) : scatterMatrix θ α β i k = 0 := by
  fin_cases i <;> fin_cases k <;> simp_all [scatterMatrix, pairParticles]

theorem scatterMatrix_preserves_sector (θ α β : ℝ) (n : ℕ) (v : PairState → ℂ)
    (hv : ∀ i, v i ≠ 0 → pairParticles i = n) :
    ∀ i, (scatterMatrix θ α β *ᵥ v) i ≠ 0 → pairParticles i = n := by
  intro i hi
  by_contra hne
  apply hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : pairParticles k = n
  · rw [scatterMatrix_eq_zero_of_particles_ne θ α β (by intro h; exact hne (h.trans hk))]
    simp
  · have hvk : v k = 0 := by
      by_contra h
      exact hk (hv k h)
    rw [hvk]
    simp

end Qatlib.Papers.QCellAutomata96.MainResults
