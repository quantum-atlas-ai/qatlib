/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Nat.Log
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction

abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

structure SignedKraus (d r : ℕ) where

  K : Fin r → Op d

  α : Fin r → ℂ

  sign : ∀ i, α i = 1 ∨ α i = -1

  tracePreserving : ∑ i, α i • ((K i)ᴴ * K i) = 1

namespace SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

def action (ρ : Op d) : Op d :=
  ∑ i, D.α i • (D.K i * ρ * (D.K i)ᴴ)

def krausSum : Op d :=
  ∑ i, (D.K i)ᴴ * D.K i

def sqrtScale (γ : ℝ) : ℂ := ((Real.sqrt γ : ℂ))⁻¹

def normalizedKraus (γ : ℝ) (i : Fin r) : Op d :=
  sqrtScale γ • D.K i

def normalizedSum (γ : ℝ) : Op d :=
  ∑ i, (D.normalizedKraus γ i)ᴴ * D.normalizedKraus γ i

def completedKraus (γ : ℝ) (C : Op d) : Fin (r + 1) → Op d :=
  Fin.lastCases C (fun i => D.normalizedKraus γ i)

def postProcessingWeight (γ : ℝ) : Fin (r + 1) → ℂ :=
  Fin.lastCases 0 (fun i => (γ : ℂ) * D.α i)

def compiledMean (ρ O : Op d) : ℝ := (D.action ρ * O).trace.re

lemma sqrtScale_mul_star (γ : ℝ) (hγ : 0 < γ) :
    sqrtScale γ * star (sqrtScale γ) = ((γ : ℂ))⁻¹ := by
  unfold sqrtScale
  rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_inv, Complex.ofReal_inj, ← mul_inv, Real.mul_self_sqrt hγ.le]

lemma star_mul_sqrtScale (γ : ℝ) (hγ : 0 < γ) :
    star (sqrtScale γ) * sqrtScale γ = ((γ : ℂ))⁻¹ := by
  rw [mul_comm, sqrtScale_mul_star γ hγ]

lemma normalizedSum_eq (γ : ℝ) :
    D.normalizedSum γ = (star (sqrtScale γ) * sqrtScale γ) • D.krausSum := by
  unfold normalizedSum krausSum normalizedKraus sqrtScale
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma normalizedSum_eq_inv (γ : ℝ) (hγ : 0 < γ) :
    D.normalizedSum γ = ((γ : ℂ))⁻¹ • D.krausSum := by
  rw [D.normalizedSum_eq γ, star_mul_sqrtScale γ hγ]

@[simp] lemma completedKraus_last (γ : ℝ) (C : Op d) :
    D.completedKraus γ C (Fin.last r) = C :=
  Fin.lastCases_last

@[simp] lemma completedKraus_castSucc (γ : ℝ) (C : Op d) (i : Fin r) :
    D.completedKraus γ C i.castSucc = D.normalizedKraus γ i :=
  Fin.lastCases_castSucc i

@[simp] lemma postProcessingWeight_castSucc (γ : ℝ) (i : Fin r) :
    D.postProcessingWeight γ i.castSucc = (γ : ℂ) * D.α i :=
  Fin.lastCases_castSucc i

@[simp] lemma postProcessingWeight_last (γ : ℝ) :
    D.postProcessingWeight γ (Fin.last r) = 0 :=
  Fin.lastCases_last

theorem completedKraus_complete (γ : ℝ) {C : Op d}
    (hC : Cᴴ * C = 1 - D.normalizedSum γ) :
    Qatlib.Concepts.ChannelTheory.Stinespring.KrausComplete
      (D.completedKraus γ C) := by
  unfold Qatlib.Concepts.ChannelTheory.Stinespring.KrausComplete
  rw [Fin.sum_univ_castSucc]
  simp only [completedKraus_castSucc, completedKraus_last]
  unfold normalizedSum at hC
  rw [hC]
  abel

end SignedKraus

end Qatlib.Papers.HermitianMap26.Construction
