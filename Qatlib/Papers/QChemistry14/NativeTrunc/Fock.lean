/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.OperatorCutoff.Contraction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QChemistry14.NativeTrunc
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.MatrixGeometry.OperatorCutoff

abbrev Fock (n : ℕ) := EuclideanSpace ℂ (Reg n)

def ann {n : ℕ} (i : Fin n) : Fock n →L[ℂ] Fock n :=
  Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) (annihilation i)

def cre {n : ℕ} (i : Fin n) : Fock n →L[ℂ] Fock n :=
  Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) (creation i)

theorem cre_eq_adjoint {n : ℕ} (i : Fin n) : cre i = (ann i).adjoint := by
  have hc := (g1 n).2.1 i
  unfold cre ann
  rw [hc]
  exact (map_star (Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ)) (annihilation i)).trans
    (ContinuousLinearMap.star_eq_adjoint _)

theorem ann_car {n : ℕ} (i : Fin n) :
    ann i * (ann i).adjoint + (ann i).adjoint * ann i = 1 := by
  have hc := ((g1 n).1 i i).1
  simp only [ite_true] at hc
  have ht :=
      congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) M) hc
  simp only [map_add, map_mul, map_one] at ht
  change ann i * cre i + cre i * ann i = 1 at ht
  simpa only [cre_eq_adjoint] using! ht

theorem ann_norm_le_one {n : ℕ} (i : Fin n) : ‖ann i‖ ≤ 1 :=
  car_opNorm (ann i) (ann_car i)

theorem cre_norm_le_one {n : ℕ} (i : Fin n) : ‖cre i‖ ≤ 1 := by
  rw [cre_eq_adjoint]
  have h := ann_norm_le_one i
  simpa only [ContinuousLinearMap.adjoint.norm_map] using! h

def ladder {n : ℕ} (a : Fin n × Bool) : Fock n →L[ℂ] Fock n :=
  if a.2 then cre a.1 else ann a.1

theorem ladder_norm_le_one {n : ℕ} (a : Fin n × Bool) : ‖ladder a‖ ≤ 1 := by
  unfold ladder
  split
  · exact cre_norm_le_one _
  · exact ann_norm_le_one _

def monomial {n : ℕ} (w : List (Fin n × Bool)) : Fock n →L[ℂ] Fock n :=
  (w.map ladder).prod

theorem monomial_norm_le_one {n : ℕ} (w : List (Fin n × Bool)) : ‖monomial w‖ ≤ 1 := by
  apply word_opNorm
  intro A hA
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hA
  exact ladder_norm_le_one a
end Qatlib.Papers.QChemistry14.NativeTrunc
