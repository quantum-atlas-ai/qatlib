/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.OperatorCutoff.Contraction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Finite Fock ladder operators and norm bounds

This module turns the concrete occupation-register creation and annihilation matrices into
continuous linear maps on finite Fock space. The single-mode canonical anticommutation identity
yields operator-norm bounds for each ladder operator and every finite ordered product. See
[McCleanEtAl2014].

## Main statements

* `cre_eq_adjoint`: Creation at a mode is the Hilbert-space adjoint of annihilation at that
  mode.
* `ann_norm_le_one`: The operator norm of each finite Fock annihilation map is at most one.
* `monomial_norm_le_one`: Every finite ordered ladder-operator monomial has operator norm at
  most one.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QChemistry14.NativeTrunc
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.MatrixGeometry.OperatorCutoff

/-- The complex Euclidean space indexed by the occupation register `Reg n`. -/
abbrev Fock (n : ℕ) := EuclideanSpace ℂ (Reg n)

/-- The continuous linear map on finite Fock space induced by the concrete annihilation matrix
at mode `i`. -/
def ann {n : ℕ} (i : Fin n) : Fock n →L[ℂ] Fock n :=
  Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) (annihilation i)

/-- The continuous linear map on finite Fock space induced by the concrete creation matrix at
mode `i`. -/
def cre {n : ℕ} (i : Fin n) : Fock n →L[ℂ] Fock n :=
  Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) (creation i)

/-- Creation at a mode is the Hilbert-space adjoint of annihilation at that mode. -/
theorem cre_eq_adjoint {n : ℕ} (i : Fin n) : cre i = (ann i).adjoint := by
  have hc := (g1 n).2.1 i
  unfold cre ann
  rw [hc]
  exact (map_star (Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ)) (annihilation i)).trans
    (ContinuousLinearMap.star_eq_adjoint _)

/-- Annihilation at one mode satisfies `ann i * (ann i).adjoint + (ann i).adjoint * ann i = 1`.
See [McCleanEtAl2014]. -/
theorem ann_car {n : ℕ} (i : Fin n) :
    ann i * (ann i).adjoint + (ann i).adjoint * ann i = 1 := by
  have hc := ((g1 n).1 i i).1
  simp only [ite_true] at hc
  have ht :=
      congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => Matrix.toEuclideanCLM (n := Reg n) (𝕜 := ℂ) M) hc
  simp only [map_add, map_mul, map_one] at ht
  change ann i * cre i + cre i * ann i = 1 at ht
  simpa only [cre_eq_adjoint] using! ht

/-- The operator norm of each finite Fock annihilation map is at most one. See
[McCleanEtAl2014]. -/
theorem ann_norm_le_one {n : ℕ} (i : Fin n) : ‖ann i‖ ≤ 1 :=
  car_opNorm (ann i) (ann_car i)

/-- The operator norm of each finite Fock creation map is at most one. See [McCleanEtAl2014]. -/
theorem cre_norm_le_one {n : ℕ} (i : Fin n) : ‖cre i‖ ≤ 1 := by
  rw [cre_eq_adjoint]
  have h := ann_norm_le_one i
  simpa only [ContinuousLinearMap.adjoint.norm_map] using! h

/-- Select creation when the Boolean label is true and annihilation when it is false. -/
def ladder {n : ℕ} (a : Fin n × Bool) : Fock n →L[ℂ] Fock n :=
  if a.2 then cre a.1 else ann a.1

/-- Every Boolean-labelled ladder operator has operator norm at most one. -/
theorem ladder_norm_le_one {n : ℕ} (a : Fin n × Bool) : ‖ladder a‖ ≤ 1 := by
  unfold ladder
  split
  · exact cre_norm_le_one _
  · exact ann_norm_le_one _

/-- The ordered product of the ladder operators specified by a finite list of mode and Boolean
labels. -/
def monomial {n : ℕ} (w : List (Fin n × Bool)) : Fock n →L[ℂ] Fock n :=
  (w.map ladder).prod

/-- Every finite ordered ladder-operator monomial has operator norm at most one. See
[McCleanEtAl2014]. -/
theorem monomial_norm_le_one {n : ℕ} (w : List (Fin n × Bool)) : ‖monomial w‖ ≤ 1 := by
  apply word_opNorm
  intro A hA
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hA
  exact ladder_norm_le_one a
end Qatlib.Papers.QChemistry14.NativeTrunc
