/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.WeightedHamiltonian

/-!
# Two-site partial trace and lifted observables

`split` separates two distinct register sites from the remaining bits, allowing `reduced` to
form their two-qubit partial trace. The construction preserves density matrices, and
`lift_trace` identifies reduced expectations with expectations of lifted observables on the full
register, transporting the two-qubit correlation bound.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `reduced_density`: proves physicality of the reduced state.
* `lift_trace`: relates full-register and reduced traces.
* `global_zz_bound`: lifts the two-qubit ZZ inequality.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical ComplexOrder Kronecker
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Reduction

/-- The subtype of register sites different from both `i` and `j`. -/
abbrev Rest {n : ℕ} (i j : Fin n) := {h : Fin n // h≠i ∧ h≠j}

/-- The register bit string assembled from two selected qubit values and a bit assignment on the
remaining sites, with site `i` taking priority if the selected sites coincide. -/
def join {n : ℕ} (i j : Fin n) (p : (Fin 2×Fin 2)×(Rest i j → Bool)) : Reg n :=
  fun h => if hi : h=i then boolEquivFin2.symm p.1.1
    else if hj : h=j then boolEquivFin2.symm p.1.2 else p.2 ⟨h,hi,hj⟩

/-- The equivalence separating distinct sites `i` and `j` from the remaining register bits. -/
def split {n : ℕ} (i j : Fin n) (hij : i≠j) : Reg n ≃ (Fin 2×Fin 2)×(Rest i j → Bool) where
  toFun x := ((boolEquivFin2 (x i),boolEquivFin2 (x j)),fun h => x h.val)
  invFun := join i j
  left_inv x := by
    funext h
    by_cases hi : h=i
    · subst h
      simp [join]
    · by_cases hj : h=j
      · subst h
        simp [join,hi]
      · simp [join,hi,hj]
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · simp [join]
      · simp [join,hij.symm]
    · funext h
      simp [join,h.property.1,h.property.2]

/-- The matrix `ρ` reindexed by the two selected sites followed by the remaining register bits. -/
def reordered {n : ℕ} (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :=
  ρ.submatrix (split i j hij).symm (split i j hij).symm

/-- The two-qubit reduced matrix obtained by reordering `ρ` and tracing out all remaining sites. -/
noncomputable def reduced {n : ℕ} (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ :=
  (reordered i j hij ρ).traceRight

/-- The two-site reduction of a positive semidefinite trace-one register matrix is positive
semidefinite and has trace one. -/
theorem reduced_density {n : ℕ} (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : (reduced i j hij ρ).PosSemidef ∧ (reduced i j hij ρ).trace=1 := by
  refine ⟨?_,?_⟩
  · exact ((Matrix.posSemidef_submatrix_equiv _).mpr hρ).traceRight
  · rw [reduced,Matrix.traceRight_trace]
    change (∑ x, ρ ((split i j hij).symm x) ((split i j hij).symm x))=1
    exact (Equiv.sum_comp (split i j hij).symm (fun x => ρ x x)).trans htr

/-- The full-register operator obtained by tensoring the two-qubit matrix `A` with identity on
the remaining sites and undoing the reordering. -/
noncomputable def lift {n : ℕ} (i j : Fin n) (hij : i≠j)
    (A : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (A ⊗ₖ (1 : Matrix (Rest i j→Bool) (Rest i j→Bool) ℂ)).submatrix (split i j hij) (split i j hij)

/-- The trace of a lifted two-qubit observable against `ρ` equals its trace against the two-site
reduced matrix. -/
theorem lift_trace {n : ℕ} (i j : Fin n) (hij : i≠j)
    (A : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    (lift i j hij A*ρ).trace = (A*reduced i j hij ρ).trace := by
  have he : ρ = (reordered i j hij ρ).submatrix (split i j hij) (split i j hij) := by
    ext x y
    simp [reordered]
  conv_lhs => rw [he]
  rw [lift,Matrix.submatrix_mul_equiv]
  change (∑ x, (((A ⊗ₖ (1 : Matrix (Rest i j→Bool) (Rest i j→Bool) ℂ))*reordered i j hij ρ)
      (split i j hij x) (split i j hij x))) = _
  have hs := Equiv.sum_comp (split i j hij)
    (fun x => (((A ⊗ₖ (1 : Matrix (Rest i j→Bool) (Rest i j→Bool) ℂ))*reordered i j hij ρ) x x))
  rw [hs]
  change (((A ⊗ₖ (1 : Matrix (Rest i j→Bool) (Rest i j→Bool) ℂ))*reordered i j hij ρ).trace) = _
  rw [Matrix.trace_mul_comm,Matrix.trace_mul_kron_one_right,Matrix.trace_mul_comm]
  rfl

/-- For a physical register density matrix, the lifted ZZ expectation is at most one minus twice
the absolute mean of the lifted XX and YY expectations. This transports [Crosta et al.,
Lemma 3][CrostaSaubanereHuber2026] to any two distinct sites. -/
theorem global_zz_bound {n : ℕ} (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    ((lift i j hij Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opZZ*ρ).trace).re ≤
      1-2*|(((lift i j hij Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opXX*ρ).trace).re+
        ((lift i j hij Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.opYY*ρ).trace).re)/2| := by
  have hd := reduced_density i j hij ρ hρ htr
  simpa only [lift_trace,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrZZ,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.tParam,
    Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrXX,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.corrYY,Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.expect] using
    Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit.lemma3_zz_bound (reduced i j hij ρ) hd.1 hd.2
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Reduction
