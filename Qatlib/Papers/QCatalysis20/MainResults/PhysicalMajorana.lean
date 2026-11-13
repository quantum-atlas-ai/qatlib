/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.FiniteMajoranaWord
import Qatlib.Foundations.MatrixGeometry.AxisRotations.ComplexStructureExp

/-!
# Physical Majorana synthesis

This module selects concrete Majorana matrices at fixed spin and parity and transfers their
Clifford relations to the selected family. It identifies the trigonometric rotations with matrix
exponentials and obtains a unitary exponential word synthesizing any real unit vector. See
[VonBurgEtAl2021].

## Main statements

* `majoranaRotation_eq_exp`: For distinct anticommuting involutions, the trigonometric Majorana
  rotation equals the exponential of `θ • (γ p * γ q)`.
* `actual_physical_majorana_synthesis`: For fixed spin and parity, any real unit vector on `n +
  2` orbitals is synthesized by a unitary word of `n + 1` adjacent Majorana exponentials
  conjugating the first physical Majorana.
* `actual_physical_weighted_square`: A real unit-vector combination of physical Majoranas at
  fixed spin and parity squares to the identity.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.MatrixGeometry.AxisRotations.ComplexStructureExp

namespace Qatlib.Papers.QCatalysis20.MainResults

/-- The concrete Majorana index `2 * (2 * p + σ) + x` for orbital `p`, spin `σ`, and parity `x`. -/
def physicalIndex {N : ℕ} (σ x : Fin 2) (p : Fin N) : Fin (2*(2*N)) :=
  ⟨2*(2*p.val+σ.val)+x.val,by omega⟩

/-- For fixed spin and parity, distinct orbital indices give distinct concrete Majorana indices.
See [VonBurgEtAl2021]. -/
theorem physicalIndex_injective {N : ℕ} (σ x : Fin 2) : Function.Injective (physicalIndex (N:=N) σ x) := by
  intro p q he
  have h:=congrArg Fin.val he
  simp only [physicalIndex] at h
  exact Fin.ext (by omega)

/-- The concrete finite Majorana matrix with the specified orbital, spin, and parity. -/
def physicalMajorana {N : ℕ} (σ x : Fin 2) (p : Fin N) :
    Matrix (Reg (2*N)) (Reg (2*N)) ℂ := majorana (physicalIndex σ x p)

/-- Each selected physical Majorana matrix squares to the identity. -/
theorem physicalMajorana_sq {N : ℕ} (σ x : Fin 2) (p : Fin N) :
    physicalMajorana σ x p*physicalMajorana σ x p=1 := frozen_majorana_sq _

/-- For fixed spin and parity, physical Majorana matrices of distinct orbitals anticommute. See
[VonBurgEtAl2021]. -/
theorem physicalMajorana_anticommute {N : ℕ} (σ x : Fin 2) (p q : Fin N) (h : p≠q) :
    physicalMajorana σ x p*physicalMajorana σ x q= -(physicalMajorana σ x q*physicalMajorana σ x p) :=
  frozen_majorana_anticommute _ _ (fun he=>h (physicalIndex_injective σ x he))

/-- Each selected physical Majorana matrix is Hermitian. -/
theorem physicalMajorana_hermitian {N : ℕ} (σ x : Fin 2) (p : Fin N) :
    (physicalMajorana σ x p)ᴴ=physicalMajorana σ x p := frozen_majorana_herm _

/-- For distinct anticommuting involutions, the trigonometric Majorana rotation equals the
exponential of `θ • (γ p * γ q)`. See [VonBurgEtAl2021]. -/
theorem majoranaRotation_eq_exp {N : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (γ : Fin N→Matrix H H ℂ) (hsq : ∀p,γ p*γ p=1)
    (hanti : ∀p q,p≠q→γ p*γ q= -(γ q*γ p)) (p q : Fin N) (hpq : p≠q) (θ : ℝ) :
    majoranaRotation γ p q θ=NormedSpace.exp (θ•(γ p*γ q)) := by
  letI : NormedAlgebra ℚ (Matrix H H ℂ) := NormedAlgebra.restrictScalars ℚ ℝ (Matrix H H ℂ)
  have he := exp_square_neg_one (A:=Matrix H H ℂ) (γ p*γ q) (pairGenerator_sq γ hsq hanti p q hpq) θ
  exact he.symm

/-- The ordered product of exponentials of adjacent Majorana pair generators, with identity at
length zero. -/
def exponentialWord {H : Type*} [Fintype H] [DecidableEq H] :
    (n : ℕ)→(Fin (n+1)→Matrix H H ℂ)→(Fin n→ℝ)→Matrix H H ℂ
  | 0,_,_=>1
  | n+1,γ,θ=>NormedSpace.exp ((θ 0)•(γ 0*γ (Fin.succ 0)))*
      exponentialWord n (fun i=>γ i.succ) (fun i=>θ i.succ)

/-- Under the Clifford relations, the exponential word equals the trigonometric finite rotation
word. -/
theorem exponentialWord_eq {H : Type*} [Fintype H] [DecidableEq H]
    (n : ℕ) (γ : Fin (n+1)→Matrix H H ℂ) (hsq : ∀p,γ p*γ p=1)
    (hanti : ∀p q,p≠q→γ p*γ q= -(γ q*γ p)) (θ : Fin n→ℝ) :
    exponentialWord n γ θ=finiteWord n γ θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exponentialWord,finiteWord,← majoranaRotation_eq_exp γ hsq hanti 0 (Fin.succ 0) (by simp)]
    rw [ih (fun i=>γ i.succ) (fun i=>hsq i.succ)
      (fun i j h=>hanti i.succ j.succ (fun he=>h (Fin.succ_inj.mp he))) (fun i=>θ i.succ)]

/-- For fixed spin and parity, any real unit vector on `n + 2` orbitals is synthesized by a
unitary word of `n + 1` adjacent Majorana exponentials conjugating the first physical
Majorana. See [VonBurgEtAl2021]. -/
theorem actual_physical_majorana_synthesis (n : ℕ) (σ x : Fin 2) (u : Fin (n+2)→ℝ)
    (hu : ∑i,u i^2=1) :
    ∃θ : Fin (n+1)→ℝ,
      exponentialWord (n+1) (physicalMajorana σ x) θ∈unitaryGroup (Reg (2*(n+2))) ℂ ∧
      (exponentialWord (n+1) (physicalMajorana σ x) θ)ᴴ*physicalMajorana σ x 0*
        exponentialWord (n+1) (physicalMajorana σ x) θ=∑p,(u p:ℂ)•physicalMajorana σ x p := by
  obtain ⟨θ,hU,hc⟩:=finite_majorana_synthesis n (physicalMajorana σ x)
    (physicalMajorana_sq σ x) (physicalMajorana_anticommute σ x) (physicalMajorana_hermitian σ x) u hu
  refine ⟨θ,?_,?_⟩ <;>
    simpa only [exponentialWord_eq _ _ (physicalMajorana_sq σ x) (physicalMajorana_anticommute σ x)] using!
      (by assumption)

/-- A real unit-vector combination of physical Majoranas at fixed spin and parity squares to the
identity. See [VonBurgEtAl2021]. -/
theorem actual_physical_weighted_square (n : ℕ) (σ x : Fin 2) (u : Fin (n+2)→ℝ)
    (hu : ∑i,u i^2=1) :
    (∑p,(u p:ℂ)•physicalMajorana σ x p)*(∑p,(u p:ℂ)•physicalMajorana σ x p)=1 := by
  obtain ⟨θ,hU,hc⟩:=actual_physical_majorana_synthesis n σ x u hu
  let W:=exponentialWord (n+1) (physicalMajorana σ x) θ
  have hl : Wᴴ*W=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  have hr : W*Wᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  rw [← hc]
  change (Wᴴ*physicalMajorana σ x 0*W)*(Wᴴ*physicalMajorana σ x 0*W)=1
  calc
    _=Wᴴ*physicalMajorana σ x 0*(W*Wᴴ)*physicalMajorana σ x 0*W := by noncomm_ring
    _=Wᴴ*(physicalMajorana σ x 0*physicalMajorana σ x 0)*W := by rw [hr];noncomm_ring
    _=1 := by rw [physicalMajorana_sq,mul_one,hl]

end Qatlib.Papers.QCatalysis20.MainResults
