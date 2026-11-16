/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliCoordinates
public import Qatlib.Concepts.GibbsSource.SourceForms.NormalizedPauli
public import Qatlib.Concepts.GibbsSource.SourceForms.FullPhysicalSource

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-! One exchange cell, exact finite physical Pauli coordinates and six
complex unitary label modes. The middle columns have phase (1+i)/√2;
this gives the same exchange projectors using only Gaussian rationals. -/
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.CodingDecoding.CssTesters
open Matrix
open scoped BigOperators
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ExchangeCell
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
def phase : ℂ := (1+Complex.I)/2
def basis : Operator 4 := !![1,0,0,0;0,phase,phase,0;0,phase,-phase,0;0,0,0,1]
def mix : Fin 6→Fin 2×Fin 3→ℂ := fun p j =>
  ![![![(1:ℂ)/2, Complex.I/2,0],![1/2,Complex.I/2,0]],
    ![![1/2,Complex.I/2,0],![-1/2,-Complex.I/2,0]],
    ![![1/2,-Complex.I/2,0],![1/2,-Complex.I/2,0]],
    ![![1/2,-Complex.I/2,0],![-1/2,Complex.I/2,0]],
    ![![0,0,phase],![0,0,phase]],![![0,0,phase],![0,0,-phase]]] p j.1 j.2

def proposals : Fin 2×Fin 3→Operator 4 := fun q =>
  ![![!![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0],
      !![0,0,-Complex.I,0;0,0,0,-Complex.I;Complex.I,0,0,0;0,Complex.I,0,0],
      !![1,0,0,0;0,1,0,0;0,0,-1,0;0,0,0,-1]],
    ![!![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0],
      !![0,-Complex.I,0,0;Complex.I,0,0,0;0,0,0,-Complex.I;0,0,Complex.I,0],
      !![1,0,0,0;0,-1,0,0;0,0,1,0;0,0,0,-1]]] q.1 q.2

local macro "ecnorm" : tactic => `(tactic| norm_num [Complex.ext_iff,Complex.add_re,Complex.add_im,
  Complex.neg_re,Complex.neg_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
  Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.conj_re,Complex.conj_im])

/-- Basis unitary for the stated finite source data. -/
theorem basis_unitary : basisᴴ*basis=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis,phase,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] <;> ecnorm

def rowWitness : Fin 6→Fin 4→Fin 4 := ![![1,3,0,0],![2,0,3,0],![0,0,0,1],
  ![0,0,0,2],![0,0,0,3],![0,2,1,0]]
def colWitness : Fin 6→Fin 4→Fin 4 := ![![0,0,0,1],![0,0,0,2],![1,3,0,0],
  ![2,0,3,0],![0,0,0,3],![0,2,1,0]]

def bits : Fin 4→(Fin 2→ZMod 2) := ![![0,0],![0,1],![1,0],![1,1]]
/-- Bits bijective for the stated finite source data. -/
theorem bits_bijective : Function.Bijective bits := by decide +kernel
noncomputable def equiv : Fin 4 ≃ Fin (fullPauliDim 2) :=
  (Equiv.ofBijective bits bits_bijective).trans (regIndexEquiv (Fin 2))
/-- Eqv apply for the stated finite source data. -/
theorem eqv_apply (i : Fin 4) : equiv i = regIndexEquiv (Fin 2) (bits i) := rfl
/-- Peq for the stated finite source data. -/
theorem peq (k : Fin 2) (a b : Fin 4) :
    (equiv a = fullPauliFlip 2 k (equiv b)) ↔ bits a = bits b + Pi.single k 1 := by
  simp only [eqv_apply, fullPauliFlip, Equiv.symm_apply_apply]
  exact (regIndexEquiv (Fin 2)).injective.eq_iff
/-- Bit eq for the stated finite source data. -/
theorem bit_eq (k : Fin 2) (a : Fin 4) : fullPauliBit 2 k (equiv a)=bits a k := by
  simp [eqv_apply,fullPauliBit]

def liftAlg := Matrix.reindexAlgEquiv ℂ ℂ equiv

/-- Lift Alg apply eq for the stated finite source data. -/
theorem liftAlg_apply_eq (E : Operator 4) (a b : Fin 4) : liftAlg E (equiv a) (equiv b)=E a b := by
  simp [liftAlg,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply]

def cflip : Fin 2→Fin 4→Fin 4 := ![![2,3,0,1],![1,0,3,2]]
/-- Physical Flip table for the stated finite source data. -/
theorem physicalFlip_table (i : Fin 2) (b : Fin 4) :
    fullPauliFlip 2 i (equiv b)=equiv (cflip i b) := by
  apply Eq.symm
  apply (peq i _ b).2
  fin_cases i <;> fin_cases b <;> decide +kernel

/-- Eq If for the stated finite source data. -/
private theorem eqIf (a b : Fin 4) (z w : ℂ) :
    (if equiv a=equiv b then z else w) = if a=b then z else w := by
  by_cases h : a=b
  · subst b; simp
  · rw [ite_eq_right (equiv.injective.ne h),ite_eq_right h]

/-- Original pauli table for the stated finite source data. -/
theorem original_pauli_table (q : Fin 2×Fin 3) : fullPauliFamily 2 q=liftAlg (proposals q) := by
  ext x y
  obtain ⟨a,rfl⟩ := equiv.surjective x
  obtain ⟨b,rfl⟩ := equiv.surjective y
  rw [liftAlg_apply_eq]
  obtain ⟨i,z⟩ := q
  fin_cases z
  · change fullPauliX 2 i (equiv a) (equiv b) = _
    rw [fullPauliX_apply,physicalFlip_table]
    apply (eqIf a (cflip i b) 1 0).trans
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [cflip,proposals]
  · change fullPauliY 2 i (equiv a) (equiv b) = _
    rw [fullPauliY_apply,physicalFlip_table,bit_eq]
    apply (eqIf a (cflip i b) _ 0).trans
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [bits,cflip,proposals,phaseOfBit]
  · change fullPauliZ 2 i (equiv a) (equiv b) = _
    rw [fullPauliZ_apply,bit_eq]
    apply (eqIf a b _ 0).trans
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [bits,proposals,phaseOfBit]

def physicalBasis := liftAlg basis

/-- Lift Alg star for the stated finite source data. -/
theorem liftAlg_star (E : Operator 4) : (liftAlg E)ᴴ=liftAlg Eᴴ := by
  simp only [liftAlg,Matrix.coe_reindexAlgEquiv,Matrix.conjTranspose_reindex]

/-- Physical Basis unitary for the stated finite source data. -/
theorem physicalBasis_unitary : physicalBasisᴴ*physicalBasis=1 := by
  unfold physicalBasis
  rw [liftAlg_star,← map_mul,basis_unitary,map_one]

def physicalHamiltonian (lam : Fin (fullPauliDim 2)→ℝ) :=
  fullPhysicalHamiltonian physicalBasis lam

/-- Physical Hamiltonian hermitian for the stated finite source data. -/
theorem physicalHamiltonian_hermitian (lam : Fin (fullPauliDim 2)→ℝ) :
    (physicalHamiltonian lam).IsHermitian := by
  have hd : (Matrix.diagonal (fun i => (lam i:ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun _ => by simp [IsSelfAdjoint]
  change (physicalBasis * Matrix.diagonal (fun i => (lam i:ℂ)) * physicalBasisᴴ)ᴴ=_
  simp only [Matrix.conjTranspose_mul,conjTranspose_conjTranspose,hd.eq,Matrix.mul_assoc]
  exact (Matrix.mul_assoc _ _ _).symm

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ExchangeCell
